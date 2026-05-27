//! `OperandSimplify` — fan-out pass that locates the first
//! variable-dependent `Mul` whose operands carry non-leaf bitwise
//! structure and emits per-operand `SignatureState` children. The
//! results are stitched back via `OperandRewriteCont` in
//! `ResolveCompetition`.
//!
//! Operates on `FoldedAst` payloads. Each `Mul(L, R)` is examined
//! once; when both sides carry variables and at least one has bitwise
//! structure that admits independent simplification, the pass spawns:
//!
//! - one child per bitwise side (LHS / RHS), and
//! - a shared `OperandJoinState` whose `lhs_resolved` /
//!   `rhs_resolved` flags are pre-set for any non-bitwise side, so the
//!   join can converge once the spawned side closes.

use cobra_core::evaluate_boolean_signature;
use cobra_core::expr::{Expr, Kind};
use cobra_core::expr_cost::compute_cost;
use cobra_core::expr_rewrite::has_nonleaf_bitwise;
use cobra_core::expr_utils::has_var_dep;
use cobra_core::pass_contract::ReasonDetail;
use cobra_core::result::Result;

use cobra_orchestrator::{
    create_group, create_join, expr_identity_hash, ContinuationData, EliminationResult,
    ItemDisposition, JoinState, OperandJoinState, OperandRewriteCont, OperandRole,
    OrchestratorContext, PassDecision, PassResult, SignatureStatePayload,
    SignatureSubproblemContext, StateData, WorkItem,
};

struct OperandSite<'a> {
    mul: &'a Expr,
    mul_hash: u64,
    lhs_bitwise: bool,
    rhs_bitwise: bool,
}

fn find_first_operand_site(root: &Expr) -> Option<OperandSite<'_>> {
    if matches!(root.kind, Kind::Mul) && root.children.len() == 2 {
        let lhs_vd = has_var_dep(&root.children[0]);
        let rhs_vd = has_var_dep(&root.children[1]);
        if lhs_vd && rhs_vd {
            let lhs_bw = has_nonleaf_bitwise(&root.children[0]);
            let rhs_bw = has_nonleaf_bitwise(&root.children[1]);
            if lhs_bw || rhs_bw {
                return Some(OperandSite {
                    mul: root,
                    mul_hash: expr_identity_hash(root),
                    lhs_bitwise: lhs_bw,
                    rhs_bitwise: rhs_bw,
                });
            }
        }
    }
    for child in &root.children {
        if let Some(s) = find_first_operand_site(child) {
            return Some(s);
        }
    }
    None
}

fn active_ast_vars(item: &WorkItem, ctx: &OrchestratorContext) -> Vec<String> {
    if let StateData::FoldedAst(ast) = &item.payload {
        if let Some(sc) = &ast.solve_ctx {
            return sc.vars.clone();
        }
    }
    ctx.original_vars.clone()
}

#[allow(clippy::unnecessary_wraps, clippy::too_many_lines)]
pub fn run_operand_simplify(item: &WorkItem, ctx: &mut OrchestratorContext) -> Result<PassResult> {
    let StateData::FoldedAst(ast) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let Some(site) = find_first_operand_site(&ast.expr) else {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let active_vars = active_ast_vars(item, ctx);
    let num_vars = active_vars.len() as u32;
    let baseline_cost = compute_cost(site.mul).cost;

    let solve_ctx = ast.solve_ctx.as_ref();
    let mut join = OperandJoinState {
        lhs_winner: None,
        rhs_winner: None,
        lhs_resolved: false,
        rhs_resolved: false,
        full_ast: ast.expr.clone_tree(),
        original_mul: site.mul.clone_tree(),
        target_hash: site.mul_hash,
        baseline_cost,
        vars: active_vars.clone(),
        parent_group_id: item.group_id,
        has_solve_ctx: solve_ctx.is_some(),
        solve_ctx_vars: solve_ctx.map(|s| s.vars.clone()).unwrap_or_default(),
        solve_ctx_evaluator: solve_ctx.and_then(|s| s.evaluator.clone()),
        solve_ctx_input_sig: solve_ctx.map(|s| s.input_sig.clone()).unwrap_or_default(),
        bitwidth: ctx.bitwidth,
        parent_depth: item.depth,
        rewrite_gen: item.rewrite_gen,
        parent_history: item.history.clone(),
    };
    // Pre-resolve sides we won't spawn a child for.
    if !site.lhs_bitwise {
        join.lhs_resolved = true;
    }
    if !site.rhs_bitwise {
        join.rhs_resolved = true;
    }

    let join_id = create_join(
        &mut ctx.join_states,
        &mut ctx.next_join_id,
        JoinState::Operand(Box::new(join)),
    );

    let mut next: Vec<WorkItem> = Vec::new();
    let mut emit_child = |operand: &Expr, role: OperandRole, ctx: &mut OrchestratorContext| {
        let sig = evaluate_boolean_signature(operand, num_vars, ctx.bitwidth);
        let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        ctx.competition_groups
            .get_mut(&group_id)
            .expect("group just created")
            .continuation = Some(ContinuationData::OperandRewrite(OperandRewriteCont {
            join_id,
            role,
        }));

        let indices: Vec<u32> = (0..num_vars).collect();
        let elim = EliminationResult {
            reduced_sig: sig.clone(),
            real_vars: active_vars.clone(),
            spurious_vars: Vec::new(),
        };
        let mut child = WorkItem::new(StateData::Signature(Box::new(SignatureStatePayload {
            ctx: SignatureSubproblemContext {
                sig,
                real_vars: active_vars.clone(),
                elimination: elim,
                original_indices: indices,
                needs_original_space_verification: false,
            },
        })));
        child.features = item.features.clone();
        child.metadata = item.metadata.clone();
        child.metadata.lean_certificate = None;
        child.metadata.lean_signature_certificate = None;
        child.depth = item.depth;
        child.rewrite_gen = item.rewrite_gen;
        child.attempted_mask = item.attempted_mask;
        child.group_id = Some(group_id);
        child.history.clone_from(&item.history);
        next.push(child);
    };

    if site.lhs_bitwise {
        emit_child(&site.mul.children[0], OperandRole::Lhs, ctx);
    }
    if site.rhs_bitwise {
        emit_child(&site.mul.children[1], OperandRole::Rhs, ctx);
    }

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::ConsumeCurrent,
        next,
        reason: ReasonDetail::default(),
    })
}

#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::FoldedAst(_))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluator::Evaluator;
    use cobra_core::simplify_outcome::Options;
    use cobra_orchestrator::{AstPayload, Provenance};

    fn mk_ast_item(expr: Box<Expr>) -> WorkItem {
        WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
            expr,
            classification: None,
            provenance: Provenance::Original,
            solve_ctx: None,
        })))
    }

    #[test]
    fn no_mul_returns_no_progress() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let expr = Expr::add(Expr::variable(0), Expr::variable(1));
        let item = mk_ast_item(expr);
        let pr = run_operand_simplify(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
    }

    #[test]
    fn mul_with_leaf_operands_returns_no_progress() {
        // x * y — both leaves, no bitwise structure.
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let expr = Expr::mul(Expr::variable(0), Expr::variable(1));
        let item = mk_ast_item(expr);
        let pr = run_operand_simplify(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
    }

    #[test]
    fn mul_with_bitwise_lhs_emits_one_child() {
        // (x ^ y) * z — LHS has bitwise structure, RHS is a leaf.
        let mut ctx = OrchestratorContext::new(
            Options::default(),
            vec!["x".into(), "y".into(), "z".into()],
            64,
        );
        ctx.evaluator = Some(Evaluator::from_expr(
            &Expr::mul(
                Expr::xor(Expr::variable(0), Expr::variable(1)),
                Expr::variable(2),
            ),
            64,
        ));
        let expr = Expr::mul(
            Expr::xor(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        let item = mk_ast_item(expr);
        let pr = run_operand_simplify(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        assert_eq!(pr.next.len(), 1);
        // The join state must mark the RHS as already-resolved.
        let join_id = ctx.next_join_id - 1;
        let JoinState::Operand(j) = &ctx.join_states[&join_id] else {
            panic!("expected operand join")
        };
        assert!(j.rhs_resolved);
        assert!(!j.lhs_resolved);
    }

    #[test]
    fn mul_with_two_bitwise_sides_emits_two_children() {
        // (x ^ y) * (a | b).
        let mut ctx = OrchestratorContext::new(
            Options::default(),
            vec!["a".into(), "b".into(), "x".into(), "y".into()],
            64,
        );
        let expr = Expr::mul(
            Expr::xor(Expr::variable(2), Expr::variable(3)),
            Expr::or(Expr::variable(0), Expr::variable(1)),
        );
        ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
        let item = mk_ast_item(expr);
        let pr = run_operand_simplify(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        assert_eq!(pr.next.len(), 2);
        let join_id = ctx.next_join_id - 1;
        let JoinState::Operand(j) = &ctx.join_states[&join_id] else {
            panic!("expected operand join")
        };
        assert!(!j.lhs_resolved);
        assert!(!j.rhs_resolved);
    }
}
