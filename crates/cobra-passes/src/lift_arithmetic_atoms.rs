//! `LiftArithmeticAtoms` — finds pure-arithmetic subtrees sitting
//! directly under bitwise parents, replaces each unique one with a
//! virtual variable, and emits a `LiftedSkeletonPayload` so the outer
//! (now smaller) bitwise problem is re-solved by the rest of the
//! pipeline. `ResolveCompetition` substitutes the original arithmetic
//! atoms back in once the outer winner is known.

use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame,
};
use cobra_core::result::Result;

use cobra_orchestrator::{
    AstSolveContext, ItemDisposition, LiftedSkeletonPayload, LiftedValueKind, OrchestratorContext,
    PassDecision, PassResult, StateData, WorkItem,
};

use crate::lifting::{
    allocate_fresh_virtual_names, baseline_cost, boolean_signature, collect_liftable_atoms,
    deduplicate_atoms, is_bitwise_kind, make_binding, replace_atoms_with_virtual,
};

fn resource_limit(msg: String) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category: ReasonCategory::ResourceLimit,
                domain: ReasonDomain::Orchestrator,
                subcode: 0,
            },
            message: msg,
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

fn active_ast_vars(item: &WorkItem, ctx: &OrchestratorContext) -> Vec<String> {
    if let StateData::FoldedAst(ast) = &item.payload {
        if let Some(sc) = &ast.solve_ctx {
            return sc.vars.clone();
        }
    }
    ctx.original_vars.clone()
}

fn active_ast_evaluator(
    item: &WorkItem,
    ctx: &OrchestratorContext,
) -> Option<cobra_core::evaluator::Evaluator> {
    if let StateData::FoldedAst(ast) = &item.payload {
        if let Some(sc) = &ast.solve_ctx {
            return sc.evaluator.clone();
        }
    }
    ctx.evaluator.clone()
}

#[allow(clippy::unnecessary_wraps)]
pub fn run_lift_arithmetic_atoms(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::FoldedAst(ast) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let vars = active_ast_vars(item, ctx);
    let active_eval = active_ast_evaluator(item, ctx);
    let original_var_count = vars.len() as u32;

    let mut candidates = Vec::new();
    let root_is_bitwise = is_bitwise_kind(&ast.expr.kind);
    for child in &ast.expr.children {
        collect_liftable_atoms(child, root_is_bitwise, &vars, ctx.bitwidth, &mut candidates);
    }
    if candidates.is_empty() {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    let atoms = deduplicate_atoms(&candidates, original_var_count);
    let total_vars = original_var_count + atoms.len() as u32;
    if total_vars > ctx.opts.max_vars {
        return Ok(PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: resource_limit(format!(
                "Lifting would exceed max_vars ({total_vars} > {})",
                ctx.opts.max_vars
            )),
        });
    }

    let outer_expr = replace_atoms_with_virtual(&ast.expr, false, &atoms, &vars, ctx.bitwidth);
    let mut outer_vars = vars.clone();
    let virtual_names = allocate_fresh_virtual_names(&vars, "v", atoms.len());
    outer_vars.extend(virtual_names);

    let bindings = atoms
        .iter()
        .map(|a| make_binding(a, LiftedValueKind::ArithmeticAtom))
        .collect();

    let outer_num_vars = outer_vars.len() as u32;
    let outer_sig = boolean_signature(&outer_expr, outer_num_vars, ctx.bitwidth);
    let source_sig = boolean_signature(&ast.expr, original_var_count, ctx.bitwidth);
    let baseline = baseline_cost(&ast.expr);

    let mut skel_item = WorkItem::new(StateData::LiftedSkeleton(Box::new(LiftedSkeletonPayload {
        outer_expr,
        outer_ctx: AstSolveContext {
            vars: outer_vars,
            evaluator: None,
            input_sig: outer_sig,
        },
        bindings,
        original_var_count,
        baseline_cost: baseline,
        source_sig,
        original_ctx: AstSolveContext {
            vars,
            evaluator: active_eval,
            input_sig: Vec::new(),
        },
    })));
    skel_item.features = item.features.clone();
    skel_item.metadata = item.metadata.clone();
    skel_item.depth = item.depth;
    skel_item.rewrite_gen = item.rewrite_gen;
    skel_item.history.clone_from(&item.history);

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::RetainCurrent,
        next: vec![skel_item],
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
    use cobra_core::expr::Expr;
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
    fn no_arithmetic_inside_bitwise_returns_not_applicable() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let item = mk_ast_item(Expr::and(Expr::variable(0), Expr::variable(1)));
        let pr = run_lift_arithmetic_atoms(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NotApplicable);
    }

    #[test]
    fn arithmetic_inside_bitwise_lifts_and_emits_skeleton() {
        // (x + y) & z — `x + y` is a pure-arithmetic, var-dependent subtree
        // sitting directly under an `And`. Lifting replaces it with v0.
        let mut ctx = OrchestratorContext::new(
            Options::default(),
            vec!["x".into(), "y".into(), "z".into()],
            64,
        );
        let expr = Expr::and(
            Expr::add(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        let item = mk_ast_item(expr);
        let pr = run_lift_arithmetic_atoms(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        assert_eq!(pr.next.len(), 1);
        let StateData::LiftedSkeleton(skel) = &pr.next[0].payload else {
            panic!("expected LiftedSkeleton")
        };
        assert_eq!(skel.bindings.len(), 1);
        assert_eq!(skel.outer_ctx.vars.len(), 4); // 3 originals + 1 virtual
        assert_eq!(skel.bindings[0].outer_var_index, 3);
    }

    #[test]
    fn duplicate_atoms_share_one_binding() {
        // `(x+y) & (x+y) | z` — the two `x+y` subtrees deduplicate to a
        // single virtual variable.
        let mut ctx = OrchestratorContext::new(
            Options::default(),
            vec!["x".into(), "y".into(), "z".into()],
            64,
        );
        let xy = Expr::add(Expr::variable(0), Expr::variable(1));
        let xy2 = Expr::add(Expr::variable(0), Expr::variable(1));
        let expr = Expr::or(Expr::and(xy, xy2), Expr::variable(2));
        let item = mk_ast_item(expr);
        let pr = run_lift_arithmetic_atoms(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        let StateData::LiftedSkeleton(skel) = &pr.next[0].payload else {
            panic!("expected LiftedSkeleton")
        };
        assert_eq!(skel.bindings.len(), 1);
    }
}
