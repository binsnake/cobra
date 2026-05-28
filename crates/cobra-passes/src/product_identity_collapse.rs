//! `ProductIdentityCollapse` — pattern-rewrites
//! `(a & m1) * (b & m1) + (c & m2) * (d & m2)` shapes by emitting two
//! `SignatureState` children per valid partition assignment, joined via
//! `ProductCollapseCont`.
//!
//! Operates on `FoldedAst` payloads and finds the first `Add(Mul, Mul)`
//! site (depth-first walk, left-to-right). Up to four assignments are
//! enumerated.

use cobra_core::arith::bitmask;
use cobra_core::classification::Classification;
use cobra_core::evaluate_boolean_signature;
use cobra_core::expr::{Expr, Kind};
use cobra_core::expr_cost::compute_cost;
use cobra_core::pass_contract::ReasonDetail;
use cobra_core::result::Result;

use cobra_orchestrator::{
    create_group, create_join, expr_identity_hash, AstSolveContext, ContinuationData,
    EliminationResult, FactorRole, ItemDisposition, JoinState, OrchestratorContext, PassDecision,
    PassResult, ProductCollapseCont, ProductJoinState, SignatureStatePayload,
    SignatureSubproblemContext, StateData, WorkItem,
};

const MAX_ASSIGNMENTS: usize = 4;

struct ProductSite<'a> {
    add_node: &'a Expr,
    add_hash: u64,
}

fn find_first_product_site(root: &Expr) -> Option<ProductSite<'_>> {
    if matches!(root.kind, Kind::Add) && root.children.len() == 2 {
        let lhs_mul2 =
            matches!(root.children[0].kind, Kind::Mul) && root.children[0].children.len() == 2;
        let rhs_mul2 =
            matches!(root.children[1].kind, Kind::Mul) && root.children[1].children.len() == 2;
        if lhs_mul2 && rhs_mul2 {
            return Some(ProductSite {
                add_node: root,
                add_hash: expr_identity_hash(root),
            });
        }
    }
    for child in &root.children {
        if let Some(s) = find_first_product_site(child) {
            return Some(s);
        }
    }
    None
}

#[derive(Clone)]
struct ProductAssignment {
    sig_x: Vec<u64>,
    sig_y: Vec<u64>,
}

/// 8 role assignments over the 4 factors `[L0, L1, R0, R1]`.
const ASSIGNMENTS: [(usize, usize, usize, usize); 8] = [
    (0, 1, 2, 3),
    (1, 0, 2, 3),
    (0, 1, 3, 2),
    (1, 0, 3, 2),
    (2, 3, 0, 1),
    (3, 2, 0, 1),
    (2, 3, 1, 0),
    (3, 2, 1, 0),
];

fn enumerate_valid_assignments(
    add_node: &Expr,
    num_vars: u32,
    bitwidth: u32,
) -> Vec<ProductAssignment> {
    let sig_len: usize = 1 << num_vars;
    let mask = bitmask(bitwidth);

    let factors = [
        &add_node.children[0].children[0],
        &add_node.children[0].children[1],
        &add_node.children[1].children[0],
        &add_node.children[1].children[1],
    ];
    let sigs: Vec<Vec<u64>> = factors
        .iter()
        .map(|f| evaluate_boolean_signature(f, num_vars, bitwidth))
        .collect();

    let mut out: Vec<ProductAssignment> = Vec::new();
    for &(i, o, l, r) in &ASSIGNMENTS {
        let sig_i = &sigs[i];
        let sig_o = &sigs[o];
        let sig_l = &sigs[l];
        let sig_r = &sigs[r];

        let mut ok = true;
        for j in 0..sig_len {
            let mi = sig_i[j] & mask;
            let mo = sig_o[j] & mask;
            let ml = sig_l[j] & mask;
            let mr = sig_r[j] & mask;
            if ((mi & ml) | (mi & mr) | (ml & mr)) != 0 {
                ok = false;
                break;
            }
            if mo != (mi | ml | mr) {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        let sig_x: Vec<u64> = (0..sig_len).map(|j| (sig_i[j] | sig_l[j]) & mask).collect();
        let sig_y: Vec<u64> = (0..sig_len).map(|j| (sig_i[j] | sig_r[j]) & mask).collect();
        out.push(ProductAssignment { sig_x, sig_y });
        if out.len() >= MAX_ASSIGNMENTS {
            break;
        }
    }
    out
}

/// `(a & m) * (a & n)` → `a` when both AND-terms share a factor.
fn active_ast_vars(item: &WorkItem, ctx: &OrchestratorContext) -> Vec<String> {
    if let StateData::FoldedAst(ast) = &item.payload {
        if let Some(sc) = &ast.solve_ctx {
            return sc.vars.clone();
        }
    }
    ctx.original_vars.clone()
}

#[allow(clippy::unnecessary_wraps, clippy::too_many_lines)]
pub fn run_product_identity_collapse(
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

    let Some(site) = find_first_product_site(&ast.expr) else {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let active_vars = active_ast_vars(item, ctx);
    let num_vars = active_vars.len() as u32;

    let assignments = enumerate_valid_assignments(site.add_node, num_vars, ctx.bitwidth);
    if assignments.is_empty() {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    let baseline_cost = compute_cost(site.add_node).cost;

    // Direct product reconstruction is only a Boolean-signature identity for
    // some mask partitions, not a full 64-bit endpoint identity. Keep this
    // pass on the verified path by emitting child signature subproblems and
    // letting `ResolveCompetition` produce replayed source-signature evidence.
    let solve_ctx = ast.solve_ctx.as_ref();
    let solve_ctx_vars = solve_ctx.map(|s| s.vars.clone()).unwrap_or_default();
    let solve_ctx_evaluator = solve_ctx.and_then(|s| s.evaluator.clone());
    let solve_ctx_input_sig = solve_ctx.map(|s| s.input_sig.clone()).unwrap_or_default();
    let has_solve_ctx = solve_ctx.is_some();

    let mut next: Vec<WorkItem> = Vec::new();
    let indices: Vec<u32> = (0..num_vars).collect();
    for assign in assignments {
        let join = ProductJoinState {
            x_winner: None,
            y_winner: None,
            x_resolved: false,
            y_resolved: false,
            original_expr: site.add_node.clone_tree(),
            baseline_cost,
            vars: active_vars.clone(),
            parent_group_id: item.group_id,
            has_solve_ctx,
            solve_ctx_vars: solve_ctx_vars.clone(),
            solve_ctx_evaluator: solve_ctx_evaluator.clone(),
            solve_ctx_input_sig: solve_ctx_input_sig.clone(),
            bitwidth: ctx.bitwidth,
            parent_depth: item.depth,
            rewrite_gen: item.rewrite_gen,
            parent_history: item.history.clone(),
            full_ast: ast.expr.clone_tree(),
            target_hash: site.add_hash,
        };
        let join_id = create_join(
            &mut ctx.join_states,
            &mut ctx.next_join_id,
            JoinState::Product(Box::new(join)),
        );

        let mut emit_factor = |sig: Vec<u64>, role: FactorRole, ctx: &mut OrchestratorContext| {
            let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
            ctx.competition_groups
                .get_mut(&group_id)
                .expect("group just created")
                .continuation = Some(ContinuationData::ProductCollapse(ProductCollapseCont {
                join_id,
                role,
            }));

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
                    original_indices: indices.clone(),
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

        emit_factor(assign.sig_x, FactorRole::X, ctx);
        emit_factor(assign.sig_y, FactorRole::Y, ctx);
    }

    let _ = AstSolveContext::default;
    let _ = Classification::default;

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
    fn no_product_site_returns_no_progress() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        let item = mk_ast_item(Expr::variable(0));
        let pr = run_product_identity_collapse(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
    }

    #[test]
    fn add_of_two_muls_with_no_partition_misses() {
        // (x*y) + (a*b) — overlapping non-bitwise factors, no
        // disjoint-mask partition is valid.
        let mut ctx = OrchestratorContext::new(
            Options::default(),
            vec!["a".into(), "b".into(), "x".into(), "y".into()],
            64,
        );
        let expr = Expr::add(
            Expr::mul(Expr::variable(2), Expr::variable(3)),
            Expr::mul(Expr::variable(0), Expr::variable(1)),
        );
        let item = mk_ast_item(expr);
        let pr = run_product_identity_collapse(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
    }

    #[test]
    fn fanout_clears_stale_proof_metadata() {
        let expr = Expr::add(
            Expr::mul(
                Expr::and(Expr::variable(0), Expr::variable(1)),
                Expr::or(Expr::variable(0), Expr::variable(1)),
            ),
            Expr::mul(
                Expr::and(Expr::variable(0), Expr::not(Expr::variable(1))),
                Expr::and(Expr::not(Expr::variable(0)), Expr::variable(1)),
            ),
        );
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let mut item = mk_ast_item(expr);
        item.metadata.lean_certificate = Some(cobra_orchestrator::LeanCertificate::new(
            64,
            Expr::variable(0),
            Expr::variable(0),
        ));
        item.metadata.lean_signature_certificate =
            cobra_orchestrator::LeanSignatureCertificate::new(64, 1, vec![0, 1], Expr::variable(0));

        let pr = run_product_identity_collapse(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        assert_eq!(pr.disposition, ItemDisposition::ConsumeCurrent);
        assert!(!pr.next.is_empty());
        for child in pr.next {
            assert!(matches!(child.payload, StateData::Signature(_)));
            assert!(child.metadata.lean_certificate.is_none());
            assert!(child.metadata.lean_signature_certificate.is_none());
        }
    }
}
