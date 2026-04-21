//! `ProductIdentityCollapse` — pattern-rewrites
//! `(a & m1) * (b & m1) + (c & m2) * (d & m2)` shapes by:
//!   1. trying a direct `Mul` reconstruction when shared `And` factors
//!      coincide, then
//!   2. falling back to two `SignatureState` children per valid
//!      partition assignment, joined via `ProductCollapseCont`.
//!
//! Operates on `FoldedAst` payloads and finds the first `Add(Mul, Mul)`
//! site (depth-first walk, left-to-right). Up to four assignments are
//! enumerated.

use cobra_core::arith::bitmask;
use cobra_core::classification::Classification;
use cobra_core::evaluate_boolean_signature;
use cobra_core::expr::{Expr, Kind};
use cobra_core::expr_cost::{compute_cost, is_better};
use cobra_core::pass_contract::ReasonDetail;
use cobra_core::result::Result;

use cobra_orchestrator::{
    create_group, create_join, expr_identity_hash, replace_by_hash, AstPayload, AstSolveContext,
    ContinuationData, EliminationResult, FactorRole, ItemDisposition, JoinState,
    OrchestratorContext, PassDecision, PassResult, ProductCollapseCont, ProductJoinState,
    Provenance, SignatureStatePayload, SignatureSubproblemContext, StateData, WorkItem,
};

use crate::classifier::classify_structural;
use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};

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
    i: usize,
    l: usize,
    r: usize,
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
        out.push(ProductAssignment {
            sig_x,
            sig_y,
            i,
            l,
            r,
        });
        if out.len() >= MAX_ASSIGNMENTS {
            break;
        }
    }
    out
}

/// `(a & m) * (a & n)` → `a` when both AND-terms share a factor.
fn reconstruct_masked_product_factor(
    inclusive_term: &Expr,
    exclusive_term: &Expr,
) -> Option<Box<Expr>> {
    if !matches!(inclusive_term.kind, Kind::And)
        || !matches!(exclusive_term.kind, Kind::And)
        || inclusive_term.children.len() != 2
        || exclusive_term.children.len() != 2
    {
        return None;
    }
    for lhs_child in &inclusive_term.children {
        for rhs_child in &exclusive_term.children {
            if **lhs_child == **rhs_child {
                return Some(lhs_child.clone_tree());
            }
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

fn rewrite_with_direct_candidate(
    ast: &AstPayload,
    item: &WorkItem,
    add_hash: u64,
    candidate: Box<Expr>,
) -> WorkItem {
    let mut repl = Some(candidate);
    let (rebuilt, _) = replace_by_hash(ast.expr.clone_tree(), add_hash, &mut repl);
    let new_cls = classify_structural(&rebuilt);
    let solve_ctx = ast.solve_ctx.clone();
    let mut rewritten = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
        expr: rebuilt,
        classification: Some(new_cls),
        provenance: Provenance::Rewritten,
        solve_ctx,
    })));
    rewritten.features = item.features.clone();
    rewritten.features.classification = Some(new_cls);
    rewritten.features.provenance = Provenance::Rewritten;
    rewritten.metadata = item.metadata.clone();
    rewritten.depth = item.depth;
    rewritten.rewrite_gen = item.rewrite_gen + 1;
    rewritten.attempted_mask = 0;
    rewritten.group_id = item.group_id;
    rewritten.history.clone_from(&item.history);
    rewritten
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
    let factors = [
        &site.add_node.children[0].children[0],
        &site.add_node.children[0].children[1],
        &site.add_node.children[1].children[0],
        &site.add_node.children[1].children[1],
    ];

    // Step 1: try direct Mul reconstruction.
    let mut best_direct: Option<(Box<Expr>, _)> = None;
    let chk_eval = cobra_core::evaluator::Evaluator::from_expr(site.add_node, ctx.bitwidth);
    for assign in &assignments {
        let direct_x = reconstruct_masked_product_factor(factors[assign.i], factors[assign.l]);
        let direct_y = reconstruct_masked_product_factor(factors[assign.i], factors[assign.r]);
        let (Some(dx), Some(dy)) = (direct_x, direct_y) else {
            continue;
        };
        let direct = Expr::mul(dx, dy);
        let chk = full_width_check_eval(
            &chk_eval,
            num_vars,
            &direct,
            ctx.bitwidth,
            DEFAULT_NUM_SAMPLES,
        );
        if !chk.passed {
            continue;
        }
        let cost = compute_cost(&direct).cost;
        if !is_better(&cost, &baseline_cost) {
            continue;
        }
        if let Some((_, bc)) = &best_direct {
            if !is_better(&cost, bc) {
                continue;
            }
        }
        best_direct = Some((direct, cost));
    }

    if let Some((direct, _)) = best_direct {
        let rewritten = rewrite_with_direct_candidate(ast, item, site.add_hash, direct);
        return Ok(PassResult {
            decision: PassDecision::Advance,
            disposition: ItemDisposition::ConsumeCurrent,
            next: vec![rewritten],
            reason: ReasonDetail::default(),
        });
    }

    // Step 2: fan out into ProductJoinState per assignment.
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
}
