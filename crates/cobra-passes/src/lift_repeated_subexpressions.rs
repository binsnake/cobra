//! `LiftRepeatedSubexpressions` — finds non-leaf subtrees that occur
//! at least twice and have ≥4 nodes each, picks a non-overlapping
//! greedy subset bounded by the variable budget, and emits a
//! `LiftedSkeletonPayload` with one virtual variable per selected
//! subtree.

use std::collections::HashMap;

use cobra_core::pass_contract::ReasonDetail;
use cobra_core::result::Result;

use cobra_orchestrator::{
    AstSolveContext, ItemDisposition, LiftedSkeletonPayload, LiftedValueKind, OrchestratorContext,
    PassDecision, PassResult, StateData, WorkItem,
};

use crate::lifting::{
    allocate_fresh_virtual_names, baseline_cost, boolean_signature, collect_non_leaf_subtrees,
    count_nodes, is_ancestor_of, make_binding, replace_repeats_with_virtual, DeduplicatedAtom,
    RepeatEntry, MAX_LIFTABLE_NODES, MIN_REPEAT_SIZE,
};

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

#[allow(clippy::unnecessary_wraps, clippy::too_many_lines)]
pub fn run_lift_repeated_subexpressions(
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

    if count_nodes(&ast.expr) > MAX_LIFTABLE_NODES {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    let mut by_hash: HashMap<u64, Vec<usize>> = HashMap::new();
    let mut entries: Vec<RepeatEntry<'_>> = Vec::new();
    let mut preorder: u32 = 0;
    collect_non_leaf_subtrees(&ast.expr, &mut preorder, &mut by_hash, &mut entries);

    let mut viable: Vec<&RepeatEntry<'_>> = entries
        .iter()
        .filter(|e| e.count >= 2 && e.size >= MIN_REPEAT_SIZE)
        .collect();
    if viable.is_empty() {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    // Sort by impact: benefit = (count - 1) * size, then larger size,
    // deeper preorder, higher count.
    viable.sort_by(|a, b| {
        let ba = u64::from(a.count - 1) * u64::from(a.size);
        let bb = u64::from(b.count - 1) * u64::from(b.size);
        bb.cmp(&ba)
            .then_with(|| b.size.cmp(&a.size))
            .then_with(|| b.first_preorder.cmp(&a.first_preorder))
            .then_with(|| b.count.cmp(&a.count))
    });

    let var_budget = ctx.opts.max_vars.saturating_sub(original_var_count) as usize;

    let mut selected: Vec<&RepeatEntry<'_>> = Vec::new();
    for cand in viable {
        if selected.len() >= var_budget {
            break;
        }
        let overlaps = selected.iter().any(|sel| {
            is_ancestor_of(sel.first_occurrence, cand.first_occurrence)
                || is_ancestor_of(cand.first_occurrence, sel.first_occurrence)
        });
        if !overlaps {
            selected.push(cand);
        }
    }

    if selected.is_empty() {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    let atoms: Vec<DeduplicatedAtom<'_>> = selected
        .iter()
        .enumerate()
        .map(|(i, sel)| DeduplicatedAtom {
            subtree: sel.first_occurrence,
            hash: sel.hash,
            rendered: cobra_core::expr::render(sel.first_occurrence, &vars, ctx.bitwidth),
            virtual_index: original_var_count + i as u32,
        })
        .collect();

    let outer_expr = replace_repeats_with_virtual(&ast.expr, &atoms, &vars, ctx.bitwidth);
    let mut outer_vars = vars.clone();
    let virtual_names = allocate_fresh_virtual_names(&vars, "r", atoms.len());
    outer_vars.extend(virtual_names);

    let bindings = atoms
        .iter()
        .map(|a| make_binding(a, LiftedValueKind::RepeatedSubexpression))
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
    skel_item.metadata.lean_certificate = None;
    skel_item.metadata.lean_signature_certificate = None;
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
    fn no_repeats_returns_not_applicable() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let item = mk_ast_item(Expr::add(Expr::variable(0), Expr::variable(1)));
        let pr = run_lift_repeated_subexpressions(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NotApplicable);
    }

    #[test]
    fn lifts_a_repeated_4node_subtree() {
        // ((x ^ y) | z) + ((x ^ y) | z) — the (x ^ y | z) subtree of size
        // 4 occurs twice, so it gets lifted to a virtual variable.
        let mut ctx = OrchestratorContext::new(
            Options::default(),
            vec!["x".into(), "y".into(), "z".into()],
            64,
        );
        let inner1 = Expr::or(
            Expr::xor(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        let inner2 = Expr::or(
            Expr::xor(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        let item = mk_ast_item(Expr::add(inner1, inner2));
        let pr = run_lift_repeated_subexpressions(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        let StateData::LiftedSkeleton(skel) = &pr.next[0].payload else {
            panic!("expected LiftedSkeleton")
        };
        assert!(!skel.bindings.is_empty());
    }
}
