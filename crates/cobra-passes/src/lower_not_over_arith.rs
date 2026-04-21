//! `RunLowerNotOverArith` pass. Rewrites every `~(arith)` subtree into
//!
//! - Only fires on `FoldedAst` items with `Provenance::Original`.
//! - When no `~(arith)` exists the pass is a retained no-op
//!   (`NoProgress` + `RetainCurrent`) so the scheduler moves on.
//! - When lowering fires, emits a new `FoldedAst` item with
//!   `Provenance::Lowered`, re-runs `EvaluateBooleanSignature` over the
//!   rewritten tree, and stashes the new signature in
//!   `metadata.sig_vector`. The current item is retained (the scheduler
//!   also wants to keep the original around for a potential semilinear
//!   pathway).

use cobra_core::pass_contract::ReasonDetail;
use cobra_core::result::Result;
use cobra_core::signature_eval::evaluate_boolean_signature;

use cobra_orchestrator::{
    AstPayload, ItemDisposition, OrchestratorContext, PassDecision, PassResult, Provenance,
    StateData, WorkItem,
};

use crate::not_over_arith::{has_not_over_arith, lower_not_over_arith};

#[allow(clippy::unnecessary_wraps)]
pub fn run_lower_not_over_arith(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::FoldedAst(ast) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    if ast.provenance != Provenance::Original {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    if !has_not_over_arith(&ast.expr) {
        // Nothing to lower — signal no progress, leave the item for
        // subsequent passes.
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    let lowered_expr = lower_not_over_arith(ast.expr.clone_tree(), ctx.bitwidth);

    // Recompute the Boolean signature over the lowered tree. The number
    // of variables is taken from the solve_ctx when present, else from
    // the outer context.
    let num_vars = match ast.solve_ctx.as_ref() {
        Some(sc) => sc.vars.len() as u32,
        None => ctx.original_vars.len() as u32,
    };
    let new_sig = evaluate_boolean_signature(&lowered_expr, num_vars, ctx.bitwidth);

    let mut new_solve_ctx = ast.solve_ctx.clone();
    if let Some(sc) = new_solve_ctx.as_mut() {
        sc.input_sig.clone_from(&new_sig);
    }

    let new_payload = AstPayload {
        expr: lowered_expr,
        classification: ast.classification,
        provenance: Provenance::Lowered,
        solve_ctx: new_solve_ctx,
    };

    let mut new_item = item.clone();
    new_item.payload = StateData::FoldedAst(Box::new(new_payload));
    new_item.features.provenance = Provenance::Lowered;
    new_item.metadata.sig_vector = new_sig;

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::RetainCurrent,
        next: vec![new_item],
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard: only fires on `FoldedAst` items with
/// `Provenance::Original`.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(&item.payload, StateData::FoldedAst(ast) if ast.provenance == Provenance::Original)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::expr::{Expr, Kind};
    use cobra_core::simplify_outcome::Options;

    fn mk_ast_item(e: Box<Expr>, prov: Provenance) -> WorkItem {
        let mut item = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
            expr: e,
            classification: None,
            provenance: prov,
            solve_ctx: None,
        })));
        item.features.provenance = prov;
        item
    }

    #[test]
    fn noop_when_no_not_over_arith() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        // Plain x + 1 has no Not anywhere.
        let item = mk_ast_item(
            Expr::add(Expr::variable(0), Expr::constant(1)),
            Provenance::Original,
        );
        let pr = run_lower_not_over_arith(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
        assert_eq!(pr.disposition, ItemDisposition::RetainCurrent);
        assert!(pr.next.is_empty());
    }

    #[test]
    fn not_applicable_on_non_original_provenance() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        // Even if the tree has Not-over-arith, Lowered provenance declines.
        let item = mk_ast_item(
            Expr::not(Expr::add(Expr::variable(0), Expr::constant(1))),
            Provenance::Lowered,
        );
        let pr = run_lower_not_over_arith(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NotApplicable);
    }

    #[test]
    fn lowering_fires_and_stamps_new_sig_on_metadata() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 8);
        let item = mk_ast_item(
            Expr::not(Expr::add(Expr::variable(0), Expr::constant(1))),
            Provenance::Original,
        );
        let pr = run_lower_not_over_arith(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        assert_eq!(pr.disposition, ItemDisposition::RetainCurrent);
        assert_eq!(pr.next.len(), 1);

        let emitted = &pr.next[0];
        // New item has Lowered provenance stamped on both places.
        if let StateData::FoldedAst(ast) = &emitted.payload {
            assert_eq!(ast.provenance, Provenance::Lowered);
            // Top-level node is Add (since ~(x+1) lowered to Add(Neg(x+1), 0xFF))
            assert!(matches!(ast.expr.kind, Kind::Add));
        } else {
            panic!("expected FoldedAst payload");
        }
        assert_eq!(emitted.features.provenance, Provenance::Lowered);

        // sig_vector populated; signatures equal between original and
        // lowered expressions (semantics preserved).
        let original = Expr::not(Expr::add(Expr::variable(0), Expr::constant(1)));
        let original_sig = cobra_core::evaluate_boolean_signature(&original, 1, 8);
        assert_eq!(emitted.metadata.sig_vector, original_sig);
    }
}
