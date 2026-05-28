//! `PrepareLiftedOuterSolve` — consumes a `LiftedSkeletonPayload`,
//! creates a new competition group with a `LiftedSubstituteCont`,
//! pre-simplifies the outer expression with the pattern-table
//! collapser, builds a proper outer evaluator, and emits a
//! `Rewritten`-provenance AST child for the rest of the pipeline to
//! solve.
//!
//! On resolution `ResolveCompetition` substitutes the lifted bindings
//! back into the winning outer expression to recover a candidate in
//! the original variable space.

use cobra_core::evaluator::Evaluator;
use cobra_core::pass_contract::ReasonDetail;
use cobra_core::result::Result;

use cobra_orchestrator::{
    create_group, AstPayload, ContinuationData, ItemDisposition, LiftedSubstituteCont,
    OrchestratorContext, PassDecision, PassResult, Provenance, StateData, WorkItem,
};

use crate::classifier::classify_structural;
use crate::pattern_matcher::simplify_pattern_subtrees_certified;

#[allow(clippy::unnecessary_wraps)]
pub fn run_prepare_lifted_outer_solve(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::LiftedSkeleton(skel) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let group_id = create_group(
        &mut ctx.competition_groups,
        &mut ctx.next_group_id,
        Some(skel.baseline_cost),
    );

    let original_eval = if skel.original_ctx.evaluator.is_some() {
        skel.original_ctx.evaluator.clone()
    } else {
        ctx.evaluator.clone()
    };
    let original_vars = if skel.original_ctx.vars.is_empty() {
        ctx.original_vars.clone()
    } else {
        skel.original_ctx.vars.clone()
    };

    let cont = LiftedSubstituteCont {
        bindings: skel.bindings.clone(),
        outer_vars: skel.outer_ctx.vars.clone(),
        original_var_count: skel.original_var_count,
        original_eval,
        original_vars,
        source_sig: skel.source_sig.clone(),
    };
    ctx.competition_groups
        .get_mut(&group_id)
        .expect("group just created")
        .continuation = Some(ContinuationData::LiftedSubstitute(Box::new(cont)));

    // Pre-simplify the outer expression — lifting often exposes small
    // pattern-collapsible shells.
    let (outer, lean_certificate) =
        simplify_pattern_subtrees_certified(skel.outer_expr.clone_tree(), ctx.bitwidth);
    let cls = classify_structural(&outer);

    let mut solve_ctx = skel.outer_ctx.clone();
    solve_ctx.evaluator = Some(Evaluator::from_expr(&outer, ctx.bitwidth));

    let mut child = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
        expr: outer,
        classification: Some(cls),
        provenance: Provenance::Rewritten,
        solve_ctx: Some(solve_ctx),
    })));
    child.features = item.features.clone();
    child.features.classification = Some(cls);
    child.features.provenance = Provenance::Rewritten;
    child.metadata = item.metadata.clone();
    child.metadata.lean_certificate = lean_certificate;
    child.metadata.lean_signature_certificate = None;
    child.depth = item.depth;
    child.rewrite_gen = item.rewrite_gen;
    child.group_id = Some(group_id);
    child.history.clone_from(&item.history);

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::ConsumeCurrent,
        next: vec![child],
        reason: ReasonDetail::default(),
    })
}

#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::LiftedSkeleton(_))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::expr::Expr;
    use cobra_core::expr_cost::ExprCost;
    use cobra_core::simplify_outcome::Options;
    use cobra_orchestrator::{AstSolveContext, LiftedSkeletonPayload, LiftedValueKind};

    #[test]
    fn opens_group_and_emits_outer_ast() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let payload = LiftedSkeletonPayload {
            outer_expr: Expr::and(Expr::variable(2), Expr::variable(0)),
            outer_ctx: AstSolveContext {
                vars: vec!["x".into(), "y".into(), "v0".into()],
                evaluator: None,
                input_sig: vec![0, 0, 0, 0, 0, 1, 0, 1],
            },
            bindings: vec![cobra_orchestrator::LiftedBinding {
                kind: LiftedValueKind::ArithmeticAtom,
                outer_var_index: 2,
                subtree: Expr::add(Expr::variable(0), Expr::variable(1)),
                structural_hash: 0,
                original_support: vec![0, 1],
            }],
            original_var_count: 2,
            baseline_cost: ExprCost::default(),
            source_sig: vec![],
            original_ctx: AstSolveContext::default(),
        };
        let mut item = WorkItem::new(StateData::LiftedSkeleton(Box::new(payload)));
        item.metadata.lean_certificate = Some(cobra_orchestrator::LeanCertificate::new(
            64,
            Expr::variable(0),
            Expr::variable(0),
        ));
        item.metadata.lean_signature_certificate =
            cobra_orchestrator::LeanSignatureCertificate::new(64, 1, vec![0, 1], Expr::variable(0));
        let pr = run_prepare_lifted_outer_solve(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        assert_eq!(pr.next.len(), 1);
        let StateData::FoldedAst(ast) = &pr.next[0].payload else {
            panic!("expected FoldedAst child")
        };
        assert!(matches!(ast.provenance, Provenance::Rewritten));
        let gid = pr.next[0].group_id.unwrap();
        assert!(matches!(
            ctx.competition_groups[&gid].continuation,
            Some(ContinuationData::LiftedSubstitute(_))
        ));
        assert!(pr.next[0].metadata.lean_certificate.is_none());
        assert!(pr.next[0].metadata.lean_signature_certificate.is_none());
    }

    #[test]
    fn outer_pattern_presimplify_attaches_endpoint_certificate() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let payload = LiftedSkeletonPayload {
            outer_expr: Expr::add(Expr::variable(2), Expr::constant(0)),
            outer_ctx: AstSolveContext {
                vars: vec!["x".into(), "y".into(), "v0".into()],
                evaluator: None,
                input_sig: vec![0, 0, 0, 1, 0, 0, 0, 1],
            },
            bindings: vec![cobra_orchestrator::LiftedBinding {
                kind: LiftedValueKind::ArithmeticAtom,
                outer_var_index: 2,
                subtree: Expr::add(Expr::variable(0), Expr::variable(1)),
                structural_hash: 0,
                original_support: vec![0, 1],
            }],
            original_var_count: 2,
            baseline_cost: ExprCost::default(),
            source_sig: vec![],
            original_ctx: AstSolveContext::default(),
        };
        let item = WorkItem::new(StateData::LiftedSkeleton(Box::new(payload)));

        let pr = run_prepare_lifted_outer_solve(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        let StateData::FoldedAst(ast) = &pr.next[0].payload else {
            panic!("expected FoldedAst child")
        };
        assert_eq!(*ast.expr, *Expr::variable(2));
        let cert = pr.next[0]
            .metadata
            .lean_certificate
            .as_ref()
            .expect("outer simplification certificate");
        assert!(cert.matches_endpoints(
            64,
            &Expr::add(Expr::variable(2), Expr::constant(0)),
            &Expr::variable(2)
        ));
    }
}
