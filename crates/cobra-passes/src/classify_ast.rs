//! `RunClassifyAst` pass. Runs [`classify_structural`] on the AST,
//! emits a replacement work item with the classification stamped into
//! both payload and features, and stores the classification in
//! `ctx.run_metadata.input_classification` for later passes to
//! consult.

use cobra_core::pass_contract::ReasonDetail;
use cobra_core::result::Result;

use cobra_orchestrator::{
    AstPayload, ItemDisposition, OrchestratorContext, PassDecision, PassResult, StateData, WorkItem,
};

use crate::classifier::classify_structural;

/// Pass body. Matches C++ `RunClassifyAst`.
#[allow(clippy::unnecessary_wraps)] // `PassFn` signature requires `Result`
pub fn run_classify_ast(item: &WorkItem, ctx: &mut OrchestratorContext) -> Result<PassResult> {
    let StateData::FoldedAst(ast) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let cls = classify_structural(&ast.expr);
    ctx.run_metadata.input_classification = cls;

    let new_payload = AstPayload {
        expr: ast.expr.clone_tree(),
        classification: Some(cls),
        provenance: ast.provenance,
        solve_ctx: ast.solve_ctx.clone(),
    };

    let mut new_item = item.clone();
    new_item.payload = StateData::FoldedAst(Box::new(new_payload));
    new_item.features.classification = Some(cls);

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::ConsumeCurrent,
        next: vec![new_item],
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard: only fires on `FoldedAst` payloads.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::FoldedAst(_))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::classification::{SemanticClass, StructuralFlag};
    use cobra_core::expr::Expr;
    use cobra_core::simplify_outcome::Options;
    use cobra_orchestrator::Provenance;

    fn mk_ast_item(e: Box<Expr>) -> WorkItem {
        WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
            expr: e,
            classification: None,
            provenance: Provenance::Original,
            solve_ctx: None,
        })))
    }

    #[test]
    fn classify_writes_classification_to_features_and_run_metadata() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        let item = mk_ast_item(Expr::and(Expr::variable(0), Expr::constant(0xFF)));
        let pr = run_classify_ast(&item, &mut ctx).unwrap();

        assert_eq!(pr.decision, PassDecision::Advance);
        assert_eq!(pr.disposition, ItemDisposition::ConsumeCurrent);
        assert_eq!(pr.next.len(), 1);

        let cls = pr.next[0].features.classification.unwrap();
        assert_eq!(cls.semantic, SemanticClass::Semilinear);
        assert!(cls.flags.contains(StructuralFlag::HAS_BITWISE));

        // And the same classification lands on run_metadata.
        assert_eq!(
            ctx.run_metadata.input_classification.semantic,
            SemanticClass::Semilinear
        );
    }

    #[test]
    fn classify_noop_on_non_ast_payload() {
        use cobra_core::expr_cost::ExprCost;
        use cobra_orchestrator::{CandidatePayload, PassId};

        let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
        let item = WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
            expr: Expr::variable(0),
            real_vars: vec![],
            cost: ExprCost::default(),
            producing_pass: PassId::VerifyCandidate,
            needs_original_space_verification: false,
        })));
        let pr = run_classify_ast(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NotApplicable);
        assert!(pr.next.is_empty());
    }
}
