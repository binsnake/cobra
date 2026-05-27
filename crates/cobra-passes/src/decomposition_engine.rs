//! Extractor trait + inputs/outputs shared by the decomposition
//! engine. Each concrete extractor (`extract_product_core`,
//! `extract_poly_core`, `extract_template_core`) implements
//! [`Extractor`] to plug into the pass layer.
//!
//! `RunExtractor<ExtractorKind>` — a `&dyn Extractor` is dispatched
//! from the pass, so per-kind customisations (like `AcceptCore`
//! gating) can live on the trait impl instead of `if constexpr`
//! branching.

use cobra_core::classification::{Classification, SemanticClass, StructuralFlag};
use cobra_core::evaluate_boolean_signature;
use cobra_core::evaluator::Evaluator;
use cobra_core::expr::Expr;
use cobra_core::expr_cost::compute_cost;
use cobra_core::pass_contract::{ReasonDetail, SolverResult};
use cobra_core::result::Result;
use cobra_core::simplify_outcome::Options;

use cobra_orchestrator::{
    CandidatePayload, CoreCandidatePayload, ExtractorKind, ItemDisposition, OrchestratorContext,
    PassDecision, PassId, PassResult, RemainderTargetContext, StateData, WorkItem,
};

use crate::candidate_normalize::signature_certificate_for_candidate;
use crate::classifier::classify_structural;
use crate::decomposition_helpers::accept_core;
use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};

/// `DecompositionContext` layout, with the evaluator passed in
/// separately so it can be `None`.
pub struct DecompositionContext<'a> {
    pub opts: &'a Options,
    pub bitwidth: u32,
    pub evaluator: Option<&'a Evaluator>,
    pub vars: &'a [String],
    pub sig: &'a [u64],
    pub current_expr: Option<&'a Expr>,
    pub cls: &'a Classification,
}

/// Emitted by a successful extractor. `degree_used` is only set by the
/// polynomial extractor and is zero otherwise.
pub struct CoreCandidate {
    pub expr: Box<Expr>,
    pub kind: ExtractorKind,
    pub degree_used: u8,
}

/// Trait for a concrete core-extractor implementation. Each
/// implementor knows its own `ExtractorKind` and runs independently.
pub trait Extractor {
    fn kind(&self) -> ExtractorKind;

    /// Run the extractor on the supplied context.
    fn extract(&self, ctx: &DecompositionContext<'_>) -> SolverResult<CoreCandidate>;
}

fn not_applicable() -> PassResult {
    PassResult {
        decision: PassDecision::NotApplicable,
        disposition: ItemDisposition::RetainCurrent,
        next: Vec::new(),
        reason: ReasonDetail::default(),
    }
}

fn blocked(reason: ReasonDetail) -> PassResult {
    PassResult {
        decision: PassDecision::Blocked,
        disposition: ItemDisposition::RetainCurrent,
        next: Vec::new(),
        reason,
    }
}

fn source_pass(kind: ExtractorKind, degree: u8) -> PassId {
    match kind {
        ExtractorKind::ProductAst | ExtractorKind::BooleanNullDirect => PassId::ExtractProductCore,
        ExtractorKind::Polynomial => {
            if degree == 3 {
                PassId::ExtractPolyCoreD3
            } else if degree == 4 {
                PassId::ExtractPolyCoreD4
            } else {
                PassId::ExtractPolyCoreD2
            }
        }
        ExtractorKind::Template => PassId::ExtractTemplateCore,
    }
}

/// Applicability guard shared by every `Extract*` pass — `FoldedAst` only.
#[must_use]
pub fn extractor_applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::FoldedAst(_))
}

/// Shared pass body for every `Extract*` pass. Builds a
/// `DecompositionContext` from the active AST view, invokes the
/// extractor, gates on `accept_core` when an evaluator is available,
/// and emits a `CoreCandidatePayload` on success.
#[allow(clippy::unnecessary_wraps)]
pub fn run_extractor(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
    extractor: &dyn Extractor,
) -> Result<PassResult> {
    let StateData::FoldedAst(ast) = &item.payload else {
        return Ok(not_applicable());
    };

    let (active_vars, active_eval, target_vars) = active_view(item, ctx);
    let num_vars = active_vars.len() as u32;
    let sig = evaluate_boolean_signature(&ast.expr, num_vars, ctx.bitwidth);
    let cls = ast
        .classification
        .unwrap_or_else(|| classify_structural(&ast.expr));

    let dctx = DecompositionContext {
        opts: &ctx.opts,
        bitwidth: ctx.bitwidth,
        evaluator: active_eval.as_ref(),
        vars: &active_vars,
        sig: &sig,
        current_expr: Some(&ast.expr),
        cls: &cls,
    };

    match extractor.extract(&dctx) {
        SolverResult::Inapplicable(_) => Ok(not_applicable()),
        SolverResult::Blocked(r) | SolverResult::VerifyFailed { reason: r, .. } => Ok(blocked(r)),
        SolverResult::Success(core) => {
            if let Some(eval) = active_eval.as_ref() {
                let can_emit_direct = matches!(
                    core.kind,
                    ExtractorKind::ProductAst | ExtractorKind::Polynomial
                ) || (core.kind == ExtractorKind::Template
                    && cls.semantic == SemanticClass::NonPolynomial
                    && cls.flags.contains(StructuralFlag::HAS_BITWISE_OVER_ARITH));
                if can_emit_direct
                    && full_width_check_eval(
                        eval,
                        num_vars,
                        &core.expr,
                        ctx.bitwidth,
                        DEFAULT_NUM_SAMPLES,
                    )
                    .passed
                {
                    let cost = compute_cost(&core.expr).cost;
                    let lean_signature_certificate = signature_certificate_for_candidate(
                        ctx.bitwidth,
                        &sig,
                        &active_vars,
                        &core.expr,
                    );
                    let mut next = item.clone();
                    next.payload = StateData::Candidate(Box::new(CandidatePayload {
                        expr: core.expr,
                        real_vars: active_vars.clone(),
                        cost,
                        producing_pass: source_pass(core.kind, core.degree_used),
                        needs_original_space_verification: false,
                    }));
                    next.metadata.verification =
                        cobra_core::pass_contract::VerificationState::Verified;
                    next.metadata.sig_vector = sig;
                    next.metadata.lean_certificate = None;
                    next.metadata.lean_signature_certificate = lean_signature_certificate;
                    next.metadata.decomposition_meta =
                        Some(cobra_core::pass_contract::DecompositionMeta {
                            extractor_kind: core.kind as u8,
                            solver_kind: 0,
                            has_solver: false,
                            core_degree: core.degree_used,
                        });

                    return Ok(PassResult {
                        decision: PassDecision::SolvedCandidate,
                        disposition: ItemDisposition::RetainCurrent,
                        next: vec![next],
                        reason: ReasonDetail::default(),
                    });
                }

                if !accept_core(eval, &core.expr, num_vars, ctx.bitwidth) {
                    return Ok(blocked(ReasonDetail::default()));
                }
            }

            let target = RemainderTargetContext {
                eval: active_eval.unwrap_or_default(),
                vars: target_vars,
                remap_support: Vec::new(),
            };

            let payload = CoreCandidatePayload {
                core_expr: core.expr,
                extractor_kind: core.kind,
                degree_used: core.degree_used,
                source_sig: sig,
                target,
            };

            let mut next = item.clone();
            next.payload = StateData::CoreCandidate(Box::new(payload));
            next.metadata.lean_certificate = None;
            next.metadata.lean_signature_certificate = None;

            Ok(PassResult {
                decision: PassDecision::Advance,
                disposition: ItemDisposition::RetainCurrent,
                next: vec![next],
                reason: ReasonDetail::default(),
            })
        }
    }
}

/// Returns `(vars, evaluator, target_vars)` where `target_vars` is
/// either the solve-ctx's own vars (when present) or empty, signalling
/// to `PrepareRemainderFromCore` that the global context should be
/// used.
fn active_view(
    item: &WorkItem,
    ctx: &OrchestratorContext,
) -> (Vec<String>, Option<Evaluator>, Vec<String>) {
    if let StateData::FoldedAst(ast) = &item.payload {
        if let Some(sc) = &ast.solve_ctx {
            return (sc.vars.clone(), sc.evaluator.clone(), sc.vars.clone());
        }
    }
    (ctx.original_vars.clone(), ctx.evaluator.clone(), Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluator::Evaluator;
    use cobra_core::expr::Expr;
    use cobra_core::simplify_outcome::Options;
    use cobra_orchestrator::{AstPayload, Provenance};

    struct IdentityExtractor;

    impl Extractor for IdentityExtractor {
        fn kind(&self) -> ExtractorKind {
            ExtractorKind::ProductAst
        }

        fn extract(&self, _ctx: &DecompositionContext<'_>) -> SolverResult<CoreCandidate> {
            SolverResult::Success(CoreCandidate {
                expr: Expr::variable(0),
                kind: ExtractorKind::ProductAst,
                degree_used: 0,
            })
        }
    }

    #[test]
    fn direct_extractor_candidate_attaches_source_signature_certificate() {
        let expr = Expr::variable(0);
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".to_owned()], 64);
        ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
        let item = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
            expr,
            classification: None,
            provenance: Provenance::Original,
            solve_ctx: None,
        })));

        let pr = run_extractor(&item, &mut ctx, &IdentityExtractor).unwrap();
        assert_eq!(pr.decision, PassDecision::SolvedCandidate);
        let cert = pr.next[0]
            .metadata
            .lean_signature_certificate
            .as_ref()
            .expect("direct extractor candidate has source signature certificate");
        assert!(cert.matches_signature(64, 1, &[0, 1], cert.expr.as_ref()));
        assert!(pr.next[0].metadata.lean_certificate.is_none());
    }

    #[test]
    fn core_candidate_path_clears_stale_proof_metadata() {
        let expr = Expr::variable(0);
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".to_owned()], 64);
        let mut item = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
            expr,
            classification: None,
            provenance: Provenance::Original,
            solve_ctx: None,
        })));
        item.metadata.lean_certificate = Some(cobra_orchestrator::LeanCertificate::new(
            64,
            Expr::variable(0),
            Expr::variable(0),
        ));
        item.metadata.lean_signature_certificate =
            cobra_orchestrator::LeanSignatureCertificate::new(64, 1, vec![0, 1], Expr::variable(0));

        let pr = run_extractor(&item, &mut ctx, &IdentityExtractor).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        assert!(matches!(pr.next[0].payload, StateData::CoreCandidate(_)));
        assert!(pr.next[0].metadata.lean_certificate.is_none());
        assert!(pr.next[0].metadata.lean_signature_certificate.is_none());
    }
}
