//! Extractor trait + inputs/outputs shared by the decomposition
//! engine. Each concrete extractor (`extract_product_core`,
//! `extract_poly_core`, `extract_template_core`) implements
//! [`Extractor`] to plug into the pass layer.
//!
//! `RunExtractor<ExtractorKind>` — a `&dyn Extractor` is dispatched
//! from the pass, so per-kind customisations (like `AcceptCore`
//! gating) can live on the trait impl instead of `if constexpr`
//! branching.

use cobra_core::classification::Classification;
use cobra_core::evaluate_boolean_signature;
use cobra_core::evaluator::Evaluator;
use cobra_core::expr::Expr;
use cobra_core::pass_contract::{ReasonDetail, SolverResult};
use cobra_core::result::Result;
use cobra_core::simplify_outcome::Options;

use cobra_orchestrator::{
    CoreCandidatePayload, ExtractorKind, ItemDisposition, OrchestratorContext, PassDecision,
    PassResult, RemainderTargetContext, StateData, WorkItem,
};

use crate::classifier::classify_structural;
use crate::decomposition_helpers::accept_core;

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

            Ok(PassResult {
                decision: PassDecision::Advance,
                disposition: ItemDisposition::ConsumeCurrent,
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
