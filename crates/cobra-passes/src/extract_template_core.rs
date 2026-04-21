//! Template-core extractor — invokes the layered template search
//! against the current evaluator and emits the recovered expression as
//! a verified core candidate.

use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, SolverResult,
};
use cobra_core::result::Result;

use cobra_orchestrator::{ExtractorKind, OrchestratorContext, PassResult, WorkItem};

use crate::decomposition_engine::{
    extractor_applicable, run_extractor, CoreCandidate, DecompositionContext, Extractor,
};
use crate::template_decomposer::try_template_decomposition;

pub struct TemplateCoreExtractor;

impl Extractor for TemplateCoreExtractor {
    fn kind(&self) -> ExtractorKind {
        ExtractorKind::Template
    }

    fn extract(&self, ctx: &DecompositionContext<'_>) -> SolverResult<CoreCandidate> {
        let num_vars = ctx.vars.len() as u32;
        match try_template_decomposition(ctx.evaluator, num_vars, ctx.bitwidth, None) {
            SolverResult::Success(t) => SolverResult::Success(CoreCandidate {
                expr: t.expr,
                kind: ExtractorKind::Template,
                degree_used: 0,
            }),
            SolverResult::Inapplicable(r) => SolverResult::Inapplicable(r),
            SolverResult::Blocked(r) => SolverResult::Blocked(r),
            SolverResult::VerifyFailed { reason, .. } => SolverResult::Blocked(ReasonDetail {
                top: ReasonFrame {
                    code: ReasonCode {
                        category: ReasonCategory::VerifyFailed,
                        domain: ReasonDomain::TemplateDecomposer,
                        subcode: 11,
                    },
                    message: "template candidate failed full-width verification".into(),
                    fields: Vec::new(),
                },
                causes: vec![reason.top],
            }),
        }
    }
}

pub fn run_extract_template_core(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    run_extractor(item, ctx, &TemplateCoreExtractor)
}

#[must_use]
pub fn applicable(item: &WorkItem, ctx: &OrchestratorContext) -> bool {
    extractor_applicable(item, ctx)
}
