//! `ResidualTemplate` pass — runs the layered template decomposer
//! against the residual evaluator and recombines the recovered
//! expression with the core's prefix.

use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, SolverResult,
};
use cobra_core::result::Result;

use cobra_orchestrator::{
    ItemDisposition, OrchestratorContext, PassDecision, PassId, PassResult, ResidualSolverKind,
    StateData, WorkItem,
};

use crate::residual_common::try_recombine_and_emit;
use crate::template_decomposer::try_template_decomposition;

fn fail(msg: &'static str) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category: ReasonCategory::VerifyFailed,
                domain: ReasonDomain::TemplateDecomposer,
                subcode: 50,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

#[allow(clippy::unnecessary_wraps)]
pub fn run_residual_template(item: &WorkItem, ctx: &mut OrchestratorContext) -> Result<PassResult> {
    let StateData::Remainder(residual) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let target_vars = if residual.target.vars.is_empty() {
        ctx.original_vars.clone()
    } else {
        residual.target.vars.clone()
    };
    let num_vars = target_vars.len() as u32;

    let solver =
        try_template_decomposition(Some(&residual.remainder_eval), num_vars, ctx.bitwidth, None);

    let SolverResult::Success(t) = solver else {
        return Ok(PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: solver.reason().cloned().unwrap_or_default(),
        });
    };

    if let Some(pr) = try_recombine_and_emit(
        residual,
        t.expr,
        &target_vars,
        item,
        ctx,
        PassId::ResidualTemplate,
        ResidualSolverKind::TemplateDecomposition,
    ) {
        return Ok(pr);
    }

    Ok(PassResult {
        decision: PassDecision::Blocked,
        disposition: ItemDisposition::RetainCurrent,
        next: Vec::new(),
        reason: fail("template residual recombination failed full-width verification"),
    })
}

#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::Remainder(_))
}
