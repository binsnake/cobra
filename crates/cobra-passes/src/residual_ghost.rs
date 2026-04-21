//! `ResidualGhost` pass — uses
//! [`crate::ghost_residual_solver::solve_ghost_residual`] on a
//! Boolean-null residual, then recombines the ghost expression with
//! the core's prefix.

use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, SolverResult,
};
use cobra_core::result::Result;

use cobra_orchestrator::{
    ItemDisposition, OrchestratorContext, PassDecision, PassId, PassResult, ResidualSolverKind,
    StateData, WorkItem,
};

use crate::ghost_residual_solver::solve_ghost_residual;
use crate::residual_common::try_recombine_and_emit;

fn fail(msg: &'static str) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category: ReasonCategory::VerifyFailed,
                domain: ReasonDomain::GhostResidual,
                subcode: 50,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

#[allow(clippy::unnecessary_wraps)]
pub fn run_residual_ghost(item: &WorkItem, ctx: &mut OrchestratorContext) -> Result<PassResult> {
    let StateData::Remainder(residual) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };
    if !residual.is_boolean_null {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }
    let res_real_count = residual.remainder_elim.real_vars.len() as u32;
    if res_real_count > 6 {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    let target_vars = if residual.target.vars.is_empty() {
        ctx.original_vars.clone()
    } else {
        residual.target.vars.clone()
    };
    let num_vars = target_vars.len() as u32;

    let ghost = solve_ghost_residual(
        &residual.remainder_eval,
        &residual.remainder_support,
        num_vars,
        ctx.bitwidth,
    );

    let SolverResult::Success(payload) = ghost else {
        return Ok(PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ghost.reason().cloned().unwrap_or_default(),
        });
    };

    let recombined = try_recombine_and_emit(
        residual,
        payload.expr,
        &target_vars,
        item,
        ctx,
        PassId::ResidualGhost,
        ResidualSolverKind::GhostResidual,
    );

    if let Some(pr) = recombined {
        return Ok(pr);
    }

    Ok(PassResult {
        decision: PassDecision::Blocked,
        disposition: ItemDisposition::RetainCurrent,
        next: Vec::new(),
        reason: fail("ghost residual recombination failed full-width verification"),
    })
}

#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::Remainder(_))
}
