//! `ResidualFactoredGhost` / `ResidualFactoredGhostEscalated` —
//! solve a Boolean-null residual as `Q(x) · g(x)` for some polynomial
//! `Q` and ghost primitive `g` via the weighted falling-factorial
//! 2-adic solve, then recombine with the prefix.
//!
//! The escalated variant raises the interpolation grid degree from 2
//! to 3 when the residual support fits in two variables, trading
//! solve time for a wider basis.

use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, SolverResult,
};
use cobra_core::result::Result;

use cobra_orchestrator::{
    ItemDisposition, OrchestratorContext, PassDecision, PassId, PassResult, ResidualSolverKind,
    StateData, WorkItem,
};

use crate::ghost_residual_solver::solve_factored_ghost_residual;
use crate::residual_common::try_recombine_and_emit;

const RESIDUAL_FAILED: u16 = 50;

fn fail(domain: ReasonDomain, msg: &'static str) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category: ReasonCategory::VerifyFailed,
                domain,
                subcode: RESIDUAL_FAILED,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

#[allow(clippy::unnecessary_wraps)]
fn run_inner(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
    pass_id: PassId,
    grid_degree: u8,
) -> Result<PassResult> {
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

    let target_vars: Vec<String> = if residual.target.vars.is_empty() {
        ctx.original_vars.clone()
    } else {
        residual.target.vars.clone()
    };
    let num_vars = target_vars.len() as u32;

    let factored = solve_factored_ghost_residual(
        &residual.remainder_eval,
        &residual.remainder_support,
        num_vars,
        ctx.bitwidth,
        2,
        grid_degree,
    );

    let SolverResult::Success(payload) = factored else {
        return Ok(PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: factored.reason().cloned().unwrap_or_default(),
        });
    };

    if let Some(pr) = try_recombine_and_emit(
        residual,
        payload.expr,
        &target_vars,
        item,
        ctx,
        pass_id,
        ResidualSolverKind::GhostResidual,
    ) {
        return Ok(pr);
    }

    Ok(PassResult {
        decision: PassDecision::Blocked,
        disposition: ItemDisposition::RetainCurrent,
        next: Vec::new(),
        reason: fail(
            ReasonDomain::GhostResidual,
            "factored ghost recombination failed full-width verification",
        ),
    })
}

pub fn run_residual_factored_ghost(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    run_inner(item, ctx, PassId::ResidualFactoredGhost, 2)
}

pub fn run_residual_factored_ghost_escalated(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::Remainder(residual) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };
    let res_real_count = residual.remainder_elim.real_vars.len() as u32;
    let grid: u8 = if res_real_count <= 2 { 3 } else { 2 };
    run_inner(item, ctx, PassId::ResidualFactoredGhostEscalated, grid)
}

#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::Remainder(_))
}
