//! `ResidualPolyRecovery` pass — retry `recover_and_verify_poly` on
//! the residual with `min_degree = residual.degree_floor`. Used when
//! a polynomial core was extracted but the residual is itself
//! polynomial at a higher degree.

use cobra_core::expr::Expr;
use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, SolverResult,
};
use cobra_core::result::Result;

use cobra_ir::{recover_and_verify_poly, PolyRecoveryResult};
use cobra_orchestrator::{
    ItemDisposition, OrchestratorContext, PassDecision, PassId, PassResult, ResidualSolverKind,
    StateData, WorkItem,
};

use crate::residual_common::try_recombine_and_emit;
use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};

fn fail(msg: &'static str) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category: ReasonCategory::VerifyFailed,
                domain: ReasonDomain::Decomposition,
                subcode: 60,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

#[allow(clippy::unnecessary_wraps)]
pub fn run_residual_poly_recovery(
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

    let verify =
        |eval: &cobra_core::evaluator::Evaluator, arity: u32, candidate: &Expr, bw: u32| {
            full_width_check_eval(eval, arity, candidate, bw, DEFAULT_NUM_SAMPLES).passed
        };

    let recovery = recover_and_verify_poly(
        &residual.remainder_eval,
        &residual.remainder_support,
        num_vars,
        ctx.bitwidth,
        4,
        residual.degree_floor,
        verify,
    );
    let SolverResult::Success(PolyRecoveryResult { expr, .. }) = recovery else {
        return Ok(PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: recovery.reason().cloned().unwrap_or_default(),
        });
    };

    let recombined = try_recombine_and_emit(
        residual,
        expr,
        &target_vars,
        item,
        ctx,
        PassId::ResidualPolyRecovery,
        ResidualSolverKind::PolynomialRecovery,
    );
    if let Some(pr) = recombined {
        return Ok(pr);
    }
    Ok(PassResult {
        decision: PassDecision::Blocked,
        disposition: ItemDisposition::RetainCurrent,
        next: Vec::new(),
        reason: fail("residual poly recombination failed full-width verification"),
    })
}

#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::Remainder(_))
}
