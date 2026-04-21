//! `SemilinearCheck` pass — run `simplify_structure` on the normalised
//! IR, reconstruct a plain Expr (no partitions yet), then symbolically
//! self-check that round-tripping preserves coefficient semantics.

use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame,
};
use cobra_core::result::Result;

use cobra_ir::reconstruct_masked_atoms;
use cobra_orchestrator::{
    CheckedSemilinearPayload, ItemDisposition, OrchestratorContext, PassDecision, PassResult,
    SemilinearContext, StateData, WorkItem,
};

use crate::atom_simplifier::simplify_structure;
use crate::self_check::self_check_semilinear;

fn reason(msg: &'static str, category: ReasonCategory) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category,
                domain: ReasonDomain::Semilinear,
                subcode: 0,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

/// Pass body.
#[allow(clippy::unnecessary_wraps)]
pub fn run_semilinear_check(item: &WorkItem, ctx: &mut OrchestratorContext) -> Result<PassResult> {
    let StateData::SemilinearNormalized(payload) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let mut ir = payload.ctx.ir.clone();
    let vars = if payload.ctx.vars.is_empty() {
        ctx.original_vars.clone()
    } else {
        payload.ctx.vars.clone()
    };

    simplify_structure(&mut ir);

    let plain = reconstruct_masked_atoms(&ir, &[]);
    let check = self_check_semilinear(&ir, &plain, &vars, ctx.bitwidth);
    if !check.passed {
        let r = reason(
            "semilinear self-check failed",
            ReasonCategory::InternalInvariant,
        );
        ctx.run_metadata.semilinear_failure = Some(r.clone());
        return Ok(PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: r,
        });
    }

    let mut next = item.clone();
    next.payload = StateData::SemilinearChecked(Box::new(CheckedSemilinearPayload {
        ctx: SemilinearContext {
            ir,
            vars,
            evaluator: payload.ctx.evaluator.clone(),
        },
    }));

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::ConsumeCurrent,
        next: vec![next],
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard — normalized semilinear only.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::SemilinearNormalized(_))
}
