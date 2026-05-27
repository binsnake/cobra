//! `SemilinearRewrite` pass — run the refinement chain (flatten →
//! coalesce → recover → refine → coalesce) and sample-probe the result
//! at full width. On probe failure, block so the next attempt reroutes
//! via other techniques.

use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame,
};
use cobra_core::result::Result;

use cobra_ir::{
    coalesce_terms, flatten_complex_atoms, reconstruct_masked_atoms, recover_structure,
    refine_terms,
};
use cobra_orchestrator::{
    ItemDisposition, OrchestratorContext, PassDecision, PassResult, RewrittenSemilinearPayload,
    SemilinearContext, StateData, WorkItem,
};

use crate::spot_check::full_width_check_eval;

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
pub fn run_semilinear_rewrite(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::SemilinearChecked(payload) = &item.payload else {
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
    let local_eval = payload
        .ctx
        .evaluator
        .clone()
        .or_else(|| ctx.evaluator.clone());

    if flatten_complex_atoms(&mut ir) {
        coalesce_terms(&mut ir);
    }
    recover_structure(&mut ir);
    refine_terms(&mut ir);
    coalesce_terms(&mut ir);

    if let Some(eval) = local_eval.as_ref() {
        let num_vars = vars.len() as u32;
        let probe_expr = reconstruct_masked_atoms(&ir, &[]);
        let probe = full_width_check_eval(eval, num_vars, &probe_expr, ctx.bitwidth, 16);
        if !probe.passed {
            let r = reason(
                "post-rewrite probe verification failed",
                ReasonCategory::VerifyFailed,
            );
            ctx.run_metadata.semilinear_failure = Some(r.clone());
            return Ok(PassResult {
                decision: PassDecision::Blocked,
                disposition: ItemDisposition::ConsumeCurrent,
                next: Vec::new(),
                reason: r,
            });
        }
    }

    let mut next = item.clone();
    next.payload = StateData::SemilinearRewritten(Box::new(RewrittenSemilinearPayload {
        ctx: SemilinearContext {
            ir,
            vars,
            evaluator: local_eval,
        },
    }));
    next.metadata.lean_certificate = None;
    next.metadata.lean_signature_certificate = None;

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::ConsumeCurrent,
        next: vec![next],
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard — checked semilinear only.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::SemilinearChecked(_))
}
