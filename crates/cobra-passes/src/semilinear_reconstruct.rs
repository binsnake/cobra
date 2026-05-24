//! `SemilinearReconstruct` pass — compact the atom table, compute
//! partitions, reconstruct with partition-guided OR-merge, normalise
//! subtrees via [`simplify_pattern_subtrees`], and emit a candidate.
//!
//! When a local evaluator is available, a full-width check gates
//! acceptance. Failure returns `Blocked` so the scheduler can fall
//! through to other techniques.

use cobra_core::expr_cost::compute_cost;
use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, VerificationState,
};
use cobra_core::result::Result;

use cobra_ir::reconstruct_masked_atoms;
use cobra_ir::semilinear::compact_atom_table;
use cobra_orchestrator::{
    CandidatePayload, ItemDisposition, OrchestratorContext, PassDecision, PassId, PassResult,
    StateData, WorkItem,
};

use crate::bit_partitioner::compute_partitions;
use crate::pattern_matcher::normalize_late_candidate_expr;
use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};

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
pub fn run_semilinear_reconstruct(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::SemilinearRewritten(payload) = &item.payload else {
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

    compact_atom_table(&mut ir);
    let partitions = compute_partitions(&ir);
    let mut simplified = reconstruct_masked_atoms(&ir, &partitions);
    simplified = normalize_late_candidate_expr(simplified, ctx.bitwidth);

    let num_vars = vars.len() as u32;
    let mut verification = VerificationState::Unverified;

    if let Some(eval) = local_eval.as_ref() {
        let check = full_width_check_eval(
            eval,
            num_vars,
            &simplified,
            ctx.bitwidth,
            DEFAULT_NUM_SAMPLES,
        );
        if !check.passed {
            let r = reason(
                "final full-width verification failed",
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
        verification = VerificationState::Verified;
    }

    let cost = compute_cost(&simplified).cost;
    let mut cand_item = item.clone();
    cand_item.payload = StateData::Candidate(Box::new(CandidatePayload {
        expr: simplified,
        real_vars: vars,
        cost,
        producing_pass: PassId::SemilinearReconstruct,
        needs_original_space_verification: false,
    }));
    cand_item.metadata.verification = verification;

    Ok(PassResult {
        decision: PassDecision::SolvedCandidate,
        disposition: ItemDisposition::ConsumeCurrent,
        next: vec![cand_item],
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard — rewritten semilinear only.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::SemilinearRewritten(_))
}
