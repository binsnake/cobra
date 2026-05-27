//! `SemilinearReconstruct` pass — compact the atom table, compute
//! partitions, reconstruct with partition-guided OR-merge, normalise
//! subtrees via [`simplify_pattern_subtrees`], and emit a candidate.
//!
//! When a local evaluator is available, a full-width check gates
//! acceptance. Failure returns `Blocked` so the scheduler can fall
//! through to other techniques.

use cobra_core::evaluate_boolean_signature_from_evaluator;
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
use crate::candidate_normalize::signature_certificate_for_candidate;
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

    let source_sig = local_eval
        .as_ref()
        .map(|eval| evaluate_boolean_signature_from_evaluator(eval, num_vars, ctx.bitwidth));
    let lean_signature_certificate = source_sig
        .as_ref()
        .and_then(|sig| signature_certificate_for_candidate(ctx.bitwidth, sig, &vars, &simplified));

    let cost = compute_cost(&simplified).cost;
    let mut cand_item = item.clone();
    cand_item.payload = StateData::Candidate(Box::new(CandidatePayload {
        expr: simplified,
        real_vars: vars.clone(),
        cost,
        producing_pass: PassId::SemilinearReconstruct,
        needs_original_space_verification: false,
    }));
    cand_item.metadata.verification = verification;
    if let Some(sig) = source_sig {
        cand_item.metadata.sig_vector = sig;
    }
    cand_item.metadata.lean_certificate = None;
    cand_item.metadata.lean_signature_certificate = lean_signature_certificate;

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

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluator::Evaluator;
    use cobra_core::expr::Expr;
    use cobra_core::simplify_outcome::Options;
    use cobra_ir::normalize_to_semilinear;
    use cobra_orchestrator::{RewrittenSemilinearPayload, SemilinearContext};

    #[test]
    fn reconstruct_attaches_source_signature_certificate() {
        let vars = vec!["x".to_owned(), "y".to_owned()];
        let expr = Expr::and(Expr::variable(0), Expr::variable(1));
        let ir = normalize_to_semilinear(&expr, &vars, 64).unwrap();
        let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
        ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
        let item = WorkItem::new(StateData::SemilinearRewritten(Box::new(
            RewrittenSemilinearPayload {
                ctx: SemilinearContext {
                    ir,
                    vars,
                    evaluator: ctx.evaluator.clone(),
                },
            },
        )));

        let pr = run_semilinear_reconstruct(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::SolvedCandidate);
        let cert = pr.next[0]
            .metadata
            .lean_signature_certificate
            .as_ref()
            .expect("semilinear reconstruction certifies source signature");
        assert!(cert.matches_signature(64, 2, &[0, 0, 0, 1], cert.expr.as_ref()));
        assert!(pr.next[0].metadata.lean_certificate.is_none());
    }
}
