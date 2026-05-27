//! `SignatureCobCandidate` pass — emit a candidate expression built
//! from the AND-monomial coefficient vector produced by
//! [`crate::prepare_coeff_model`]. Submits the candidate to the
//! parent's competition group so it races the other signature-path
//! solvers (pattern match, ANF, etc.).
//!
//! A signature spot-check runs first (cheap), then an optional
//! full-width check against the original evaluator. A full-width
//! mismatch is fatal and returns `NoProgress` — `BuildCobExpr` is
//! exact when its input came from `InterpolateCoefficients`, so any
//! mismatch points at an evaluator / provenance issue rather than a
//! recoverable one.

use cobra_core::expr_cost::compute_cost;
use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, VerificationState,
};
use cobra_core::result::Result;

use cobra_orchestrator::{
    CandidateRecord, ItemDisposition, OrchestratorContext, PassDecision, PassId, PassResult,
    StateData, WorkItem,
};

use crate::candidate_normalize::{
    signature_certificate_for_candidate, submit_normalized_candidate,
};
use crate::cob_expr_builder::build_cob_expr;
use crate::mapped_evaluator::build_mapped_evaluator;
use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};

fn verify_failed(message: &'static str) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category: ReasonCategory::VerifyFailed,
                domain: ReasonDomain::Signature,
                subcode: 0,
            },
            message: message.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

/// Pass body. Consumes a `SignatureCoeff` payload and submits a
/// candidate to the parent's competition group.
#[allow(clippy::unnecessary_wraps)]
pub fn run_signature_cob_candidate(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::SignatureCoeff(payload) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };
    let sub = &payload.ctx;
    let num_vars = sub.real_vars.len() as u32;

    let expr = build_cob_expr(&payload.coeffs, num_vars, ctx.bitwidth);

    // Signature spot-check against the reduced vector. `build_cob_expr`
    // is exact by construction, so a mismatch here is a bug, not a
    // valid rejection path — but we still gate on it to catch drift.
    let sig = &sub.elimination.reduced_sig;
    let mut verification = VerificationState::Unverified;
    if ctx.opts.spot_check {
        let emitted = cobra_core::evaluate_boolean_signature(&expr, num_vars, ctx.bitwidth);
        let matches =
            sig.len() == emitted.len() && sig.iter().zip(emitted.iter()).all(|(a, b)| a == b);
        if matches {
            verification = VerificationState::Verified;
        }
    }

    // Full-width check against the original evaluator when available.
    // A failure here is fatal — the CoB expression came straight from
    // the interpolated coefficients, so any disagreement means the
    // signature itself was not a faithful projection of the original
    // function (e.g. wrong subproblem scoping).
    if let Some(eval) = build_mapped_evaluator(ctx, sub, item) {
        let check =
            full_width_check_eval(&eval, num_vars, &expr, ctx.bitwidth, DEFAULT_NUM_SAMPLES);
        if check.passed {
            verification = VerificationState::Verified;
        } else {
            return Ok(PassResult {
                decision: PassDecision::NoProgress,
                disposition: ItemDisposition::RetainCurrent,
                next: Vec::new(),
                reason: verify_failed("CoB candidate failed full-width check"),
            });
        }
    }

    let cost = compute_cost(&expr).cost;
    let lean_signature_certificate =
        signature_certificate_for_candidate(ctx.bitwidth, sig, &sub.real_vars, &expr);
    let group_id = item
        .group_id
        .expect("SignatureCobCandidate requires a group_id");

    submit_normalized_candidate(
        &mut ctx.competition_groups,
        group_id,
        CandidateRecord {
            expr,
            cost,
            verification,
            real_vars: sub.real_vars.clone(),
            source_pass: PassId::SignatureCobCandidate,
            needs_original_space_verification: sub.needs_original_space_verification,
            sig_vector: sub.elimination.reduced_sig.clone(),
            lean_certificate: None,
            lean_signature_certificate,
        },
        ctx.bitwidth,
    );

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::RetainCurrent,
        next: Vec::new(),
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard — only signature-coeff-state items.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::SignatureCoeff(_))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluator::Evaluator;
    use cobra_core::expr::Expr;
    use cobra_core::simplify_outcome::Options;
    use cobra_ir::interpolate_coefficients;
    use cobra_orchestrator::{
        create_group, EliminationResult, SignatureCoeffStatePayload, SignatureSubproblemContext,
    };

    fn mk_coeff_item(
        sig: Vec<u64>,
        real_vars: Vec<String>,
        ctx: &mut OrchestratorContext,
    ) -> WorkItem {
        let num_vars = real_vars.len() as u32;
        let coeffs = interpolate_coefficients(sig.clone(), num_vars, ctx.bitwidth);
        let elim = EliminationResult {
            reduced_sig: sig.clone(),
            real_vars: real_vars.clone(),
            spurious_vars: Vec::new(),
        };
        let payload = SignatureCoeffStatePayload {
            ctx: SignatureSubproblemContext {
                sig,
                real_vars,
                elimination: elim,
                original_indices: Vec::new(),
                needs_original_space_verification: false,
            },
            coeffs,
        };
        let mut item = WorkItem::new(StateData::SignatureCoeff(Box::new(payload)));
        let gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        item.group_id = Some(gid);
        item
    }

    #[test]
    fn submits_candidate_for_two_var_xor() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let orig = Expr::xor(Expr::variable(0), Expr::variable(1));
        ctx.evaluator = Some(Evaluator::from_expr(&orig, 64));

        let item = mk_coeff_item(vec![0, 1, 1, 0], vec!["x".into(), "y".into()], &mut ctx);
        let gid = item.group_id.unwrap();

        let pr = run_signature_cob_candidate(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);

        let group = &ctx.competition_groups[&gid];
        let best = group.best.as_ref().expect("candidate submitted");
        assert_eq!(best.source_pass, PassId::SignatureCobCandidate);
        assert_eq!(best.verification, VerificationState::Verified);
        let cert = best
            .lean_signature_certificate
            .as_ref()
            .expect("Lean signature certificate");
        assert!(cert.matches_signature(64, 2, &[0, 1, 1, 0], &best.expr));
    }

    #[test]
    fn prefers_item_evaluator_override_for_reduced_subproblem() {
        let mut ctx = OrchestratorContext::new(
            Options::default(),
            vec!["x".into(), "y".into(), "z".into()],
            64,
        );
        // The global evaluator disagrees with the subproblem; the item-level
        // override is the authoritative evaluator for this child solve.
        ctx.evaluator = Some(Evaluator::from_expr(
            &Expr::add(Expr::variable(0), Expr::variable(1)),
            64,
        ));

        let mut item = mk_coeff_item(vec![0, 1, 1, 0], vec!["x".into(), "y".into()], &mut ctx);
        if let StateData::SignatureCoeff(payload) = &mut item.payload {
            payload.ctx.original_indices = vec![0, 1];
        }
        item.evaluator_override = Some(Evaluator::from_expr(
            &Expr::xor(Expr::variable(0), Expr::variable(1)),
            64,
        ));
        item.evaluator_override_arity = 2;

        let gid = item.group_id.unwrap();
        let pr = run_signature_cob_candidate(&item, &mut ctx).unwrap();

        assert_eq!(pr.decision, PassDecision::Advance);
        let best = ctx.competition_groups[&gid]
            .best
            .as_ref()
            .expect("candidate submitted");
        assert_eq!(best.verification, VerificationState::Verified);
    }

    #[test]
    fn rejects_when_evaluator_disagrees() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        // Evaluator is for `x + y`, but coeffs encode `x ^ y`.
        let bogus = Expr::add(Expr::variable(0), Expr::variable(1));
        ctx.evaluator = Some(Evaluator::from_expr(&bogus, 64));

        let item = mk_coeff_item(vec![0, 1, 1, 0], vec!["x".into(), "y".into()], &mut ctx);
        let pr = run_signature_cob_candidate(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
        assert_eq!(pr.reason.top.code.category, ReasonCategory::VerifyFailed);
    }

    #[test]
    fn non_coeff_payload_is_not_applicable() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
        let item = WorkItem::new(StateData::CompetitionResolved(
            cobra_orchestrator::CompetitionResolvedPayload { group_id: 0 },
        ));
        let pr = run_signature_cob_candidate(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NotApplicable);
    }
}
