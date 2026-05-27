//! `SignatureMultivarPolyRecovery` pass — tries to recover a verified
//! multivariate polynomial form for the signature-state item by
//! escalating through degrees 2..=4. Gated on:
//!
//! - `num_vars <= 6` (tensor-product forward differences explode past
//!   that — 5^6 = 15625 evaluations per degree-4 attempt)
//! - the classifier-set `HAS_MULTIVAR_HIGH_POWER` flag
//! - a full-width evaluator (otherwise verification can't run)
//!
//! Emits a verified `CandidateRecord` into the parent competition
//! group; the winning candidate is materialised by `ResolveCompetition`
//! once all handles are released.

use cobra_core::classification::StructuralFlag;
use cobra_core::expr_cost::compute_cost;
use cobra_core::pass_contract::{ReasonDetail, VerificationState};
use cobra_core::result::Result;

use cobra_ir::{recover_and_verify_poly, PolyRecoveryResult};
use cobra_orchestrator::{
    CandidateRecord, ItemDisposition, OrchestratorContext, PassDecision, PassId, PassResult,
    StateData, WorkItem,
};

use crate::candidate_normalize::{
    signature_certificate_for_candidate, submit_normalized_candidate,
};
use crate::mapped_evaluator::build_mapped_evaluator;
use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};

fn has_multivar_flag(item: &WorkItem) -> bool {
    item.features
        .classification
        .as_ref()
        .is_some_and(|c| c.flags.contains(StructuralFlag::HAS_MULTIVAR_HIGH_POWER))
}

/// Pass body. Runs degree-escalating polynomial recovery when the
/// classifier flags `HAS_MULTIVAR_HIGH_POWER` and the problem fits
/// within the `num_vars <= 6` gate.
#[allow(clippy::unnecessary_wraps)]
pub fn run_signature_multivar_poly_recovery(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::Signature(payload) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };
    let sub = &payload.ctx;
    let num_vars = sub.real_vars.len() as u32;

    if !has_multivar_flag(item) || num_vars > 6 {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    // Use `BuildMappedEvaluator` so the arity seen by
    // `recover_multivar_poly` matches `num_vars = real_vars.len()`,
    // whether we're at the top level or inside a residual /
    // lifted-outer signature solve.
    let Some(eval_owned) = build_mapped_evaluator(ctx, sub, item) else {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };
    let eval = &eval_owned;

    let support: Vec<u32> = (0..num_vars).collect();

    let verify = |eval: &cobra_core::evaluator::Evaluator,
                  arity: u32,
                  candidate: &cobra_core::expr::Expr,
                  bitwidth: u32| {
        full_width_check_eval(eval, arity, candidate, bitwidth, DEFAULT_NUM_SAMPLES).passed
    };

    let recovery = recover_and_verify_poly(eval, &support, num_vars, ctx.bitwidth, 4, 2, verify);

    let Some(PolyRecoveryResult { expr, .. }) = recovery.take_payload() else {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let cost = compute_cost(&expr).cost;
    let lean_signature_certificate = signature_certificate_for_candidate(
        ctx.bitwidth,
        &sub.elimination.reduced_sig,
        &sub.real_vars,
        &expr,
    );
    let group_id = item
        .group_id
        .expect("SignatureMultivarPolyRecovery requires a group_id");

    submit_normalized_candidate(
        &mut ctx.competition_groups,
        group_id,
        CandidateRecord {
            expr,
            cost,
            verification: VerificationState::Verified,
            real_vars: sub.real_vars.clone(),
            source_pass: PassId::SignatureMultivarPolyRecovery,
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

/// Applicability guard — signature-state only.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::Signature(_))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::classification::{Classification, SemanticClass};
    use cobra_core::evaluator::Evaluator;
    use cobra_core::expr::Expr;
    use cobra_core::simplify_outcome::Options;
    use cobra_orchestrator::{
        create_group, EliminationResult, SignatureStatePayload, SignatureSubproblemContext,
    };

    fn mk_item(
        orig: &Expr,
        real_vars: Vec<String>,
        sig: Vec<u64>,
        ctx: &mut OrchestratorContext,
        with_multivar_flag: bool,
    ) -> WorkItem {
        let elim = EliminationResult {
            reduced_sig: sig.clone(),
            real_vars: real_vars.clone(),
            spurious_vars: Vec::new(),
        };
        let payload = SignatureStatePayload {
            ctx: SignatureSubproblemContext {
                sig,
                real_vars,
                elimination: elim,
                original_indices: Vec::new(),
                needs_original_space_verification: false,
            },
        };
        let mut item = WorkItem::new(StateData::Signature(Box::new(payload)));
        let gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        item.group_id = Some(gid);
        ctx.evaluator = Some(Evaluator::from_expr(orig, ctx.bitwidth));

        let mut cls = Classification {
            semantic: SemanticClass::Polynomial,
            flags: StructuralFlag::HAS_MUL,
        };
        if with_multivar_flag {
            cls.flags |= StructuralFlag::HAS_MULTIVAR_HIGH_POWER;
        }
        item.features.classification = Some(cls);
        item
    }

    #[test]
    fn recovers_two_var_quadratic() {
        let orig = Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::mul(Expr::variable(0), Expr::variable(0)),
        );
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        // Signature at Boolean width doesn't matter for this path — the
        // pass uses the evaluator, not the reduced sig. But plumb a
        // valid 4-entry vector anyway.
        let sig = vec![0u64, 1, 0, 2];
        let item = mk_item(&orig, vec!["x".into(), "y".into()], sig, &mut ctx, true);
        let gid = item.group_id.unwrap();

        let pr = run_signature_multivar_poly_recovery(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);

        let best = ctx.competition_groups[&gid]
            .best
            .as_ref()
            .expect("candidate submitted");
        assert_eq!(best.source_pass, PassId::SignatureMultivarPolyRecovery);
        assert_eq!(best.verification, VerificationState::Verified);
    }

    #[test]
    fn skips_when_multivar_flag_missing() {
        let orig = Expr::mul(Expr::variable(0), Expr::variable(1));
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let sig = vec![0u64, 0, 0, 1];
        let item = mk_item(&orig, vec!["x".into(), "y".into()], sig, &mut ctx, false);
        let pr = run_signature_multivar_poly_recovery(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
    }

    #[test]
    fn skips_when_num_vars_exceeds_six() {
        let mut ctx = OrchestratorContext::new(
            Options::default(),
            (0..7).map(|i| format!("x{i}")).collect(),
            64,
        );
        let vars: Vec<String> = (0..7).map(|i| format!("x{i}")).collect();
        let orig = Expr::variable(0);
        let sig = vec![0u64; 1 << 7];
        let item = mk_item(&orig, vars, sig, &mut ctx, true);
        let pr = run_signature_multivar_poly_recovery(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
    }

    #[test]
    fn non_signature_payload_is_not_applicable() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
        let item = WorkItem::new(StateData::CompetitionResolved(
            cobra_orchestrator::CompetitionResolvedPayload { group_id: 0 },
        ));
        let pr = run_signature_multivar_poly_recovery(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NotApplicable);
    }
}
