//! `RunSignaturePatternMatch` pass — turns a signature-keyed pattern
//! with the competition-group submission path simplified to a direct
//! worklist push (groups will be wired through the signature passes
//! in a later session).

use cobra_core::expr_cost::compute_cost;
use cobra_core::pass_contract::{ReasonDetail, VerificationState};
use cobra_core::result::Result;

use cobra_orchestrator::{
    CandidatePayload, CandidateRecord, ItemDisposition, OrchestratorContext, PassDecision, PassId,
    PassResult, StateData, WorkItem,
};

use crate::candidate_normalize::{
    signature_certificate_for_candidate, submit_normalized_candidate,
};
use crate::mapped_evaluator::build_mapped_evaluator;
use crate::pattern_matcher::match_pattern;
use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};

/// look up the reduced sig in the pattern table; on a hit, build a
/// `Candidate` work item carrying the simplified expression. The
/// candidate's `needs_original_space_verification` flag is inherited
/// from the upstream `SignatureSubproblemContext` — when it's `true`,
/// the main loop routes the candidate through `RunVerifyCandidate`
/// before accepting it.
#[allow(clippy::unnecessary_wraps)]
pub fn run_signature_pattern_match(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::Signature(payload) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };
    let sub = &payload.ctx;
    let sig = &sub.elimination.reduced_sig;
    let num_vars = sub.real_vars.len() as u32;

    let Some(matched) = match_pattern(sig, num_vars, ctx.bitwidth) else {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    // Optional pre-emptive full-width check: when an evaluator is
    // available we can short-circuit a verify-failed candidate before
    // `BuildMappedEvaluator` + `FullWidthCheckEval` step — the mapped
    // evaluator is already in the reduced `real_vars` space, so no
    // `verify_in_original_space` remap is needed.
    if let Some(mapped) = build_mapped_evaluator(ctx, sub, item) {
        let check = full_width_check_eval(
            &mapped,
            num_vars,
            &matched,
            ctx.bitwidth,
            DEFAULT_NUM_SAMPLES,
        );
        if !check.passed {
            return Ok(PassResult {
                decision: PassDecision::NoProgress,
                disposition: ItemDisposition::RetainCurrent,
                next: Vec::new(),
                reason: ReasonDetail::default(),
            });
        }
    }

    // Pattern match on the Boolean signature is exact by construction.
    // When the item belongs to a competition group (residual /
    // lifted-outer / operand-split sub-problems), submit the candidate
    // directly to the group so its continuation (e.g.
    // `RemainderRecombineCont`) can stitch the full answer and
    // full-width-verify it. Otherwise emit a top-level candidate as
    // before.
    let cost = compute_cost(&matched).cost;
    let lean_signature_certificate =
        signature_certificate_for_candidate(ctx.bitwidth, sig, &sub.real_vars, &matched);
    if let Some(gid) = item.group_id {
        submit_normalized_candidate(
            &mut ctx.competition_groups,
            gid,
            CandidateRecord {
                expr: matched,
                cost,
                verification: VerificationState::Verified,
                real_vars: sub.real_vars.clone(),
                source_pass: PassId::SignaturePatternMatch,
                needs_original_space_verification: sub.needs_original_space_verification,
                sig_vector: sub.elimination.reduced_sig.clone(),
                lean_certificate: None,
                lean_signature_certificate,
            },
            ctx.bitwidth,
        );
        return Ok(PassResult {
            decision: PassDecision::Advance,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    let candidate = CandidatePayload {
        expr: matched,
        real_vars: sub.real_vars.clone(),
        cost,
        producing_pass: PassId::SignaturePatternMatch,
        needs_original_space_verification: sub.needs_original_space_verification,
    };
    let mut child = item.clone();
    child.payload = StateData::Candidate(Box::new(candidate));
    child.metadata.verification = VerificationState::Verified;
    child.metadata.sig_vector.clone_from(sig);
    child.metadata.lean_certificate = None;
    child.metadata.lean_signature_certificate = lean_signature_certificate;

    Ok(PassResult {
        decision: PassDecision::SolvedCandidate,
        disposition: ItemDisposition::RetainCurrent,
        next: vec![child],
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard — only fires on signature-state items.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::Signature(_))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluator::Evaluator;
    use cobra_core::expr::{Expr, Kind};
    use cobra_core::simplify_outcome::Options;
    use cobra_orchestrator::{
        EliminationResult, SignatureStatePayload, SignatureSubproblemContext,
    };

    fn mk_sig_item(sig: Vec<u64>, real_vars: Vec<String>, needs_verify: bool) -> WorkItem {
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
                needs_original_space_verification: needs_verify,
            },
        };
        WorkItem::new(StateData::Signature(Box::new(payload)))
    }

    #[test]
    fn pattern_match_hits_xor_signature() {
        // x ^ y over 2 vars
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let mut item = mk_sig_item(vec![0, 1, 1, 0], vec!["x".into(), "y".into()], false);
        item.metadata.lean_certificate = Some(cobra_orchestrator::LeanCertificate::new(
            64,
            Expr::constant(0),
            Expr::constant(0),
        ));
        let pr = run_signature_pattern_match(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::SolvedCandidate);
        assert_eq!(pr.disposition, ItemDisposition::RetainCurrent);
        assert_eq!(pr.next.len(), 1);
        match &pr.next[0].payload {
            StateData::Candidate(c) => {
                assert!(matches!(c.expr.kind, Kind::Xor));
                assert!(!c.needs_original_space_verification);
                assert_eq!(c.producing_pass, PassId::SignaturePatternMatch);
            }
            _ => panic!("expected Candidate payload"),
        }
        assert_eq!(
            pr.next[0].metadata.verification,
            VerificationState::Verified
        );
        assert!(pr.next[0].metadata.lean_certificate.is_none());
        let cert = pr.next[0]
            .metadata
            .lean_signature_certificate
            .as_ref()
            .expect("Lean signature certificate");
        assert!(cert.matches_signature(
            64,
            2,
            &[0, 1, 1, 0],
            match &pr.next[0].payload {
                StateData::Candidate(c) => &c.expr,
                _ => unreachable!(),
            },
        ));
    }

    #[test]
    fn pattern_match_no_progress_for_unknown_sig() {
        // 3-var non-boolean — pattern matcher misses for now.
        let mut ctx = OrchestratorContext::new(
            Options::default(),
            vec!["x".into(), "y".into(), "z".into()],
            64,
        );
        let item = mk_sig_item(
            vec![0, 1, 2, 3, 4, 5, 6, 7],
            vec!["x".into(), "y".into(), "z".into()],
            false,
        );
        let pr = run_signature_pattern_match(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
        assert!(pr.next.is_empty());
    }

    #[test]
    fn pattern_match_with_evaluator_pre_checks_full_width() {
        // Original = (x & y) + (x | y) (which equals x + y at full width).
        // Sig at boolean inputs = [0, 1, 1, 2] — non-Boolean-valued, so
        // the 2-var pattern table misses; pass should report NoProgress
        // so other signature techniques get a shot.
        let original = Expr::add(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::or(Expr::variable(0), Expr::variable(1)),
        );
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        ctx.evaluator = Some(Evaluator::from_expr(&original, 64));
        let item = mk_sig_item(vec![0, 1, 1, 2], vec!["x".into(), "y".into()], true);
        let pr = run_signature_pattern_match(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
    }

    #[test]
    fn pattern_match_noop_on_non_signature_payload() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
        let item = WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
            expr: Expr::variable(0),
            real_vars: Vec::new(),
            cost: cobra_core::expr_cost::ExprCost::default(),
            producing_pass: PassId::VerifyCandidate,
            needs_original_space_verification: false,
        })));
        let pr = run_signature_pattern_match(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NotApplicable);
    }
}
