//! `RunVerifyCandidate` pass. Full-width-checks a candidate
//! expression against the context's original evaluator; on success,
//! emits a new `CandidatePayload` with
//! `needs_original_space_verification = false` and
//! `VerificationState::Verified`, which lets the main loop accept it.

use crate::core::expr::Expr;
use crate::core::expr_rewrite::try_build_var_support;
use crate::core::expr_utils::remap_var_indices;
use crate::core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, VerificationState,
};
use crate::core::result::Result;
use std::sync::Arc;

use crate::orchestrator::{
    CandidatePayload, ItemDisposition, LeanCertificate, OrchestratorContext, PassDecision,
    PassResult, StateData, WorkItem,
};

use crate::passes::spot_check::verify_in_original_space;

#[allow(clippy::unnecessary_wraps)]
pub fn run_verify_candidate(item: &WorkItem, ctx: &mut OrchestratorContext) -> Result<PassResult> {
    let StateData::Candidate(cand) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };
    if !cand.needs_original_space_verification {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    // Require an evaluator — VerifyCandidate cannot do a full-width
    // check without it.
    let Some(eval) = ctx.evaluator.as_ref() else {
        return Ok(PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail {
                top: ReasonFrame {
                    code: ReasonCode {
                        category: ReasonCategory::GuardFailed,
                        domain: ReasonDomain::Verifier,
                        subcode: 0,
                    },
                    message: "Verification requires evaluator".into(),
                    fields: Vec::new(),
                },
                causes: Vec::new(),
            },
        });
    };

    let check = verify_in_original_space(
        eval,
        &ctx.original_vars,
        &cand.real_vars,
        &cand.expr,
        ctx.bitwidth,
    );

    if check.passed {
        let certificate = remapped_endpoint_certificate(ctx, &cand.expr, &cand.real_vars);
        let Some(certificate) = certificate else {
            return Ok(PassResult {
                decision: PassDecision::NoProgress,
                disposition: ItemDisposition::RetainCurrent,
                next: Vec::new(),
                reason: ReasonDetail {
                    top: ReasonFrame {
                        code: ReasonCode {
                            category: ReasonCategory::VerifyFailed,
                            domain: ReasonDomain::Verifier,
                            subcode: 1,
                        },
                        message:
                            "Finite checks passed, but no replayable proof covers the exact candidate"
                                .into(),
                        fields: Vec::new(),
                    },
                    causes: Vec::new(),
                },
            });
        };
        let verified_payload = CandidatePayload {
            expr: cand.expr.clone_tree(),
            real_vars: cand.real_vars.clone(),
            cost: cand.cost,
            producing_pass: cand.producing_pass,
            needs_original_space_verification: false,
        };
        let mut verified_item = item.clone();
        verified_item.payload = StateData::Candidate(Box::new(verified_payload));
        verified_item.metadata.verification = VerificationState::Verified;
        verified_item.metadata.lean_certificate = Some(certificate);

        return Ok(PassResult {
            decision: PassDecision::Advance,
            disposition: ItemDisposition::ConsumeCurrent,
            next: vec![verified_item],
            reason: ReasonDetail::default(),
        });
    }

    Ok(PassResult {
        decision: PassDecision::NoProgress,
        disposition: ItemDisposition::RetainCurrent,
        next: Vec::new(),
        reason: ReasonDetail {
            top: ReasonFrame {
                code: ReasonCode {
                    category: ReasonCategory::VerifyFailed,
                    domain: ReasonDomain::Orchestrator,
                    subcode: 0,
                },
                message: "Full-width verification failed".into(),
                fields: Vec::new(),
            },
            causes: Vec::new(),
        },
    })
}

/// Applicability guard — `CandidatePayload` only.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::Candidate(_))
}

fn remapped_endpoint_certificate(
    ctx: &OrchestratorContext,
    expr: &Expr,
    real_vars: &[String],
) -> Option<LeanCertificate> {
    let original = ctx.original_expr.as_ref()?;
    let remapped = if real_vars == ctx.original_vars {
        expr.clone_tree()
    } else {
        let idx_map = try_build_var_support(&ctx.original_vars, real_vars)?;
        let mut remapped = expr.clone_tree();
        remap_var_indices(Arc::make_mut(&mut remapped), &idx_map);
        remapped
    };
    LeanCertificate::try_single_rewrite_between_64(
        ctx.bitwidth,
        original.clone_tree(),
        remapped.clone_tree(),
    )
    .or_else(|| {
        (**original == *remapped)
            .then(|| LeanCertificate::new(ctx.bitwidth, original.clone_tree(), remapped))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::evaluator::Evaluator;
    use crate::core::expr::Expr;
    use crate::core::expr_cost::ExprCost;
    use crate::core::simplify_outcome::Options;
    use crate::orchestrator::PassId;

    fn mk_cand_item(simplified: Arc<Expr>) -> WorkItem {
        WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
            expr: simplified,
            real_vars: vec!["x".into(), "y".into()],
            cost: ExprCost::default(),
            producing_pass: PassId::VerifyCandidate,
            needs_original_space_verification: true,
        })))
    }

    #[test]
    fn verify_passes_on_equivalent_candidate() {
        let original = Expr::add(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::or(Expr::variable(0), Expr::variable(1)),
        );
        let simplified = Expr::add(Expr::variable(0), Expr::variable(1));

        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        ctx.original_expr = Some(original.clone_tree());
        ctx.evaluator = Some(Evaluator::from_expr(&original, 64));

        let item = mk_cand_item(simplified);
        let pr = run_verify_candidate(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        assert_eq!(pr.next.len(), 1);
        if let StateData::Candidate(verified) = &pr.next[0].payload {
            assert!(!verified.needs_original_space_verification);
        } else {
            panic!("expected Candidate payload");
        }
        assert_eq!(
            pr.next[0].metadata.verification,
            VerificationState::Verified
        );
        assert!(
            pr.next[0].metadata.lean_certificate.is_some(),
            "verified original-space candidate should get endpoint Lean certificate"
        );
    }

    #[test]
    fn verify_attaches_endpoint_certificate_for_remapped_vars() {
        let original = Expr::variable(0);
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        ctx.original_expr = Some(original.clone_tree());
        ctx.evaluator = Some(Evaluator::from_expr(&original, 64));

        let mut item = mk_cand_item(Expr::variable(0));
        if let StateData::Candidate(cand) = &mut item.payload {
            cand.real_vars = vec!["x".into()];
        }

        let pr = run_verify_candidate(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        let cert = pr.next[0]
            .metadata
            .lean_certificate
            .as_ref()
            .expect("remapped endpoint certificate");
        assert_eq!(*cert.original, *original);
        assert_eq!(*cert.simplified, *Expr::variable(0));
    }

    #[test]
    fn verify_fails_on_non_equivalent_candidate() {
        // Original = x + y, simplified = x * y — not equivalent.
        let original = Expr::add(Expr::variable(0), Expr::variable(1));
        let bogus = Expr::mul(Expr::variable(0), Expr::variable(1));

        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        ctx.evaluator = Some(Evaluator::from_expr(&original, 64));

        let item = mk_cand_item(bogus);
        let pr = run_verify_candidate(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
        assert_eq!(pr.disposition, ItemDisposition::RetainCurrent);
        assert_eq!(pr.reason.top.code.category, ReasonCategory::VerifyFailed);
    }

    #[test]
    fn finite_probe_survivor_is_not_promoted_without_replayable_proof() {
        // This expression is one only at x=27. It survives the deterministic
        // finite probe schedule against zero, but no theorem proves it equal
        // to zero over the complete 64-bit domain.
        let target = Expr::mul(
            Expr::mul(Expr::constant(3), Expr::constant(3)),
            Expr::constant(3),
        );
        let difference = Expr::xor(Expr::variable(0), target);
        let nonzero = Expr::shr(Expr::or(difference.clone_tree(), Expr::neg(difference)), 63);
        let original = Expr::xor(Expr::constant(1), nonzero);

        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        ctx.original_expr = Some(original.clone_tree());
        ctx.evaluator = Some(Evaluator::from_expr(&original, 64));

        let item = WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
            expr: Expr::constant(0),
            real_vars: vec!["x".into()],
            cost: ExprCost::default(),
            producing_pass: PassId::VerifyCandidate,
            needs_original_space_verification: true,
        })));
        let result = run_verify_candidate(&item, &mut ctx).expect("verification pass");
        assert_eq!(result.decision, PassDecision::NoProgress);
        assert!(result.next.is_empty());
        assert!(result.reason.top.message.contains("replayable proof"));
    }

    #[test]
    fn verify_blocked_without_evaluator() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        // No evaluator installed.
        let item = mk_cand_item(Expr::add(Expr::variable(0), Expr::variable(1)));
        let pr = run_verify_candidate(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Blocked);
        assert_eq!(pr.reason.top.code.category, ReasonCategory::GuardFailed);
    }

    #[test]
    fn verify_noop_when_already_verified() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
        let mut payload = CandidatePayload {
            expr: Expr::variable(0),
            real_vars: vec![],
            cost: ExprCost::default(),
            producing_pass: PassId::VerifyCandidate,
            needs_original_space_verification: false,
        };
        payload.real_vars.push("x".into());
        let item = WorkItem::new(StateData::Candidate(Box::new(payload)));
        let pr = run_verify_candidate(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NotApplicable);
    }
}
