//! `PrepareCoeffModel` pass — transforms a signature-state work item
//! into a coefficient-state child by running the AND-monomial
//! change-of-basis interpolation. Downstream passes
//! (`SignatureCobCandidate`, `SignatureSingletonPolyRecovery`) consume
//! the resulting [`SignatureCoeffStatePayload`].
//!
//! The pass acquires an extra handle on the parent's competition group
//! — the child inherits the group so that every `CoB`-derived candidate
//! races against the same baseline. Public seeding and
//! `BuildSignatureState` now create that group before signature
//! techniques run; the fallback creation path only protects direct
//! pass-level callers.

use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame,
};
use cobra_core::result::Result;

use cobra_ir::interpolate_coefficients;
use cobra_orchestrator::{
    acquire_handle, create_group, ItemDisposition, OrchestratorContext, PassDecision, PassResult,
    SignatureCoeffStatePayload, StateData, WorkItem,
};

fn guard_failed(message: &'static str) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category: ReasonCategory::GuardFailed,
                domain: ReasonDomain::Signature,
                subcode: 0,
            },
            message: message.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

/// Pass body. Consumes a `Signature` payload; emits a `SignatureCoeff`
/// child carrying the interpolated AND-monomial coefficient vector.
#[allow(clippy::unnecessary_wraps)]
pub fn run_prepare_coeff_model(
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
    let sig = sub.elimination.reduced_sig.clone();
    let num_vars = sub.real_vars.len() as u32;
    let expected = 1usize << num_vars;

    if sig.len() != expected {
        return Ok(PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: guard_failed("Reduced signature arity does not match the active variable set"),
        });
    }

    let coeffs = interpolate_coefficients(sig, num_vars, ctx.bitwidth);

    // Reuse the item's group when it already has one; otherwise create
    // a fresh group for direct pass-level callers.
    let group_id = if let Some(gid) = item.group_id {
        acquire_handle(&mut ctx.competition_groups, gid);
        gid
    } else {
        create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None)
    };

    let child_payload = SignatureCoeffStatePayload {
        ctx: sub.clone(),
        coeffs,
    };
    let mut child = item.clone();
    child.payload = StateData::SignatureCoeff(Box::new(child_payload));
    child.metadata.lean_certificate = None;
    child.metadata.lean_signature_certificate = None;
    child.signature_recursion_depth = item.signature_recursion_depth.saturating_add(1);
    child.attempted_mask = 0;
    child.group_id = Some(group_id);

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::RetainCurrent,
        next: vec![child],
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard — only signature-state items.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::Signature(_))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::simplify_outcome::Options;
    use cobra_orchestrator::{
        create_group, EliminationResult, SignatureStatePayload, SignatureSubproblemContext,
    };

    fn mk_sig_item(
        sig: Vec<u64>,
        real_vars: Vec<String>,
        ctx: &mut OrchestratorContext,
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
        item
    }

    #[test]
    fn emits_coeff_child_for_two_var_signature() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let mut item = mk_sig_item(vec![0, 1, 1, 0], vec!["x".into(), "y".into()], &mut ctx);
        item.metadata.lean_certificate = Some(cobra_orchestrator::LeanCertificate::new(
            64,
            cobra_core::expr::Expr::variable(0),
            cobra_core::expr::Expr::variable(0),
        ));
        item.metadata.lean_signature_certificate =
            cobra_orchestrator::LeanSignatureCertificate::new(
                64,
                1,
                vec![0, 1],
                cobra_core::expr::Expr::variable(0),
            );
        let gid_before = item.group_id.unwrap();
        let handles_before = ctx.competition_groups[&gid_before].open_handles;

        let pr = run_prepare_coeff_model(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        assert_eq!(pr.next.len(), 1);

        let StateData::SignatureCoeff(p) = &pr.next[0].payload else {
            panic!("expected SignatureCoeff payload");
        };
        // Coefficients for XOR: [0, 1, 1, -2 mod 2^64]
        assert_eq!(p.coeffs[0], 0);
        assert_eq!(p.coeffs[1], 1);
        assert_eq!(p.coeffs[2], 1);
        assert_eq!(p.coeffs[3], u64::MAX.wrapping_sub(1));

        // Handle was acquired on the parent group.
        let handles_after = ctx.competition_groups[&gid_before].open_handles;
        assert_eq!(handles_after, handles_before + 1);

        // Recursion depth advanced.
        assert_eq!(pr.next[0].signature_recursion_depth, 1);
        assert!(pr.next[0].metadata.lean_certificate.is_none());
        assert!(pr.next[0].metadata.lean_signature_certificate.is_none());
    }

    #[test]
    fn blocks_when_sig_len_mismatches() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        // sig has 3 entries but num_vars = 2 expects 4.
        let elim = EliminationResult {
            reduced_sig: vec![0, 1, 1],
            real_vars: vec!["x".into(), "y".into()],
            spurious_vars: Vec::new(),
        };
        let payload = SignatureStatePayload {
            ctx: SignatureSubproblemContext {
                sig: vec![0, 1, 1],
                real_vars: vec!["x".into(), "y".into()],
                elimination: elim,
                original_indices: Vec::new(),
                needs_original_space_verification: false,
            },
        };
        let mut item = WorkItem::new(StateData::Signature(Box::new(payload)));
        let gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        item.group_id = Some(gid);

        let pr = run_prepare_coeff_model(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Blocked);
        assert_eq!(pr.reason.top.code.category, ReasonCategory::GuardFailed);
    }

    #[test]
    fn non_signature_payload_is_not_applicable() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
        let item = WorkItem::new(StateData::CompetitionResolved(
            cobra_orchestrator::CompetitionResolvedPayload { group_id: 0 },
        ));
        let pr = run_prepare_coeff_model(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NotApplicable);
    }
}
