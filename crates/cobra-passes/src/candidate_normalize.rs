//! Late candidate normalization before competition submission.

use crate::core::evaluate_boolean_signature;
use crate::core::expr::Expr;
use crate::core::expr_cost::compute_cost;
use crate::core::pass_contract::VerificationState;
use crate::orchestrator::{
    submit_candidate, CandidateRecord, GroupId, GroupMap, LeanCertificate, LeanSignatureCertificate,
};

use crate::passes::pattern_matcher::normalize_late_candidate_expr;

/// Append `next` onto an optional Lean certificate chain, seeding the
/// chain when it is empty. Wraps [`LeanCertificate::merge_step_chain`]
/// so the rewrite passes share one definition.
#[must_use]
pub fn merge_certificate(
    previous: Option<LeanCertificate>,
    next: LeanCertificate,
) -> Option<LeanCertificate> {
    match previous {
        Some(prev) => prev.merge_step_chain(next),
        None => Some(next),
    }
}

#[must_use]
pub fn normalize_candidate_record(mut record: CandidateRecord, bitwidth: u32) -> CandidateRecord {
    let before = record.expr.clone_tree();
    record.expr = normalize_late_candidate_expr(record.expr, bitwidth);
    if *record.expr != *before {
        record.verification = VerificationState::Unverified;
        record.needs_original_space_verification = true;
        record.lean_certificate = None;
    }
    record.cost = compute_cost(&record.expr).cost;
    record.lean_signature_certificate = signature_certificate_for_candidate(
        bitwidth,
        &record.sig_vector,
        &record.real_vars,
        &record.expr,
    );
    record
}

pub fn submit_normalized_candidate(
    groups: &mut GroupMap,
    group_id: GroupId,
    record: CandidateRecord,
    bitwidth: u32,
) -> bool {
    let record = normalize_candidate_record(record, bitwidth);
    if record.verification == VerificationState::Verified
        && record.lean_signature_certificate.is_none()
    {
        return false;
    }
    submit_candidate(groups, group_id, record, bitwidth)
}

#[must_use]
pub fn signature_certificate_for_candidate(
    bitwidth: u32,
    signature: &[u64],
    real_vars: &[String],
    expr: &Expr,
) -> Option<LeanSignatureCertificate> {
    let num_vars = real_vars.len() as u32;
    if evaluate_boolean_signature(expr, num_vars, bitwidth) != signature {
        return None;
    }
    LeanSignatureCertificate::new(bitwidth, num_vars, signature.to_vec(), expr.clone_tree())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signature_certificate_requires_matching_truth_table() {
        let vars = vec!["x".to_owned()];
        let cert = signature_certificate_for_candidate(64, &[0, 1], &vars, &Expr::variable(0));
        assert!(cert.is_some());

        let stale = signature_certificate_for_candidate(64, &[1, 0], &vars, &Expr::variable(0));
        assert!(stale.is_none());
    }

    #[test]
    fn changed_candidate_invalidates_expression_bound_verification() {
        let expr = Expr::add(Expr::variable(0), Expr::constant(0));
        let record = CandidateRecord {
            expr: expr.clone_tree(),
            cost: compute_cost(&expr).cost,
            verification: VerificationState::Verified,
            real_vars: vec!["x".to_owned()],
            source_pass: crate::orchestrator::PassId::SignaturePatternMatch,
            needs_original_space_verification: false,
            sig_vector: vec![0, 1],
            lean_certificate: Some(LeanCertificate {
                bitwidth: 64,
                original: expr.clone_tree(),
                simplified: expr,
                steps: Vec::new(),
            }),
            lean_signature_certificate: None,
        };

        let normalized = normalize_candidate_record(record, 64);
        assert_eq!(normalized.verification, VerificationState::Unverified);
        assert!(normalized.needs_original_space_verification);
        assert!(normalized.lean_certificate.is_none());
    }

    #[test]
    fn verified_normalized_candidate_requires_proof_metadata() {
        let mut groups = GroupMap::default();
        groups.insert(0, crate::orchestrator::CompetitionGroup::default());
        let submitted = submit_normalized_candidate(
            &mut groups,
            0,
            CandidateRecord {
                expr: Expr::variable(0),
                cost: crate::core::expr_cost::ExprCost::default(),
                verification: VerificationState::Verified,
                real_vars: vec!["x".to_owned()],
                source_pass: crate::orchestrator::PassId::SignaturePatternMatch,
                needs_original_space_verification: false,
                sig_vector: vec![1, 0],
                lean_certificate: None,
                lean_signature_certificate: None,
            },
            64,
        );

        assert!(!submitted);
        assert!(groups[&0].best.is_none());
    }

    #[test]
    fn verified_normalized_candidate_requires_matching_signature_certificate() {
        let mut groups = GroupMap::default();
        groups.insert(0, crate::orchestrator::CompetitionGroup::default());
        let submitted = submit_normalized_candidate(
            &mut groups,
            0,
            CandidateRecord {
                expr: Expr::variable(0),
                cost: crate::core::expr_cost::ExprCost::default(),
                verification: VerificationState::Verified,
                real_vars: vec!["x".to_owned()],
                source_pass: crate::orchestrator::PassId::SignaturePatternMatch,
                needs_original_space_verification: false,
                sig_vector: vec![1, 0],
                lean_certificate: Some(crate::orchestrator::LeanCertificate::new(
                    64,
                    Expr::variable(0),
                    Expr::variable(0),
                )),
                lean_signature_certificate: None,
            },
            64,
        );

        assert!(!submitted);
        assert!(groups[&0].best.is_none());
    }
}
