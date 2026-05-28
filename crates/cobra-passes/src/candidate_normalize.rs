//! Late candidate normalization before competition submission.

use cobra_core::evaluate_boolean_signature;
use cobra_core::expr::Expr;
use cobra_core::expr_cost::compute_cost;
use cobra_core::pass_contract::VerificationState;
use cobra_orchestrator::{
    submit_candidate, CandidateRecord, GroupId, GroupMap, LeanSignatureCertificate,
};

use crate::pattern_matcher::normalize_late_candidate_expr;

#[must_use]
pub fn normalize_candidate_record(mut record: CandidateRecord, bitwidth: u32) -> CandidateRecord {
    record.expr = normalize_late_candidate_expr(record.expr, bitwidth);
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
    fn verified_normalized_candidate_requires_proof_metadata() {
        let mut groups = GroupMap::default();
        groups.insert(0, cobra_orchestrator::CompetitionGroup::default());
        let submitted = submit_normalized_candidate(
            &mut groups,
            0,
            CandidateRecord {
                expr: Expr::variable(0),
                cost: cobra_core::expr_cost::ExprCost::default(),
                verification: VerificationState::Verified,
                real_vars: vec!["x".to_owned()],
                source_pass: cobra_orchestrator::PassId::SignaturePatternMatch,
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
        groups.insert(0, cobra_orchestrator::CompetitionGroup::default());
        let submitted = submit_normalized_candidate(
            &mut groups,
            0,
            CandidateRecord {
                expr: Expr::variable(0),
                cost: cobra_core::expr_cost::ExprCost::default(),
                verification: VerificationState::Verified,
                real_vars: vec!["x".to_owned()],
                source_pass: cobra_orchestrator::PassId::SignaturePatternMatch,
                needs_original_space_verification: false,
                sig_vector: vec![1, 0],
                lean_certificate: Some(cobra_orchestrator::LeanCertificate::new(
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
