//! Late candidate normalization before competition submission.

use cobra_core::expr_cost::compute_cost;
use cobra_orchestrator::{submit_candidate, CandidateRecord, GroupId, GroupMap};

use crate::pattern_matcher::normalize_late_candidate_expr;

#[must_use]
pub fn normalize_candidate_record(mut record: CandidateRecord, bitwidth: u32) -> CandidateRecord {
    record.expr = normalize_late_candidate_expr(record.expr, bitwidth);
    record.cost = compute_cost(&record.expr).cost;
    record
}

pub fn submit_normalized_candidate(
    groups: &mut GroupMap,
    group_id: GroupId,
    record: CandidateRecord,
    bitwidth: u32,
) -> bool {
    submit_candidate(
        groups,
        group_id,
        normalize_candidate_record(record, bitwidth),
    )
}
