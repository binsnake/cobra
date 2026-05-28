//! `lib/core/CompetitionGroup.{h,cpp}`.

use cobra_core::evaluate_boolean_signature;
use cobra_core::expr::Expr;
use cobra_core::expr_cost::{is_better, ExprCost};
use cobra_core::pass_contract::{ReasonDetail, VerificationState};
use cobra_verify::{LeanCertificate, LeanSignatureCertificate};

use crate::continuation::{ContinuationData, GroupId};
use crate::enums::PassId;
use crate::state::{CompetitionResolvedPayload, StateData};
use crate::work_item::WorkItem;

// Re-exported for API ergonomics — downstream code typically reaches for
// `competition::GroupId` / `competition::JoinId`.
pub use crate::continuation::JoinId;

#[derive(Clone, Debug)]
pub struct CandidateRecord {
    pub expr: Box<Expr>,
    pub cost: ExprCost,
    pub verification: VerificationState,
    pub real_vars: Vec<String>,
    pub source_pass: PassId,
    pub needs_original_space_verification: bool,
    pub sig_vector: Vec<u64>,
    pub lean_certificate: Option<LeanCertificate>,
    pub lean_signature_certificate: Option<LeanSignatureCertificate>,
}

/// Live competition group. Holds the best candidate seen so far, a
/// handle counter that gates resolution, an optional baseline cost
/// (rejecting anything not strictly better), and an optional
/// continuation for deferred recombination.
#[derive(Clone, Debug, Default)]
pub struct CompetitionGroup {
    pub open_handles: u32,
    pub best: Option<CandidateRecord>,
    pub baseline_cost: Option<ExprCost>,
    pub continuation: Option<ContinuationData>,
    pub technique_failures: Vec<ReasonDetail>,
}

impl CompetitionGroup {
    #[must_use]
    pub fn new(baseline_cost: Option<ExprCost>) -> Self {
        Self {
            open_handles: 1,
            best: None,
            baseline_cost,
            continuation: None,
            technique_failures: Vec::new(),
        }
    }
}

/// Pure helper separated from lifecycle logic: does this group hold a
/// verified candidate whose cost is within the budget? Used by the
/// scheduler to short-circuit decomposition passes when an algebraic
/// `HasVerifiedCandidate` but does not take a map — callers pass the
/// group directly so the fn is trivially testable.
#[must_use]
pub fn group_has_verified_candidate(
    group: &CompetitionGroup,
    max_weighted_size: u32,
    bitwidth: u32,
) -> bool {
    group.best.as_ref().is_some_and(|c| {
        c.verification == VerificationState::Verified
            && c.cost.weighted_size <= max_weighted_size
            && candidate_has_matching_signature_evidence(c, bitwidth)
    })
}

#[must_use]
pub fn candidate_has_matching_lean_evidence(record: &CandidateRecord, bitwidth: u32) -> bool {
    let endpoint_ok = record.lean_certificate.as_ref().is_some_and(|cert| {
        endpoint_certificate_matches_candidate_signature(
            cert,
            bitwidth,
            &record.expr,
            &record.real_vars,
            &record.sig_vector,
        )
    });
    let signature_ok = record
        .lean_signature_certificate
        .as_ref()
        .is_some_and(|cert| {
            cert.matches_signature(
                bitwidth,
                record.real_vars.len() as u32,
                &record.sig_vector,
                &record.expr,
            )
        });
    endpoint_ok || signature_ok
}

#[must_use]
pub fn endpoint_certificate_matches_candidate_signature(
    cert: &LeanCertificate,
    bitwidth: u32,
    expr: &Expr,
    real_vars: &[String],
    sig_vector: &[u64],
) -> bool {
    cert.matches_endpoints(bitwidth, &cert.original, expr)
        && evaluate_boolean_signature(&cert.original, real_vars.len() as u32, bitwidth)
            == sig_vector
}

#[must_use]
pub fn candidate_has_matching_signature_evidence(record: &CandidateRecord, bitwidth: u32) -> bool {
    record
        .lean_signature_certificate
        .as_ref()
        .is_some_and(|cert| {
            cert.matches_signature(
                bitwidth,
                record.real_vars.len() as u32,
                &record.sig_vector,
                &record.expr,
            )
        })
}

/// `absl::flat_hash_map<GroupId, CompetitionGroup>`. Uses
/// `ahash::RandomState` under the hood — pin its seed at the call site
/// (orchestrator context) if determinism is required.
pub type GroupMap = std::collections::HashMap<GroupId, CompetitionGroup, ahash::RandomState>;

// ---------------------------------------------------------------
// ---------------------------------------------------------------

/// Allocate a fresh group with `open_handles = 1` and the supplied
pub fn create_group(
    groups: &mut GroupMap,
    next_id: &mut GroupId,
    baseline_cost: Option<ExprCost>,
) -> GroupId {
    let id = *next_id;
    *next_id = next_id.wrapping_add(1);
    groups.insert(id, CompetitionGroup::new(baseline_cost));
    id
}

/// Submit a candidate to `group_id`. Accepted iff:
/// - the group still exists (parent may have already been resolved and
///   erased in fanout — silent no-op in that case),
/// - the candidate strictly beats the baseline (when present), and
/// - the candidate strictly beats any incumbent `best`.
///
/// `SubmitCandidate`.
pub fn submit_candidate(
    groups: &mut GroupMap,
    group_id: GroupId,
    record: CandidateRecord,
    bitwidth: u32,
) -> bool {
    if record.verification == VerificationState::Verified
        && !candidate_has_matching_lean_evidence(&record, bitwidth)
    {
        return false;
    }
    let Some(group) = groups.get_mut(&group_id) else {
        return false;
    };
    if let Some(baseline) = group.baseline_cost {
        if !is_better(&record.cost, &baseline) {
            return false;
        }
    }
    match group.best.as_ref() {
        None => {
            group.best = Some(record);
            true
        }
        Some(current) if is_better(&record.cost, &current.cost) => {
            group.best = Some(record);
            true
        }
        Some(_) => false,
    }
}

/// Increment the group's handle count. Returns `false` if the group has
pub fn acquire_handle(groups: &mut GroupMap, group_id: GroupId) -> bool {
    match groups.get_mut(&group_id) {
        Some(g) => {
            g.open_handles += 1;
            true
        }
        None => false,
    }
}

/// Decrement the group's handle count. When the count hits zero,
/// returns a `WorkItem` carrying a `CompetitionResolved` payload so the
/// scheduler can run the `ResolveCompetition` pass. Late releases
/// (against an already-erased group) are silently accepted as no-ops.
pub fn release_handle(groups: &mut GroupMap, group_id: GroupId) -> Option<WorkItem> {
    let group = groups.get_mut(&group_id)?;
    debug_assert!(group.open_handles > 0);
    group.open_handles = group.open_handles.saturating_sub(1);
    if group.open_handles > 0 {
        return None;
    }
    Some(WorkItem::new(StateData::CompetitionResolved(
        CompetitionResolvedPayload { group_id },
    )))
}

/// `HasVerifiedCandidate`. Missing groups return `false`.
#[must_use]
pub fn has_verified_candidate(
    groups: &GroupMap,
    group_id: GroupId,
    max_weighted_size: u32,
    bitwidth: u32,
) -> bool {
    groups
        .get(&group_id)
        .is_some_and(|g| group_has_verified_candidate(g, max_weighted_size, bitwidth))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_record(ws: u32, verified: bool) -> CandidateRecord {
        let expr = Expr::variable(0);
        CandidateRecord {
            expr: expr.clone_tree(),
            cost: ExprCost {
                weighted_size: ws,
                nonlinear_mul_count: 0,
                max_depth: 1,
            },
            verification: if verified {
                VerificationState::Verified
            } else {
                VerificationState::Unverified
            },
            real_vars: vec!["x".into()],
            source_pass: PassId::ClassifyAst,
            needs_original_space_verification: false,
            sig_vector: vec![0, 1],
            lean_certificate: None,
            lean_signature_certificate: verified
                .then(|| LeanSignatureCertificate::new(64, 1, vec![0, 1], expr))
                .flatten(),
        }
    }

    fn mk_record_without_lean_evidence(ws: u32) -> CandidateRecord {
        let mut record = mk_record(ws, true);
        record.lean_certificate = None;
        record.lean_signature_certificate = None;
        record
    }

    fn mk_record_with_endpoint_evidence_only(ws: u32) -> CandidateRecord {
        let expr = Expr::variable(0);
        let mut record = mk_record(ws, true);
        record.lean_certificate = Some(LeanCertificate::new(64, expr.clone_tree(), expr));
        record.lean_signature_certificate = None;
        record
    }

    #[test]
    fn new_group_starts_with_one_handle() {
        let g = CompetitionGroup::new(None);
        assert_eq!(g.open_handles, 1);
        assert!(g.best.is_none());
        assert!(g.baseline_cost.is_none());
    }

    #[test]
    fn has_verified_candidate_checks_cost_budget() {
        let mut g = CompetitionGroup::new(None);
        assert!(!group_has_verified_candidate(&g, u32::MAX, 64));
        g.best = Some(mk_record(10, true));
        assert!(group_has_verified_candidate(&g, 10, 64));
        assert!(group_has_verified_candidate(&g, 20, 64));
        // Over budget
        assert!(!group_has_verified_candidate(&g, 5, 64));
    }

    #[test]
    fn has_verified_candidate_requires_verified_state() {
        let mut g = CompetitionGroup::new(None);
        g.best = Some(mk_record(5, false));
        assert!(!group_has_verified_candidate(&g, 100, 64));
    }

    #[test]
    fn has_verified_candidate_requires_lean_evidence() {
        let mut g = CompetitionGroup::new(None);
        g.best = Some(mk_record_without_lean_evidence(5));
        assert!(!group_has_verified_candidate(&g, 100, 64));
    }

    #[test]
    fn has_verified_candidate_requires_signature_evidence() {
        let mut g = CompetitionGroup::new(None);
        g.best = Some(mk_record_with_endpoint_evidence_only(5));
        assert!(!group_has_verified_candidate(&g, 100, 64));
    }

    fn empty_group_map() -> GroupMap {
        GroupMap::with_hasher(crate::context::determinism_seeds_ahash())
    }

    #[test]
    fn create_group_allocates_sequential_ids() {
        let mut groups = empty_group_map();
        let mut next = 0;
        assert_eq!(create_group(&mut groups, &mut next, None), 0);
        assert_eq!(create_group(&mut groups, &mut next, None), 1);
        assert_eq!(next, 2);
        assert_eq!(groups.len(), 2);
    }

    #[test]
    fn submit_candidate_requires_baseline_beat() {
        let mut groups = empty_group_map();
        let mut next = 0;
        // `mk_record` emits records with max_depth = 1, so match the
        // baseline's max_depth to keep the compare focused on weighted_size.
        let baseline = ExprCost {
            weighted_size: 10,
            nonlinear_mul_count: 0,
            max_depth: 1,
        };
        let id = create_group(&mut groups, &mut next, Some(baseline));
        // Equal to baseline → rejected
        assert!(!submit_candidate(&mut groups, id, mk_record(10, false), 64));
        // Strictly better → accepted
        assert!(submit_candidate(&mut groups, id, mk_record(5, false), 64));
        assert_eq!(groups[&id].best.as_ref().unwrap().cost.weighted_size, 5);
    }

    #[test]
    fn submit_candidate_keeps_best() {
        let mut groups = empty_group_map();
        let mut next = 0;
        let id = create_group(&mut groups, &mut next, None);
        assert!(submit_candidate(&mut groups, id, mk_record(8, false), 64));
        // Worse candidate → rejected
        assert!(!submit_candidate(&mut groups, id, mk_record(12, false), 64));
        // Strictly better → replaces
        assert!(submit_candidate(&mut groups, id, mk_record(4, false), 64));
        assert_eq!(groups[&id].best.as_ref().unwrap().cost.weighted_size, 4);
    }

    #[test]
    fn submit_candidate_to_missing_group_is_noop() {
        let mut groups = empty_group_map();
        assert!(!submit_candidate(&mut groups, 42, mk_record(1, false), 64));
    }

    #[test]
    fn submit_candidate_rejects_verified_without_lean_evidence() {
        let mut groups = empty_group_map();
        let mut next = 0;
        let id = create_group(&mut groups, &mut next, None);
        assert!(!submit_candidate(
            &mut groups,
            id,
            mk_record_without_lean_evidence(1),
            64
        ));
        assert!(groups[&id].best.is_none());
    }

    #[test]
    fn submit_candidate_rejects_verified_with_stale_lean_evidence() {
        let mut groups = empty_group_map();
        let mut next = 0;
        let id = create_group(&mut groups, &mut next, None);
        let mut record = mk_record_with_endpoint_evidence_only(1);
        record.lean_certificate = Some(LeanCertificate::new(
            64,
            Expr::variable(0),
            Expr::constant(0),
        ));

        assert!(!submit_candidate(&mut groups, id, record, 64));
        assert!(groups[&id].best.is_none());
    }

    #[test]
    fn submit_candidate_rejects_endpoint_evidence_for_wrong_source_signature() {
        let mut groups = empty_group_map();
        let mut next = 0;
        let id = create_group(&mut groups, &mut next, None);
        let mut record = mk_record_with_endpoint_evidence_only(1);
        record.sig_vector = vec![1, 0];

        assert!(!candidate_has_matching_lean_evidence(&record, 64));
        assert!(!submit_candidate(&mut groups, id, record, 64));
        assert!(groups[&id].best.is_none());
    }

    #[test]
    fn acquire_and_release_handles() {
        let mut groups = empty_group_map();
        let mut next = 0;
        let id = create_group(&mut groups, &mut next, None);
        assert_eq!(groups[&id].open_handles, 1);
        assert!(acquire_handle(&mut groups, id));
        assert_eq!(groups[&id].open_handles, 2);
        // One release: still > 0, no resolved item.
        assert!(release_handle(&mut groups, id).is_none());
        assert_eq!(groups[&id].open_handles, 1);
        // Second release: hits zero, emits CompetitionResolved.
        let resolved = release_handle(&mut groups, id).expect("resolved item emitted");
        assert_eq!(
            resolved.payload.kind(),
            crate::enums::StateKind::CompetitionResolved
        );
    }

    #[test]
    fn acquire_handle_on_missing_group_returns_false() {
        let mut groups = empty_group_map();
        assert!(!acquire_handle(&mut groups, 99));
    }

    #[test]
    fn has_verified_candidate_map_form() {
        let mut groups = empty_group_map();
        let mut next = 0;
        let id = create_group(&mut groups, &mut next, None);
        assert!(!has_verified_candidate(&groups, id, u32::MAX, 64));
        groups.get_mut(&id).unwrap().best = Some(mk_record(3, true));
        assert!(has_verified_candidate(&groups, id, 5, 64));
        assert!(!has_verified_candidate(&groups, id, 2, 64));
        // Missing group → false.
        assert!(!has_verified_candidate(&groups, 999, u32::MAX, 64));
    }
}
