//! Competition group data + lifecycle. Ported from
//! `lib/core/CompetitionGroup.{h,cpp}`.

use cobra_core::expr::Expr;
use cobra_core::expr_cost::{is_better, ExprCost};
use cobra_core::pass_contract::{ReasonDetail, VerificationState};

use crate::continuation::{ContinuationData, GroupId};
use crate::enums::PassId;
use crate::state::{CompetitionResolvedPayload, StateData};
use crate::work_item::WorkItem;

// Re-exported for API ergonomics — downstream code typically reaches for
// `competition::GroupId` / `competition::JoinId`.
pub use crate::continuation::JoinId;

/// One candidate expression submitted to a competition group. Matches
/// the C++ `CandidateRecord` field-for-field.
#[derive(Clone, Debug)]
pub struct CandidateRecord {
    pub expr: Box<Expr>,
    pub cost: ExprCost,
    pub verification: VerificationState,
    pub real_vars: Vec<String>,
    pub source_pass: PassId,
    pub needs_original_space_verification: bool,
    pub sig_vector: Vec<u64>,
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
    /// Fresh group with one open handle and the given baseline. Matches
    /// the shape created by C++ `CreateGroup`.
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
/// path already has a compact answer. Matches the shape of C++
/// `HasVerifiedCandidate` but does not take a map — callers pass the
/// group directly so the fn is trivially testable.
#[must_use]
pub fn group_has_verified_candidate(group: &CompetitionGroup, max_weighted_size: u32) -> bool {
    group.best.as_ref().is_some_and(|c| {
        c.verification == VerificationState::Verified && c.cost.weighted_size <= max_weighted_size
    })
}

/// Type alias for the competition-group registry. Matches C++
/// `absl::flat_hash_map<GroupId, CompetitionGroup>`. Uses
/// `ahash::RandomState` under the hood — pin its seed at the call site
/// (orchestrator context) if determinism is required.
pub type GroupMap = std::collections::HashMap<GroupId, CompetitionGroup, ahash::RandomState>;

// ---------------------------------------------------------------
// Lifecycle helpers (ported from `lib/core/CompetitionGroup.cpp`)
// ---------------------------------------------------------------

/// Allocate a fresh group with `open_handles = 1` and the supplied
/// baseline cost. Returns the assigned id. Matches C++ `CreateGroup`.
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
/// Returns `true` when the group's `best` was updated. Matches C++
/// `SubmitCandidate`.
pub fn submit_candidate(groups: &mut GroupMap, group_id: GroupId, record: CandidateRecord) -> bool {
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
/// already been resolved and erased. Matches C++ `AcquireHandle`.
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
/// Matches C++ `ReleaseHandle`.
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

/// Map-taking form of [`group_has_verified_candidate`]. Matches C++
/// `HasVerifiedCandidate`. Missing groups return `false`.
#[must_use]
pub fn has_verified_candidate(
    groups: &GroupMap,
    group_id: GroupId,
    max_weighted_size: u32,
) -> bool {
    groups
        .get(&group_id)
        .is_some_and(|g| group_has_verified_candidate(g, max_weighted_size))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_record(ws: u32, verified: bool) -> CandidateRecord {
        CandidateRecord {
            expr: Expr::variable(0),
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
            sig_vector: Vec::new(),
        }
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
        assert!(!group_has_verified_candidate(&g, u32::MAX));
        g.best = Some(mk_record(10, true));
        assert!(group_has_verified_candidate(&g, 10));
        assert!(group_has_verified_candidate(&g, 20));
        // Over budget
        assert!(!group_has_verified_candidate(&g, 5));
    }

    #[test]
    fn has_verified_candidate_requires_verified_state() {
        let mut g = CompetitionGroup::new(None);
        g.best = Some(mk_record(5, false));
        assert!(!group_has_verified_candidate(&g, 100));
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
        assert!(!submit_candidate(&mut groups, id, mk_record(10, false)));
        // Strictly better → accepted
        assert!(submit_candidate(&mut groups, id, mk_record(5, false)));
        assert_eq!(groups[&id].best.as_ref().unwrap().cost.weighted_size, 5);
    }

    #[test]
    fn submit_candidate_keeps_best() {
        let mut groups = empty_group_map();
        let mut next = 0;
        let id = create_group(&mut groups, &mut next, None);
        assert!(submit_candidate(&mut groups, id, mk_record(8, false)));
        // Worse candidate → rejected
        assert!(!submit_candidate(&mut groups, id, mk_record(12, false)));
        // Strictly better → replaces
        assert!(submit_candidate(&mut groups, id, mk_record(4, false)));
        assert_eq!(groups[&id].best.as_ref().unwrap().cost.weighted_size, 4);
    }

    #[test]
    fn submit_candidate_to_missing_group_is_noop() {
        let mut groups = empty_group_map();
        assert!(!submit_candidate(&mut groups, 42, mk_record(1, false)));
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
        assert!(!has_verified_candidate(&groups, id, u32::MAX));
        groups.get_mut(&id).unwrap().best = Some(mk_record(3, true));
        assert!(has_verified_candidate(&groups, id, 5));
        assert!(!has_verified_candidate(&groups, id, 2));
        // Missing group → false.
        assert!(!has_verified_candidate(&groups, 999, u32::MAX));
    }
}
