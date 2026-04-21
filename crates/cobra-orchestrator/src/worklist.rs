//! Worklist over [`WorkItem`]s with multi-key priority ordering.
//!
//! The C++ version (`lib/core/Orchestrator.cpp::Worklist`) backs the
//! queue with a `std::vector` and does an O(n) pick on `Pop`. Priority
//! (implemented in `IsBetterPriority`) ranks by band / sub-band /
//! depth / provenance / history size, with lower values winning. The
//! Rust port mirrors those comparators exactly.

use crate::enums::StateKind;
use crate::work_item::WorkItem;

// Band 0: terminal items the main loop wants to resolve quickly
// (`CandidateExpr`, `CompetitionResolved`). Band 1: everything else.
fn band_of(item: &WorkItem) -> u8 {
    match item.payload.kind() {
        StateKind::CandidateExpr | StateKind::CompetitionResolved => 0,
        _ => 1,
    }
}

// Within band 0, CandidateExpr outranks CompetitionResolved — we want
// a verified candidate to surface before any grouped resolution runs.
fn sub_band_of(item: &WorkItem) -> u8 {
    match item.payload.kind() {
        StateKind::CandidateExpr => 0,
        StateKind::CompetitionResolved => 1,
        _ => 2,
    }
}

/// Ordering matches C++ `IsBetterPriority`: band, sub-band, depth,
/// provenance, history length — all lower-wins. Returns `true` iff
/// `a` should pop before `b`.
#[must_use]
pub fn is_better_priority(a: &WorkItem, b: &WorkItem) -> bool {
    let (ba, bb) = (band_of(a), band_of(b));
    if ba != bb {
        return ba < bb;
    }
    let (sa, sb) = (sub_band_of(a), sub_band_of(b));
    if sa != sb {
        return sa < sb;
    }
    if a.depth != b.depth {
        return a.depth < b.depth;
    }
    if a.features.provenance != b.features.provenance {
        return (a.features.provenance as u8) < (b.features.provenance as u8);
    }
    if a.history.len() != b.history.len() {
        return a.history.len() < b.history.len();
    }
    false
}

#[derive(Debug, Default)]
pub struct Worklist {
    items: Vec<WorkItem>,
    high_water: usize,
}

impl Worklist {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, item: WorkItem) {
        self.items.push(item);
        if self.items.len() > self.high_water {
            self.high_water = self.items.len();
        }
    }

    /// Remove and return the highest-priority item, as ranked by
    /// [`is_better_priority`]. Returns `None` if empty. Matches C++
    /// `Worklist::Pop` semantics — linear O(n) scan.
    ///
    /// Uses `Vec::remove` (not `swap_remove`) to preserve the relative
    /// order of the remaining items, matching C++ `vector::erase`.
    pub fn pop(&mut self) -> Option<WorkItem> {
        if self.items.is_empty() {
            return None;
        }
        let mut best = 0usize;
        for i in 1..self.items.len() {
            if is_better_priority(&self.items[i], &self.items[best]) {
                best = i;
            }
        }
        Some(self.items.remove(best))
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.items.len()
    }

    #[must_use]
    pub fn high_water_mark(&self) -> usize {
        self.high_water
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::{AstPayload, StateData};
    use cobra_core::expr::Expr;

    fn mk_item(depth: u32) -> WorkItem {
        let mut w = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
            expr: Expr::variable(0),
            classification: None,
            provenance: crate::enums::Provenance::Original,
            solve_ctx: None,
        })));
        w.depth = depth;
        w
    }

    fn mk_candidate_item(depth: u32) -> WorkItem {
        use crate::state::CandidatePayload;
        let mut w = WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
            expr: Expr::variable(0),
            real_vars: vec![],
            cost: cobra_core::expr_cost::ExprCost::default(),
            producing_pass: crate::enums::PassId::VerifyCandidate,
            needs_original_space_verification: true,
        })));
        w.depth = depth;
        w
    }

    fn mk_resolved_item(depth: u32) -> WorkItem {
        use crate::state::CompetitionResolvedPayload;
        let mut w = WorkItem::new(StateData::CompetitionResolved(CompetitionResolvedPayload {
            group_id: 0,
        }));
        w.depth = depth;
        w
    }

    #[test]
    fn empty_worklist_pops_none() {
        let mut w = Worklist::new();
        assert!(w.pop().is_none());
        assert!(w.is_empty());
    }

    #[test]
    fn pop_returns_shallowest_item_within_band() {
        let mut w = Worklist::new();
        w.push(mk_item(5));
        w.push(mk_item(2));
        w.push(mk_item(9));
        w.push(mk_item(4));
        let got = w.pop().unwrap();
        assert_eq!(got.depth, 2);
        let got = w.pop().unwrap();
        assert_eq!(got.depth, 4);
    }

    #[test]
    fn candidate_pops_before_non_candidate_regardless_of_depth() {
        let mut w = Worklist::new();
        w.push(mk_item(0)); // deep in pipeline but low depth
        w.push(mk_candidate_item(100)); // much deeper but band 0
        let got = w.pop().unwrap();
        assert_eq!(got.payload.kind(), StateKind::CandidateExpr);
    }

    #[test]
    fn candidate_expr_outranks_competition_resolved_in_band_zero() {
        let mut w = Worklist::new();
        w.push(mk_resolved_item(0));
        w.push(mk_candidate_item(0));
        let got = w.pop().unwrap();
        assert_eq!(got.payload.kind(), StateKind::CandidateExpr);
    }

    #[test]
    fn history_size_breaks_tie_after_provenance() {
        let mut w1 = mk_item(3);
        let mut w2 = mk_item(3);
        w2.history.push(crate::enums::PassId::ClassifyAst);
        w2.history.push(crate::enums::PassId::ClassifyAst);
        // w1 has 0 history, w2 has 2 → w1 should pop first.
        assert!(is_better_priority(&w1, &w2));
        assert!(!is_better_priority(&w2, &w1));
        // No-op on self: not strictly better than itself.
        assert!(!is_better_priority(&w1, &w1));
        // Needed to silence unused `mut` on w1.
        w1.history.push(crate::enums::PassId::ClassifyAst);
    }

    #[test]
    fn high_water_tracks_peak_size() {
        let mut w = Worklist::new();
        assert_eq!(w.high_water_mark(), 0);
        w.push(mk_item(0));
        w.push(mk_item(0));
        w.push(mk_item(0));
        assert_eq!(w.high_water_mark(), 3);
        let _ = w.pop();
        let _ = w.pop();
        assert_eq!(w.high_water_mark(), 3);
        w.push(mk_item(0));
        assert_eq!(w.high_water_mark(), 3);
    }
}
