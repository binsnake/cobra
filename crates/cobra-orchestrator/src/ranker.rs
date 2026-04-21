//! Deterministic ordering for picking the best "unsupported" candidate
//! to surface in the final `SimplifyOutcome` when no pass produces a

use cobra_core::pass_contract::ReasonCategory;

use crate::work_item::UnsupportedCandidate;

/// Returns `true` iff `a` should be preferred over `b`. The ordering
/// walks a fixed list of tiebreakers:
/// 1. Prefer items that *are* candidates (verification-failed
///    candidates surface over raw state items).
/// 2. Deeper `depth` wins — we made more progress before failing.
/// 3. Higher `rewrite_gen` wins.
/// 4. Larger `history_size` wins (more passes attempted).
/// 5. Later `last_pass` in the `PassId` enum wins.
/// 6. Prefer items with a `structural_transform_terminal` signal.
/// 7. When both have a terminal, prefer the higher-severity category
///    (`VerifyFailed` > `RepresentationGap` > others).
#[must_use]
pub fn unsupported_rank_better(a: &UnsupportedCandidate, b: &UnsupportedCandidate) -> bool {
    if a.is_candidate_state != b.is_candidate_state {
        return a.is_candidate_state;
    }
    if a.depth != b.depth {
        return a.depth > b.depth;
    }
    if a.rewrite_gen != b.rewrite_gen {
        return a.rewrite_gen > b.rewrite_gen;
    }
    if a.history_size != b.history_size {
        return a.history_size > b.history_size;
    }
    if a.last_pass != b.last_pass {
        // In C++ this is `a.last_pass > b.last_pass` on the raw enum
        // value (`PassId` is `uint8_t`). Use the `u8` cast to match.
        return as_u8_opt(a.last_pass) > as_u8_opt(b.last_pass);
    }

    let a_has_term = a.metadata.structural_transform_terminal.is_some();
    let b_has_term = b.metadata.structural_transform_terminal.is_some();
    if a_has_term != b_has_term {
        return a_has_term;
    }
    if a_has_term && b_has_term {
        let ra = terminal_rank(a.metadata.structural_transform_terminal.unwrap().category);
        let rb = terminal_rank(b.metadata.structural_transform_terminal.unwrap().category);
        if ra != rb {
            return ra > rb;
        }
    }
    false
}

#[inline]
fn as_u8_opt(p: Option<crate::enums::PassId>) -> u8 {
    match p {
        Some(id) => id as u8,
        None => u8::MAX,
    }
}

#[inline]
fn terminal_rank(c: ReasonCategory) -> u8 {
    match c {
        ReasonCategory::VerifyFailed => 2,
        ReasonCategory::RepresentationGap => 1,
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::enums::PassId;
    use crate::work_item::{ItemMetadata, TransformTerminalSignal};

    fn cand(is_candidate: bool, depth: u32, rewrite_gen: u32, hist: u32) -> UnsupportedCandidate {
        UnsupportedCandidate {
            metadata: ItemMetadata::default(),
            depth,
            rewrite_gen,
            history_size: hist,
            last_pass: None,
            is_candidate_state: is_candidate,
        }
    }

    #[test]
    fn candidate_state_wins_first() {
        let a = cand(true, 0, 0, 0);
        let b = cand(false, 100, 100, 100);
        assert!(unsupported_rank_better(&a, &b));
        assert!(!unsupported_rank_better(&b, &a));
    }

    #[test]
    fn deeper_depth_wins_next() {
        let a = cand(false, 5, 0, 0);
        let b = cand(false, 3, 0, 0);
        assert!(unsupported_rank_better(&a, &b));
    }

    #[test]
    fn higher_rewrite_gen_wins_after_depth() {
        let a = cand(false, 4, 2, 0);
        let b = cand(false, 4, 1, 0);
        assert!(unsupported_rank_better(&a, &b));
    }

    #[test]
    fn larger_history_wins_after_rewrite_gen() {
        let a = cand(false, 4, 2, 7);
        let b = cand(false, 4, 2, 3);
        assert!(unsupported_rank_better(&a, &b));
    }

    #[test]
    fn later_pass_id_wins() {
        let mut a = cand(false, 4, 2, 7);
        let mut b = cand(false, 4, 2, 7);
        a.last_pass = Some(PassId::VerifyCandidate);
        b.last_pass = Some(PassId::ClassifyAst);
        // VerifyCandidate has a higher u8 than ClassifyAst.
        assert!(unsupported_rank_better(&a, &b));
    }

    #[test]
    fn terminal_signal_wins_after_pass_id() {
        let mut a = cand(false, 4, 2, 7);
        let mut b = cand(false, 4, 2, 7);
        a.last_pass = Some(PassId::VerifyCandidate);
        b.last_pass = Some(PassId::VerifyCandidate);
        a.metadata.structural_transform_terminal = Some(TransformTerminalSignal {
            source_pass: PassId::VerifyCandidate,
            category: ReasonCategory::None,
        });
        // a has terminal, b doesn't → a wins.
        assert!(unsupported_rank_better(&a, &b));
    }

    #[test]
    fn terminal_category_rank_breaks_tie() {
        let mk = |category| {
            let mut c = cand(false, 4, 2, 7);
            c.last_pass = Some(PassId::VerifyCandidate);
            c.metadata.structural_transform_terminal = Some(TransformTerminalSignal {
                source_pass: PassId::VerifyCandidate,
                category,
            });
            c
        };
        let verify = mk(ReasonCategory::VerifyFailed);
        let rep_gap = mk(ReasonCategory::RepresentationGap);
        let plain = mk(ReasonCategory::NoSolution);
        assert!(unsupported_rank_better(&verify, &rep_gap));
        assert!(unsupported_rank_better(&rep_gap, &plain));
        assert!(unsupported_rank_better(&verify, &plain));
    }

    #[test]
    fn self_vs_self_is_not_better() {
        let c = cand(false, 4, 2, 7);
        assert!(!unsupported_rank_better(&c, &c));
    }
}
