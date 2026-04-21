//! Orchestrator-wide context: policy, telemetry, run metadata, and the
//! two mutable registries (competition groups + join states) that

use cobra_core::classification::Classification;
use cobra_core::evaluator::Evaluator;
use cobra_core::pass_contract::ReasonDetail;
use cobra_core::simplify_outcome::Options;

use crate::competition::GroupMap;
use crate::continuation::{GroupId, JoinId};
use crate::enums::PassId;
use crate::join::JoinMap;

/// `OrchestratorPolicy`.
#[derive(Copy, Clone, Debug)]
pub struct OrchestratorPolicy {
    pub max_expansions: u32,
    pub max_rewrite_gen: u32,
    pub max_candidates: u32,
}

impl Default for OrchestratorPolicy {
    fn default() -> Self {
        Self {
            max_expansions: 1024,
            max_rewrite_gen: 3,
            max_candidates: 8,
        }
    }
}

/// `OrchestratorTelemetry`.
#[derive(Clone, Debug, Default)]
pub struct OrchestratorTelemetry {
    pub total_expansions: u32,
    pub max_depth_reached: u32,
    pub candidates_verified: u32,
    pub queue_high_water: u32,
    pub passes_attempted: Vec<PassId>,
}

#[derive(Clone, Debug, Default)]
pub struct RunMetadata {
    pub input_classification: Classification,
    pub semilinear_failure: Option<ReasonDetail>,
}

/// Mutable context threaded through every pass call. The borrow strategy
/// method helpers (added in the scheduler session) so passes can mutate
/// them without aliasing the rest of the context.
#[derive(Debug)]
pub struct OrchestratorContext {
    pub opts: Options,
    pub original_vars: Vec<String>,
    pub evaluator: Option<Evaluator>,
    pub bitwidth: u32,
    pub run_metadata: RunMetadata,
    /// Parser-computed signature for the initial expression. Used by
    /// the first `BuildSignatureState` pass to match legacy signature
    /// computation exactly.
    pub input_sig: Vec<u64>,
    /// `true` if `LowerNotOverArith` fired on the input — signals that
    /// `input_sig` is stale and must be recomputed.
    pub lowering_fired: bool,
    pub competition_groups: GroupMap,
    pub next_group_id: GroupId,
    pub join_states: JoinMap,
    pub next_join_id: JoinId,
}

impl OrchestratorContext {
    /// Fresh context for a new `Simplify` run. Uses deterministic
    /// `ahash::RandomState::with_seeds` so the pass-attempt-cache keys
    #[must_use]
    pub fn new(opts: Options, original_vars: Vec<String>, bitwidth: u32) -> Self {
        Self {
            opts,
            original_vars,
            evaluator: None,
            bitwidth,
            run_metadata: RunMetadata::default(),
            input_sig: Vec::new(),
            lowering_fired: false,
            competition_groups: GroupMap::with_hasher(determinism_seeds_ahash()),
            next_group_id: 0,
            join_states: JoinMap::with_hasher(determinism_seeds_ahash()),
            next_join_id: 0,
        }
    }
}

/// Four `u64` seeds pinned at a known value. Any change to this tuple
/// invalidates serialized fingerprints — treat as a hash-stability
/// breaking change.
#[inline]
#[must_use]
pub const fn determinism_seeds() -> (u64, u64, u64, u64) {
    (
        0xC0BA_1001_ABBA_2002,
        0xDEAD_BEEF_CAFE_BABE,
        0x9E37_79B9_7F4A_7C15,
        0x517C_C1B7_2722_0A95,
    )
}

/// Build an `ahash::RandomState` from [`determinism_seeds`]. Used by
/// every `HashMap` in the orchestrator so fingerprint-keyed maps stay
/// deterministic across runs.
#[inline]
#[must_use]
pub fn determinism_seeds_ahash() -> ahash::RandomState {
    let s = determinism_seeds();
    ahash::RandomState::with_seeds(s.0, s.1, s.2, s.3)
}

/// Canonical `Expr → u64` hash used for structural identity across the
/// orchestrator (e.g. `target_hash` inside `OperandJoinState` and
/// `ProductJoinState`). Uses the pinned determinism seeds so callers
/// that stash a hash for later comparison are guaranteed to agree with
/// `replace_by_hash`.
#[must_use]
pub fn expr_identity_hash(expr: &cobra_core::expr::Expr) -> u64 {
    // `ahash::RandomState` is cached in a `OnceLock` so we build it once
    // per process. The deterministic seeds mean the cached instance is
    // equivalent to a freshly-built one, preserving hash stability.
    use std::sync::OnceLock;
    static STATE: OnceLock<ahash::RandomState> = OnceLock::new();
    STATE.get_or_init(determinism_seeds_ahash).hash_one(expr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn context_starts_empty() {
        let ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        assert!(ctx.competition_groups.is_empty());
        assert!(ctx.join_states.is_empty());
        assert_eq!(ctx.next_group_id, 0);
        assert_eq!(ctx.next_join_id, 0);
        assert_eq!(ctx.bitwidth, 64);
        assert!(!ctx.lowering_fired);
    }

    #[test]
    fn determinism_seeds_are_const() {
        // If this test ever changes, every stored fingerprint is
        // invalidated — intentional canary.
        assert_eq!(determinism_seeds().0, 0xC0BA_1001_ABBA_2002);
    }

    #[test]
    fn policy_defaults_match_cpp() {
        let p = OrchestratorPolicy::default();
        assert_eq!(p.max_expansions, 1024);
        assert_eq!(p.max_rewrite_gen, 3);
        assert_eq!(p.max_candidates, 8);
    }
}
