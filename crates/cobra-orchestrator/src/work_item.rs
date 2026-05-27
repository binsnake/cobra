//! The unit of work flowing through the orchestrator: a
//! [`WorkItem`] carries a [`StateData`] payload plus scheduler-visible

use cobra_core::evaluator::Evaluator;
use cobra_core::pass_contract::{
    DecompositionMeta, ReasonCode, ReasonDetail, ReasonFrame, VerificationState,
};
use cobra_verify::{LeanCertificate, LeanSignatureCertificate};

use crate::continuation::GroupId;
use crate::enums::{ItemDisposition, PassDecision, PassId, Provenance};
use crate::state::StateData;

// ----- Feature tags + metadata -----

#[derive(Clone, Debug, Default)]
pub struct StateFeatures {
    pub classification: Option<cobra_core::classification::Classification>,
    pub provenance: Provenance,
    pub needs_full_width_verification: bool,
}

impl StateFeatures {
    #[must_use]
    pub fn new() -> Self {
        Self {
            classification: None,
            provenance: Provenance::Original,
            needs_full_width_verification: true,
        }
    }
}

/// Marker left by a structural transform that decided it could make no
/// further progress. The scheduler consults this to avoid re-attempting
/// the same pass on the same shape.
#[derive(Copy, Clone, Debug)]
pub struct TransformTerminalSignal {
    pub source_pass: PassId,
    pub category: cobra_core::pass_contract::ReasonCategory,
}

/// Scheduler-visible metadata travelling alongside the payload.
#[derive(Clone, Debug, Default)]
pub struct ItemMetadata {
    pub sig_vector: Vec<u64>,
    pub verification: VerificationState,
    pub structural_transform_rounds: u32,
    pub transform_produced_candidate: bool,
    pub candidate_failed_verification: bool,
    pub reason_code: Option<ReasonCode>,
    pub cause_chain: Vec<ReasonFrame>,
    pub decomposition_meta: Option<DecompositionMeta>,
    pub decomposition_causes: Vec<ReasonFrame>,
    pub last_failure: ReasonDetail,
    pub structural_transform_terminal: Option<TransformTerminalSignal>,
    pub lean_certificate: Option<LeanCertificate>,
    pub lean_signature_certificate: Option<LeanSignatureCertificate>,
}

// ----- Work item -----

#[derive(Clone, Debug)]
pub struct WorkItem {
    pub payload: StateData,
    pub features: StateFeatures,
    pub metadata: ItemMetadata,
    pub depth: u32,
    pub rewrite_gen: u32,
    /// Bitmask of `PassId` values already attempted on this item.
    /// Width `u64` caps `PassId::COUNT` at 64.
    pub attempted_mask: u64,
    pub signature_recursion_depth: u8,
    pub group_id: Option<GroupId>,
    pub evaluator_override: Option<Evaluator>,
    pub evaluator_override_arity: u32,
    pub history: Vec<PassId>,
    /// Memoized fingerprint. Filled on first demand, invalidated whenever
    /// fingerprint-contributing state changes. Not serialized; not part
    /// of equality — `WorkItem` `Clone` copies the cache as-is.
    fingerprint_cache: std::cell::OnceCell<StateFingerprint>,
}

impl WorkItem {
    /// Construct a work item around a payload, zero-initialising all
    /// scheduler metadata.
    #[must_use]
    pub fn new(payload: StateData) -> Self {
        Self {
            payload,
            features: StateFeatures::new(),
            metadata: ItemMetadata::default(),
            depth: 0,
            rewrite_gen: 0,
            attempted_mask: 0,
            signature_recursion_depth: 0,
            group_id: None,
            evaluator_override: None,
            evaluator_override_arity: 0,
            history: Vec::new(),
            fingerprint_cache: std::cell::OnceCell::new(),
        }
    }

    /// Mark `pass` as attempted and append it to the history.
    pub fn record_attempt(&mut self, pass: PassId) {
        self.attempted_mask |= 1u64 << pass.as_u8();
        self.history.push(pass);
    }

    #[inline]
    #[must_use]
    pub fn has_attempted(&self, pass: PassId) -> bool {
        (self.attempted_mask & (1u64 << pass.as_u8())) != 0
    }

    /// Return a fingerprint for this item. If the cached fingerprint
    /// was computed at the same `bitwidth`, returns it without
    /// recomputing. If the cache is empty, fills it. If the cached
    /// fingerprint has a different bitwidth, recomputes without
    /// overwriting the cache (so callers at the original bitwidth still
    /// hit it).
    #[must_use]
    pub fn fingerprint(&self, bitwidth: u32) -> std::borrow::Cow<'_, StateFingerprint> {
        if let Some(fp) = self.fingerprint_cache.get() {
            if fp.bitwidth == bitwidth {
                return std::borrow::Cow::Borrowed(fp);
            }
            return std::borrow::Cow::Owned(crate::fingerprint::compute_fingerprint(
                self, bitwidth,
            ));
        }
        let fp = crate::fingerprint::compute_fingerprint(self, bitwidth);
        // Ignore result of set — another caller may have raced us.
        let _ = self.fingerprint_cache.set(fp);
        std::borrow::Cow::Borrowed(self.fingerprint_cache.get().expect("just set"))
    }

    /// Clear the memoized fingerprint. Call whenever a field that feeds
    /// `compute_fingerprint` mutates (payload, features.provenance,
    /// `group_id`, `signature_recursion_depth`, `evaluator_override`).
    pub fn invalidate_fingerprint_cache(&mut self) {
        self.fingerprint_cache = std::cell::OnceCell::new();
    }
}

// ----- Fingerprints -----

use cobra_ir::semilinear::{GlobalVarIdx, OperatorFamily};

/// directly from the `StateData` contents — here we only expose the
/// struct shape.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StateFingerprint {
    pub kind: crate::enums::StateKind,
    pub payload_hash: u64,
    pub vars_hash: u64,
    pub bitwidth: u32,
    pub provenance: Provenance,
}

/// `SemilinearFingerprintKey::TermKey`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SemilinearTermKey {
    pub coeff: u64,
    pub support: Vec<GlobalVarIdx>,
    pub truth_table: Vec<u64>,
    pub structural_hash: u64,
    pub provenance: OperatorFamily,
}

/// Content-based fingerprint of a [`cobra_ir::semilinear::SemilinearIR`]
/// used by the pass-attempt cache.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct SemilinearFingerprintKey {
    pub constant: u64,
    pub bitwidth: u32,
    pub terms: Vec<SemilinearTermKey>,
}

// ----- Pass result (what a pass returns to the scheduler) -----

#[derive(Clone, Debug)]
pub struct PassResult {
    pub decision: PassDecision,
    pub disposition: ItemDisposition,
    pub next: Vec<WorkItem>,
    pub reason: ReasonDetail,
}

impl PassResult {
    /// Factory for the common "not applicable, leave the item alone"
    #[must_use]
    pub fn not_applicable(reason: ReasonDetail) -> Self {
        Self {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason,
        }
    }
}

// ----- Unsupported candidate ranking -----

#[derive(Clone, Debug, Default)]
pub struct UnsupportedCandidate {
    pub metadata: ItemMetadata,
    pub depth: u32,
    pub rewrite_gen: u32,
    pub history_size: u32,
    pub last_pass: Option<PassId>,
    pub is_candidate_state: bool,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::{AstPayload, StateData};
    use cobra_core::expr::Expr;

    #[test]
    fn record_attempt_sets_bitmask_and_appends_history() {
        let mut item = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
            expr: Expr::variable(0),
            classification: None,
            provenance: Provenance::Original,
            solve_ctx: None,
        })));
        assert!(!item.has_attempted(PassId::ClassifyAst));
        item.record_attempt(PassId::ClassifyAst);
        assert!(item.has_attempted(PassId::ClassifyAst));
        assert_eq!(item.history, vec![PassId::ClassifyAst]);
        assert_eq!(item.attempted_mask, 1u64 << PassId::ClassifyAst.as_u8());

        // Same pass twice — the mask is idempotent, history grows.
        item.record_attempt(PassId::ClassifyAst);
        assert_eq!(item.history.len(), 2);
        assert_eq!(item.attempted_mask, 1u64 << PassId::ClassifyAst.as_u8());

        // Different pass sets a second bit.
        item.record_attempt(PassId::LowerNotOverArith);
        assert!(item.has_attempted(PassId::LowerNotOverArith));
        assert_eq!(
            item.attempted_mask,
            (1u64 << PassId::ClassifyAst.as_u8()) | (1u64 << PassId::LowerNotOverArith.as_u8()),
        );
    }

    #[test]
    fn pass_result_not_applicable_builds_expected_shape() {
        let r = PassResult::not_applicable(ReasonDetail::default());
        assert_eq!(r.decision, PassDecision::NotApplicable);
        assert_eq!(r.disposition, ItemDisposition::RetainCurrent);
        assert!(r.next.is_empty());
    }
}
