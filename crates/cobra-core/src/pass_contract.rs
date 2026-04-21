//! Pass-level outcome and reason types.
//!
//! shared vocabulary the orchestrator and every pass use to report
//! success, failure, and the reason behind each outcome.

use crate::classification::Classification;
use crate::expr::Expr;

/// Broad outcome bucket.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum OutcomeKind {
    Success,
    Inapplicable,
    Blocked,
    Partial,
    VerifyFailed,
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum ReasonCategory {
    #[default]
    None,
    GuardFailed,
    Inapplicable,
    RepresentationGap,
    NoSolution,
    SearchExhausted,
    VerifyFailed,
    ResourceLimit,
    CostRejected,
    InternalInvariant,
    /// Exhaustion-path fallback fired: a structural rewrite (currently
    /// `ProductIdentityCollapse`) produced an expression strictly
    /// cheaper than the original input and verified under a full-width
    /// spot check, so the orchestrator promoted it instead of returning
    /// successful simplify.
    BestRewritePromoted,
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum ReasonDomain {
    #[default]
    Orchestrator,
    Semilinear,
    Signature,
    StructuralTransform,
    Decomposition,
    TemplateDecomposer,
    WeightedPolyFit,
    MultivarPoly,
    PolynomialRecovery,
    BitwiseDecomposer,
    HybridDecomposer,
    GhostResidual,
    OperandSimplifier,
    Lifting,
    Verifier,
}

/// Structured diagnostic identifier attached to reason frames.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ReasonCode {
    pub category: ReasonCategory,
    pub domain: ReasonDomain,
    pub subcode: u16,
}

/// One key/value field on a diagnostic frame.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DiagField {
    pub key: String,
    pub value: String,
}

/// One level of reason detail. A `ReasonDetail` has a top frame and a
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ReasonFrame {
    pub code: ReasonCode,
    pub message: String,
    pub fields: Vec<DiagField>,
}

/// Full reason tree: top frame plus 0+ cause frames.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ReasonDetail {
    pub top: ReasonFrame,
    pub causes: Vec<ReasonFrame>,
}

// ---------------------------------------------------------------
// SolverResult<T>
// ---------------------------------------------------------------

/// `SolverResult<T>` template: five success/failure arms, at most one of
/// `payload` / `reason` populated per arm.
#[derive(Clone, Debug)]
#[must_use]
pub enum SolverResult<T> {
    Success(T),
    Inapplicable(ReasonDetail),
    Blocked(ReasonDetail),
    VerifyFailed { payload: T, reason: ReasonDetail },
}

impl<T> SolverResult<T> {
    #[must_use]
    pub fn kind(&self) -> OutcomeKind {
        match self {
            Self::Success(_) => OutcomeKind::Success,
            Self::Inapplicable(_) => OutcomeKind::Inapplicable,
            Self::Blocked(_) => OutcomeKind::Blocked,
            Self::VerifyFailed { .. } => OutcomeKind::VerifyFailed,
        }
    }

    #[must_use]
    pub fn succeeded(&self) -> bool {
        matches!(self, Self::Success(_))
    }

    /// Takes the payload if this is `Success` or `VerifyFailed`.
    pub fn take_payload(self) -> Option<T> {
        match self {
            Self::Success(p) | Self::VerifyFailed { payload: p, .. } => Some(p),
            _ => None,
        }
    }

    #[must_use]
    pub fn reason(&self) -> Option<&ReasonDetail> {
        match self {
            Self::Inapplicable(r) | Self::Blocked(r) | Self::VerifyFailed { reason: r, .. } => {
                Some(r)
            }
            Self::Success(_) => None,
        }
    }
}

// ---------------------------------------------------------------
// DecompositionMeta
// ---------------------------------------------------------------

/// Metadata attached by the decomposition family when it produces a
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct DecompositionMeta {
    pub extractor_kind: u8,
    pub solver_kind: u8,
    pub has_solver: bool,
    pub core_degree: u8,
}

// ---------------------------------------------------------------
// PassOutcome
// ---------------------------------------------------------------

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum VerificationState {
    #[default]
    Unverified,
    Verified,
    Rejected,
}

/// Work the pass couldn't consume — the remaining residual plus its
#[derive(Clone, Debug)]
pub struct PendingWork {
    pub residual: Box<Expr>,
    pub residual_classification: Classification,
}

#[derive(Clone, Debug)]
#[must_use]
pub enum PassOutcome {
    Success {
        expr: Box<Expr>,
        real_vars: Vec<String>,
        verification: VerificationState,
        sig_vector: Vec<u64>,
        decomposition_meta: Option<DecompositionMeta>,
    },
    Inapplicable(ReasonDetail),
    Blocked(ReasonDetail),
    Partial {
        expr: Box<Expr>,
        real_vars: Vec<String>,
        verification: VerificationState,
        pending: PendingWork,
        reason: ReasonDetail,
        sig_vector: Vec<u64>,
        decomposition_meta: Option<DecompositionMeta>,
    },
    VerifyFailed {
        expr: Box<Expr>,
        real_vars: Vec<String>,
        reason: ReasonDetail,
        sig_vector: Vec<u64>,
        decomposition_meta: Option<DecompositionMeta>,
    },
}

impl PassOutcome {
    #[must_use]
    pub fn kind(&self) -> OutcomeKind {
        match self {
            Self::Success { .. } => OutcomeKind::Success,
            Self::Inapplicable(_) => OutcomeKind::Inapplicable,
            Self::Blocked(_) => OutcomeKind::Blocked,
            Self::Partial { .. } => OutcomeKind::Partial,
            Self::VerifyFailed { .. } => OutcomeKind::VerifyFailed,
        }
    }

    #[must_use]
    pub fn succeeded(&self) -> bool {
        matches!(self, Self::Success { .. })
    }

    pub fn success(
        expr: Box<Expr>,
        real_vars: Vec<String>,
        verification: VerificationState,
    ) -> Self {
        Self::Success {
            expr,
            real_vars,
            verification,
            sig_vector: Vec::new(),
            decomposition_meta: None,
        }
    }

    pub fn inapplicable(reason: ReasonDetail) -> Self {
        Self::Inapplicable(reason)
    }

    pub fn blocked(reason: ReasonDetail) -> Self {
        Self::Blocked(reason)
    }

    pub fn partial(
        expr: Box<Expr>,
        real_vars: Vec<String>,
        verification: VerificationState,
        pending: PendingWork,
        reason: ReasonDetail,
    ) -> Self {
        Self::Partial {
            expr,
            real_vars,
            verification,
            pending,
            reason,
            sig_vector: Vec::new(),
            decomposition_meta: None,
        }
    }

    pub fn verify_failed(expr: Box<Expr>, real_vars: Vec<String>, reason: ReasonDetail) -> Self {
        Self::VerifyFailed {
            expr,
            real_vars,
            reason,
            sig_vector: Vec::new(),
            decomposition_meta: None,
        }
    }

    /// Attach a signature vector to any arm that carries one. No-op for
    pub fn set_sig_vector(&mut self, sv: Vec<u64>) {
        match self {
            Self::Success { sig_vector, .. }
            | Self::Partial { sig_vector, .. }
            | Self::VerifyFailed { sig_vector, .. } => *sig_vector = sv,
            Self::Inapplicable(_) | Self::Blocked(_) => {}
        }
    }

    /// Attach decomposition metadata to any arm that carries it.
    pub fn set_decomposition_meta(&mut self, meta: DecompositionMeta) {
        match self {
            Self::Success {
                decomposition_meta, ..
            }
            | Self::Partial {
                decomposition_meta, ..
            }
            | Self::VerifyFailed {
                decomposition_meta, ..
            } => *decomposition_meta = Some(meta),
            Self::Inapplicable(_) | Self::Blocked(_) => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn solver_result_success_roundtrip() {
        let r: SolverResult<u32> = SolverResult::Success(42);
        assert!(r.succeeded());
        assert_eq!(r.kind(), OutcomeKind::Success);
        assert_eq!(r.take_payload(), Some(42));
    }

    #[test]
    fn solver_result_verify_failed_carries_payload_and_reason() {
        let reason = ReasonDetail {
            top: ReasonFrame {
                message: "x".into(),
                ..Default::default()
            },
            causes: vec![],
        };
        let r: SolverResult<u32> = SolverResult::VerifyFailed {
            payload: 7,
            reason: reason.clone(),
        };
        assert_eq!(r.kind(), OutcomeKind::VerifyFailed);
        assert!(!r.succeeded());
        assert_eq!(r.reason().unwrap().top.message, "x");
        assert_eq!(r.take_payload(), Some(7));
    }

    #[test]
    fn solver_result_inapplicable_and_blocked_have_no_payload() {
        let reason = ReasonDetail::default();
        let r: SolverResult<u32> = SolverResult::Inapplicable(reason.clone());
        assert_eq!(r.kind(), OutcomeKind::Inapplicable);
        assert!(r.take_payload().is_none());

        let r: SolverResult<u32> = SolverResult::Blocked(reason);
        assert_eq!(r.kind(), OutcomeKind::Blocked);
        assert!(r.take_payload().is_none());
    }

    #[test]
    fn pass_outcome_factories_and_kinds() {
        let e = Expr::variable(0);
        let ok = PassOutcome::success(e.clone(), vec!["x".into()], VerificationState::Verified);
        assert_eq!(ok.kind(), OutcomeKind::Success);
        assert!(ok.succeeded());

        let inapp = PassOutcome::inapplicable(ReasonDetail::default());
        assert_eq!(inapp.kind(), OutcomeKind::Inapplicable);
        assert!(!inapp.succeeded());

        let vf = PassOutcome::verify_failed(e.clone(), vec![], ReasonDetail::default());
        assert_eq!(vf.kind(), OutcomeKind::VerifyFailed);
    }

    #[test]
    fn pass_outcome_set_sig_vector_and_meta() {
        let mut o = PassOutcome::success(Expr::variable(0), vec![], VerificationState::Verified);
        o.set_sig_vector(vec![1, 2, 3]);
        o.set_decomposition_meta(DecompositionMeta {
            extractor_kind: 2,
            solver_kind: 3,
            has_solver: true,
            core_degree: 4,
        });
        if let PassOutcome::Success {
            sig_vector,
            decomposition_meta,
            ..
        } = o
        {
            assert_eq!(sig_vector, vec![1, 2, 3]);
            assert_eq!(decomposition_meta.unwrap().core_degree, 4);
        } else {
            panic!("expected Success arm");
        }
    }

    #[test]
    fn pass_outcome_setters_are_noop_on_inapplicable() {
        let mut o = PassOutcome::inapplicable(ReasonDetail::default());
        o.set_sig_vector(vec![9]);
        o.set_decomposition_meta(DecompositionMeta::default());
        // Nothing to assert beyond "did not panic" — Inapplicable has no
        // sig_vector / decomposition_meta fields.
        assert_eq!(o.kind(), OutcomeKind::Inapplicable);
    }
}
