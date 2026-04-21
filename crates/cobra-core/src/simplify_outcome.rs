//! Top-level outcome of [`Simplify`]: the simplified expression, its
//! signature vector, and a diagnostic bundle.
//!
//! Ported from `include/cobra/core/SimplifyOutcome.h` and
//! `include/cobra/core/Simplifier.h`.

use crate::classification::{Classification, SemanticClass, StructuralFlag};
use crate::evaluator::Evaluator;
use crate::expr::Expr;
use crate::pass_contract::{ReasonCode, ReasonFrame};

/// Input options for the public `Simplify` API. Defaults match the C++
/// struct (`bitwidth = 64`, `max_vars = 16`, `spot_check = true`,
/// `enable_bitwise_decomposition = true`).
#[derive(Clone, Debug)]
pub struct Options {
    pub bitwidth: u32,
    pub max_vars: u32,
    pub spot_check: bool,
    pub enable_bitwise_decomposition: bool,
    pub structural_flags: StructuralFlag,
    pub evaluator: Evaluator,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            bitwidth: 64,
            max_vars: 16,
            spot_check: true,
            enable_bitwise_decomposition: true,
            structural_flags: StructuralFlag::NONE,
            evaluator: Evaluator::default(),
        }
    }
}

/// Structured diagnostic attached to every `SimplifyOutcome`. Captures
/// which classification the input received, how many rounds of
/// structural transforms ran, and — when the run failed — the top
/// reason code and cause chain.
#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub classification: Classification,
    pub structural_transform_rounds: u32,
    pub transform_produced_candidate: bool,
    pub candidate_failed_verification: bool,
    pub reason: String,
    pub reason_code: Option<ReasonCode>,
    pub cause_chain: Vec<ReasonFrame>,
}

impl Default for Diagnostic {
    fn default() -> Self {
        Self {
            classification: Classification {
                semantic: SemanticClass::Linear,
                flags: StructuralFlag::NONE,
            },
            structural_transform_rounds: 0,
            transform_produced_candidate: false,
            candidate_failed_verification: false,
            reason: String::new(),
            reason_code: None,
            cause_chain: Vec::new(),
        }
    }
}

/// Per-run counters surfaced by the orchestrator. Used for profiling
/// and as an integration-test signal that the pipeline actually ran.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct SimplifyTelemetry {
    pub total_expansions: u32,
    pub max_depth_reached: u32,
    pub candidates_verified: u32,
    pub queue_high_water: u32,
}

/// Top-level outcome. One of three arms (simplified / unchanged /
/// error) matching C++ `SimplifyOutcome::Kind`.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum SimplifyOutcomeKind {
    #[default]
    Simplified,
    UnchangedUnsupported,
    Error,
}

/// Result of a single call to `Simplify`.
#[derive(Clone, Debug)]
pub struct SimplifyOutcome {
    pub kind: SimplifyOutcomeKind,
    pub expr: Option<Box<Expr>>,
    pub sig_vector: Vec<u64>,
    pub real_vars: Vec<String>,
    pub verified: bool,
    pub diag: Diagnostic,
    pub telemetry: SimplifyTelemetry,
}

impl Default for SimplifyOutcome {
    fn default() -> Self {
        Self {
            kind: SimplifyOutcomeKind::Simplified,
            expr: None,
            sig_vector: Vec::new(),
            real_vars: Vec::new(),
            verified: false,
            diag: Diagnostic::default(),
            telemetry: SimplifyTelemetry::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn options_defaults_match_cpp() {
        let o = Options::default();
        assert_eq!(o.bitwidth, 64);
        assert_eq!(o.max_vars, 16);
        assert!(o.spot_check);
        assert!(o.enable_bitwise_decomposition);
        assert_eq!(o.structural_flags, StructuralFlag::NONE);
        assert!(!o.evaluator.has_body());
    }

    #[test]
    fn diagnostic_default_is_linear() {
        let d = Diagnostic::default();
        assert_eq!(d.classification.semantic, SemanticClass::Linear);
        assert_eq!(d.structural_transform_rounds, 0);
        assert!(d.reason.is_empty());
        assert!(d.cause_chain.is_empty());
    }

    #[test]
    fn simplify_outcome_default_is_simplified_empty() {
        let o = SimplifyOutcome::default();
        assert_eq!(o.kind, SimplifyOutcomeKind::Simplified);
        assert!(o.expr.is_none());
        assert!(o.sig_vector.is_empty());
        assert!(!o.verified);
    }
}
