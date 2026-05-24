//! Verifier trait and optional Z3 backend.
//!
//! `Box<dyn Verifier>` so that Z3 stays optional — without the `z3`
//! feature, downstream crates compile against [`NullVerifier`] which
//! always reports [`VerifyOutcome::Unverified`].

#![forbid(unsafe_code)]

use cobra_core::expr::Expr;

pub mod null;
#[cfg(feature = "z3")]
pub mod z3_backend;

pub use crate::null::NullVerifier;
#[cfg(feature = "z3")]
pub use crate::z3_backend::Z3Verifier;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyOutcome {
    Equivalent,
    /// A counterexample was found; payload is the solver's model string
    /// (best-effort human-readable — format is backend-dependent).
    Disproved {
        counterexample: String,
    },
    TimedOut,
    /// No backend available (e.g. null verifier). Not a failure — callers
    /// that require a hard proof should treat this as "cannot confirm".
    Unverified,
}

impl VerifyOutcome {
    #[must_use]
    pub fn is_equivalent(&self) -> bool {
        matches!(self, Self::Equivalent)
    }

    #[must_use]
    pub fn counterexample(&self) -> Option<&str> {
        match self {
            Self::Disproved { counterexample } => Some(counterexample.as_str()),
            _ => None,
        }
    }
}

/// `timeout_ms = 500` from `Z3Verifier.h`.
#[derive(Copy, Clone, Debug)]
pub struct VerifyOpts {
    pub bitwidth: u32,
    pub timeout_ms: u32,
}

impl Default for VerifyOpts {
    fn default() -> Self {
        Self {
            bitwidth: 64,
            timeout_ms: 500,
        }
    }
}

/// Trait implemented by any backend that can prove two expressions equal
/// over all `2^bitwidth` inputs.
pub trait Verifier: Send + Sync {
    /// Compare two `Expr` trees for equivalence.
    fn prove_equiv(
        &self,
        original: &Expr,
        simplified: &Expr,
        var_names: &[String],
        opts: VerifyOpts,
    ) -> VerifyOutcome;

    /// Compare an expression reconstructed from `CoB` coefficients against a
    /// simplified `Expr`. `cob_coeffs` has length `2^num_vars`; index `i`
    /// is the coefficient of the AND-product of variables whose bit is set
    /// entry point.
    fn prove_reconstruction(
        &self,
        cob_coeffs: &[u64],
        simplified: &Expr,
        var_names: &[String],
        num_vars: u32,
        opts: VerifyOpts,
    ) -> VerifyOutcome;
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::expr::Expr;

    #[test]
    fn verifier_usable_as_trait_object() {
        // The orchestrator holds a `Box<dyn Verifier>`. Sanity-check that
        // both the null impl and (when enabled) the Z3 impl satisfy the
        // trait's `Send + Sync` bound and can be boxed.
        let v: Box<dyn Verifier> = Box::new(NullVerifier);
        let e = Expr::variable(0);
        let out = v.prove_equiv(&e, &e, &["x".into()], VerifyOpts::default());
        assert_eq!(out, VerifyOutcome::Unverified);
    }

    #[test]
    fn verify_outcome_helpers() {
        assert!(VerifyOutcome::Equivalent.is_equivalent());
        assert!(!VerifyOutcome::TimedOut.is_equivalent());
        assert!(!VerifyOutcome::Unverified.is_equivalent());

        let disp = VerifyOutcome::Disproved {
            counterexample: "x = 1".into(),
        };
        assert_eq!(disp.counterexample(), Some("x = 1"));
        assert_eq!(VerifyOutcome::Equivalent.counterexample(), None);
    }

    #[test]
    fn default_opts_match_cpp() {
        let opts = VerifyOpts::default();
        assert_eq!(opts.bitwidth, 64);
        assert_eq!(opts.timeout_ms, 500);
    }
}
