//! Fallback verifier that always returns [`VerifyOutcome::Unverified`].
//! Used when the `z3` feature is disabled.

use cobra_core::expr::Expr;

use crate::{Verifier, VerifyOpts, VerifyOutcome};

/// hard proof must run a real backend.
#[derive(Copy, Clone, Debug, Default)]
pub struct NullVerifier;

impl Verifier for NullVerifier {
    fn prove_equiv(
        &self,
        _original: &Expr,
        _simplified: &Expr,
        _var_names: &[String],
        _opts: VerifyOpts,
    ) -> VerifyOutcome {
        VerifyOutcome::Unverified
    }

    fn prove_reconstruction(
        &self,
        _cob_coeffs: &[u64],
        _simplified: &Expr,
        _var_names: &[String],
        _num_vars: u32,
        _opts: VerifyOpts,
    ) -> VerifyOutcome {
        VerifyOutcome::Unverified
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn null_verifier_always_unverified() {
        let v = NullVerifier;
        let a = Expr::add(Expr::variable(0), Expr::variable(1));
        let b = Expr::add(Expr::variable(1), Expr::variable(0));
        let vars = vec!["x".into(), "y".into()];
        let out = v.prove_equiv(&a, &b, &vars, VerifyOpts::default());
        assert_eq!(out, VerifyOutcome::Unverified);

        let out = v.prove_reconstruction(&[0, 1, 1, 0], &a, &vars, 2, VerifyOpts::default());
        assert_eq!(out, VerifyOutcome::Unverified);
    }
}
