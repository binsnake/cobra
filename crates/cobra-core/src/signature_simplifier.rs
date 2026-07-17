//! Shared public helpers for signature-oriented simplification.
//!
//! This mirrors upstream `SignatureSimplifier.h`: a small payload/context
//! surface plus the Boolean-valued signature predicate.

use crate::core::evaluator::Evaluator;
use crate::core::expr::Expr;
use crate::core::expr_cost::ExprCost;
use crate::core::pass_contract::VerificationState;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct SignaturePayload {
    pub expr: Arc<Expr>,
    pub cost: ExprCost,
    pub verification: VerificationState,
    pub real_vars: Vec<String>,
}

impl SignaturePayload {
    #[must_use]
    pub fn new(expr: Arc<Expr>, cost: ExprCost, real_vars: Vec<String>) -> Self {
        Self {
            expr,
            cost,
            verification: VerificationState::Unverified,
            real_vars,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct SignatureContext {
    pub vars: Vec<String>,
    pub original_indices: Vec<u32>,
    pub eval: Option<Evaluator>,
}

#[must_use]
pub fn is_boolean_valued(sig: &[u64]) -> bool {
    sig.iter().all(|&v| v <= 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::expr::Kind;

    #[test]
    fn boolean_valued_accepts_only_zero_and_one() {
        assert!(is_boolean_valued(&[]));
        assert!(is_boolean_valued(&[0, 1, 1, 0]));
        assert!(!is_boolean_valued(&[0, 1, 2, 0]));
    }

    #[test]
    fn payload_default_verification_is_unverified() {
        let payload = SignaturePayload::new(
            Expr::variable(0),
            ExprCost::default(),
            vec!["x".to_string()],
        );
        assert!(matches!(payload.expr.kind, Kind::Variable(0)));
        assert_eq!(payload.verification, VerificationState::Unverified);
        assert_eq!(payload.real_vars, ["x"]);
    }
}
