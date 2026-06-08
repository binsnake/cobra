//! Node-width queries for the mixed-width IR.
//!
//! All non-cast/Concat variants are **same-width**: their result width equals
//! their (first) child's width, and constants take the surrounding context
//! width. The width-changing variants are the casts (`ZExt`/`SExt`/`Trunc`,
//! whose result width is the payload) and `Concat` (whose result width is the
//! sum of its children's widths).
//!
//! [`is_uniform_width`] is the soundness oracle: a subtree is uniform iff it
//! contains no width-changing node and every variable has the queried width.
//! Passes that assume uniform width must wall off non-uniform subtrees before
//! feeding them to signature/truth-table machinery.

use crate::expr::{Expr, Kind};
use crate::result::{err, CobraError, Result};

/// Result width of `expr`.
///
/// `var_widths[i]` gives the width of `Variable(i)`; callers that don't track
/// per-variable widths pass an empty slice and let every variable default to
/// `default_w`. `Constant` also takes `default_w` (the context width).
#[must_use]
pub fn width_of(expr: &Expr, var_widths: &[u32], default_w: u32) -> u32 {
    match &expr.kind {
        Kind::Constant(_) => default_w,
        Kind::Variable(i) => var_widths.get(*i as usize).copied().unwrap_or(default_w),
        Kind::ZExt(w) | Kind::SExt(w) | Kind::Trunc(w) => *w,
        Kind::Concat => {
            width_of(&expr.children[0], var_widths, default_w)
                + width_of(&expr.children[1], var_widths, default_w)
        }
        // Same-width ops: inherit the (first) child's width.
        Kind::Not
        | Kind::Neg
        | Kind::Shr(_)
        | Kind::Add
        | Kind::Mul
        | Kind::And
        | Kind::Or
        | Kind::Xor => width_of(&expr.children[0], var_widths, default_w),
    }
}

/// `true` iff `expr` is uniformly `w`-wide: no cast/`Concat` node anywhere and
/// every `Variable` has width `w`.
#[must_use]
pub fn is_uniform_width(expr: &Expr, var_widths: &[u32], w: u32) -> bool {
    match &expr.kind {
        Kind::ZExt(_) | Kind::SExt(_) | Kind::Trunc(_) | Kind::Concat => false,
        Kind::Constant(_) => true,
        Kind::Variable(i) => var_widths.get(*i as usize).copied().unwrap_or(w) == w,
        Kind::Not
        | Kind::Neg
        | Kind::Shr(_)
        | Kind::Add
        | Kind::Mul
        | Kind::And
        | Kind::Or
        | Kind::Xor => expr
            .children
            .iter()
            .all(|c| is_uniform_width(c, var_widths, w)),
    }
}

/// Validate that `expr` is width-consistent.
///
/// Same-width binary operands must agree on width; `Concat` children may have
/// any widths; casts are well-formed for any payload. Returns
/// `CobraError::InvalidArgument` on the first mismatch.
pub fn validate_widths(expr: &Expr, var_widths: &[u32], default_w: u32) -> Result<()> {
    for child in &expr.children {
        validate_widths(child, var_widths, default_w)?;
    }
    match &expr.kind {
        // Same-width binary: both operands must have equal width.
        Kind::Add | Kind::Mul | Kind::And | Kind::Or | Kind::Xor => {
            let lw = width_of(&expr.children[0], var_widths, default_w);
            let rw = width_of(&expr.children[1], var_widths, default_w);
            if lw != rw {
                return Err(err(
                    CobraError::InvalidArgument,
                    format!("width mismatch: operands are {lw} and {rw} bits wide"),
                ));
            }
        }
        // Concat children may differ; casts are well-formed for any payload;
        // same-width unary ops and leaves impose no cross-operand constraint.
        _ => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    fn v(i: u32) -> Arc<Expr> {
        Expr::variable(i)
    }

    #[test]
    fn width_of_leaves_and_same_width_ops() {
        // Constant takes the context width.
        assert_eq!(width_of(&Expr::constant(5), &[], 32), 32);
        // Variable with no width table defaults to the context width.
        assert_eq!(width_of(&v(0), &[], 16), 16);
        // Variable width from the table.
        assert_eq!(width_of(&v(1), &[8, 24], 64), 24);
        // Same-width op inherits the first child's width.
        let e = Expr::add(v(0), v(1));
        assert_eq!(width_of(&e, &[8, 8], 64), 8);
        assert_eq!(width_of(&Expr::not(v(0)), &[8], 64), 8);
    }

    #[test]
    fn width_of_casts_return_payload() {
        assert_eq!(width_of(&Expr::zext(v(0), 16), &[8], 8), 16);
        assert_eq!(width_of(&Expr::sext(v(0), 32), &[8], 8), 32);
        assert_eq!(width_of(&Expr::trunc(v(0), 4), &[8], 8), 4);
    }

    #[test]
    fn width_of_concat_sums_children() {
        // u8 ++ u8 -> u16
        let e = Expr::concat(v(0), v(1));
        assert_eq!(width_of(&e, &[8, 8], 64), 16);
        // zext(a,16) ++ trunc(b,4) -> 20
        let e = Expr::concat(Expr::zext(v(0), 16), Expr::trunc(v(1), 4));
        assert_eq!(width_of(&e, &[8, 8], 64), 20);
    }

    #[test]
    fn is_uniform_width_true_for_same_width_tree() {
        // (a + b) * c with all vars at width 8.
        let e = Expr::mul(Expr::add(v(0), v(1)), v(2));
        assert!(is_uniform_width(&e, &[8, 8, 8], 8));
        // A bare constant is uniform at any width.
        assert!(is_uniform_width(&Expr::constant(7), &[], 8));
    }

    #[test]
    fn is_uniform_width_false_on_any_cast_or_concat() {
        assert!(!is_uniform_width(&Expr::zext(v(0), 8), &[8], 8));
        assert!(!is_uniform_width(&Expr::sext(v(0), 8), &[8], 8));
        assert!(!is_uniform_width(&Expr::trunc(v(0), 8), &[8], 8));
        assert!(!is_uniform_width(&Expr::concat(v(0), v(1)), &[8, 8], 8));
        // A cast buried deep still flips the answer to false.
        let e = Expr::add(v(0), Expr::trunc(v(1), 8));
        assert!(!is_uniform_width(&e, &[8, 8], 8));
    }

    #[test]
    fn is_uniform_width_false_on_mismatched_variable() {
        // Variable 1 is 16-wide but we're asking about width 8.
        let e = Expr::add(v(0), v(1));
        assert!(!is_uniform_width(&e, &[8, 16], 8));
        assert!(is_uniform_width(&e, &[8, 8], 8));
    }

    #[test]
    fn validate_widths_accepts_same_width_inference() {
        // Empty table: every var defaults to default_w, so an Add is consistent.
        let e = Expr::add(v(0), v(1));
        assert!(validate_widths(&e, &[], 32).is_ok());
        // Explicit, matching widths.
        assert!(validate_widths(&e, &[8, 8], 64).is_ok());
    }

    #[test]
    fn validate_widths_rejects_mismatched_operands() {
        let e = Expr::add(v(0), v(1));
        let r = validate_widths(&e, &[8, 16], 64);
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().code, CobraError::InvalidArgument);
    }

    #[test]
    fn validate_widths_allows_concat_children_of_any_width() {
        // u8 ++ u16 is well-formed even though the children differ.
        let e = Expr::concat(v(0), v(1));
        assert!(validate_widths(&e, &[8, 16], 64).is_ok());
    }
}
