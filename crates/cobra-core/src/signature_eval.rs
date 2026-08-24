//! Boolean-signature evaluator: computes `expr`'s output at every point
//!
//! The recursive form does one bottom-up tree walk producing a length-`2^n`
//! vector per node — far cheaper than `2^n` separate tree evaluations.

use crate::core::arith::bitmask;
use crate::core::evaluator::{Evaluator, Workspace};
use crate::core::expr::Expr;
use crate::core::result::{err, CobraError, Result};
use crate::core::width::checked_width_of;

pub const MAX_SIGNATURE_VARS: u32 = 20;
pub const MAX_SIGNATURE_BYTES: usize = 8 * 1024 * 1024;

/// Validate a Boolean-signature dimension before shifting or allocating.
pub fn checked_signature_len(num_vars: u32) -> Result<usize> {
    if num_vars > MAX_SIGNATURE_VARS {
        return Err(err(
            CobraError::TooManyVariables,
            format!("signature dimension {num_vars} exceeds {MAX_SIGNATURE_VARS} variables"),
        ));
    }
    let len = 1usize.checked_shl(num_vars).ok_or_else(|| {
        err(
            CobraError::TooManyVariables,
            "signature dimension exceeds addressable memory",
        )
    })?;
    let bytes = len.checked_mul(std::mem::size_of::<u64>()).ok_or_else(|| {
        err(
            CobraError::TooManyVariables,
            "signature byte size overflows",
        )
    })?;
    if bytes > MAX_SIGNATURE_BYTES {
        return Err(err(
            CobraError::TooManyVariables,
            format!("signature requires {bytes} bytes; limit is {MAX_SIGNATURE_BYTES}"),
        ));
    }
    Ok(len)
}

/// Fallible Boolean-signature evaluation for untrusted dimensions.
pub fn try_evaluate_boolean_signature(
    expr: &Expr,
    num_vars: u32,
    bitwidth: u32,
) -> Result<Vec<u64>> {
    checked_signature_len(num_vars)?;
    // Route through the compiled evaluator, which is the reference semantics.
    // The tree walker this replaced threaded the run-global `bitwidth` into
    // every same-width operator while its cast arms used node-local widths, so
    // the two disagreed on any tree containing a cast.
    //
    // Mask at the expression's own result width, not the run-global one: a
    // `Concat` of two 8-bit children is a 16-bit value even at bitwidth 8.
    let result_w = checked_width_of(expr, &[], bitwidth)?;
    let eval = Evaluator::from_expr(expr, bitwidth);
    signature_masked_at(&eval, num_vars, result_w)
}

/// Evaluate `expr` at every assignment in `{0, 1}^num_vars`. Variable
/// index `v` corresponds to bit `v` of the signature index. Returns a
/// vector of length `2^num_vars`.
#[must_use]
pub fn evaluate_boolean_signature(expr: &Expr, num_vars: u32, bitwidth: u32) -> Vec<u64> {
    try_evaluate_boolean_signature(expr, num_vars, bitwidth).unwrap_or_default()
}

/// `Evaluator` overload and reuses a single `Workspace` when the
/// evaluator has a compiled body.
#[must_use]
pub fn evaluate_boolean_signature_from_evaluator(
    eval: &Evaluator,
    num_vars: u32,
    bitwidth: u32,
) -> Vec<u64> {
    try_evaluate_boolean_signature_from_evaluator(eval, num_vars, bitwidth).unwrap_or_default()
}

/// Fallible evaluator-backed signature evaluation for untrusted dimensions.
pub fn try_evaluate_boolean_signature_from_evaluator(
    eval: &Evaluator,
    num_vars: u32,
    bitwidth: u32,
) -> Result<Vec<u64>> {
    signature_masked_at(eval, num_vars, bitwidth)
}

/// Shared body: evaluate over `{0,1}^num_vars`, masking each result to
/// `mask_width` bits.
fn signature_masked_at(eval: &Evaluator, num_vars: u32, mask_width: u32) -> Result<Vec<u64>> {
    let len = checked_signature_len(num_vars)?;
    let mask = bitmask(mask_width);
    let mut sig = vec![0u64; len];
    // Size the point to cover any variable index above `num_vars`. A lifted or
    // ghost variable reads as 0 at every point, matching the tree walker this
    // replaced, where `(i >> k) & 1` was 0 for every `k >= num_vars`. Only the
    // low `num_vars` slots are ever flipped below.
    let point_width = (num_vars as usize).max(eval.input_arity() as usize);
    let mut point = vec![0u64; point_width];
    let mut workspace = Workspace::default();
    for (i, slot) in sig.iter_mut().enumerate().take(len) {
        // Incrementally maintain `point` so it matches the standard binary
        // encoding of `i`: point[v] = (i >> v) & 1. Going from i-1 to i flips
        // bits 0..=i.trailing_zeros(); across all iterations this averages O(1)
        // flips per step instead of O(num_vars).
        if i != 0 {
            let tz = (i as u32).trailing_zeros() as usize;
            // tz < 64 here since i != 0; also tz < nv because i < 2^nv.
            for p in point.iter_mut().take(tz + 1) {
                *p ^= 1;
            }
        }
        let raw = if eval.has_compiled() {
            eval.eval_with(&point, &mut workspace)
        } else {
            eval.eval(&point)
        };
        *slot = raw & mask;
    }
    Ok(sig)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_sig_fills_with_masked_value() {
        let sig = evaluate_boolean_signature(&Expr::constant(0xDEAD), 2, 8);
        assert_eq!(sig, vec![0xAD; 4]);
    }

    #[test]
    fn single_variable_sig() {
        let sig = evaluate_boolean_signature(&Expr::variable(0), 1, 64);
        assert_eq!(sig, vec![0, 1]);
    }

    #[test]
    fn xor_sig_two_vars() {
        let e = Expr::xor(Expr::variable(0), Expr::variable(1));
        let sig = evaluate_boolean_signature(&e, 2, 64);
        // (0,0) → 0, (1,0) → 1, (0,1) → 1, (1,1) → 0
        assert_eq!(sig, vec![0, 1, 1, 0]);
    }

    #[test]
    fn oversized_signature_dimension_fails_before_allocation() {
        assert_eq!(
            checked_signature_len(MAX_SIGNATURE_VARS + 1)
                .expect_err("oversized dimension must fail")
                .code,
            CobraError::TooManyVariables
        );
        assert!(
            try_evaluate_boolean_signature(&Expr::variable(0), MAX_SIGNATURE_VARS + 1, 64).is_err()
        );
        assert!(
            evaluate_boolean_signature(&Expr::variable(0), MAX_SIGNATURE_VARS + 1, 64).is_empty()
        );
    }

    #[test]
    fn mba_identity_matches() {
        // (x & y) + (x | y) = x + y at every Boolean point.
        let x = Expr::variable(0);
        let y = Expr::variable(1);
        let lhs = Expr::add(
            Expr::and(x.clone_tree(), y.clone_tree()),
            Expr::or(x.clone_tree(), y.clone_tree()),
        );
        let rhs = Expr::add(x, y);
        let a = evaluate_boolean_signature(&lhs, 2, 64);
        let b = evaluate_boolean_signature(&rhs, 2, 64);
        assert_eq!(a, b);
    }

    #[test]
    fn cast_and_concat_signatures() {
        // concat(a:u8, b:u8) over Boolean inputs at bitwidth 8.
        // Points (a,b): 00->0x0000, 10->0x0100, 01->0x0001, 11->0x0101.
        let e = Expr::concat(Expr::variable(0), Expr::variable(1));
        let sig = evaluate_boolean_signature(&e, 2, 8);
        assert_eq!(sig, vec![0x0000, 0x0100, 0x0001, 0x0101]);

        // sext(a, 16) at bw 8: a in {0,1}; never the sign bit, so stays 0/1.
        let e = Expr::sext(Expr::variable(0), 16);
        let sig = evaluate_boolean_signature(&e, 1, 8);
        assert_eq!(sig, vec![0, 1]);

        // trunc(zext(a,16), 1) collapses to the low bit.
        let e = Expr::trunc(Expr::zext(Expr::variable(0), 16), 1);
        let sig = evaluate_boolean_signature(&e, 1, 8);
        assert_eq!(sig, vec![0, 1]);
    }

    #[test]
    fn evaluator_overload_matches_expr_overload() {
        let expr = Expr::add(Expr::variable(0), Expr::constant(3));
        let eval = Evaluator::from_expr(&expr, 8);
        let from_expr = evaluate_boolean_signature(&expr, 1, 8);
        let from_eval = evaluate_boolean_signature_from_evaluator(&eval, 1, 8);
        assert_eq!(from_expr, from_eval);
    }
}
