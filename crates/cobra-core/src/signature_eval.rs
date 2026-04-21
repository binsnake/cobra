//! Boolean-signature evaluator: computes `expr`'s output at every point
//!
//! The recursive form does one bottom-up tree walk producing a length-`2^n`
//! vector per node — far cheaper than `2^n` separate tree evaluations.

use crate::arith::bitmask;
use crate::evaluator::{Evaluator, Workspace};
use crate::expr::{Expr, Kind};

/// Evaluate `expr` at every assignment in `{0, 1}^num_vars`. Variable
/// index `v` corresponds to bit `v` of the signature index. Returns a
/// vector of length `2^num_vars`.
#[must_use]
pub fn evaluate_boolean_signature(expr: &Expr, num_vars: u32, bitwidth: u32) -> Vec<u64> {
    let len = 1usize << num_vars;
    eval_sig_recursive(expr, len, bitwidth)
}

/// `Evaluator` overload and reuses a single `Workspace` when the
/// evaluator has a compiled body.
#[must_use]
pub fn evaluate_boolean_signature_from_evaluator(
    eval: &Evaluator,
    num_vars: u32,
    bitwidth: u32,
) -> Vec<u64> {
    let len = 1usize << num_vars;
    let mask = bitmask(bitwidth);
    let mut sig = vec![0u64; len];
    let mut point = vec![0u64; num_vars as usize];
    let mut workspace = Workspace::default();
    for i in 0..len {
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
        sig[i] = raw & mask;
    }
    sig
}

fn eval_sig_recursive(expr: &Expr, len: usize, bitwidth: u32) -> Vec<u64> {
    let mask = bitmask(bitwidth);
    match &expr.kind {
        Kind::Constant(v) => vec![*v & mask; len],
        Kind::Variable(idx) => {
            let k = *idx as usize;
            (0..len).map(|i| ((i >> k) & 1) as u64).collect()
        }
        Kind::Not => {
            let mut child = eval_sig_recursive(&expr.children[0], len, bitwidth);
            for v in &mut child {
                *v = !*v & mask;
            }
            child
        }
        Kind::Neg => {
            let mut child = eval_sig_recursive(&expr.children[0], len, bitwidth);
            for v in &mut child {
                *v = 0u64.wrapping_sub(*v) & mask;
            }
            child
        }
        Kind::Shr(k) => {
            let mut child = eval_sig_recursive(&expr.children[0], len, bitwidth);
            let k = *k;
            if k >= 64 {
                child.fill(0);
            } else {
                for v in &mut child {
                    *v = (*v >> k) & mask;
                }
            }
            child
        }
        Kind::Add => {
            let mut left = eval_sig_recursive(&expr.children[0], len, bitwidth);
            let right = eval_sig_recursive(&expr.children[1], len, bitwidth);
            for (l, r) in left.iter_mut().zip(right.iter()) {
                *l = l.wrapping_add(*r) & mask;
            }
            left
        }
        Kind::Mul => {
            let mut left = eval_sig_recursive(&expr.children[0], len, bitwidth);
            let right = eval_sig_recursive(&expr.children[1], len, bitwidth);
            for (l, r) in left.iter_mut().zip(right.iter()) {
                *l = l.wrapping_mul(*r) & mask;
            }
            left
        }
        Kind::And => {
            let mut left = eval_sig_recursive(&expr.children[0], len, bitwidth);
            let right = eval_sig_recursive(&expr.children[1], len, bitwidth);
            for (l, r) in left.iter_mut().zip(right.iter()) {
                *l &= *r;
            }
            left
        }
        Kind::Or => {
            let mut left = eval_sig_recursive(&expr.children[0], len, bitwidth);
            let right = eval_sig_recursive(&expr.children[1], len, bitwidth);
            for (l, r) in left.iter_mut().zip(right.iter()) {
                *l = (*l | *r) & mask;
            }
            left
        }
        Kind::Xor => {
            let mut left = eval_sig_recursive(&expr.children[0], len, bitwidth);
            let right = eval_sig_recursive(&expr.children[1], len, bitwidth);
            for (l, r) in left.iter_mut().zip(right.iter()) {
                *l = (*l ^ *r) & mask;
            }
            left
        }
    }
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
    fn evaluator_overload_matches_expr_overload() {
        let expr = Expr::add(Expr::variable(0), Expr::constant(3));
        let eval = Evaluator::from_expr(&expr, 8);
        let from_expr = evaluate_boolean_signature(&expr, 1, 8);
        let from_eval = evaluate_boolean_signature_from_evaluator(&eval, 1, 8);
        assert_eq!(from_expr, from_eval);
    }
}
