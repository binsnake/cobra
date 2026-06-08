//! Boolean-signature evaluator: computes `expr`'s output at every point
//!
//! The recursive form does one bottom-up tree walk producing a length-`2^n`
//! vector per node — far cheaper than `2^n` separate tree evaluations.

use crate::arith::{bitmask, sext, trunc, zext};
use crate::evaluator::{Evaluator, Workspace};
use crate::expr::{Expr, Kind};
use crate::width::width_of;

/// Evaluate `expr` at every assignment in `{0, 1}^num_vars`. Variable
/// index `v` corresponds to bit `v` of the signature index. Returns a
/// vector of length `2^num_vars`.
#[must_use]
pub fn evaluate_boolean_signature(expr: &Expr, num_vars: u32, bitwidth: u32) -> Vec<u64> {
    let len = 1usize << num_vars;
    // A free-list of `len`-sized scratch buffers reused across nodes. Without
    // it the bottom-up walk allocates a fresh `Vec<u64>` per node; with it the
    // total allocation count drops to roughly the peak live-buffer depth.
    let mut pool: Vec<Vec<u64>> = Vec::new();
    eval_sig_into(expr, len, bitwidth, &mut pool)
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
    sig
}

/// Take a `len`-sized scratch buffer from the pool, or allocate one. Pooled
/// buffers are always `len`-sized (the recursion runs at a single `len`), and
/// every leaf arm overwrites all entries, so no re-initialisation is needed.
#[inline]
fn take_buf(pool: &mut Vec<Vec<u64>>, len: usize) -> Vec<u64> {
    pool.pop().unwrap_or_else(|| vec![0u64; len])
}

fn eval_sig_into(expr: &Expr, len: usize, bitwidth: u32, pool: &mut Vec<Vec<u64>>) -> Vec<u64> {
    let mask = bitmask(bitwidth);
    match &expr.kind {
        Kind::Constant(v) => {
            let val = *v & mask;
            let mut buf = take_buf(pool, len);
            buf.iter_mut().for_each(|x| *x = val);
            buf
        }
        Kind::Variable(idx) => {
            let k = *idx as usize;
            let mut buf = take_buf(pool, len);
            for (i, x) in buf.iter_mut().enumerate() {
                *x = ((i >> k) & 1) as u64;
            }
            buf
        }
        Kind::Not => {
            let mut child = eval_sig_into(&expr.children[0], len, bitwidth, pool);
            for v in &mut child {
                *v = !*v & mask;
            }
            child
        }
        Kind::Neg => {
            let mut child = eval_sig_into(&expr.children[0], len, bitwidth, pool);
            for v in &mut child {
                *v = 0u64.wrapping_sub(*v) & mask;
            }
            child
        }
        Kind::Shr(k) => {
            let mut child = eval_sig_into(&expr.children[0], len, bitwidth, pool);
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
            let mut left = eval_sig_into(&expr.children[0], len, bitwidth, pool);
            let right = eval_sig_into(&expr.children[1], len, bitwidth, pool);
            for (l, r) in left.iter_mut().zip(right.iter()) {
                *l = l.wrapping_add(*r) & mask;
            }
            pool.push(right);
            left
        }
        Kind::Mul => {
            let mut left = eval_sig_into(&expr.children[0], len, bitwidth, pool);
            let right = eval_sig_into(&expr.children[1], len, bitwidth, pool);
            for (l, r) in left.iter_mut().zip(right.iter()) {
                *l = l.wrapping_mul(*r) & mask;
            }
            pool.push(right);
            left
        }
        Kind::And => {
            let mut left = eval_sig_into(&expr.children[0], len, bitwidth, pool);
            let right = eval_sig_into(&expr.children[1], len, bitwidth, pool);
            for (l, r) in left.iter_mut().zip(right.iter()) {
                *l &= *r;
            }
            pool.push(right);
            left
        }
        Kind::Or => {
            let mut left = eval_sig_into(&expr.children[0], len, bitwidth, pool);
            let right = eval_sig_into(&expr.children[1], len, bitwidth, pool);
            for (l, r) in left.iter_mut().zip(right.iter()) {
                *l = (*l | *r) & mask;
            }
            pool.push(right);
            left
        }
        Kind::Xor => {
            let mut left = eval_sig_into(&expr.children[0], len, bitwidth, pool);
            let right = eval_sig_into(&expr.children[1], len, bitwidth, pool);
            for (l, r) in left.iter_mut().zip(right.iter()) {
                *l = (*l ^ *r) & mask;
            }
            pool.push(right);
            left
        }
        Kind::ZExt(_) | Kind::SExt(_) | Kind::Trunc(_) | Kind::Concat => {
            eval_sig_cast_into(expr, len, bitwidth, pool)
        }
    }
}

/// Signature arms for the width-changing nodes (casts and `Concat`). Split out
/// of [`eval_sig_recursive`] to keep that hot dispatch small.
fn eval_sig_cast_into(
    expr: &Expr,
    len: usize,
    bitwidth: u32,
    pool: &mut Vec<Vec<u64>>,
) -> Vec<u64> {
    match &expr.kind {
        Kind::ZExt(w) => {
            let mut child = eval_sig_into(&expr.children[0], len, bitwidth, pool);
            for v in &mut child {
                *v = zext(*v, *w);
            }
            child
        }
        Kind::SExt(w) => {
            let from = width_of(&expr.children[0], &[], bitwidth);
            let mut child = eval_sig_into(&expr.children[0], len, bitwidth, pool);
            for v in &mut child {
                *v = sext(*v, from, *w);
            }
            child
        }
        Kind::Trunc(w) => {
            let mut child = eval_sig_into(&expr.children[0], len, bitwidth, pool);
            for v in &mut child {
                *v = trunc(*v, *w);
            }
            child
        }
        // Concat (the only remaining width-changing kind here).
        _ => {
            let low_w = width_of(&expr.children[1], &[], bitwidth);
            let out_mask = bitmask(width_of(expr, &[], bitwidth));
            let low_mask = bitmask(low_w);
            let mut high = eval_sig_into(&expr.children[0], len, bitwidth, pool);
            let low = eval_sig_into(&expr.children[1], len, bitwidth, pool);
            for (h, l) in high.iter_mut().zip(low.iter()) {
                *h = (h.wrapping_shl(low_w) | (*l & low_mask)) & out_mask;
            }
            pool.push(low);
            high
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
