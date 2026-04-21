//! Cost-aware `Expr` builder for `CoB` (AND-monomial) coefficient
//! vectors. Performs greedy bitwise recognition before emitting a sum:
//!
//! - **OR match**: two disjoint-ish monomials with identical coefficient
//!   `c` combined with a `-c`-weighted union yield `c * (T(m1) | T(m2))`.
//! - **XOR match**: identical coefficient `c` combined with a
//!   `-2c`-weighted union yield `c * (T(m1) ^ T(m2))`.
//! - **NOT recognition**: a standalone `-1` constant term together with
//!   a single remaining `-1`-coefficient monomial collapses to
//!   `~T(m)` (since `-1 + -T(m) = ~T(m)` mod `2^bitwidth`).
//!
//! Everything else falls through to a straight
//! `Σ ApplyCoefficient(c_i, T(m_i))` sum.
//!
//! implementation's shape but driven through iterators and slice
//! indices rather than raw pointer-carrying `Term` structs. Compound
//! results re-enter the term vector but are excluded from further
//! pairing by being appended *after* the sort step.
//!
//! Inputs are assumed to come from
//! [`cobra_ir::interpolate_coefficients`] — i.e. `coeffs[0]` is the
//! constant term and `coeffs[i]` for `i > 0` is the coefficient of
//! `∏_{k ∈ bits(i)} x_k`.

use cobra_core::arith::{bitmask, mod_mul, mod_neg};
use cobra_core::expr::Expr;
use cobra_core::expr_rewrite::{apply_coefficient, build_and_product};
use std::collections::HashMap;

struct Term {
    mask: u64,
    coeff: u64,
    expr: Option<Box<Expr>>,
    consumed: bool,
}

impl Term {
    fn take_operand(&mut self) -> Box<Expr> {
        if let Some(e) = self.expr.take() {
            return e;
        }
        build_and_product(self.mask).expect("non-zero mask")
    }
}

fn greedy_rewrite(terms: &mut Vec<Term>, mask_index: &HashMap<u64, usize>, bitwidth: u32) {
    let mut sorted: Vec<usize> = (0..terms.len()).filter(|&i| terms[i].mask != 0).collect();
    sorted.sort_by(|&a, &b| {
        let pa = terms[a].mask.count_ones();
        let pb = terms[b].mask.count_ones();
        pa.cmp(&pb).then_with(|| terms[a].mask.cmp(&terms[b].mask))
    });

    for si in 0..sorted.len() {
        let i = sorted[si];
        if terms[i].consumed {
            continue;
        }
        for &j in sorted.iter().skip(si + 1) {
            if terms[j].consumed {
                continue;
            }
            if terms[i].consumed {
                break;
            }

            let c1 = terms[i].coeff;
            let c2 = terms[j].coeff;
            if c1 != c2 {
                continue;
            }

            let m1 = terms[i].mask;
            let m2 = terms[j].mask;
            let m_union = m1 | m2;
            if m_union == m1 || m_union == m2 {
                continue;
            }

            let (c_union, union_idx) = mask_index
                .get(&m_union)
                .copied()
                .filter(|&idx| !terms[idx].consumed)
                .map_or((0u64, None), |idx| (terms[idx].coeff, Some(idx)));

            let c = c1;
            let neg_c = mod_neg(c, bitwidth);
            let neg_two_c = mod_neg(mod_mul(2, c, bitwidth), bitwidth);

            let compound = if c_union == neg_c {
                let lhs = terms[i].take_operand();
                let rhs = terms[j].take_operand();
                Some(Expr::or(lhs, rhs))
            } else if c_union == neg_two_c {
                let lhs = terms[i].take_operand();
                let rhs = terms[j].take_operand();
                Some(Expr::xor(lhs, rhs))
            } else {
                None
            };

            if let Some(expr) = compound {
                terms[i].consumed = true;
                terms[j].consumed = true;
                if let Some(idx) = union_idx {
                    terms[idx].consumed = true;
                }
                terms.push(Term {
                    mask: m_union,
                    coeff: c,
                    expr: Some(expr),
                    consumed: false,
                });
                break;
            }
        }
    }
}

fn try_not_recognition(terms: &mut [Term], const_coeff: u64, bitwidth: u32) -> bool {
    let neg1 = bitmask(bitwidth);
    if const_coeff != neg1 {
        return false;
    }

    let mut match_idx: Option<usize> = None;
    for (i, t) in terms.iter().enumerate() {
        if t.consumed || t.mask == 0 {
            continue;
        }
        if t.coeff != neg1 {
            return false;
        }
        if match_idx.is_some() {
            return false;
        }
        match_idx = Some(i);
    }
    let Some(idx) = match_idx else {
        return false;
    };

    let operand = terms[idx].take_operand();
    terms[idx].expr = Some(Expr::not(operand));
    terms[idx].coeff = 1;
    true
}

/// Build an `Expr` from a `CoB` coefficient vector. `coeffs[0]` is the
/// constant term; `coeffs[i]` for `i > 0` is the coefficient of the
/// AND-monomial whose variable set is the bits of `i`.
#[must_use]
pub fn build_cob_expr(coeffs: &[u64], _num_vars: u32, bitwidth: u32) -> Box<Expr> {
    let mut const_coeff = coeffs.first().copied().unwrap_or(0);
    let mut terms: Vec<Term> = Vec::new();
    let mut mask_index: HashMap<u64, usize> = HashMap::new();

    for (i, &c) in coeffs.iter().enumerate().skip(1) {
        if c == 0 {
            continue;
        }
        let idx = terms.len();
        terms.push(Term {
            mask: i as u64,
            coeff: c,
            expr: None,
            consumed: false,
        });
        mask_index.insert(i as u64, idx);
    }

    greedy_rewrite(&mut terms, &mask_index, bitwidth);

    if try_not_recognition(&mut terms, const_coeff, bitwidth) {
        const_coeff = 0;
    }

    let mut result: Option<Box<Expr>> = None;
    if const_coeff != 0 {
        result = Some(Expr::constant(const_coeff));
    }

    for t in &mut terms {
        if t.consumed {
            continue;
        }
        let operand = t.take_operand();
        let term_expr = apply_coefficient(operand, t.coeff, bitwidth);
        result = Some(match result {
            Some(acc) => Expr::add(acc, term_expr),
            None => term_expr,
        });
    }

    result.unwrap_or_else(|| Expr::constant(0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluate_boolean_signature;
    use cobra_core::expr::Kind;
    use cobra_ir::interpolate_coefficients;

    fn all_assignments_match(expr: &Expr, sig: &[u64], num_vars: u32, bitwidth: u32) {
        let got = evaluate_boolean_signature(expr, num_vars, bitwidth);
        assert_eq!(got, sig, "expr does not match signature");
    }

    #[test]
    fn constant_only_coeffs_produce_constant_expr() {
        let expr = build_cob_expr(&[42, 0, 0, 0], 2, 64);
        assert!(matches!(expr.kind, Kind::Constant(42)));
    }

    #[test]
    fn empty_coefficient_vector_produces_zero() {
        let expr = build_cob_expr(&[0, 0, 0, 0], 2, 64);
        assert!(matches!(expr.kind, Kind::Constant(0)));
    }

    #[test]
    fn or_pattern_is_recognized() {
        // x + y - (x & y) = x | y at full width — CoB form `x + y - x*y`
        // so coeffs[01]=1, coeffs[10]=1, coeffs[11]=-1 under a 64-bit mask.
        let coeffs = vec![0u64, 1, 1, bitmask(64).wrapping_sub(0)];
        let expr = build_cob_expr(&coeffs, 2, 64);
        // Should collapse to a single OR node at the top.
        assert!(matches!(expr.kind, Kind::Or));
    }

    #[test]
    fn xor_pattern_is_recognized() {
        // x ^ y = x + y - 2*(x & y). Under CoB:
        // coeffs[01]=1, coeffs[10]=1, coeffs[11]=-2.
        let coeffs = vec![0u64, 1, 1, mod_neg(2, 64)];
        let expr = build_cob_expr(&coeffs, 2, 64);
        assert!(matches!(expr.kind, Kind::Xor));
    }

    #[test]
    fn not_pattern_is_recognized() {
        // ~x at bitwidth 64: constant -1, coeff on x is -1.
        let neg1 = bitmask(64);
        let coeffs = vec![neg1, neg1];
        let expr = build_cob_expr(&coeffs, 1, 64);
        assert!(matches!(expr.kind, Kind::Not));
    }

    #[test]
    fn round_trip_from_interpolator_matches_signature() {
        // f(x, y) = x | y — signature is [0, 1, 1, 1] at Boolean width.
        let sig = vec![0u64, 1, 1, 1];
        let coeffs = interpolate_coefficients(sig.clone(), 2, 64);
        let expr = build_cob_expr(&coeffs, 2, 64);
        all_assignments_match(&expr, &sig, 2, 64);
    }

    #[test]
    fn round_trip_xor_three_vars() {
        let sig = vec![0u64, 1, 1, 0, 1, 0, 0, 1]; // x ^ y ^ z
        let coeffs = interpolate_coefficients(sig.clone(), 3, 64);
        let expr = build_cob_expr(&coeffs, 3, 64);
        all_assignments_match(&expr, &sig, 3, 64);
    }

    #[test]
    fn narrow_bitwidth_or_pattern() {
        // At 8-bit: x | y = x + y - (x & y) still, with mask 0xFF.
        let coeffs = vec![0u64, 1, 1, mod_neg(1, 8)];
        let expr = build_cob_expr(&coeffs, 2, 8);
        assert!(matches!(expr.kind, Kind::Or));
    }
}
