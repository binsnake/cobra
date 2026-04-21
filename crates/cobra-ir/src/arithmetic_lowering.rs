//! Lower a change-of-basis signature split into (monomial-polynomial,
//! residual-AND) form.
//!
//! Given:
//! - `and_coeffs[mask]` — coefficient of `∏ x_i` (AND monomial) at
//!   support `mask`,
//! - `mul_coeffs[mask]` — coefficient of `∏ x_i` (MUL monomial) at
//!   support `mask`, with singletons reinterpreted as squared terms,
//!
//! produce a [`PolyIR`] that gathers every multiplicative contribution
//! (linear, square, multilinear products of 2+ variables) and a
//! residual AND-coefficient vector with the singleton slots zeroed.
//! The residual captures the pure-bitwise remainder that the caller
//! assembles alongside the poly expression.

use cobra_core::arith::bitmask;
use cobra_core::result::{err, CobraError, Result};

use crate::mono::{MonomialKey, MAX_POLY_VARS};
use crate::poly::{Coeff, CoeffMap, PolyIR};

pub struct LoweringResult {
    pub poly: PolyIR,
    pub residual_and_coeffs: Vec<Coeff>,
}

/// Split `and_coeffs` / `mul_coeffs` into a polynomial (captures all
/// singleton linear / singleton square / multivariate product terms)
/// and a residual AND-coefficient vector. Returns
/// [`CobraError::TooManyVariables`] if `num_vars > MAX_POLY_VARS`.
pub fn lower_arithmetic_fragment(
    and_coeffs: &[Coeff],
    mul_coeffs: &[Coeff],
    num_vars: u8,
    bitwidth: u32,
) -> Result<LoweringResult> {
    if usize::from(num_vars) > MAX_POLY_VARS {
        return Err(err(
            CobraError::TooManyVariables,
            format!(
                "lower_arithmetic_fragment: num_vars ({num_vars}) exceeds MAX_POLY_VARS ({MAX_POLY_VARS})"
            ),
        ));
    }

    let len = 1usize << num_vars;
    assert_eq!(and_coeffs.len(), len, "and_coeffs length mismatch");
    assert_eq!(mul_coeffs.len(), len, "mul_coeffs length mismatch");

    let mask = bitmask(bitwidth);
    let mut terms: CoeffMap = CoeffMap::with_hasher(ahash::RandomState::with_seeds(1, 2, 3, 4));
    let mut residual: Vec<Coeff> = and_coeffs.to_vec();

    for i in 0..num_vars {
        let singleton = 1usize << i;
        let linear = and_coeffs[singleton] & mask;
        let square = mul_coeffs[singleton] & mask;

        if linear != 0 {
            let mut exps = [0u8; MAX_POLY_VARS];
            exps[usize::from(i)] = 1;
            let key = MonomialKey::from_exponents(&exps, num_vars);
            let slot = terms.entry(key).or_insert(0);
            *slot = slot.wrapping_add(linear) & mask;
        }

        if square != 0 {
            let mut exps = [0u8; MAX_POLY_VARS];
            exps[usize::from(i)] = 2;
            let key = MonomialKey::from_exponents(&exps, num_vars);
            let slot = terms.entry(key).or_insert(0);
            *slot = slot.wrapping_add(square) & mask;
        }

        residual[singleton] = 0;
    }

    for (m, &raw) in mul_coeffs.iter().enumerate() {
        if (m as u64).count_ones() < 2 {
            continue;
        }
        let c = raw & mask;
        if c == 0 {
            continue;
        }
        let mut exps = [0u8; MAX_POLY_VARS];
        for v in 0..num_vars {
            if (m & (1usize << v)) != 0 {
                exps[usize::from(v)] = 1;
            }
        }
        let key = MonomialKey::from_exponents(&exps, num_vars);
        let slot = terms.entry(key).or_insert(0);
        *slot = slot.wrapping_add(c) & mask;
    }

    terms.retain(|_, &mut v| v != 0);

    Ok(LoweringResult {
        poly: PolyIR {
            num_vars,
            bitwidth,
            terms,
        },
        residual_and_coeffs: residual,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn singletons_transfer_to_poly_and_zero_the_residual() {
        // num_vars=2, linear part = 3x + 5y.
        let and_coeffs = vec![0u64, 3, 5, 0];
        let mul_coeffs = vec![0u64, 0, 0, 0];
        let r = lower_arithmetic_fragment(&and_coeffs, &mul_coeffs, 2, 64).unwrap();
        assert_eq!(r.residual_and_coeffs, vec![0u64, 0, 0, 0]);
        assert_eq!(r.poly.terms.len(), 2);
    }

    #[test]
    fn square_terms_are_degree_two_monomials() {
        let and_coeffs = vec![0u64, 0, 0, 0];
        let mul_coeffs = vec![0u64, 2, 3, 0];
        let r = lower_arithmetic_fragment(&and_coeffs, &mul_coeffs, 2, 64).unwrap();
        assert_eq!(r.poly.terms.len(), 2);
        let x2 = MonomialKey::from_exponents(&[2, 0], 2);
        let y2 = MonomialKey::from_exponents(&[0, 2], 2);
        assert_eq!(r.poly.terms.get(&x2), Some(&2));
        assert_eq!(r.poly.terms.get(&y2), Some(&3));
    }

    #[test]
    fn multilinear_products_transfer_from_mul_coeffs() {
        // num_vars = 2, mul_coeffs[3] = 7 → xy term.
        let and_coeffs = vec![0u64, 0, 0, 0];
        let mul_coeffs = vec![0u64, 0, 0, 7];
        let r = lower_arithmetic_fragment(&and_coeffs, &mul_coeffs, 2, 64).unwrap();
        assert_eq!(r.poly.terms.len(), 1);
        let xy = MonomialKey::from_exponents(&[1, 1], 2);
        assert_eq!(r.poly.terms.get(&xy), Some(&7));
    }

    #[test]
    fn multivariate_residual_preserves_nonsingleton_and_coeffs() {
        // and_coeffs[3] = 5 (xy AND monomial) — stays in residual.
        let and_coeffs = vec![0u64, 1, 2, 5];
        let mul_coeffs = vec![0u64; 4];
        let r = lower_arithmetic_fragment(&and_coeffs, &mul_coeffs, 2, 64).unwrap();
        assert_eq!(r.residual_and_coeffs, vec![0u64, 0, 0, 5]);
    }

    #[test]
    fn too_many_vars_returns_err() {
        let and = vec![0u64; 1];
        let mul = vec![0u64; 1];
        // The MAX_POLY_VARS check fires on num_vars, not the length.
        let res = lower_arithmetic_fragment(&and, &mul, 21, 64);
        assert!(res.is_err());
    }
}
