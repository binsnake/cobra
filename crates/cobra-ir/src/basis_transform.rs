//! Monomial ↔ factorial basis transforms for `CoeffMap`s.
//!
//! [`to_factorial_basis`] rewrites `Σ c_i · x^i` as `Σ c_i · x^(i)`
//! where `x^(i) = x · (x-1) · … · (x-i+1)` via Stirling numbers of the
//! second kind. [`to_monomial_basis`] is the inverse, using signed
//! Stirling numbers of the first kind.
//!
//! Both transforms operate variable-by-variable and redistribute
//! coefficients within a `HashMap`. Accumulation is modulo
//! `2^bitwidth`; zero coefficients are stripped from the output.
//! Degrees ≤ 1 are identity — the transforms are no-ops on pure-linear
//! inputs.

use cobra_core::arith::bitmask;

use crate::math_utils::{build_stirling_first_kind, build_stirling_second_kind};
use crate::mono::MonomialKey;
use crate::poly::CoeffMap;

enum Direction {
    ToFactorial,
    ToMonomial,
}

fn transform_basis(input: &CoeffMap, num_vars: u8, bitwidth: u32, dir: &Direction) -> CoeffMap {
    let mask = bitmask(bitwidth);
    let mut current: CoeffMap = input.clone();

    let max_deg = current
        .keys()
        .map(|k| k.max_degree(num_vars))
        .max()
        .unwrap_or(0);
    if max_deg <= 1 {
        return current;
    }

    let stirling = match dir {
        Direction::ToFactorial => build_stirling_second_kind(max_deg, bitwidth),
        Direction::ToMonomial => build_stirling_first_kind(max_deg, bitwidth),
    };

    for var in 0..num_vars {
        let mut next: CoeffMap = CoeffMap::with_hasher(ahash::RandomState::with_seeds(1, 2, 3, 4));
        for (tuple, &c) in &current {
            let e = tuple.exponent_at(var);
            if e <= 1 {
                let slot = next.entry(*tuple).or_insert(0);
                *slot = (*slot).wrapping_add(c) & mask;
            } else {
                for j in 1..=e {
                    let s_coeff = stirling[usize::from(e)][usize::from(j)];
                    if s_coeff == 0 {
                        continue;
                    }
                    let new_tuple: MonomialKey = tuple.with_exponent(var, j);
                    let slot = next.entry(new_tuple).or_insert(0);
                    let add = c.wrapping_mul(s_coeff) & mask;
                    *slot = (*slot).wrapping_add(add) & mask;
                }
            }
        }
        next.retain(|_, &mut v| v != 0);
        current = next;
    }
    current
}

/// Monomial-basis → factorial-basis via `S₂(n, k)`.
#[must_use]
pub fn to_factorial_basis(terms: &CoeffMap, num_vars: u8, bitwidth: u32) -> CoeffMap {
    transform_basis(terms, num_vars, bitwidth, &Direction::ToFactorial)
}

/// Factorial-basis → monomial-basis via signed `s₁(n, k)`.
#[must_use]
pub fn to_monomial_basis(coeffs: &CoeffMap, num_vars: u8, bitwidth: u32) -> CoeffMap {
    transform_basis(coeffs, num_vars, bitwidth, &Direction::ToMonomial)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ahash::RandomState;

    fn coeffs_from(entries: &[(&[u8], u64)]) -> CoeffMap {
        let mut m = CoeffMap::with_hasher(RandomState::with_seeds(1, 2, 3, 4));
        for &(exps, c) in entries {
            m.insert(MonomialKey::from_exponents(exps, exps.len() as u8), c);
        }
        m
    }

    #[test]
    fn degree_one_is_identity() {
        // x + 2y under either transform stays untouched.
        let input = coeffs_from(&[(&[1, 0], 1), (&[0, 1], 2)]);
        let out_fact = to_factorial_basis(&input, 2, 64);
        let out_mono = to_monomial_basis(&input, 2, 64);
        assert_eq!(out_fact, input);
        assert_eq!(out_mono, input);
    }

    #[test]
    fn round_trip_preserves_coeffs() {
        // 3x^2 + 5xy + 7y^3
        let input = coeffs_from(&[(&[2, 0], 3), (&[1, 1], 5), (&[0, 3], 7)]);
        let factorial = to_factorial_basis(&input, 2, 64);
        let back = to_monomial_basis(&factorial, 2, 64);
        assert_eq!(back, input);
    }

    #[test]
    fn degree_two_single_var_matches_hand_computation() {
        // x^2 in monomial basis becomes x^(1) + x^(2) in factorial basis.
        // S₂(2, 1) = 1, S₂(2, 2) = 1 — so coefficient 1 at exponent 2 maps
        // to { (1): 1, (2): 1 }.
        let input = coeffs_from(&[(&[2], 1)]);
        let out = to_factorial_basis(&input, 1, 64);
        let exp1 = MonomialKey::from_exponents(&[1], 1);
        let exp2 = MonomialKey::from_exponents(&[2], 1);
        assert_eq!(out.get(&exp1), Some(&1));
        assert_eq!(out.get(&exp2), Some(&1));
    }
}
