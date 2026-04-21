//! Monomial-basis [`PolyIR`] → factorial-basis [`NormalizedPoly`].
//!
//! Two steps: apply [`to_factorial_basis`] per variable, then reduce
//! each coefficient modulo `2^(bitwidth - v2_factorial_weight(key))`.
//! Coefficients whose 2-adic weight exceeds the bitwidth drop out
//! (the monomial is in the null space).

use crate::basis_transform::to_factorial_basis;
use crate::poly::{NormalizedPoly, PolyIR};

/// Normalise a [`PolyIR`] into a [`NormalizedPoly`]. The output
/// coefficients are each reduced to their valid precision band.
#[must_use]
pub fn normalize_polynomial(poly: &PolyIR) -> NormalizedPoly {
    let n = poly.num_vars;
    let w = poly.bitwidth;

    let mut current = to_factorial_basis(&poly.terms, n, w);

    current.retain(|key, coeff| {
        let q = key.v2_factorial_weight(n);
        if q >= w {
            return false;
        }
        let bound_bits = w - q;
        if bound_bits < 64 {
            *coeff &= (1u64 << bound_bits) - 1;
        }
        *coeff != 0
    });

    NormalizedPoly {
        num_vars: n,
        bitwidth: w,
        coeffs: current,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mono::MonomialKey;
    use crate::poly::CoeffMap;
    use ahash::RandomState;

    #[test]
    fn linear_poly_is_unchanged() {
        let mut p = PolyIR::empty(2, 64);
        p.terms = CoeffMap::with_hasher(RandomState::with_seeds(1, 2, 3, 4));
        p.terms.insert(MonomialKey::from_exponents(&[1, 0], 2), 3);
        p.terms.insert(MonomialKey::from_exponents(&[0, 1], 2), 5);

        let normalized = normalize_polynomial(&p);
        assert_eq!(normalized.num_vars, 2);
        assert_eq!(normalized.bitwidth, 64);
        assert_eq!(normalized.coeffs.len(), 2);
    }

    #[test]
    fn quadratic_produces_factorial_basis() {
        // x^2 in monomial basis maps to x + x^(2) in factorial basis.
        let mut p = PolyIR::empty(1, 64);
        p.terms = CoeffMap::with_hasher(RandomState::with_seeds(1, 2, 3, 4));
        p.terms.insert(MonomialKey::from_exponents(&[2], 1), 1);

        let normalized = normalize_polynomial(&p);
        assert_eq!(normalized.coeffs.len(), 2);
        let k1 = MonomialKey::from_exponents(&[1], 1);
        let k2 = MonomialKey::from_exponents(&[2], 1);
        assert_eq!(normalized.coeffs.get(&k1), Some(&1));
        assert_eq!(normalized.coeffs.get(&k2), Some(&1));
    }
}
