//! `PolyIR` — multivariate polynomial keyed by `MonomialKey`.
//!
//! `NormalizedPoly` hold a map from `MonomialKey` to `Coeff` (`u64`); the
//! under `ahash::RandomState` for fast deterministic hashing.

use std::collections::HashMap;

use ahash::RandomState;

use crate::mono::MonomialKey;

/// Coefficient type: always `u64`, interpreted modulo `2^bitwidth`.
pub type Coeff = u64;

/// Coefficient map. Keeps the hasher explicit so we don't accidentally pick
/// up std's per-process-randomized `RandomState`.
pub type CoeffMap = HashMap<MonomialKey, Coeff, RandomState>;

/// Raw polynomial. No invariants beyond `2 <= bitwidth <= 64`; callers are
/// responsible for ensuring that coefficients are already reduced modulo
/// `2^bitwidth` if they want the canonical form.
#[derive(Clone, Debug, Default)]
pub struct PolyIR {
    pub num_vars: u8,
    /// Required range: `2..=64`.
    pub bitwidth: u32,
    pub terms: CoeffMap,
}

impl PolyIR {
    #[must_use]
    pub fn empty(num_vars: u8, bitwidth: u32) -> Self {
        Self {
            num_vars,
            bitwidth,
            terms: CoeffMap::with_hasher(RandomState::new()),
        }
    }
}

/// Normalized polynomial — stores the factorial-basis coefficients of the
/// underlying multivariate power series. Invariants are checked by
/// [`NormalizedPoly::is_valid`].
#[derive(Clone, Debug, Default)]
pub struct NormalizedPoly {
    pub num_vars: u8,
    /// Required range: `2..=64`.
    pub bitwidth: u32,
    pub coeffs: CoeffMap,
}

impl NormalizedPoly {
    #[must_use]
    pub fn empty(num_vars: u8, bitwidth: u32) -> Self {
        Self {
            num_vars,
            bitwidth,
            coeffs: CoeffMap::with_hasher(RandomState::new()),
        }
    }

    /// must fit in `bitwidth - v2_factorial_weight(key)` bits.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        if self.bitwidth < 2 || self.bitwidth > 64 {
            return false;
        }
        for (tuple, &c) in &self.coeffs {
            if c == 0 {
                return false;
            }
            let q = tuple.v2_factorial_weight(self.num_vars);
            if q >= self.bitwidth {
                return false;
            }
            let bound_bits = self.bitwidth - q;
            if bound_bits < 64 && c >= 1u64 << bound_bits {
                return false;
            }
        }
        true
    }
}

/// Compare two polynomials for equality by field. Two `CoeffMap`s are equal
/// iff they have the same (key, value) set — order-independent.
impl PartialEq for NormalizedPoly {
    fn eq(&self, other: &Self) -> bool {
        self.num_vars == other.num_vars
            && self.bitwidth == other.bitwidth
            && self.coeffs == other.coeffs
    }
}

impl Eq for NormalizedPoly {}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(exps: &[u8]) -> MonomialKey {
        MonomialKey::from_exponents(exps, exps.len() as u8)
    }

    #[test]
    fn empty_poly_is_valid_default_except_bitwidth() {
        // bitwidth 0 is invalid by the 2..=64 rule.
        let p = NormalizedPoly::default();
        assert!(!p.is_valid());
        // A default-initialised poly with a sane bitwidth and no terms is valid.
        let p = NormalizedPoly::empty(2, 8);
        assert!(p.is_valid());
    }

    #[test]
    fn zero_coefficient_is_invalid() {
        let mut p = NormalizedPoly::empty(2, 8);
        p.coeffs.insert(key(&[1, 0]), 0);
        assert!(!p.is_valid());
    }

    #[test]
    fn coefficient_within_bound() {
        // bitwidth=8, key = [2] → v2_factorial_weight = 1, bound = 7 bits.
        // Coeff 0x7F is fine, 0x80 is not.
        let mut p = NormalizedPoly::empty(1, 8);
        p.coeffs.insert(key(&[2]), 0x7F);
        assert!(p.is_valid());
        p.coeffs.insert(key(&[2]), 0x80);
        assert!(!p.is_valid());
    }

    #[test]
    fn q_meeting_or_exceeding_bitwidth_is_invalid() {
        // At bitwidth=8, exponent 8 gives twos_in_factorial(8)=7, bound=1 bit.
        let mut p = NormalizedPoly::empty(1, 8);
        p.coeffs.insert(key(&[8]), 1);
        assert!(p.is_valid());
        // Exponent 16 gives twos_in_factorial(16)=15 ≥ 8, invalid.
        let mut p = NormalizedPoly::empty(1, 8);
        p.coeffs.insert(key(&[16]), 1);
        assert!(!p.is_valid());
    }

    #[test]
    fn equality_is_order_independent() {
        let mut a = NormalizedPoly::empty(2, 8);
        let mut b = NormalizedPoly::empty(2, 8);
        a.coeffs.insert(key(&[1, 0]), 3);
        a.coeffs.insert(key(&[0, 1]), 5);
        b.coeffs.insert(key(&[0, 1]), 5);
        b.coeffs.insert(key(&[1, 0]), 3);
        assert_eq!(a, b);
    }
}
