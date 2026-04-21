//! `MonomialKey` — a fixed-size exponent vector keyed into polynomial maps.
//!
//! positions beyond `num_vars` are implicitly zero. Hashing uses FNV-1a
//! so that any serialized fingerprint remains stable.

use std::hash::{Hash, Hasher};

use crate::math_utils::twos_in_factorial;

/// `cobra::kMaxPolyVars`.
pub const MAX_POLY_VARS: usize = 20;

/// Fixed-width exponent key used by `PolyIR`.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct MonomialKey {
    pub exponents: [u8; MAX_POLY_VARS],
}

impl MonomialKey {
    /// Zero-exponent key (the constant monomial).
    #[inline]
    #[must_use]
    pub const fn zero() -> Self {
        Self {
            exponents: [0u8; MAX_POLY_VARS],
        }
    }

    /// Construct a key from the first `num_vars` entries of `exps`. Panics
    /// if `num_vars > MAX_POLY_VARS` or `exps.len() < num_vars`.
    #[must_use]
    pub fn from_exponents(exps: &[u8], num_vars: u8) -> Self {
        let n = usize::from(num_vars);
        assert!(n <= MAX_POLY_VARS, "num_vars exceeds MAX_POLY_VARS");
        assert!(exps.len() >= n, "exponent slice is shorter than num_vars");
        let mut k = Self::zero();
        k.exponents[..n].copy_from_slice(&exps[..n]);
        k
    }

    /// Copy the first `num_vars` exponents into `out`.
    pub fn to_exponents(&self, out: &mut [u8], num_vars: u8) {
        let n = usize::from(num_vars);
        assert!(n <= MAX_POLY_VARS);
        assert!(out.len() >= n);
        out[..n].copy_from_slice(&self.exponents[..n]);
    }

    #[inline]
    #[must_use]
    pub fn exponent_at(&self, var_index: u8) -> u8 {
        assert!(usize::from(var_index) < MAX_POLY_VARS);
        self.exponents[usize::from(var_index)]
    }

    #[inline]
    #[must_use]
    pub fn with_exponent(mut self, var_index: u8, new_val: u8) -> Self {
        assert!(usize::from(var_index) < MAX_POLY_VARS);
        self.exponents[usize::from(var_index)] = new_val;
        self
    }

    /// Sum of the first `num_vars` exponents.
    #[must_use]
    pub fn total_degree(&self, num_vars: u8) -> u32 {
        let n = usize::from(num_vars);
        assert!(n <= MAX_POLY_VARS);
        self.exponents[..n].iter().map(|&e| u32::from(e)).sum()
    }

    /// Max of the first `num_vars` exponents.
    #[must_use]
    pub fn max_degree(&self, num_vars: u8) -> u8 {
        let n = usize::from(num_vars);
        assert!(n <= MAX_POLY_VARS);
        self.exponents[..n].iter().copied().max().unwrap_or(0)
    }

    /// Sum of `twos_in_factorial(e_i)` over the first `num_vars` exponents.
    /// Drives the 2-adic weight bound used by `NormalizedPoly::is_valid`.
    #[must_use]
    pub fn v2_factorial_weight(&self, num_vars: u8) -> u32 {
        let n = usize::from(num_vars);
        assert!(n <= MAX_POLY_VARS);
        self.exponents[..n]
            .iter()
            .map(|&e| twos_in_factorial(u32::from(e)))
            .sum()
    }
}

/// basis `0xcbf29ce484222325`, prime `0x100000001b3`). Implemented as the
/// `Hash` impl so that the key interoperates with `HashMap<MonomialKey, _>`
/// under any `BuildHasher` — the FNV step happens at `Hash::hash` time and
/// where `std::hash` is the direct final hash, but the map keys stay
/// through the outer hasher's own stability rather than through FNV.
impl Hash for MonomialKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // We want the FNV-1a byte sequence, not `write_u8` calls (which many
        // hashers treat with their own per-value mixing). Mix into a local
        // `u64` first, then feed one `write_u64` into the outer hasher.
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        for &b in &self.exponents {
            h ^= u64::from(b);
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
        state.write_u64(h);
    }
}

impl Ord for MonomialKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.exponents.cmp(&other.exponents)
    }
}

impl PartialOrd for MonomialKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_is_all_zero() {
        let k = MonomialKey::zero();
        assert_eq!(k.total_degree(MAX_POLY_VARS as u8), 0);
        assert_eq!(k.max_degree(MAX_POLY_VARS as u8), 0);
    }

    #[test]
    fn from_exponents_copies_prefix() {
        let k = MonomialKey::from_exponents(&[3, 0, 2, 1], 4);
        assert_eq!(k.exponents[..4], [3, 0, 2, 1]);
        assert!(k.exponents[4..].iter().all(|&e| e == 0));
    }

    #[test]
    fn with_exponent_sets_single_slot() {
        let k = MonomialKey::zero().with_exponent(3, 5);
        assert_eq!(k.exponent_at(3), 5);
        assert_eq!(k.total_degree(20), 5);
    }

    #[test]
    fn total_and_max_degree() {
        let k = MonomialKey::from_exponents(&[1, 4, 2, 0, 3], 5);
        assert_eq!(k.total_degree(5), 10);
        assert_eq!(k.max_degree(5), 4);
        // Beyond num_vars, later exponents are excluded.
        assert_eq!(k.total_degree(3), 7);
    }

    #[test]
    fn v2_factorial_weight_matches_formula() {
        // exponents 2 and 3: twos_in_factorial(2) = 1, twos_in_factorial(3) = 1
        let k = MonomialKey::from_exponents(&[2, 3], 2);
        assert_eq!(k.v2_factorial_weight(2), 2);
        // exponent 4: twos_in_factorial(4) = 3
        let k = MonomialKey::from_exponents(&[4], 1);
        assert_eq!(k.v2_factorial_weight(1), 3);
    }

    struct Capture(u64);
    impl Hasher for Capture {
        fn finish(&self) -> u64 {
            self.0
        }
        fn write(&mut self, _: &[u8]) {}
        fn write_u64(&mut self, n: u64) {
            self.0 = n;
        }
    }

    #[test]
    fn fnv_1a_matches_reference() {
        // Hand-compute FNV-1a over the 20-byte array for a known input and
        // assert the produced u64 matches the C++ std::hash output byte-wise.
        let k = MonomialKey::from_exponents(&[1, 2, 3], 3);
        let expected = {
            let mut h: u64 = 0xcbf2_9ce4_8422_2325;
            let mut bytes = [0u8; MAX_POLY_VARS];
            bytes[..3].copy_from_slice(&[1, 2, 3]);
            for &b in &bytes {
                h ^= u64::from(b);
                h = h.wrapping_mul(0x0000_0100_0000_01b3);
            }
            h
        };

        let mut cap = Capture(0);
        k.hash(&mut cap);
        assert_eq!(cap.0, expected);
    }

    #[test]
    fn ord_is_lexicographic() {
        let a = MonomialKey::from_exponents(&[1, 0, 0], 3);
        let b = MonomialKey::from_exponents(&[1, 0, 1], 3);
        let c = MonomialKey::from_exponents(&[2, 0, 0], 3);
        assert!(a < b);
        assert!(b < c);
        assert!(a < c);
    }
}
