//! Null-polynomial injection for generating equivalent polynomial variants.
//!
//! A factorial-basis coefficient at tuple `k` is semantically null modulo
//! `2^w` when it is a multiple of `2^(w - v2(k!))`. Converting such sampled
//! null terms back to monomial basis and adding them to a seed polynomial
//! preserves the seed's normalized form.

use ahash::RandomState;
use cobra_core::arith::bitmask;

use crate::basis_transform::to_monomial_basis;
use crate::mono::{MonomialKey, MAX_POLY_VARS};
use crate::poly::{CoeffMap, PolyIR};

/// Configuration for null-polynomial injection.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NullPolyConfig {
    /// Upper bound on sampled factorial-basis coordinates.
    pub num_terms: u32,
    /// Maximum exponent sampled per variable. Values below 2 have no
    /// non-trivial null-space contribution.
    pub max_degree: u8,
    /// Deterministic seed for reproducible variant generation.
    pub rng_seed: u64,
}

/// Add a deterministic null polynomial to `seed`.
///
/// The returned [`PolyIR`] is semantically equivalent to `seed` modulo
/// `2^seed.bitwidth`, and has the same normalized polynomial.
#[must_use]
pub fn add_null_polynomial(seed: &PolyIR, config: NullPolyConfig) -> PolyIR {
    assert!(
        (2..=64).contains(&seed.bitwidth),
        "seed bitwidth must be in 2..=64"
    );
    assert!(
        seed.num_vars > 0 && usize::from(seed.num_vars) <= MAX_POLY_VARS,
        "seed num_vars must be in 1..=MAX_POLY_VARS"
    );
    if config.max_degree < 2 || config.num_terms == 0 {
        return seed.clone();
    }

    let num_vars = seed.num_vars;
    let bitwidth = seed.bitwidth;
    let mask = bitmask(bitwidth);
    let mut rng = SplitMix64::new(config.rng_seed);
    let mut null_factorial = CoeffMap::with_hasher(RandomState::with_seeds(1, 2, 3, 4));

    for _ in 0..config.num_terms {
        let tuple = sample_tuple_with_positive_null_weight(&mut rng, num_vars, config.max_degree);
        let q = tuple.v2_factorial_weight(num_vars);

        let coeff = if q >= bitwidth {
            rng.gen_range_inclusive(1, mask)
        } else {
            let bound = 1u64 << (bitwidth - q);
            let max_mult = (1u64 << q) - 1;
            rng.gen_range_inclusive(1, max_mult).wrapping_mul(bound) & mask
        };

        let slot = null_factorial.entry(tuple).or_insert(0);
        *slot = slot.wrapping_add(coeff) & mask;
    }

    null_factorial.retain(|_, coeff| *coeff != 0);
    if null_factorial.is_empty() {
        return seed.clone();
    }

    let null_monomial = to_monomial_basis(&null_factorial, num_vars, bitwidth);
    let mut result = PolyIR {
        num_vars,
        bitwidth,
        terms: seed.terms.clone(),
    };

    for (tuple, coeff) in null_monomial {
        let slot = result.terms.entry(tuple).or_insert(0);
        *slot = slot.wrapping_add(coeff) & mask;
    }
    result.terms.retain(|_, coeff| *coeff != 0);
    result
}

/// Generate `count` deterministic equivalent variants of `seed`.
#[must_use]
pub fn generate_equivalent_variants(
    seed: &PolyIR,
    count: u32,
    config: NullPolyConfig,
) -> Vec<PolyIR> {
    let mut variants = Vec::with_capacity(count as usize);
    for i in 0..count {
        let mut variant_config = config;
        variant_config.rng_seed = splitmix64(config.rng_seed ^ u64::from(i));
        variants.push(add_null_polynomial(seed, variant_config));
    }
    variants
}

fn sample_tuple_with_positive_null_weight(
    rng: &mut SplitMix64,
    num_vars: u8,
    max_degree: u8,
) -> MonomialKey {
    let mut exps = [0u8; MAX_POLY_VARS];
    loop {
        for exp in exps.iter_mut().take(usize::from(num_vars)) {
            *exp = rng.gen_range_inclusive(0, u64::from(max_degree)) as u8;
        }
        let candidate = MonomialKey::from_exponents(&exps, num_vars);
        if candidate.v2_factorial_weight(num_vars) > 0 {
            return candidate;
        }
    }
}

fn splitmix64(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

#[derive(Clone, Debug)]
struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    const fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        let out = splitmix64(self.state);
        self.state = self.state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        out
    }

    fn gen_range_inclusive(&mut self, low: u64, high: u64) -> u64 {
        debug_assert!(low <= high);
        let span = high - low + 1;
        let zone = u64::MAX - (u64::MAX % span);
        loop {
            let value = self.next_u64();
            if value < zone {
                return low + (value % span);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mono::MonomialKey;
    use crate::poly_normalizer::normalize_polynomial;

    fn seed_poly() -> PolyIR {
        let mut seed = PolyIR::empty(2, 8);
        seed.terms
            .insert(MonomialKey::from_exponents(&[2, 0], 2), 3);
        seed.terms
            .insert(MonomialKey::from_exponents(&[1, 1], 2), 5);
        seed.terms
            .insert(MonomialKey::from_exponents(&[0, 1], 2), 7);
        seed
    }

    #[test]
    fn max_degree_below_two_returns_seed() {
        let seed = seed_poly();
        let result = add_null_polynomial(
            &seed,
            NullPolyConfig {
                num_terms: 10,
                max_degree: 1,
                rng_seed: 42,
            },
        );
        assert_eq!(result.terms, seed.terms);
    }

    #[test]
    fn add_null_preserves_normalization() {
        let seed = seed_poly();
        let result = add_null_polynomial(
            &seed,
            NullPolyConfig {
                num_terms: 20,
                max_degree: 3,
                rng_seed: 42,
            },
        );
        assert_eq!(normalize_polynomial(&result), normalize_polynomial(&seed));
    }

    #[test]
    fn deterministic_reproducibility() {
        let seed = seed_poly();
        let config = NullPolyConfig {
            num_terms: 20,
            max_degree: 3,
            rng_seed: 777,
        };
        let a = add_null_polynomial(&seed, config);
        let b = add_null_polynomial(&seed, config);
        assert_eq!(a.terms, b.terms);
    }

    #[test]
    fn generated_variants_preserve_normalization() {
        let seed = seed_poly();
        let variants = generate_equivalent_variants(
            &seed,
            5,
            NullPolyConfig {
                num_terms: 10,
                max_degree: 2,
                rng_seed: 12345,
            },
        );

        assert_eq!(variants.len(), 5);
        for variant in variants {
            assert_eq!(normalize_polynomial(&variant), normalize_polynomial(&seed));
        }
    }
}
