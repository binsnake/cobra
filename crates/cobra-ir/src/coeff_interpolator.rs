//! Change-of-basis interpolation from a raw signature vector into `CoB`
//! (AND-monomial) coefficients.
//!
//! For an input signature of length `2^n` where entry `i` is the value
//! at the `{0, 1}^n` assignment whose bits read the truth table of
//! `i`, the output at index `i` is the coefficient of the monomial
//! `∏_{k ∈ bits(i)} x_k` in the polynomial's AND-basis expansion.
//!
//! The kernel is a single in-place Möbius butterfly: for each variable
//! `v`, subtract the `i & ~(1<<v)` entry from the `i | (1<<v)` entry —
//! isolating that variable's contribution. One pass per variable;
//! `O(n · 2^n)` total work.

use crate::core::arith::{bitmask, mod_sub};

/// In-place interpolation. Overwrites `sig` with the `CoB` coefficient
/// vector. `num_vars` must satisfy `sig.len() >= 1 << num_vars`.
pub fn interpolate_coefficients_in_place(sig: &mut [u64], num_vars: u32, bitwidth: u32) {
    let n = 1usize << num_vars;
    assert!(
        sig.len() >= n,
        "signature length {} shorter than 2^num_vars = {}",
        sig.len(),
        n
    );
    let mask = bitmask(bitwidth);
    for var in 0..num_vars {
        let half = 1usize << var;
        let block = half << 1;
        for base in (0..n).step_by(block) {
            for i in base..base + half {
                sig[i + half] = mod_sub(sig[i + half], sig[i], bitwidth) & mask;
            }
        }
    }
}

/// Owning wrapper that takes a signature by value, interpolates, and
/// returns the coefficient vector.
#[must_use]
pub fn interpolate_coefficients(mut sig: Vec<u64>, num_vars: u32, bitwidth: u32) -> Vec<u64> {
    interpolate_coefficients_in_place(&mut sig, num_vars, bitwidth);
    sig
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_function_gives_single_coefficient() {
        // f = 7 — sig is all 7s across 4 entries.
        let coeffs = interpolate_coefficients(vec![7, 7, 7, 7], 2, 64);
        // Only the constant term (index 0) has a nonzero coefficient.
        assert_eq!(coeffs, vec![7, 0, 0, 0]);
    }

    #[test]
    fn linear_function_recovers_slopes() {
        // f(x, y) = 3*x + 5*y. sig = [0, 3, 5, 8].
        let coeffs = interpolate_coefficients(vec![0, 3, 5, 8], 2, 64);
        // Constant 0, x=3, y=5, x·y=0.
        assert_eq!(coeffs, vec![0, 3, 5, 0]);
    }

    #[test]
    fn interaction_term_is_recovered() {
        // f(x, y) = 1 + x + y + x·y. sig at (0,0)=1, (1,0)=2, (0,1)=2, (1,1)=4.
        let coeffs = interpolate_coefficients(vec![1, 2, 2, 4], 2, 64);
        assert_eq!(coeffs, vec![1, 1, 1, 1]);
    }

    #[test]
    fn three_var_affine_recovers() {
        // f(x, y, z) = 2 + 3*x - y + 7*x*z.
        // Evaluate at all 8 points.
        fn f(x: u64, y: u64, z: u64) -> u64 {
            2u64.wrapping_add(3u64.wrapping_mul(x))
                .wrapping_sub(y)
                .wrapping_add(7u64.wrapping_mul(x).wrapping_mul(z))
        }
        let sig: Vec<u64> = (0..8u64)
            .map(|i| f(i & 1, (i >> 1) & 1, (i >> 2) & 1))
            .collect();
        let coeffs = interpolate_coefficients(sig, 3, 64);
        // Layout: bit0=x, bit1=y, bit2=z. Monomials:
        // 000=const=2, 001=x=3, 010=y=-1, 011=xy=0, 100=z=0, 101=xz=7,
        // 110=yz=0, 111=xyz=0.
        assert_eq!(coeffs[0], 2);
        assert_eq!(coeffs[1], 3);
        assert_eq!(coeffs[2], u64::MAX); // -1 under 2's complement
        assert_eq!(coeffs[3], 0);
        assert_eq!(coeffs[4], 0);
        assert_eq!(coeffs[5], 7);
        assert_eq!(coeffs[6], 0);
        assert_eq!(coeffs[7], 0);
    }

    #[test]
    fn in_place_matches_owning_wrapper() {
        let sig = vec![4, 9, 1, 2, 7, 5, 0, 3];
        let mut a = sig.clone();
        interpolate_coefficients_in_place(&mut a, 3, 32);
        let b = interpolate_coefficients(sig, 3, 32);
        assert_eq!(a, b);
    }

    #[test]
    fn narrow_bitwidth_wraps_correctly() {
        // 8-bit arithmetic. f(x) = 200 + 100*x → sig at x=0 is 200,
        // at x=1 is 300 mod 256 = 44. Coefficients:
        // c0 = 200, c1 = (44 - 200) mod 256 = 100.
        let coeffs = interpolate_coefficients(vec![200, 44], 1, 8);
        assert_eq!(coeffs, vec![200, 100]);
    }

    #[test]
    fn butterfly_matches_naive_subset_mobius_transform() {
        fn next(state: &mut u64) -> u64 {
            *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = *state;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        let mut state = 0x0000_000C_0B7A_1234u64;
        for num_vars in [0u32, 1, 2, 3, 4, 5, 6] {
            for bitwidth in [1u32, 8, 16, 32, 64] {
                let mask = bitmask(bitwidth);
                let len = 1usize << num_vars;
                let sig: Vec<u64> = (0..len).map(|_| next(&mut state) & mask).collect();

                let mut expected = vec![0u64; len];
                for (i, expected_value) in expected.iter_mut().enumerate() {
                    let mut j = i;
                    loop {
                        let mut term = sig[j] & mask;
                        if (i.count_ones() - j.count_ones()) & 1 != 0 {
                            term = term.wrapping_neg() & mask;
                        }
                        *expected_value = expected_value.wrapping_add(term) & mask;
                        if j == 0 {
                            break;
                        }
                        j = (j - 1) & i;
                    }
                }

                assert_eq!(
                    interpolate_coefficients(sig, num_vars, bitwidth),
                    expected,
                    "num_vars={num_vars}, bitwidth={bitwidth}"
                );
            }
        }
    }
}
