//! Packed Möbius transform for computing the Algebraic Normal Form of a
//! Boolean-valued signature vector.
//!
//! For a signature of length `2^n` (interpreted mod 2), the output
//! `PackedAnf` has bit `m` set iff the monomial
//! `∏_{i ∈ bits(m)} x_i` appears in the ANF. Bit `0` is the constant
//! term.
//!
//! The butterfly runs in two phases:
//! 1. Intra-word: for each variable index `i` in `0..min(n, 6)`, XOR
//!    the even-indexed bits of every word into the matching odd
//!    positions using a precomputed GF(2) mask.
//! 2. Inter-word: for each variable index `i` in `6..n`, XOR whole
//!    words at stride `2^(i - 6)`.

use crate::packed_anf::PackedAnf;

const INTRA_MASKS: [u64; 6] = [
    0x5555_5555_5555_5555, // step 1
    0x3333_3333_3333_3333, // step 2
    0x0F0F_0F0F_0F0F_0F0F, // step 4
    0x00FF_00FF_00FF_00FF, // step 8
    0x0000_FFFF_0000_FFFF, // step 16
    0x0000_0000_FFFF_FFFF, // step 32
];

/// Compute ANF coefficients from a Boolean-valued signature vector.
#[must_use]
pub fn compute_anf(sig: &[u64], num_vars: u32) -> PackedAnf {
    let n = 1usize << num_vars;
    assert!(
        sig.len() >= n,
        "signature length {} shorter than 2^num_vars = {}",
        sig.len(),
        n
    );

    let mut anf = PackedAnf::new(n);
    for (i, &v) in sig.iter().take(n).enumerate() {
        if (v & 1) != 0 {
            anf.set(i);
        }
    }

    let intra = num_vars.min(6);
    for i in 0..intra {
        let shift = 1u64 << i;
        let mask = INTRA_MASKS[i as usize];
        for w in 0..anf.word_count() {
            let word = anf.word(w);
            *anf.word_mut(w) = word ^ ((word & mask) << shift);
        }
    }

    for i in 6..num_vars {
        let word_step = 1usize << (i - 6);
        let mut w = word_step;
        while w < anf.word_count() {
            for k in 0..word_step {
                let src = anf.word(w - word_step + k);
                let dst = anf.word(w + k) ^ src;
                *anf.word_mut(w + k) = dst;
            }
            w += 2 * word_step;
        }
    }

    anf
}

#[cfg(test)]
mod tests {
    use super::*;

    fn collect_set_bits(anf: &PackedAnf) -> Vec<usize> {
        (0..anf.len()).filter(|&i| anf.get(i) != 0).collect()
    }

    #[test]
    fn zero_signature_yields_empty_anf() {
        let anf = compute_anf(&[0, 0, 0, 0], 2);
        assert!(collect_set_bits(&anf).is_empty());
    }

    #[test]
    fn constant_one_yields_bit_zero() {
        // sig == all 1 → ANF is just the constant term.
        let anf = compute_anf(&[1, 1, 1, 1], 2);
        assert_eq!(collect_set_bits(&anf), vec![0]);
    }

    #[test]
    fn xor_sig_recovers_two_linear_monomials() {
        // f(x, y) = x ^ y — sig [0, 1, 1, 0]. ANF: monomials {x, y}.
        let anf = compute_anf(&[0, 1, 1, 0], 2);
        // Bit 1 = x, bit 2 = y.
        assert_eq!(collect_set_bits(&anf), vec![1, 2]);
    }

    #[test]
    fn and_sig_recovers_single_bilinear_monomial() {
        // f(x, y) = x & y — sig [0, 0, 0, 1]. ANF: {xy}.
        let anf = compute_anf(&[0, 0, 0, 1], 2);
        assert_eq!(collect_set_bits(&anf), vec![3]);
    }

    #[test]
    fn or_sig_recovers_three_monomials() {
        // f(x, y) = x | y — sig [0, 1, 1, 1]. ANF: x ^ y ^ xy.
        let anf = compute_anf(&[0, 1, 1, 1], 2);
        assert_eq!(collect_set_bits(&anf), vec![1, 2, 3]);
    }

    #[test]
    fn three_var_all_ones_minus_constant() {
        // f ≡ 1 across 8 entries — ANF has only the constant bit set.
        let anf = compute_anf(&[1, 1, 1, 1, 1, 1, 1, 1], 3);
        assert_eq!(collect_set_bits(&anf), vec![0]);
    }

    #[test]
    fn seven_var_exercises_inter_word_stage() {
        // Sig is all zero except index 127 (which is the AND of all 7 vars).
        // ANF should have exactly one set bit at position 127.
        let n = 1 << 7;
        let mut sig = vec![0u64; n];
        sig[n - 1] = 1;
        let anf = compute_anf(&sig, 7);
        assert_eq!(collect_set_bits(&anf), vec![n - 1]);
    }

    #[test]
    fn involution_property_holds() {
        // ANF is an involution over GF(2) — applying it twice recovers the input.
        let sig = vec![0, 1, 0, 1, 1, 0, 1, 0];
        let anf = compute_anf(&sig, 3);
        // Convert ANF bits back into a length-8 u64 signature and re-transform.
        let recovered_sig: Vec<u64> = (0..8).map(|i| u64::from(anf.get(i))).collect();
        let twice = compute_anf(&recovered_sig, 3);
        for (i, &s) in sig.iter().enumerate() {
            assert_eq!(u64::from(twice.get(i)), s & 1);
        }
    }
}
