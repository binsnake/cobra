//! Number-theory helpers for polynomial normalization.
//!
//! Ported from `include/cobra/core/MathUtils.h`. All routines operate on
//! `uint64_t` modulo `2^bitwidth`.

use cobra_core::arith::bitmask;

/// Number of factors of 2 in `k!` (Legendre's formula for prime 2).
/// Closed form: `k - popcount(k)`.
#[inline]
#[must_use]
pub const fn twos_in_factorial(k: u32) -> u32 {
    k - k.count_ones()
}

/// Smallest `d` such that `twos_in_factorial(d) >= bitwidth`.
/// Concrete values: `8 → 10`, `16 → 18`, `32 → 34`, `64 → 66`.
#[must_use]
pub fn degree_cap(bitwidth: u32) -> u32 {
    let mut d: u32 = 0;
    while twos_in_factorial(d) < bitwidth {
        d += 1;
    }
    d
}

/// Odd part of `k!` modulo `2^bitwidth` — i.e. `k! / 2^twos_in_factorial(k)`
/// reduced modulo `2^bitwidth`. Computed by multiplying the odd residues of
/// `1..=k`.
#[must_use]
pub fn odd_part_factorial(k: u32, bitwidth: u32) -> u64 {
    let mask = bitmask(bitwidth);
    let mut result: u64 = 1;
    for i in 1..=k {
        let mut x = i;
        while x & 1 == 0 {
            x >>= 1;
        }
        result = result.wrapping_mul(u64::from(x)) & mask;
    }
    result
}

/// Modular inverse of an odd `x` modulo `2^bits`. Uses Hensel lifting:
/// `x*x == 1 (mod 8)` for any odd `x`, giving 3 correct bits to start;
/// each step doubles the number of correct bits.
#[must_use]
pub fn mod_inverse_odd(x: u64, bits: u32) -> u64 {
    assert!(bits >= 1, "bits must be >= 1");
    assert!(x & 1 == 1, "x must be odd");
    let mod_mask: u64 = if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let mut inv = x & mod_mask;
    let mut b: u32 = 3;
    while b < bits {
        let two_minus_xi = 2u64.wrapping_sub(x.wrapping_mul(inv));
        inv = inv.wrapping_mul(two_minus_xi) & mod_mask;
        b = b.wrapping_mul(2);
    }
    inv & mod_mask
}

/// Stirling numbers of the second kind `S(n, k)` modulo `2^bitwidth`, tabled
/// up to degree `max_degree`. Indexed as `table[n][k]`, `0..=max_degree`.
/// Recurrence: `S(n, k) = k * S(n-1, k) + S(n-1, k-1)`.
#[must_use]
pub fn build_stirling_second_kind(max_degree: u8, bitwidth: u32) -> Vec<Vec<u64>> {
    let mask = bitmask(bitwidth);
    let n = usize::from(max_degree) + 1;
    let mut s = vec![vec![0u64; n]; n];
    s[0][0] = 1;
    for i in 1..n {
        for j in 1..=i {
            let k = j as u64;
            s[i][j] = (k.wrapping_mul(s[i - 1][j]).wrapping_add(s[i - 1][j - 1])) & mask;
        }
    }
    s
}

/// Signed Stirling numbers of the first kind `s(n, k)` modulo `2^bitwidth`.
/// Recurrence: `s(n, k) = -(n-1) * s(n-1, k) + s(n-1, k-1)`.
#[must_use]
pub fn build_stirling_first_kind(max_degree: u8, bitwidth: u32) -> Vec<Vec<u64>> {
    let mask = bitmask(bitwidth);
    let n = usize::from(max_degree) + 1;
    let mut s = vec![vec![0u64; n]; n];
    s[0][0] = 1;
    for i in 1..n {
        for j in 1..=i {
            let neg_nm1 = 0u64.wrapping_sub(i as u64 - 1) & mask;
            s[i][j] = (neg_nm1
                .wrapping_mul(s[i - 1][j])
                .wrapping_add(s[i - 1][j - 1]))
                & mask;
        }
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn twos_in_factorial_matches_formula() {
        // Reference values (k - popcount(k)):
        //   0! = 1,  0
        //   1! = 1,  0
        //   2! = 2,  1
        //   3! = 6,  1
        //   4! = 24, 3
        //   5! = 120, 3
        //   6! = 720, 4
        //   7! = 5040, 4
        //   8! = 40320, 7
        assert_eq!(twos_in_factorial(0), 0);
        assert_eq!(twos_in_factorial(1), 0);
        assert_eq!(twos_in_factorial(2), 1);
        assert_eq!(twos_in_factorial(3), 1);
        assert_eq!(twos_in_factorial(4), 3);
        assert_eq!(twos_in_factorial(5), 3);
        assert_eq!(twos_in_factorial(6), 4);
        assert_eq!(twos_in_factorial(7), 4);
        assert_eq!(twos_in_factorial(8), 7);
    }

    #[test]
    fn degree_cap_matches_cpp_reference() {
        // Values lifted directly from the C++ comment.
        assert_eq!(degree_cap(8), 10);
        assert_eq!(degree_cap(16), 18);
        assert_eq!(degree_cap(32), 34);
        assert_eq!(degree_cap(64), 66);
    }

    #[test]
    fn odd_part_factorial_sanity() {
        // 5! = 120 = 2^3 * 15. Odd part = 15.
        assert_eq!(odd_part_factorial(5, 64), 15);
        // 7! = 5040 = 2^4 * 315. Odd part = 315.
        assert_eq!(odd_part_factorial(7, 64), 315);
        // 0! = 1, odd part is 1.
        assert_eq!(odd_part_factorial(0, 64), 1);
    }

    #[test]
    fn mod_inverse_odd_roundtrips() {
        for &x in &[1u64, 3, 5, 7, 17, 0x00AB_CDEFu64 | 1] {
            for &bits in &[8u32, 16, 32, 64] {
                let inv = mod_inverse_odd(x, bits);
                let mask = bitmask(bits);
                let prod = x.wrapping_mul(inv) & mask;
                assert_eq!(prod, 1 & mask, "x={x} bits={bits}");
            }
        }
    }

    #[test]
    fn stirling_second_kind_reference() {
        // Known values:
        //   S(0,0) = 1
        //   S(1,1) = 1
        //   S(4,2) = 7
        //   S(5,3) = 25
        //   S(6,3) = 90
        let t = build_stirling_second_kind(6, 64);
        assert_eq!(t[0][0], 1);
        assert_eq!(t[1][1], 1);
        assert_eq!(t[4][2], 7);
        assert_eq!(t[5][3], 25);
        assert_eq!(t[6][3], 90);
    }

    #[test]
    fn stirling_first_kind_reference() {
        // Signed Stirling firsts (mod 2^64 — negatives show as wraps):
        //   s(0,0) = 1
        //   s(3,1) = 2
        //   s(3,2) = -3
        //   s(4,1) = -6
        //   s(4,2) = 11
        let t = build_stirling_first_kind(4, 64);
        assert_eq!(t[0][0], 1);
        assert_eq!(t[3][1], 2);
        assert_eq!(t[3][2], 0u64.wrapping_sub(3));
        assert_eq!(t[4][1], 0u64.wrapping_sub(6));
        assert_eq!(t[4][2], 11);
    }
}
