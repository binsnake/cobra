//! Modular u64 arithmetic at a configurable bitwidth (1..=64).
//!
//! are wrapping — any overflow is masked back into the `bitwidth`-wide modulus.

/// Low-`bitwidth` all-ones mask. `bitwidth == 0` returns 0; `bitwidth >= 64`
/// returns `u64::MAX`.
#[inline]
#[must_use]
pub const fn bitmask(bitwidth: u32) -> u64 {
    if bitwidth >= 64 {
        u64::MAX
    } else if bitwidth == 0 {
        0
    } else {
        (1u64 << bitwidth) - 1
    }
}

/// Returns true when `bitwidth` is in `CoBRA`'s supported public range.
#[inline]
#[must_use]
pub const fn is_valid_bitwidth(bitwidth: u32) -> bool {
    bitwidth >= 1 && bitwidth <= 64
}

/// Mask with only the sign bit set. `bitwidth == 0` returns 0; `bitwidth >= 64`
/// returns the high bit of `u64`.
#[inline]
#[must_use]
pub const fn sign_bit_mask(bitwidth: u32) -> u64 {
    if bitwidth == 0 {
        0
    } else if bitwidth >= 64 {
        1u64 << 63
    } else {
        1u64 << (bitwidth - 1)
    }
}

#[inline]
#[must_use]
pub const fn mod_add(a: u64, b: u64, bitwidth: u32) -> u64 {
    a.wrapping_add(b) & bitmask(bitwidth)
}

#[inline]
#[must_use]
pub const fn mod_sub(a: u64, b: u64, bitwidth: u32) -> u64 {
    a.wrapping_sub(b) & bitmask(bitwidth)
}

#[inline]
#[must_use]
pub const fn mod_mul(a: u64, b: u64, bitwidth: u32) -> u64 {
    a.wrapping_mul(b) & bitmask(bitwidth)
}

#[inline]
#[must_use]
pub const fn mod_neg(a: u64, bitwidth: u32) -> u64 {
    mod_sub(0, a, bitwidth)
}

#[inline]
#[must_use]
pub const fn mod_not(a: u64, bitwidth: u32) -> u64 {
    (!a) & bitmask(bitwidth)
}

#[inline]
#[must_use]
pub const fn mod_shr(a: u64, k: u64, bitwidth: u32) -> u64 {
    if k >= 64 {
        return 0;
    }
    (a >> k) & bitmask(bitwidth)
}

/// Zero-extend `v` to width `to`. Zero-extension never adds set bits, so this
/// is just a mask of the (already-narrow) value to the result width.
#[inline]
#[must_use]
pub const fn zext(v: u64, to: u32) -> u64 {
    v & bitmask(to)
}

/// Sign-extend `v` (interpreted as a `from`-bit two's-complement value) to
/// width `to`, then mask to `to`. Widening (`to >= from`) replicates the sign
/// bit; narrowing (`to < from`) degenerates to a truncation to `to`.
#[inline]
#[must_use]
pub const fn sext(v: u64, from: u32, to: u32) -> u64 {
    let from_mask = bitmask(from);
    let low = v & from_mask;
    if from == 0 || to <= from {
        // No source sign bit to replicate, or we're truncating: just mask.
        return low & bitmask(to);
    }
    let sign = sign_bit_mask(from);
    if low & sign != 0 {
        // Set every bit from `from` up to `to` (the extension region).
        let ext = bitmask(to) & !from_mask;
        (low | ext) & bitmask(to)
    } else {
        low & bitmask(to)
    }
}

/// Truncate `v` to its low `to` bits.
#[inline]
#[must_use]
pub const fn trunc(v: u64, to: u32) -> u64 {
    v & bitmask(to)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bitmask_edges() {
        assert_eq!(bitmask(0), 0);
        assert_eq!(bitmask(1), 0x1);
        assert_eq!(bitmask(8), 0xFF);
        assert_eq!(bitmask(16), 0xFFFF);
        assert_eq!(bitmask(63), 0x7FFF_FFFF_FFFF_FFFF);
        assert_eq!(bitmask(64), u64::MAX);
        assert_eq!(bitmask(65), u64::MAX);
    }

    #[test]
    fn bitwidth_range_matches_public_contract() {
        assert!(!is_valid_bitwidth(0));
        assert!(is_valid_bitwidth(1));
        assert!(is_valid_bitwidth(64));
        assert!(!is_valid_bitwidth(65));
    }

    #[test]
    fn sign_bit_mask_edges() {
        assert_eq!(sign_bit_mask(0), 0);
        assert_eq!(sign_bit_mask(1), 0x1);
        assert_eq!(sign_bit_mask(8), 0x80);
        assert_eq!(sign_bit_mask(63), 1u64 << 62);
        assert_eq!(sign_bit_mask(64), 1u64 << 63);
        assert_eq!(sign_bit_mask(65), 1u64 << 63);
    }

    #[test]
    fn add_wraps() {
        assert_eq!(mod_add(u64::MAX, 1, 64), 0);
        assert_eq!(mod_add(0xFF, 1, 8), 0);
        assert_eq!(mod_add(0x80, 0x80, 8), 0);
        assert_eq!(mod_add(3, 5, 16), 8);
    }

    #[test]
    fn sub_wraps() {
        assert_eq!(mod_sub(0, 1, 64), u64::MAX);
        assert_eq!(mod_sub(0, 1, 8), 0xFF);
        assert_eq!(mod_sub(5, 3, 16), 2);
    }

    #[test]
    fn mul_wraps() {
        assert_eq!(mod_mul(0xFF, 0xFF, 8), (0xFFu64.wrapping_mul(0xFF)) & 0xFF);
        assert_eq!(mod_mul(u64::MAX, 2, 64), u64::MAX.wrapping_mul(2));
        assert_eq!(mod_mul(3, 4, 32), 12);
    }

    #[test]
    fn neg_and_not() {
        assert_eq!(mod_neg(1, 8), 0xFF);
        assert_eq!(mod_neg(0, 64), 0);
        assert_eq!(mod_not(0, 8), 0xFF);
        assert_eq!(mod_not(0xF0, 8), 0x0F);
    }

    #[test]
    fn shr_saturates_past_width() {
        assert_eq!(mod_shr(0xFF, 4, 8), 0x0F);
        assert_eq!(mod_shr(0xFF, 8, 8), 0);
        assert_eq!(mod_shr(u64::MAX, 64, 64), 0);
        assert_eq!(mod_shr(u64::MAX, 100, 64), 0);
    }

    #[test]
    fn zext_is_a_widen_mask() {
        // 0xAB zero-extended to 16 bits stays 0x00AB.
        assert_eq!(zext(0xAB, 16), 0x00AB);
        // Already-wide input is masked to the target width.
        assert_eq!(zext(0x1_2345, 8), 0x45);
        assert_eq!(zext(0x1, 1), 0x1);
        assert_eq!(zext(u64::MAX, 64), u64::MAX);
    }

    #[test]
    fn sext_widens_with_sign() {
        // 0xFF as an 8-bit value is -1; sign-extend to 16 → 0xFFFF.
        assert_eq!(sext(0xFF, 8, 16), 0xFFFF);
        // 0x7F is positive at width 8 → stays 0x007F at width 16.
        assert_eq!(sext(0x7F, 8, 16), 0x007F);
        // width-1 sign bit: 1 → all ones at the target width.
        assert_eq!(sext(0x1, 1, 8), 0xFF);
        assert_eq!(sext(0x0, 1, 8), 0x00);
        // 8 → 64 negative.
        assert_eq!(sext(0x80, 8, 64), 0xFFFF_FFFF_FFFF_FF80);
        // 16 → 64 negative and positive.
        assert_eq!(sext(0x8000, 16, 64), 0xFFFF_FFFF_FFFF_8000);
        assert_eq!(sext(0x7FFF, 16, 64), 0x0000_0000_0000_7FFF);
        // Same width is identity (mod mask).
        assert_eq!(sext(0xFF, 8, 8), 0xFF);
        // Narrowing degenerates to truncation.
        assert_eq!(sext(0xABCD, 16, 8), 0xCD);
    }

    #[test]
    fn trunc_keeps_low_bits() {
        assert_eq!(trunc(0xABCD, 8), 0xCD);
        assert_eq!(trunc(0xABCD, 16), 0xABCD);
        assert_eq!(trunc(0xFF, 1), 0x1);
        assert_eq!(trunc(u64::MAX, 64), u64::MAX);
        // Truncating to 32 keeps only the low half.
        assert_eq!(trunc(0xDEAD_BEEF_CAFE_F00D, 32), 0xCAFE_F00D);
    }
}
