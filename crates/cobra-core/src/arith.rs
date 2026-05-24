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
}
