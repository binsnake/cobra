//! Root-level contiguous low-bit mask detection for dynamic masking.
//!
//! Ported from `include/cobra/core/DynamicMask.h` and
//! `lib/core/DynamicMask.cpp`. Detects expressions of the form
//! `(2^m - 1) & g` at the AST root. When found, `g` can be solved under
//! `bitwidth = m` instead of the full width, provided `g` contains no
//! right-shift nodes (shifts break the modular homomorphism).

use cobra_core::expr::{Expr, Kind};

/// Describes the detected mask: `mask = (1 << effective_width) - 1` applied
/// to the `inner` subtree. The inner reference borrows from the input AST.
#[derive(Copy, Clone, Debug)]
pub struct MaskInfo<'a> {
    pub effective_width: u32,
    pub inner: &'a Expr,
}

/// Returns `Some(m)` when `val == 2^m - 1` for `m in 1..=63`. `val == 0`
/// and `val == u64::MAX` (the full-width mask) both return `None`,
/// matching C++ `IsPowerOfTwoMinusOne`.
#[must_use]
pub fn is_power_of_two_minus_one(val: u64) -> Option<u32> {
    if val == 0 {
        return None;
    }
    let next = val.wrapping_add(1);
    if next == 0 || !next.is_power_of_two() {
        return None;
    }
    let m = next.trailing_zeros();
    if m == 0 || m >= 64 {
        return None;
    }
    Some(m)
}

/// Detect a root-level `And(g, 2^m - 1)` or `And(2^m - 1, g)` pattern with
/// `m < bitwidth`. Returns `None` otherwise.
#[must_use]
pub fn detect_root_low_bit_mask(expr: &Expr, bitwidth: u32) -> Option<MaskInfo<'_>> {
    if !matches!(expr.kind, Kind::And) || expr.children.len() != 2 {
        return None;
    }

    let (constant_val, other_child): (u64, &Expr) =
        match (&expr.children[0].kind, &expr.children[1].kind) {
            (Kind::Constant(c), _) => (*c, &expr.children[1]),
            (_, Kind::Constant(c)) => (*c, &expr.children[0]),
            _ => return None,
        };

    let m = is_power_of_two_minus_one(constant_val)?;
    if m >= bitwidth {
        return None;
    }
    Some(MaskInfo {
        effective_width: m,
        inner: other_child,
    })
}

/// Returns `true` if any node in the AST is `Shr`.
#[must_use]
pub fn contains_shr(expr: &Expr) -> bool {
    if matches!(expr.kind, Kind::Shr(_)) {
        return true;
    }
    expr.children.iter().any(|c| contains_shr(c))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pow2_minus_one_edges() {
        assert_eq!(is_power_of_two_minus_one(0), None);
        assert_eq!(is_power_of_two_minus_one(1), Some(1));
        assert_eq!(is_power_of_two_minus_one(3), Some(2));
        assert_eq!(is_power_of_two_minus_one(7), Some(3));
        assert_eq!(is_power_of_two_minus_one(0xFF), Some(8));
        assert_eq!(is_power_of_two_minus_one(0xFFFF), Some(16));
        assert_eq!(is_power_of_two_minus_one(0x7FFF_FFFF_FFFF_FFFF), Some(63));
        // u64::MAX = 2^64 - 1 is rejected per the C++ wrap-around check.
        assert_eq!(is_power_of_two_minus_one(u64::MAX), None);
        // Non-mask value.
        assert_eq!(is_power_of_two_minus_one(0xDEAD), None);
    }

    #[test]
    fn detect_rhs_constant() {
        // (x & 0xFF) at bitwidth 64 → m = 8, inner = x
        let expr = Expr::and(Expr::variable(0), Expr::constant(0xFF));
        let info = detect_root_low_bit_mask(&expr, 64).expect("should detect");
        assert_eq!(info.effective_width, 8);
        assert!(matches!(info.inner.kind, Kind::Variable(0)));
    }

    #[test]
    fn detect_lhs_constant() {
        // (0xFFFF & (x + y)) at bitwidth 64 → m = 16
        let expr = Expr::and(
            Expr::constant(0xFFFF),
            Expr::add(Expr::variable(0), Expr::variable(1)),
        );
        let info = detect_root_low_bit_mask(&expr, 64).expect("should detect");
        assert_eq!(info.effective_width, 16);
        assert!(matches!(info.inner.kind, Kind::Add));
    }

    #[test]
    fn reject_when_m_ge_bitwidth() {
        // (x & 0xFF) at bitwidth 8 should NOT match — m == bitwidth, no reduction possible
        let expr = Expr::and(Expr::variable(0), Expr::constant(0xFF));
        assert!(detect_root_low_bit_mask(&expr, 8).is_none());
        // At bitwidth 7 it would match (m=8 not < 7) — wait, m=8 >= 7, still reject.
        assert!(detect_root_low_bit_mask(&expr, 7).is_none());
        // At bitwidth 9, m=8 < 9, should match.
        assert!(detect_root_low_bit_mask(&expr, 9).is_some());
    }

    #[test]
    fn reject_non_and_root() {
        let expr = Expr::or(Expr::variable(0), Expr::constant(0xFF));
        assert!(detect_root_low_bit_mask(&expr, 64).is_none());
    }

    #[test]
    fn reject_no_constant_child() {
        let expr = Expr::and(Expr::variable(0), Expr::variable(1));
        assert!(detect_root_low_bit_mask(&expr, 64).is_none());
    }

    #[test]
    fn reject_non_mask_constant() {
        let expr = Expr::and(Expr::variable(0), Expr::constant(0xDEAD));
        assert!(detect_root_low_bit_mask(&expr, 64).is_none());
    }

    #[test]
    fn contains_shr_walks_tree() {
        let plain = Expr::add(Expr::variable(0), Expr::variable(1));
        assert!(!contains_shr(&plain));
        let with_shr = Expr::add(Expr::shr(Expr::variable(0), 2), Expr::variable(1));
        assert!(contains_shr(&with_shr));
        // Shr at root
        assert!(contains_shr(&Expr::shr(Expr::variable(0), 1)));
    }
}
