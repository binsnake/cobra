//! Fast-path signature recognition. Maps known signature vectors back
//! 1-variable / 2-variable Boolean arms of
//!
//! Higher-arity tables — 3-var Boolean (256 entries), 4-var NPN
//! equivalence classes (an externally generated table), 5/6-var
//! Shannon decomposition, and the scaled-boolean coefficient sweep —
//! land in follow-up sessions. The current subset is enough to
//! recognise constants, single-variable affine patterns (`a + k*x`),
//! and every 2-variable Boolean function — which covers the bulk of
//! the README's smaller MBA examples.

use cobra_core::arith::{bitmask, mod_add, mod_mul, mod_sub};
use cobra_core::evaluate_boolean_signature;
use cobra_core::evaluator::Evaluator;
use cobra_core::expr::{Expr, Kind};
use cobra_core::expr_cost::{compute_cost, is_better, ExprCost};
use cobra_core::expr_rewrite::apply_coefficient;
use cobra_core::expr_utils::{collect_vars, remap_var_indices};

use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};
use crate::weighted_poly_fit::solve_2adic_fixed;

/// True when every entry of `sig` is the same value.
#[must_use]
pub fn all_equal(sig: &[u64]) -> bool {
    sig.windows(2).all(|w| w[0] == w[1])
}

/// True when every entry of `sig` is `0` or `1`.
#[must_use]
pub fn is_boolean_sig(sig: &[u64]) -> bool {
    sig.iter().all(|&v| v <= 1)
}

/// Pack a Boolean signature into the integer key used by the lookup
/// `PackBoolSig` (`u32` form — sufficient up to 5 variables).
#[must_use]
pub fn pack_bool_sig(sig: &[u64]) -> u32 {
    let mut key: u32 = 0;
    for (i, &v) in sig.iter().enumerate() {
        if v != 0 {
            key |= 1u32 << i;
        }
    }
    key
}

/// 1-variable affine recognition: `sig = [s0, s1]` is matched as
/// `s0 + (s1 - s0) * x`. Returns `None` only when `s1 == s0`
/// (handled earlier by [`all_equal`] so this arm is just a safety net).
#[must_use]
pub fn match_1var(sig: &[u64], bitwidth: u32) -> Option<Box<Expr>> {
    let s0 = sig[0];
    let s1 = sig[1];
    if s0 == 0 && s1 == 1 {
        return Some(Expr::variable(0));
    }
    if s0 == 0 && s1 != 0 {
        return Some(Expr::mul(Expr::constant(s1), Expr::variable(0)));
    }
    let a = mod_sub(s1, s0, bitwidth);
    if a == 0 {
        return None;
    }
    let term = Expr::mul(Expr::constant(a), Expr::variable(0));
    Some(Expr::add(Expr::constant(s0), term))
}

/// All 16 Boolean functions of two variables, keyed by packed sig.
/// Constants `0x0` and `0xF` are filtered out by [`all_equal`] before
/// reaching this table. Indexing convention: `key bit i` is `f(x, y)`
/// `Match2varBoolean`.
#[must_use]
pub fn match_2var_boolean(key: u8) -> Option<Box<Expr>> {
    let x = || Expr::variable(0);
    let y = || Expr::variable(1);
    let m = match key {
        0x1 => Expr::not(Expr::or(x(), y())),
        0x2 => Expr::and(x(), Expr::not(y())),
        0x3 => Expr::not(y()),
        0x4 => Expr::and(Expr::not(x()), y()),
        0x5 => Expr::not(x()),
        0x6 => Expr::xor(x(), y()),
        0x7 => Expr::not(Expr::and(x(), y())),
        0x8 => Expr::and(x(), y()),
        0x9 => Expr::not(Expr::xor(x(), y())),
        0xA => x(),
        0xB => Expr::or(x(), Expr::not(y())),
        0xC => y(),
        0xD => Expr::or(Expr::not(x()), y()),
        0xE => Expr::or(x(), y()),
        _ => return None,
    };
    Some(m)
}

/// Pack a Boolean signature into a 64-bit key for the 6-variable
/// Shannon decomposer. Bit `i` is set when `sig[i] != 0`.
#[must_use]
pub fn pack_bool_sig_64(sig: &[u64]) -> u64 {
    let mut key: u64 = 0;
    for (i, &v) in sig.iter().enumerate() {
        if v != 0 {
            key |= 1u64 << i;
        }
    }
    key
}

/// Complete table of the 254 non-constant Boolean functions of three
/// variables. Each arm returns the minimal-cost AST found by BFS over
/// `Match3varBoolean`.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn match_3var_boolean(key: u8) -> Option<Box<Expr>> {
    let x = || Expr::variable(0);
    let y = || Expr::variable(1);
    let z = || Expr::variable(2);
    let m = match key {
        0x01 => Expr::not(Expr::or(x(), Expr::or(y(), z()))),
        0x02 => Expr::and(x(), Expr::not(Expr::or(y(), z()))),
        0x03 => Expr::not(Expr::or(y(), z())),
        0x04 => Expr::and(y(), Expr::not(Expr::or(x(), z()))),
        0x05 => Expr::not(Expr::or(x(), z())),
        0x06 => Expr::and(Expr::not(z()), Expr::xor(x(), y())),
        0x07 => Expr::not(Expr::or(z(), Expr::and(x(), y()))),
        0x08 => Expr::and(x(), Expr::and(y(), Expr::not(z()))),
        0x09 => Expr::not(Expr::or(z(), Expr::xor(x(), y()))),
        0x0A => Expr::and(x(), Expr::not(z())),
        0x0B => Expr::and(Expr::not(z()), Expr::or(x(), Expr::not(y()))),
        0x0C => Expr::and(y(), Expr::not(z())),
        0x0D => Expr::and(Expr::not(z()), Expr::or(y(), Expr::not(x()))),
        0x0E => Expr::and(Expr::not(z()), Expr::or(x(), y())),
        0x0F => Expr::not(z()),
        0x10 => Expr::and(z(), Expr::not(Expr::or(x(), y()))),
        0x11 => Expr::not(Expr::or(x(), y())),
        0x12 => Expr::and(Expr::not(y()), Expr::xor(x(), z())),
        0x13 => Expr::not(Expr::or(y(), Expr::and(x(), z()))),
        0x14 => Expr::and(Expr::not(x()), Expr::xor(y(), z())),
        0x15 => Expr::not(Expr::or(x(), Expr::and(y(), z()))),
        0x16 => Expr::xor(x(), Expr::or(Expr::and(x(), y()), Expr::xor(y(), z()))),
        0x17 => Expr::xor(
            x(),
            Expr::or(Expr::xor(x(), Expr::not(y())), Expr::xor(y(), z())),
        ),
        0x18 => Expr::and(Expr::xor(x(), z()), Expr::xor(y(), z())),
        0x19 => Expr::not(Expr::or(Expr::xor(x(), y()), Expr::and(x(), z()))),
        0x1A => Expr::xor(z(), Expr::or(x(), Expr::and(y(), z()))),
        0x1B => Expr::xor(Expr::or(x(), y()), Expr::or(z(), Expr::not(x()))),
        0x1C => Expr::xor(z(), Expr::or(y(), Expr::and(x(), z()))),
        0x1D => Expr::xor(Expr::or(x(), y()), Expr::or(z(), Expr::not(y()))),
        0x1E => Expr::xor(z(), Expr::or(x(), y())),
        0x1F => Expr::not(Expr::and(z(), Expr::or(x(), y()))),
        0x20 => Expr::and(x(), Expr::and(z(), Expr::not(y()))),
        0x21 => Expr::not(Expr::or(y(), Expr::xor(x(), z()))),
        0x22 => Expr::and(x(), Expr::not(y())),
        0x23 => Expr::and(Expr::not(y()), Expr::or(x(), Expr::not(z()))),
        0x24 => Expr::and(Expr::xor(x(), y()), Expr::xor(y(), z())),
        0x25 => Expr::not(Expr::or(Expr::and(x(), y()), Expr::xor(x(), z()))),
        0x26 => Expr::xor(y(), Expr::or(x(), Expr::and(y(), z()))),
        0x27 => Expr::xor(Expr::and(x(), y()), Expr::or(x(), Expr::not(z()))),
        0x28 => Expr::and(x(), Expr::xor(y(), z())),
        0x29 => Expr::xor(
            y(),
            Expr::or(Expr::xor(x(), Expr::not(z())), Expr::and(y(), z())),
        ),
        0x2A => Expr::and(x(), Expr::not(Expr::and(y(), z()))),
        0x2B => Expr::xor(
            x(),
            Expr::not(Expr::or(Expr::xor(x(), y()), Expr::xor(x(), z()))),
        ),
        0x2C => Expr::and(Expr::or(x(), y()), Expr::xor(y(), z())),
        0x2D => Expr::xor(z(), Expr::or(y(), Expr::not(x()))),
        0x2E => Expr::xor(Expr::or(x(), y()), Expr::and(y(), z())),
        0x2F => Expr::or(Expr::not(z()), Expr::and(x(), Expr::not(y()))),
        0x30 => Expr::and(z(), Expr::not(y())),
        0x31 => Expr::and(Expr::not(y()), Expr::or(z(), Expr::not(x()))),
        0x32 => Expr::and(Expr::not(y()), Expr::or(x(), z())),
        0x33 => Expr::not(y()),
        0x34 => Expr::xor(y(), Expr::or(z(), Expr::and(x(), y()))),
        0x35 => Expr::xor(Expr::or(x(), z()), Expr::or(y(), Expr::not(z()))),
        0x36 => Expr::xor(y(), Expr::or(x(), z())),
        0x37 => Expr::not(Expr::and(y(), Expr::or(x(), z()))),
        0x38 => Expr::and(Expr::or(x(), z()), Expr::xor(y(), z())),
        0x39 => Expr::xor(y(), Expr::or(z(), Expr::not(x()))),
        0x3A => Expr::xor(Expr::or(x(), z()), Expr::and(y(), z())),
        0x3B => Expr::or(Expr::not(y()), Expr::and(x(), Expr::not(z()))),
        0x3C => Expr::xor(y(), z()),
        0x3D => Expr::or(Expr::xor(y(), z()), Expr::not(Expr::or(x(), y()))),
        0x3E => Expr::or(Expr::and(x(), Expr::not(y())), Expr::xor(y(), z())),
        0x3F => Expr::not(Expr::and(y(), z())),
        0x40 => Expr::and(y(), Expr::and(z(), Expr::not(x()))),
        0x41 => Expr::not(Expr::or(x(), Expr::xor(y(), z()))),
        0x42 => Expr::and(Expr::xor(x(), y()), Expr::xor(x(), z())),
        0x43 => Expr::not(Expr::or(Expr::and(x(), y()), Expr::xor(y(), z()))),
        0x44 => Expr::and(y(), Expr::not(x())),
        0x45 => Expr::and(Expr::not(x()), Expr::or(y(), Expr::not(z()))),
        0x46 => Expr::xor(x(), Expr::or(y(), Expr::and(x(), z()))),
        0x47 => Expr::xor(Expr::and(x(), y()), Expr::or(y(), Expr::not(z()))),
        0x48 => Expr::and(y(), Expr::xor(x(), z())),
        0x49 => Expr::xor(
            x(),
            Expr::or(Expr::and(x(), z()), Expr::xor(y(), Expr::not(z()))),
        ),
        0x4A => Expr::and(Expr::or(x(), y()), Expr::xor(x(), z())),
        0x4B => Expr::xor(z(), Expr::or(x(), Expr::not(y()))),
        0x4C => Expr::and(y(), Expr::not(Expr::and(x(), z()))),
        0x4D => Expr::xor(
            x(),
            Expr::or(Expr::xor(x(), y()), Expr::xor(x(), Expr::not(z()))),
        ),
        0x4E => Expr::xor(Expr::or(x(), y()), Expr::and(x(), z())),
        0x4F => Expr::or(Expr::not(z()), Expr::and(y(), Expr::not(x()))),
        0x50 => Expr::and(z(), Expr::not(x())),
        0x51 => Expr::and(Expr::not(x()), Expr::or(z(), Expr::not(y()))),
        0x52 => Expr::xor(x(), Expr::or(z(), Expr::and(x(), y()))),
        0x53 => Expr::xor(Expr::and(x(), z()), Expr::or(z(), Expr::not(y()))),
        0x54 => Expr::and(Expr::not(x()), Expr::or(y(), z())),
        0x55 => Expr::not(x()),
        0x56 => Expr::xor(x(), Expr::or(y(), z())),
        0x57 => Expr::not(Expr::and(x(), Expr::or(y(), z()))),
        0x58 => Expr::and(Expr::xor(x(), z()), Expr::or(y(), z())),
        0x59 => Expr::xor(x(), Expr::or(z(), Expr::not(y()))),
        0x5A => Expr::xor(x(), z()),
        0x5B => Expr::or(Expr::xor(x(), z()), Expr::not(Expr::or(x(), y()))),
        0x5C => Expr::xor(Expr::and(x(), z()), Expr::or(y(), z())),
        0x5D => Expr::or(Expr::not(x()), Expr::and(y(), Expr::not(z()))),
        0x5E => Expr::or(Expr::xor(x(), z()), Expr::and(y(), Expr::not(x()))),
        0x5F => Expr::not(Expr::and(x(), z())),
        0x60 => Expr::and(z(), Expr::xor(x(), y())),
        0x61 => Expr::xor(
            x(),
            Expr::or(Expr::and(x(), y()), Expr::xor(y(), Expr::not(z()))),
        ),
        0x62 => Expr::and(Expr::xor(x(), y()), Expr::or(x(), z())),
        0x63 => Expr::xor(y(), Expr::or(x(), Expr::not(z()))),
        0x64 => Expr::and(Expr::xor(x(), y()), Expr::or(y(), z())),
        0x65 => Expr::xor(x(), Expr::or(y(), Expr::not(z()))),
        0x66 => Expr::xor(x(), y()),
        0x67 => Expr::or(Expr::xor(x(), y()), Expr::not(Expr::or(x(), z()))),
        0x68 => Expr::xor(Expr::and(x(), y()), Expr::and(z(), Expr::or(x(), y()))),
        0x69 => Expr::xor(x(), Expr::xor(y(), Expr::not(z()))),
        0x6A => Expr::xor(x(), Expr::and(y(), z())),
        0x6B => Expr::xor(
            y(),
            Expr::not(Expr::and(Expr::xor(x(), z()), Expr::or(y(), z()))),
        ),
        0x6C => Expr::xor(y(), Expr::and(x(), z())),
        0x6D => Expr::xor(
            x(),
            Expr::not(Expr::and(Expr::or(x(), z()), Expr::xor(y(), z()))),
        ),
        0x6E => Expr::or(Expr::xor(x(), y()), Expr::and(x(), Expr::not(z()))),
        0x6F => Expr::or(Expr::not(z()), Expr::xor(x(), y())),
        0x70 => Expr::and(z(), Expr::not(Expr::and(x(), y()))),
        0x71 => Expr::xor(
            x(),
            Expr::or(Expr::xor(x(), z()), Expr::xor(x(), Expr::not(y()))),
        ),
        0x72 => Expr::xor(Expr::and(x(), y()), Expr::or(x(), z())),
        0x73 => Expr::or(Expr::not(y()), Expr::and(z(), Expr::not(x()))),
        0x74 => Expr::xor(Expr::and(x(), y()), Expr::or(y(), z())),
        0x75 => Expr::or(Expr::not(x()), Expr::and(z(), Expr::not(y()))),
        0x76 => Expr::or(Expr::xor(x(), y()), Expr::and(z(), Expr::not(x()))),
        0x77 => Expr::not(Expr::and(x(), y())),
        0x78 => Expr::xor(z(), Expr::and(x(), y())),
        0x79 => Expr::xor(
            x(),
            Expr::not(Expr::and(Expr::or(x(), y()), Expr::xor(y(), z()))),
        ),
        0x7A => Expr::or(Expr::xor(x(), z()), Expr::and(x(), Expr::not(y()))),
        0x7B => Expr::or(Expr::not(y()), Expr::xor(x(), z())),
        0x7C => Expr::or(Expr::xor(y(), z()), Expr::and(y(), Expr::not(x()))),
        0x7D => Expr::or(Expr::not(x()), Expr::xor(y(), z())),
        0x7E => Expr::or(Expr::xor(x(), y()), Expr::xor(x(), z())),
        0x7F => Expr::not(Expr::and(x(), Expr::and(y(), z()))),
        0x80 => Expr::and(x(), Expr::and(y(), z())),
        0x81 => Expr::not(Expr::or(Expr::xor(x(), y()), Expr::xor(x(), z()))),
        0x82 => Expr::and(x(), Expr::xor(y(), Expr::not(z()))),
        0x83 => Expr::and(
            Expr::or(x(), Expr::not(y())),
            Expr::xor(y(), Expr::not(z())),
        ),
        0x84 => Expr::and(y(), Expr::xor(x(), Expr::not(z()))),
        0x85 => Expr::and(
            Expr::xor(x(), Expr::not(z())),
            Expr::or(y(), Expr::not(x())),
        ),
        0x86 => Expr::xor(x(), Expr::and(Expr::or(x(), y()), Expr::xor(y(), z()))),
        0x87 => Expr::xor(z(), Expr::not(Expr::and(x(), y()))),
        0x88 => Expr::and(x(), y()),
        0x89 => Expr::and(
            Expr::xor(x(), Expr::not(y())),
            Expr::or(x(), Expr::not(z())),
        ),
        0x8A => Expr::and(x(), Expr::or(y(), Expr::not(z()))),
        0x8B => Expr::or(Expr::and(x(), y()), Expr::not(Expr::or(y(), z()))),
        0x8C => Expr::and(y(), Expr::or(x(), Expr::not(z()))),
        0x8D => Expr::or(Expr::and(x(), y()), Expr::not(Expr::or(x(), z()))),
        0x8E => Expr::xor(x(), Expr::and(Expr::xor(x(), y()), Expr::xor(y(), z()))),
        0x8F => Expr::or(Expr::not(z()), Expr::and(x(), y())),
        0x90 => Expr::and(z(), Expr::xor(x(), Expr::not(y()))),
        0x91 => Expr::and(
            Expr::xor(x(), Expr::not(y())),
            Expr::or(z(), Expr::not(x())),
        ),
        0x92 => Expr::xor(x(), Expr::and(Expr::or(x(), z()), Expr::xor(y(), z()))),
        0x93 => Expr::xor(y(), Expr::not(Expr::and(x(), z()))),
        0x94 => Expr::xor(y(), Expr::and(Expr::xor(x(), z()), Expr::or(y(), z()))),
        0x95 => Expr::xor(x(), Expr::not(Expr::and(y(), z()))),
        0x96 => Expr::xor(x(), Expr::xor(y(), z())),
        0x97 => Expr::xor(
            x(),
            Expr::or(Expr::xor(y(), z()), Expr::not(Expr::or(x(), y()))),
        ),
        0x98 => Expr::and(Expr::or(x(), z()), Expr::xor(x(), Expr::not(y()))),
        0x99 => Expr::xor(x(), Expr::not(y())),
        0x9A => Expr::xor(x(), Expr::and(z(), Expr::not(y()))),
        0x9B => Expr::not(Expr::and(Expr::xor(x(), y()), Expr::or(y(), z()))),
        0x9C => Expr::xor(y(), Expr::and(z(), Expr::not(x()))),
        0x9D => Expr::not(Expr::and(Expr::xor(x(), y()), Expr::or(x(), z()))),
        0x9E => Expr::xor(y(), Expr::xor(x(), Expr::or(z(), Expr::and(x(), y())))),
        0x9F => Expr::not(Expr::and(z(), Expr::xor(x(), y()))),
        0xA0 => Expr::and(x(), z()),
        0xA1 => Expr::and(
            Expr::or(x(), Expr::not(y())),
            Expr::xor(x(), Expr::not(z())),
        ),
        0xA2 => Expr::and(x(), Expr::or(z(), Expr::not(y()))),
        0xA3 => Expr::or(Expr::and(x(), z()), Expr::not(Expr::or(y(), z()))),
        0xA4 => Expr::and(Expr::or(x(), y()), Expr::xor(x(), Expr::not(z()))),
        0xA5 => Expr::xor(x(), Expr::not(z())),
        0xA6 => Expr::xor(x(), Expr::and(y(), Expr::not(z()))),
        0xA7 => Expr::not(Expr::and(Expr::xor(x(), z()), Expr::or(y(), z()))),
        0xA8 => Expr::and(x(), Expr::or(y(), z())),
        0xA9 => Expr::xor(x(), Expr::not(Expr::or(y(), z()))),
        0xAA => x(),
        0xAB => Expr::or(x(), Expr::not(Expr::or(y(), z()))),
        0xAC => Expr::xor(y(), Expr::and(z(), Expr::xor(x(), y()))),
        0xAD => Expr::or(Expr::and(x(), y()), Expr::xor(x(), Expr::not(z()))),
        0xAE => Expr::or(x(), Expr::and(y(), Expr::not(z()))),
        0xAF => Expr::or(x(), Expr::not(z())),
        0xB0 => Expr::and(z(), Expr::or(x(), Expr::not(y()))),
        0xB1 => Expr::xor(Expr::or(x(), y()), Expr::not(Expr::and(x(), z()))),
        0xB2 => Expr::xor(x(), Expr::and(Expr::xor(x(), z()), Expr::xor(y(), z()))),
        0xB3 => Expr::or(Expr::not(y()), Expr::and(x(), z())),
        0xB4 => Expr::xor(z(), Expr::and(y(), Expr::not(x()))),
        0xB5 => Expr::not(Expr::and(Expr::or(x(), y()), Expr::xor(x(), z()))),
        0xB6 => Expr::xor(z(), Expr::xor(x(), Expr::or(y(), Expr::and(x(), z())))),
        0xB7 => Expr::not(Expr::and(y(), Expr::xor(x(), z()))),
        0xB8 => Expr::xor(z(), Expr::and(y(), Expr::xor(x(), z()))),
        0xB9 => Expr::or(Expr::and(x(), z()), Expr::xor(x(), Expr::not(y()))),
        0xBA => Expr::or(x(), Expr::and(z(), Expr::not(y()))),
        0xBB => Expr::or(x(), Expr::not(y())),
        0xBC => Expr::or(Expr::and(x(), y()), Expr::xor(y(), z())),
        0xBD => Expr::or(Expr::xor(x(), Expr::not(y())), Expr::xor(y(), z())),
        0xBE => Expr::or(x(), Expr::xor(y(), z())),
        0xBF => Expr::or(x(), Expr::not(Expr::and(y(), z()))),
        0xC0 => Expr::and(y(), z()),
        0xC1 => Expr::and(
            Expr::or(y(), Expr::not(x())),
            Expr::xor(y(), Expr::not(z())),
        ),
        0xC2 => Expr::and(Expr::or(x(), y()), Expr::xor(y(), Expr::not(z()))),
        0xC3 => Expr::xor(y(), Expr::not(z())),
        0xC4 => Expr::and(y(), Expr::or(z(), Expr::not(x()))),
        0xC5 => Expr::xor(Expr::or(x(), z()), Expr::not(Expr::and(y(), z()))),
        0xC6 => Expr::xor(y(), Expr::and(x(), Expr::not(z()))),
        0xC7 => Expr::not(Expr::and(Expr::or(x(), z()), Expr::xor(y(), z()))),
        0xC8 => Expr::and(y(), Expr::or(x(), z())),
        0xC9 => Expr::xor(y(), Expr::not(Expr::or(x(), z()))),
        0xCA => Expr::xor(x(), Expr::and(z(), Expr::xor(x(), y()))),
        0xCB => Expr::or(Expr::and(x(), y()), Expr::xor(y(), Expr::not(z()))),
        0xCC => y(),
        0xCD => Expr::or(y(), Expr::not(Expr::or(x(), z()))),
        0xCE => Expr::or(y(), Expr::and(x(), Expr::not(z()))),
        0xCF => Expr::or(y(), Expr::not(z())),
        0xD0 => Expr::and(z(), Expr::or(y(), Expr::not(x()))),
        0xD1 => Expr::xor(Expr::or(x(), y()), Expr::not(Expr::and(y(), z()))),
        0xD2 => Expr::xor(z(), Expr::and(x(), Expr::not(y()))),
        0xD3 => Expr::not(Expr::and(Expr::or(x(), y()), Expr::xor(y(), z()))),
        0xD4 => Expr::xor(x(), Expr::or(Expr::xor(x(), y()), Expr::xor(x(), z()))),
        0xD5 => Expr::or(Expr::not(x()), Expr::and(y(), z())),
        0xD6 => Expr::xor(z(), Expr::xor(y(), Expr::or(x(), Expr::and(y(), z())))),
        0xD7 => Expr::not(Expr::and(x(), Expr::xor(y(), z()))),
        0xD8 => Expr::xor(z(), Expr::and(x(), Expr::xor(y(), z()))),
        0xD9 => Expr::or(Expr::xor(x(), Expr::not(y())), Expr::and(y(), z())),
        0xDA => Expr::or(Expr::and(x(), y()), Expr::xor(x(), z())),
        0xDB => Expr::or(Expr::xor(x(), z()), Expr::xor(x(), Expr::not(y()))),
        0xDC => Expr::or(y(), Expr::and(z(), Expr::not(x()))),
        0xDD => Expr::or(y(), Expr::not(x())),
        0xDE => Expr::or(y(), Expr::xor(x(), z())),
        0xDF => Expr::or(y(), Expr::not(Expr::and(x(), z()))),
        0xE0 => Expr::and(z(), Expr::or(x(), y())),
        0xE1 => Expr::xor(z(), Expr::not(Expr::or(x(), y()))),
        0xE2 => Expr::xor(x(), Expr::and(y(), Expr::xor(x(), z()))),
        0xE3 => Expr::or(Expr::and(x(), z()), Expr::xor(y(), Expr::not(z()))),
        0xE4 => Expr::xor(y(), Expr::and(x(), Expr::xor(y(), z()))),
        0xE5 => Expr::or(Expr::xor(x(), Expr::not(z())), Expr::and(y(), z())),
        0xE6 => Expr::or(Expr::xor(x(), y()), Expr::and(x(), z())),
        0xE7 => Expr::or(Expr::xor(x(), y()), Expr::xor(x(), Expr::not(z()))),
        0xE8 => Expr::xor(x(), Expr::and(Expr::xor(x(), y()), Expr::xor(x(), z()))),
        0xE9 => Expr::xor(
            x(),
            Expr::not(Expr::or(Expr::and(x(), y()), Expr::xor(y(), z()))),
        ),
        0xEA => Expr::or(x(), Expr::and(y(), z())),
        0xEB => Expr::or(x(), Expr::xor(y(), Expr::not(z()))),
        0xEC => Expr::or(y(), Expr::and(x(), z())),
        0xED => Expr::or(y(), Expr::xor(x(), Expr::not(z()))),
        0xEE => Expr::or(x(), y()),
        0xEF => Expr::or(x(), Expr::or(y(), Expr::not(z()))),
        0xF0 => z(),
        0xF1 => Expr::or(z(), Expr::not(Expr::or(x(), y()))),
        0xF2 => Expr::or(z(), Expr::and(x(), Expr::not(y()))),
        0xF3 => Expr::or(z(), Expr::not(y())),
        0xF4 => Expr::or(z(), Expr::and(y(), Expr::not(x()))),
        0xF5 => Expr::or(z(), Expr::not(x())),
        0xF6 => Expr::or(z(), Expr::xor(x(), y())),
        0xF7 => Expr::or(z(), Expr::not(Expr::and(x(), y()))),
        0xF8 => Expr::or(z(), Expr::and(x(), y())),
        0xF9 => Expr::or(z(), Expr::xor(x(), Expr::not(y()))),
        0xFA => Expr::or(x(), z()),
        0xFB => Expr::or(x(), Expr::or(z(), Expr::not(y()))),
        0xFC => Expr::or(y(), z()),
        0xFD => Expr::or(y(), Expr::or(z(), Expr::not(x()))),
        0xFE => Expr::or(x(), Expr::or(y(), z())),
        _ => return None,
    };
    Some(m)
}

/// Collapse `Not(Not(x))` everywhere in a tree. NPN input/output
/// negations can introduce double-NOTs when the canonical form already
/// contains a NOT at the same position.
#[allow(clippy::boxed_local)]
fn collapse_double_not(expr: Box<Expr>) -> Box<Expr> {
    let mut e = *expr;
    for i in 0..e.children.len() {
        let child = std::mem::replace(&mut e.children[i], Expr::constant(0));
        e.children[i] = collapse_double_not(child);
    }
    if matches!(e.kind, cobra_core::expr::Kind::Not) && !e.children.is_empty() {
        if let cobra_core::expr::Kind::Not = e.children[0].kind {
            // Take grandchild out — Not(Not(x)) → x.
            let mut inner = std::mem::replace(&mut e.children[0], Expr::constant(0));
            return std::mem::replace(&mut inner.children[0], Expr::constant(0));
        }
    }
    Box::new(e)
}

/// 4-variable NPN equivalence-class lookup. The 65536-entry table
/// (`KNPN4_TABLE`) maps each truth table to a canonical class plus the
/// permutation, input-negation mask, and output-negation flag that
/// transform the canonical expression back to it.
#[must_use]
pub fn match_4var_npn(key: u16) -> Option<Box<Expr>> {
    let entry = &crate::npn4_table::KNPN4_TABLE[key as usize];
    let perm = &crate::npn4_table::KPERMS4[entry.perm_idx as usize];

    let mut inv = [0u32; 4];
    for (i, &p) in perm.iter().enumerate() {
        inv[p as usize] = i as u32;
    }

    let neg = entry.neg_inputs;
    let var_fn = move |j: u32| -> Box<Expr> {
        let a = inv[j as usize];
        let mut e = Expr::variable(a);
        if (neg >> a) & 1 != 0 {
            e = Expr::not(e);
        }
        e
    };

    let mut result = crate::npn4_canonical::build_npn4_canonical(entry.class_id, var_fn)?;
    if entry.neg_output != 0 {
        result = Expr::not(result);
    }
    Some(collapse_double_not(result))
}

/// Shannon decomposition on variable 4 of a 5-variable Boolean
/// function. Splits `f(x,y,z,w,v)` into cofactors `f0 = f(...,0)` and
/// `Match5varBoolean`.
#[must_use]
pub fn match_5var_boolean(key: u32) -> Option<Box<Expr>> {
    let v = || Expr::variable(4);
    let f0 = (key & 0xFFFF) as u16;
    let f1 = ((key >> 16) & 0xFFFF) as u16;

    if f0 == 0x0000 && f1 == 0xFFFF {
        return Some(v());
    }
    if f0 == 0xFFFF && f1 == 0x0000 {
        return Some(Expr::not(v()));
    }
    if f0 == 0x0000 {
        let e1 = match_4var_npn(f1)?;
        return Some(Expr::and(v(), e1));
    }
    if f1 == 0x0000 {
        let e0 = match_4var_npn(f0)?;
        return Some(Expr::and(Expr::not(v()), e0));
    }
    if f0 == 0xFFFF {
        let e1 = match_4var_npn(f1)?;
        return Some(Expr::or(Expr::not(v()), e1));
    }
    if f1 == 0xFFFF {
        let e0 = match_4var_npn(f0)?;
        return Some(Expr::or(v(), e0));
    }
    if f0 == f1 {
        return match_4var_npn(f0);
    }
    if f0 == !f1 {
        let e0 = match_4var_npn(f0)?;
        return Some(Expr::xor(e0, v()));
    }

    let e0 = match_4var_npn(f0)?;
    let e_diff = match_4var_npn(f0 ^ f1)?;
    Some(Expr::xor(e0, Expr::and(v(), e_diff)))
}

/// Shannon decomposition on variable 5 of a 6-variable Boolean
/// function. Recurses into [`match_5var_boolean`].
#[must_use]
pub fn match_6var_boolean(key: u64) -> Option<Box<Expr>> {
    let u = || Expr::variable(5);
    let f0 = (key & 0xFFFF_FFFF) as u32;
    let f1 = ((key >> 32) & 0xFFFF_FFFF) as u32;

    if f0 == 0x0000_0000 && f1 == 0xFFFF_FFFF {
        return Some(u());
    }
    if f0 == 0xFFFF_FFFF && f1 == 0x0000_0000 {
        return Some(Expr::not(u()));
    }
    if f0 == 0x0000_0000 {
        let e1 = match_5var_boolean(f1)?;
        return Some(Expr::and(u(), e1));
    }
    if f1 == 0x0000_0000 {
        let e0 = match_5var_boolean(f0)?;
        return Some(Expr::and(Expr::not(u()), e0));
    }
    if f0 == 0xFFFF_FFFF {
        let e1 = match_5var_boolean(f1)?;
        return Some(Expr::or(Expr::not(u()), e1));
    }
    if f1 == 0xFFFF_FFFF {
        let e0 = match_5var_boolean(f0)?;
        return Some(Expr::or(u(), e0));
    }
    if f0 == f1 {
        return match_5var_boolean(f0);
    }
    if f0 == !f1 {
        let e0 = match_5var_boolean(f0)?;
        return Some(Expr::xor(e0, u()));
    }

    let e0 = match_5var_boolean(f0)?;
    let e_diff = match_5var_boolean(f0 ^ f1)?;
    Some(Expr::xor(e0, Expr::and(u(), e_diff)))
}

/// Recognise a "scaled boolean" signature — one whose entries are
/// either `c` or `c + k` for some constants `(c, k)`. Strips the
/// affine wrapper, recurses [`match_pattern`] on the resulting
///
/// Returns `None` when the signature isn't of the affine-Boolean
/// shape, when the inner Boolean form has no pattern entry, or when
/// the slope `k` is zero (caught earlier by [`all_equal`] anyway).
#[must_use]
pub fn match_scaled_boolean(sig: &[u64], num_vars: u32, bitwidth: u32) -> Option<Box<Expr>> {
    let c = sig[0];
    let mut k: u64 = 0;
    for &v in &sig[1..] {
        let r = mod_sub(v, c, bitwidth);
        if r == 0 {
            continue;
        }
        if k == 0 {
            k = r;
        } else if r != k {
            return None;
        }
    }
    if k == 0 {
        return None;
    }

    let bool_sig: Vec<u64> = sig
        .iter()
        .map(|&v| u64::from(mod_sub(v, c, bitwidth) != 0))
        .collect();

    let inner = match_pattern(&bool_sig, num_vars, bitwidth)?;
    let mut result = inner;
    if k != 1 {
        result = Expr::mul(Expr::constant(k), result);
    }
    if c != 0 {
        result = Expr::add(Expr::constant(c), result);
    }
    Some(result)
}

/// Top-level dispatcher. Tries (in order):
/// 1. Constant — every entry equal.
/// 2. 1-variable affine.
/// 3. 2-variable Boolean table.
/// 4. Scaled-boolean lift (`c + k * inner`) — covers any sig where
///    every entry is `c` or `c + k`.
///
/// Returns `None` when no arm fires; later passes (`SignatureCob`,
/// `SignatureAnf`, etc.) cover the remaining cases.
#[must_use]
pub fn match_pattern(sig: &[u64], num_vars: u32, bitwidth: u32) -> Option<Box<Expr>> {
    if all_equal(sig) {
        return Some(Expr::constant(sig[0]));
    }
    match num_vars {
        1 => return match_1var(sig, bitwidth),
        2 if is_boolean_sig(sig) => return match_2var_boolean(pack_bool_sig(sig) as u8),
        3 if is_boolean_sig(sig) => return match_3var_boolean(pack_bool_sig(sig) as u8),
        4 if is_boolean_sig(sig) => return match_4var_npn(pack_bool_sig(sig) as u16),
        5 if is_boolean_sig(sig) => return match_5var_boolean(pack_bool_sig(sig)),
        6 if is_boolean_sig(sig) => return match_6var_boolean(pack_bool_sig_64(sig)),
        _ => {}
    }
    if !is_boolean_sig(sig) {
        return match_scaled_boolean(sig, num_vars, bitwidth);
    }
    None
}

/// `TwoVarBasisPattern`.
struct TwoVarBasisPattern {
    expr: Box<Expr>,
    sig: Vec<u64>,
}

/// Build the 14 non-constant 2-var Boolean basis patterns (keys 0x1..=0xE),
/// each paired with its 4-entry boolean signature at `bitwidth`.
fn build_two_var_basis_patterns(bitwidth: u32) -> Vec<TwoVarBasisPattern> {
    let mut out = Vec::with_capacity(14);
    for key in 0x1u8..=0xE {
        let Some(expr) = match_2var_boolean(key) else {
            continue;
        };
        let sig = cobra_core::evaluate_boolean_signature(&expr, 2, bitwidth);
        out.push(TwoVarBasisPattern { expr, sig });
    }
    out
}

/// Thread-safe cache of [`build_two_var_basis_patterns`] keyed by bitwidth.
/// The basis only depends on bitwidth (1..=64), so we compute once per width
/// and hand out a shared `&'static` slice. Callers inside hot loops avoid
/// rebuilding the 14-entry expression/signature table on every invocation.
fn cached_two_var_basis_patterns(bitwidth: u32) -> &'static [TwoVarBasisPattern] {
    use std::collections::HashMap;
    use std::sync::{Mutex, OnceLock};

    static CACHE: OnceLock<Mutex<HashMap<u32, &'static [TwoVarBasisPattern]>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut guard = cache.lock().expect("two-var basis cache poisoned");
    if let Some(&slice) = guard.get(&bitwidth) {
        return slice;
    }
    let built = build_two_var_basis_patterns(bitwidth);
    let leaked: &'static [TwoVarBasisPattern] = Box::leak(built.into_boxed_slice());
    guard.insert(bitwidth, leaked);
    leaked
}

/// Coefficient candidate set: `{0}` ∪ `sig` ∪ `{sig[i] - sig[j]}`.
fn build_coefficient_candidates(sig: &[u64], bitwidth: u32) -> Vec<u64> {
    let mut out = Vec::with_capacity(1 + sig.len() + sig.len() * sig.len());
    let push_unique = |out: &mut Vec<u64>, v: u64| {
        if !out.contains(&v) {
            out.push(v);
        }
    };
    push_unique(&mut out, 0);
    for &v in sig {
        push_unique(&mut out, v);
    }
    for &lhs in sig {
        for &rhs in sig {
            push_unique(&mut out, mod_sub(lhs, rhs, bitwidth));
        }
    }
    out
}

/// Combine a constant with up to two basis summands into an affine
/// both basis terms by value since our callers always produce them.
#[allow(clippy::unnecessary_box_returns)]
fn build_affine_basis_expr(constant: u64, first: Box<Expr>, second: Box<Expr>) -> Box<Expr> {
    let sum = Expr::add(first, second);
    if constant != 0 {
        Expr::add(Expr::constant(constant), sum)
    } else {
        sum
    }
}

/// Search the space of `c + α*B_i + β*B_j` expressions over the 14
/// non-constant 2-var Boolean basis patterns `B_k`, with coefficients
/// drawn from the candidate set built from `sig`. The first candidate
/// `TrySimplifyTwoVarPatternSum`.
///
/// `sig` must be the 4-entry Boolean signature of the original
/// expression at `bitwidth`. The caller is responsible for the
/// full-width verification (typically via
/// [`crate::spot_check::verify_in_original_space`] or
/// [`crate::spot_check::full_width_check_eval`]).
#[must_use]
pub fn try_simplify_two_var_pattern_sum(
    sig: &[u64],
    bitwidth: u32,
    baseline_cost: ExprCost,
    mut verify: impl FnMut(&Expr) -> bool,
) -> Option<Box<Expr>> {
    let coeffs = build_coefficient_candidates(sig, bitwidth);
    let basis = cached_two_var_basis_patterns(bitwidth);

    let mut best: Option<Box<Expr>> = None;
    let mut best_cost = baseline_cost;

    for i in 0..basis.len() {
        for j in (i + 1)..basis.len() {
            let bi = &basis[i];
            let bj = &basis[j];
            for &a in &coeffs {
                if a == 0 {
                    continue;
                }
                for &b in &coeffs {
                    if b == 0 {
                        continue;
                    }

                    let c = mod_sub(
                        mod_sub(sig[0], mod_mul(a, bi.sig[0], bitwidth), bitwidth),
                        mod_mul(b, bj.sig[0], bitwidth),
                        bitwidth,
                    );

                    let mut matches = true;
                    for (p, &sp) in sig.iter().enumerate().skip(1) {
                        let predicted = mod_add(
                            c,
                            mod_add(
                                mod_mul(a, bi.sig[p], bitwidth),
                                mod_mul(b, bj.sig[p], bitwidth),
                                bitwidth,
                            ),
                            bitwidth,
                        );
                        if predicted != sp {
                            matches = false;
                            break;
                        }
                    }
                    if !matches {
                        continue;
                    }

                    let candidate = build_affine_basis_expr(
                        c,
                        apply_coefficient(bi.expr.clone_tree(), a, bitwidth),
                        apply_coefficient(bj.expr.clone_tree(), b, bitwidth),
                    );
                    let candidate_cost = compute_cost(&candidate).cost;
                    if !is_better(&candidate_cost, &best_cost) {
                        continue;
                    }
                    if !verify(&candidate) {
                        continue;
                    }
                    best = Some(candidate);
                    best_cost = candidate_cost;
                }
            }
        }
    }

    best
}

/// Search the space of `c + α*B_i + β*B_j + γ*B_k` expressions — a
/// 3-basis scaled-boolean sum — by solving the 4×4 `Z/2^bitwidth`
/// linear system exactly for each basis triple. Complements
/// [`try_simplify_two_var_pattern_sum`] by reaching signatures whose
/// coefficients don't appear in the 2-basis candidate pool (e.g.
/// `6*x + 6*y - 8*(x&y)`, where `-8` is not in `{sig, sig[i]-sig[j]}`).
#[must_use]
pub fn try_simplify_two_var_basis_triple(
    sig: &[u64],
    bitwidth: u32,
    baseline_cost: ExprCost,
    mut verify: impl FnMut(&Expr) -> bool,
) -> Option<Box<Expr>> {
    if sig.len() != 4 {
        return None;
    }
    let basis = cached_two_var_basis_patterns(bitwidth);
    let mask = bitmask(bitwidth);

    // Stack-allocated RHS; copy `sig` once per call, reinitialize per triple.
    let sig_arr: [u64; 4] = [sig[0], sig[1], sig[2], sig[3]];

    let mut best: Option<Box<Expr>> = None;
    let mut best_cost = baseline_cost;

    for i in 0..basis.len() {
        for j in (i + 1)..basis.len() {
            for k in (j + 1)..basis.len() {
                let bi = &basis[i];
                let bj = &basis[j];
                let bk = &basis[k];

                // Stack-allocated 4×4 system: columns are [1, B_i, B_j, B_k]
                // over the 4 boolean-signature rows. Reconstructed each
                // iteration because `solve_2adic_fixed` mutates in place.
                let mut mat: [[u64; 4]; 4] = [
                    [1, bi.sig[0], bj.sig[0], bk.sig[0]],
                    [1, bi.sig[1], bj.sig[1], bk.sig[1]],
                    [1, bi.sig[2], bj.sig[2], bk.sig[2]],
                    [1, bi.sig[3], bj.sig[3], bk.sig[3]],
                ];
                let mut rhs: [u64; 4] = sig_arr;

                let Some(sol) = solve_2adic_fixed::<4>(&mut mat, &mut rhs, mask, bitwidth) else {
                    continue;
                };
                let (c, a, b, d) = (sol[0], sol[1], sol[2], sol[3]);

                let mut terms: Vec<Box<Expr>> = Vec::new();
                if c != 0 {
                    terms.push(Expr::constant(c));
                }
                if a != 0 {
                    terms.push(apply_coefficient(bi.expr.clone_tree(), a, bitwidth));
                }
                if b != 0 {
                    terms.push(apply_coefficient(bj.expr.clone_tree(), b, bitwidth));
                }
                if d != 0 {
                    terms.push(apply_coefficient(bk.expr.clone_tree(), d, bitwidth));
                }
                if terms.is_empty() {
                    continue;
                }

                let mut iter = terms.into_iter();
                let first = iter.next().expect("non-empty");
                let candidate = iter.fold(first, Expr::add);

                let cost = compute_cost(&candidate).cost;
                if !is_better(&cost, &best_cost) {
                    continue;
                }
                if !verify(&candidate) {
                    continue;
                }
                best = Some(candidate);
                best_cost = cost;
            }
        }
    }

    best
}

/// Single-subtree pattern simplifier. Collects `expr`'s variable
/// two-variable subtrees) the [`try_simplify_two_var_pattern_sum`]
/// `TrySimplifyPatternSubtree`.
///
/// Returns `None` when the baseline expression is already a leaf
/// no candidate beats the baseline cost and verifies full-width.
#[must_use]
pub fn try_simplify_pattern_subtree(expr: &Expr, bitwidth: u32) -> Option<Box<Expr>> {
    // Trivial arithmetic identities `x + 0 = x` and `x * 1 = x`. These
    // arise after deeper pattern rewrites zero out one side (e.g., PIC
    // shapes where one `(X & ~Y) * (~X & Y)` factor reduces to zero),
    // leaving a dangling `+ 0` that blocks further structural passes.
    // The signature-based matcher below can't fold these because their
    // boolean sig matches the kept operand's sig — it would compare
    // "identical" rather than "strictly better".
    if let Some(trivial) = try_simplify_trivial_arith(expr, bitwidth) {
        return Some(trivial);
    }

    let baseline_cost = compute_cost(expr).cost;
    if baseline_cost.weighted_size <= 1 {
        return None;
    }

    let mut support: Vec<u32> = Vec::new();
    collect_vars(expr, &mut support);
    support.sort_unstable();
    support.dedup();

    let num_vars = support.len() as u32;
    if num_vars > 6 {
        return None;
    }

    let mut dense_expr = expr.clone_tree();
    if let Some(&max_idx) = support.last() {
        let mut dense_map = vec![0u32; (max_idx as usize) + 1];
        for (i, &v) in support.iter().enumerate() {
            dense_map[v as usize] = i as u32;
        }
        remap_var_indices(&mut dense_expr, &dense_map);
    }

    let sig = evaluate_boolean_signature(&dense_expr, num_vars, bitwidth);

    // Phase 1: direct pattern-table match.
    if let Some(mut candidate) = match_pattern(&sig, num_vars, bitwidth) {
        if is_better(&compute_cost(&candidate).cost, &baseline_cost) {
            let eval = Evaluator::from_expr(&dense_expr, bitwidth);
            let check =
                full_width_check_eval(&eval, num_vars, &candidate, bitwidth, DEFAULT_NUM_SAMPLES);
            if check.passed {
                if !support.is_empty() {
                    remap_var_indices(&mut candidate, &support);
                }
                return Some(candidate);
            }
        }
    }

    // Phase 2: two-var pattern-sum combinator (covers `(x & y) + (x | y)`).
    if num_vars == 2 {
        let eval = Evaluator::from_expr(&dense_expr, bitwidth);
        let combo = try_simplify_two_var_pattern_sum(&sig, bitwidth, baseline_cost, |cand| {
            full_width_check_eval(&eval, 2, cand, bitwidth, DEFAULT_NUM_SAMPLES).passed
        });
        if let Some(mut candidate) = combo {
            if !support.is_empty() {
                remap_var_indices(&mut candidate, &support);
            }
            return Some(candidate);
        }
    }

    None
}

/// Closed-form trivial-identity rewrites applied before the
/// boolean-signature pattern matcher. These are arithmetic shortcuts
///
/// - `Add(X, 0)` and `Add(0, X)` → `X`
/// - `Mul(X, 1)` and `Mul(1, X)` → `X`
/// - `Mul(X, 0)` and `Mul(0, X)` → `0`
///
/// These can't be recovered via the signature matcher because the
/// signature of e.g. `Add(X, 0)` is identical to `X`'s — they would
/// compare "equal cost" and be rejected by `is_better`. Catching the
/// shape structurally is strictly cheaper anyway.
fn try_simplify_trivial_arith(expr: &Expr, bitwidth: u32) -> Option<Box<Expr>> {
    let mask = bitmask(bitwidth);
    match expr.kind {
        Kind::Add if expr.children.len() == 2 => {
            if is_constant_masked(&expr.children[0], 0, mask) {
                return Some(expr.children[1].clone_tree());
            }
            if is_constant_masked(&expr.children[1], 0, mask) {
                return Some(expr.children[0].clone_tree());
            }
        }
        Kind::Mul if expr.children.len() == 2 => {
            // `x * 0 = 0` / `0 * x = 0` — the zero operand doesn't need
            // to be a leaf, but both operands are exprs so match either
            // side.
            if is_constant_masked(&expr.children[0], 0, mask)
                || is_constant_masked(&expr.children[1], 0, mask)
            {
                return Some(Expr::constant(0));
            }
            if is_constant_masked(&expr.children[0], 1, mask) {
                return Some(expr.children[1].clone_tree());
            }
            if is_constant_masked(&expr.children[1], 1, mask) {
                return Some(expr.children[0].clone_tree());
            }
        }
        _ => {}
    }
    None
}

#[inline]
fn is_constant_masked(expr: &Expr, target: u64, mask: u64) -> bool {
    matches!(expr.kind, Kind::Constant(v) if (v & mask) == (target & mask))
}

/// Bottom-up recursive application of [`try_simplify_pattern_subtree`].
/// retry at each newly-formed parent until a fixed point.
#[must_use]
pub fn simplify_pattern_subtrees(mut expr: Box<Expr>, bitwidth: u32) -> Box<Expr> {
    let children: Vec<Box<Expr>> = expr.children.drain(..).collect();
    for child in children {
        expr.children
            .push(simplify_pattern_subtrees(child, bitwidth));
    }

    if let Some(rewritten) = try_simplify_pattern_subtree(&expr, bitwidth) {
        return simplify_pattern_subtrees(rewritten, bitwidth);
    }
    expr
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::expr::Kind;

    fn sig_of(expr: &Expr, num_vars: u32, bitwidth: u32) -> Vec<u64> {
        evaluate_boolean_signature(expr, num_vars, bitwidth)
    }

    #[test]
    fn all_equal_matches_constants() {
        let sig = vec![7u64; 8];
        let m = match_pattern(&sig, 3, 64).expect("constant should match");
        assert!(matches!(m.kind, Kind::Constant(7)));
    }

    #[test]
    fn match_1var_recovers_variable() {
        // x → sig = [0, 1]
        let m = match_pattern(&[0, 1], 1, 64).expect("variable should match");
        assert!(matches!(m.kind, Kind::Variable(0)));
    }

    #[test]
    fn match_1var_recovers_scaled_variable() {
        // 3*x → sig = [0, 3]
        let m = match_pattern(&[0, 3], 1, 64).expect("3*x should match");
        // Expected shape: Mul(Constant(3), Variable(0))
        assert!(matches!(m.kind, Kind::Mul));
        assert!(matches!(m.children[0].kind, Kind::Constant(3)));
        assert!(matches!(m.children[1].kind, Kind::Variable(0)));
    }

    #[test]
    fn match_1var_recovers_affine_form() {
        // 5 + 2*x → sig = [5, 7]
        let m = match_pattern(&[5, 7], 1, 64).expect("5 + 2*x should match");
        // Expected shape: Add(Constant(5), Mul(Constant(2), Variable(0)))
        assert!(matches!(m.kind, Kind::Add));
        assert!(matches!(m.children[0].kind, Kind::Constant(5)));
        assert!(matches!(m.children[1].kind, Kind::Mul));
    }

    #[test]
    fn match_2var_boolean_xor() {
        // x ^ y → sig = [0, 1, 1, 0]
        let m = match_pattern(&[0, 1, 1, 0], 2, 64).expect("xor should match");
        assert!(matches!(m.kind, Kind::Xor));
    }

    #[test]
    fn match_2var_boolean_and() {
        // x & y → sig = [0, 0, 0, 1]
        let m = match_pattern(&[0, 0, 0, 1], 2, 64).expect("and should match");
        assert!(matches!(m.kind, Kind::And));
    }

    #[test]
    fn match_2var_boolean_or() {
        // x | y → sig = [0, 1, 1, 1]
        let m = match_pattern(&[0, 1, 1, 1], 2, 64).expect("or should match");
        assert!(matches!(m.kind, Kind::Or));
    }

    #[test]
    fn match_2var_boolean_xnor_round_trip() {
        // ~(x ^ y) → sig = [1, 0, 0, 1] at bw=1; identifies as Not(Xor).
        let m = match_pattern(&[1, 0, 0, 1], 2, 64).expect("xnor should match");
        assert!(matches!(m.kind, Kind::Not));
        assert!(matches!(m.children[0].kind, Kind::Xor));
    }

    #[test]
    fn match_scaled_boolean_lifts_2var_xor() {
        // 5 + 2 * (x ^ y) → sig = [5, 7, 7, 5]
        let m = match_pattern(&[5, 7, 7, 5], 2, 64).expect("scaled xor should match");
        // Expected: Add(Constant(5), Mul(Constant(2), Xor(...)))
        assert!(matches!(m.kind, Kind::Add));
        assert!(matches!(m.children[0].kind, Kind::Constant(5)));
        assert!(matches!(m.children[1].kind, Kind::Mul));
        assert!(matches!(m.children[1].children[0].kind, Kind::Constant(2)));
        assert!(matches!(m.children[1].children[1].kind, Kind::Xor));
    }

    #[test]
    fn match_scaled_boolean_lifts_2var_or() {
        // 4 * (x | y) → sig = [0, 4, 4, 4], c=0 → no outer Add
        let m = match_pattern(&[0, 4, 4, 4], 2, 64).expect("scaled or should match");
        assert!(matches!(m.kind, Kind::Mul));
        assert!(matches!(m.children[0].kind, Kind::Constant(4)));
        assert!(matches!(m.children[1].kind, Kind::Or));
    }

    #[test]
    fn match_scaled_boolean_three_value_sig_misses() {
        // [0, 1, 1, 2] — three distinct values, not c-or-c+k. Misses.
        // (This is the (x & y) + (x | y) example, which needs CoB.)
        assert!(match_pattern(&[0, 1, 1, 2], 2, 64).is_none());
    }

    #[test]
    fn match_scaled_boolean_round_trip_on_signature() {
        // Build sig of `7 + 3 * (x & y)` directly and feed it back.
        let original = Expr::add(
            Expr::constant(7),
            Expr::mul(
                Expr::constant(3),
                Expr::and(Expr::variable(0), Expr::variable(1)),
            ),
        );
        let sig = sig_of(&original, 2, 64);
        let m = match_pattern(&sig, 2, 64).expect("affine-scaled and should match");
        // Must produce semantically equivalent output.
        let m_sig = sig_of(&m, 2, 64);
        assert_eq!(sig, m_sig);
    }

    #[test]
    fn full_4var_npn_table_round_trips() {
        // Sample every 16-bit truth table at bw=1; the 222 NPN classes
        // should round-trip via permutation + input/output negation.
        // Tests a strided sample to keep test time bounded; the C++
        // table is verified at generation time.
        // Exhaustive: every 16-bit truth table except the two constants.
        for key in 1u32..0xFFFFu32 {
            let key = key as u16;
            let m = match_4var_npn(key).expect("non-constant key should match");
            let sig = sig_of(&m, 4, 1);
            let recovered = pack_bool_sig(&sig) as u16;
            assert_eq!(recovered, key, "key 0x{key:04X} round-trip failed");
        }
    }

    #[test]
    fn full_3var_boolean_table_round_trips() {
        // For every 8-bit key in 0x01..=0xFE, the matched expression's
        // truth-table at bw=1 must reproduce the key. This is the
        // strongest available smoke test for the 254-entry table.
        for key in 0x01u8..=0xFE {
            let m = match_3var_boolean(key).expect("non-constant key should match");
            let sig = sig_of(&m, 3, 1);
            let recovered = pack_bool_sig(&sig) as u8;
            assert_eq!(recovered, key, "key 0x{key:02X} round-trip failed");
        }
    }

    #[test]
    fn match_5var_boolean_pure_v_and_negation() {
        // f = v (variable 4) → f0 = 0x0000, f1 = 0xFFFF.
        let key = 0xFFFF_0000u32; // f1 in upper half
        let m = match_5var_boolean(key).expect("v should match");
        assert!(matches!(m.kind, Kind::Variable(4)));

        // f = ~v → f0 = 0xFFFF, f1 = 0x0000.
        let key = 0x0000_FFFFu32;
        let m = match_5var_boolean(key).expect("~v should match");
        assert!(matches!(m.kind, Kind::Not));
    }

    #[test]
    fn match_6var_boolean_pure_u() {
        // f = u (variable 5) → f0 = 0, f1 = 0xFFFFFFFF.
        let key = 0xFFFF_FFFF_0000_0000u64;
        let m = match_6var_boolean(key).expect("u should match");
        assert!(matches!(m.kind, Kind::Variable(5)));
    }

    #[test]
    fn full_2var_boolean_table_round_trips() {
        // For every 4-bit key in 0x1..=0xE, the matched expression's
        // own signature (evaluated at bitwidth=1 so values clip to
        // `{0, 1}`) must equal the key.
        for key in 0x1u8..=0xE {
            let m = match_2var_boolean(key).expect("non-constant key should match");
            let sig = sig_of(&m, 2, 1);
            let recovered = pack_bool_sig(&sig) as u8;
            assert_eq!(recovered, key, "key 0x{key:X} round-trip failed");
        }
    }

    #[test]
    fn two_var_pattern_sum_recovers_add_from_and_or() {
        // (x & y) + (x | y) has sig = [0, 1, 1, 2] — three distinct
        // values, so the scaled-boolean arm misses. The pattern-sum
        // combinator should pick up 1*(x & y) + 1*(x | y), equivalent
        // to x + y at full width.
        let original = Expr::add(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::or(Expr::variable(0), Expr::variable(1)),
        );
        let sig = sig_of(&original, 2, 64);
        let baseline = compute_cost(&original).cost;
        let eval = cobra_core::evaluator::Evaluator::from_expr(&original, 64);
        let m = try_simplify_two_var_pattern_sum(&sig, 64, baseline, |cand| {
            crate::spot_check::full_width_check_eval(
                &eval,
                2,
                cand,
                64,
                crate::spot_check::DEFAULT_NUM_SAMPLES,
            )
            .passed
        })
        .expect("two-var pattern-sum should recover an equivalent");
        // Resulting expression evaluated on the Boolean signature must
        // match the original's sig.
        assert_eq!(sig_of(&m, 2, 64), sig);
        // Cost must strictly improve over the baseline.
        assert!(is_better(&compute_cost(&m).cost, &baseline));
    }

    #[test]
    fn two_var_pattern_sum_refuses_when_verify_rejects() {
        // Same input, but verify always returns false — no candidate
        // should survive the gate.
        let sig = vec![0, 1, 1, 2];
        let baseline = ExprCost {
            weighted_size: 100,
            nonlinear_mul_count: 0,
            max_depth: 10,
        };
        let m = try_simplify_two_var_pattern_sum(&sig, 64, baseline, |_| false);
        assert!(m.is_none());
    }

    #[test]
    fn two_var_pattern_sum_misses_when_baseline_already_cheaper() {
        // Baseline is as cheap as it gets (size 1), so no candidate can
        // beat it — even if the signature happens to match.
        let sig = vec![0, 1, 1, 2];
        let baseline = ExprCost {
            weighted_size: 1,
            nonlinear_mul_count: 0,
            max_depth: 1,
        };
        let m = try_simplify_two_var_pattern_sum(&sig, 64, baseline, |_| true);
        assert!(m.is_none());
    }

    #[test]
    fn simplify_pattern_subtrees_rewrites_and_plus_or_to_add() {
        // (x & y) + (x | y) — the canonical README MBA example. After
        // `simplify_pattern_subtrees` this must collapse to something
        // whose full-width signature at bitwidth 64 matches `x + y`.
        let input = Expr::add(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::or(Expr::variable(0), Expr::variable(1)),
        );
        let rewritten = simplify_pattern_subtrees(input.clone_tree(), 64);
        // Strict cost improvement.
        assert!(is_better(
            &compute_cost(&rewritten).cost,
            &compute_cost(&input).cost
        ));
        // Full-width equivalence to x + y.
        let eval_input = cobra_core::evaluator::Evaluator::from_expr(&input, 64);
        let check = crate::spot_check::full_width_check_eval(
            &eval_input,
            2,
            &rewritten,
            64,
            crate::spot_check::DEFAULT_NUM_SAMPLES,
        );
        assert!(check.passed);
    }

    #[test]
    fn simplify_pattern_subtrees_leaves_leaf_expressions_alone() {
        // A raw variable has weighted_size == 1 → baseline guard hits,
        // no rewrite attempted.
        let input = Expr::variable(0);
        let out = simplify_pattern_subtrees(input.clone_tree(), 64);
        assert!(matches!(out.kind, Kind::Variable(0)));
    }

    #[test]
    fn non_matching_signatures_return_none() {
        // 3-var non-boolean Sig with three distinct values — falls through
        // every arm (boolean tables and scaled-boolean both reject it).
        assert!(match_pattern(&[0, 1, 2, 3, 4, 5, 6, 7], 3, 64).is_none());
        // 7-var problem — beyond the current dispatch table.
        let sig: Vec<u64> = (0..128).map(|i| (i & 1) as u64).collect();
        assert!(match_pattern(&sig, 7, 64).is_none());
    }
}
