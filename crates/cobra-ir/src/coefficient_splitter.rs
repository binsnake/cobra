//! Split `CoB` (AND-monomial) coefficients into an AND-part and a
//! MUL-part by probing the original evaluator at structured non-binary
//! points.
//!
//! At the Boolean corners `{0, 1}^n`, AND and MUL agree — so a `CoB`
//! coefficient alone cannot distinguish them. Evaluating at `P_m`,
//! where every variable in `m` is set to 2 and the rest to 0, breaks
//! the symmetry: `MUL_s(P_m)` grows as `2^|s|` while `AND_s(P_m)` stays
//! at 2.
//!
//! The splitter walks masks bottom-up by popcount. For each `m`, it
//! compares `f(P_m)` against the AND-only prediction `g(P_m)` (which
//! accumulates the already-split contributions of all strict submasks
//! of `m`); the residue is fed through a Hensel-lifted modular inverse
//! to extract the MUL coefficient. An odd residue means the evaluator
//! doesn't follow the `CoB` model — we fall back to treating that mask
//! as pure AND.
//!
//! When `singleton_at_2` is provided (one entry per variable, giving
//! the evaluation of the per-variable singleton polynomial at t=2),
//! singleton masks (popcount=1) are skipped entirely: their
//! contribution is modelled externally by the singleton-power path.

use cobra_core::arith::bitmask;
use cobra_core::evaluator::Evaluator;

/// `x^{-1} mod 2^{w-1}` for odd `x`. Hensel lifting, doubling correct
/// bits per iteration starting from the 3-bit base case
/// `x² ≡ 1 (mod 8)`.
#[must_use]
pub fn mod_inverse_odd_half(x: u64, w: u32) -> u64 {
    assert!(w >= 2, "w must be >= 2");
    assert!(x & 1 == 1, "x must be odd");

    let target_bits = w - 1;
    let mod_mask: u64 = if target_bits >= 64 {
        u64::MAX
    } else {
        (1u64 << target_bits) - 1
    };

    let mut inv = x & mod_mask;
    let mut bits: u32 = 3;
    while bits < target_bits {
        let two_minus_xi = 2u64.wrapping_sub(x.wrapping_mul(inv));
        inv = inv.wrapping_mul(two_minus_xi) & mod_mask;
        bits = bits.wrapping_mul(2);
    }
    inv & mod_mask
}

pub struct SplitResult {
    pub and_coeffs: Vec<u64>,
    pub mul_coeffs: Vec<u64>,
}

fn correction_factor(popcount: u32, bitwidth: u32) -> u64 {
    let deg = if popcount == 1 { 2 } else { popcount };
    if deg >= bitwidth {
        0
    } else {
        1u64 << deg
    }
}

/// Sum of contributions from all non-empty submasks of `active_mask`
/// at probe point `P_{active_mask}`. Used as the reference against
/// which a new mask's MUL contribution is extracted.
fn eval_known_contribution(
    and_coeffs: &[u64],
    mul_coeffs: &[u64],
    active_mask: u64,
    bitwidth: u32,
    singleton_at_2: &[u64],
) -> u64 {
    let mask = bitmask(bitwidth);
    let mut g = and_coeffs[0] & mask;

    let mut s = active_mask;
    while s != 0 {
        let popcount = s.count_ones();
        if popcount == 1 && !singleton_at_2.is_empty() {
            let bit = s.trailing_zeros();
            g = g.wrapping_add(singleton_at_2[bit as usize]) & mask;
        } else {
            let and_val: u64 = 2;
            let mul_val = correction_factor(popcount, bitwidth);
            let contribution = and_val
                .wrapping_mul(and_coeffs[s as usize])
                .wrapping_add(mul_val.wrapping_mul(mul_coeffs[s as usize]));
            g = g.wrapping_add(contribution) & mask;
        }
        if s == 0 {
            break;
        }
        s = s.wrapping_sub(1) & active_mask;
        if s == active_mask {
            // next iteration would repeat the full mask; we've enumerated
            // every non-empty submask.
            break;
        }
    }
    g
}

/// Deterministic coefficient splitting. `cob` is the AND-monomial
/// coefficient vector from [`crate::interpolate_coefficients`];
/// `singleton_at_2` is optional and, when present, must have length
/// `num_vars`.
#[must_use]
pub fn split_coefficients(
    cob: &[u64],
    eval: &Evaluator,
    num_vars: u32,
    bitwidth: u32,
    singleton_at_2: &[u64],
) -> SplitResult {
    assert!(bitwidth >= 2, "bitwidth must be >= 2");
    let len = 1usize << num_vars;
    assert_eq!(cob.len(), len, "cob length must be 2^num_vars");
    assert!(
        singleton_at_2.is_empty() || singleton_at_2.len() == num_vars as usize,
        "singleton_at_2 must be empty or length num_vars"
    );

    let mask = bitmask(bitwidth);
    let half_mod = bitmask(bitwidth - 1);

    let mut and_coeffs = cob.to_vec();
    let mut mul_coeffs = vec![0u64; len];

    let max_deg = num_vars.max(2);
    let mut odd_inverses = vec![0u64; (max_deg + 1) as usize];
    for d in 2..=max_deg {
        let u = (1u64 << (d - 1)) - 1;
        odd_inverses[d as usize] = mod_inverse_odd_half(u, bitwidth);
    }

    let mut point = vec![0u64; num_vars as usize];
    for k in 1..=num_vars {
        if k == 1 && !singleton_at_2.is_empty() {
            continue;
        }
        for m in 0..len {
            if (m as u64).count_ones() != k {
                continue;
            }
            if cob[m] == 0 {
                continue;
            }
            let deg = if k < 2 { 2 } else { k };

            for (v, slot) in point.iter_mut().enumerate().take(num_vars as usize) {
                *slot = if (m & (1usize << v)) != 0 { 2 } else { 0 };
            }

            let f = eval.eval(&point) & mask;
            let g = eval_known_contribution(
                &and_coeffs,
                &mul_coeffs,
                m as u64,
                bitwidth,
                singleton_at_2,
            );
            let diff = f.wrapping_sub(g) & mask;
            if diff == 0 {
                continue;
            }
            if diff & 1 != 0 {
                continue;
            }

            let mul_coeff = (diff >> 1).wrapping_mul(odd_inverses[deg as usize]) & half_mod;
            mul_coeffs[m] = mul_coeff;
            and_coeffs[m] = cob[m].wrapping_sub(mul_coeff) & mask;
        }
    }

    if !singleton_at_2.is_empty() {
        for i in 0..num_vars as usize {
            and_coeffs[1usize << i] = 0;
            mul_coeffs[1usize << i] = 0;
        }
    }

    SplitResult {
        and_coeffs,
        mul_coeffs,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::expr::Expr;

    #[test]
    fn mod_inverse_odd_half_matches_hand_computation() {
        // At w = 8: modulus = 128. x = 3, inv should satisfy 3*inv ≡ 1 (mod 128).
        let inv = mod_inverse_odd_half(3, 8);
        assert_eq!((3u64.wrapping_mul(inv)) & 0x7F, 1);
    }

    #[test]
    fn mod_inverse_odd_half_full_width() {
        let inv = mod_inverse_odd_half(7, 64);
        let half_mod: u64 = (1u64 << 63) - 1;
        assert_eq!((7u64.wrapping_mul(inv)) & half_mod, 1);
    }

    #[test]
    fn pure_and_expression_keeps_mul_zero() {
        // f = x & y — on Boolean corners the `CoB` coefficient at m=11 is 1.
        // At P_{11} = (2, 2), f = 2 & 2 = 2. Prediction from AND model: 2*and[11] = 2. Match → no MUL.
        let expr = Expr::and(Expr::variable(0), Expr::variable(1));
        let eval = Evaluator::from_expr(&expr, 64);
        let cob = vec![0u64, 0, 0, 1];
        let r = split_coefficients(&cob, &eval, 2, 64, &[]);
        assert_eq!(r.mul_coeffs, vec![0u64, 0, 0, 0]);
        assert_eq!(r.and_coeffs, vec![0u64, 0, 0, 1]);
    }

    #[test]
    fn pure_mul_expression_splits_into_mul_coeff() {
        // f = x * y — at P_{11} = (2, 2), f = 4, while AND-only prediction = 2.
        // Diff = 2, halved → 1, multiplied by odd_inverse for deg=2 → MUL coeff = 1.
        let expr = Expr::mul(Expr::variable(0), Expr::variable(1));
        let eval = Evaluator::from_expr(&expr, 64);
        let cob = vec![0u64, 0, 0, 1]; // `CoB` treats x*y same as x&y on {0,1}
        let r = split_coefficients(&cob, &eval, 2, 64, &[]);
        assert_eq!(r.mul_coeffs[3], 1);
        assert_eq!(r.and_coeffs[3], 0);
    }

    #[test]
    fn singleton_at_2_zeroes_singleton_outputs() {
        // f = x - we populate singleton_at_2[0] = 2 to mimic the external
        // singleton-power model. Singleton mask 1 must be zeroed in output.
        let expr = Expr::variable(0);
        let eval = Evaluator::from_expr(&expr, 64);
        let cob = vec![0u64, 1];
        let r = split_coefficients(&cob, &eval, 1, 64, &[2]);
        assert_eq!(r.and_coeffs[1], 0);
        assert_eq!(r.mul_coeffs[1], 0);
    }

    #[test]
    fn three_var_mixed_expression() {
        // f = x*y + z — at P_{111} = (2, 2, 2): f = 4 + 2 = 6.
        let expr = Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        let eval = Evaluator::from_expr(&expr, 64);
        // `CoB` for x*y + z: [0, 0, 0, 1, 1, 0, 0, 0]
        let cob = vec![0u64, 0, 0, 1, 1, 0, 0, 0];
        let r = split_coefficients(&cob, &eval, 3, 64, &[]);
        // mul[3] = 1 (xy), mul[4] = 0 (z is linear).
        assert_eq!(r.mul_coeffs[3], 1);
        assert_eq!(r.mul_coeffs[4], 0);
        assert_eq!(r.and_coeffs[3], 0);
        assert_eq!(r.and_coeffs[4], 1);
    }
}
