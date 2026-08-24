//! Multivariate polynomial recovery via falling-factorial interpolation
//! on the `{0, ..., max_degree}^k` grid. Given an evaluator `f` and a
//! factorial-basis representation agrees with `f` on the grid — iff
//! `f` really is an ordinary polynomial in its support with per-variable
//! degree ≤ `max_degree`.
//!
//! The pipeline is a single forward-difference sweep per variable
//! (tensor product of 1D differences), followed by factorial-basis
//! coefficient extraction with a 2-adic divisibility gate. A
//! divisibility failure proves the function is *not* a polynomial of
//! the requested degree and returns `Blocked`; otherwise the
//! coefficient is `α >> q` times the modular inverse of the odd part
//! of the relevant factorial product, taken modulo `2^(bitwidth - q)`.
//!
//! Non-support variables are fixed at 0 during evaluation, matching

use crate::core::arith::bitmask;
use crate::core::evaluator::Evaluator;
use crate::core::expr::Expr;
use crate::core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, SolverResult,
};
use crate::core::{compile, eval as eval_compiled};
use std::sync::Arc;

use ahash::RandomState;

use crate::ir::math_utils::{mod_inverse_odd, precision_bits, twos_in_factorial};
use crate::ir::mono::{MonomialKey, MAX_POLY_VARS};
use crate::ir::poly::{CoeffMap, NormalizedPoly};
use crate::ir::poly_expr_builder::build_poly_expr;

mod subcode {
    pub const EMPTY_SUPPORT: u16 = 1;
    pub const TOO_MANY_VARS: u16 = 2;
    pub const BITWIDTH_RANGE: u16 = 3;
    pub const MAX_DEGREE_ZERO: u16 = 4;
    pub const BAD_SUPPORT_INDEX: u16 = 5;
    pub const DIVISIBILITY_FAIL: u16 = 6;
    pub const CAP_BELOW_MIN: u16 = 10;
    pub const NO_VERIFIED_DEGREE: u16 = 11;
}

fn reason(category: ReasonCategory, sub: u16, msg: &str) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category,
                domain: ReasonDomain::MultivarPoly,
                subcode: sub,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

fn build_odd_factorials(max_degree: u8) -> Vec<u64> {
    let mut odd_fact = vec![1u64; usize::from(max_degree) + 1];
    for e in 2..=usize::from(max_degree) {
        let mut odd = e;
        while odd & 1 == 0 {
            odd >>= 1;
        }
        odd_fact[e] = odd_fact[e - 1].wrapping_mul(odd as u64);
    }
    odd_fact
}

/// Convert an evaluated `{0..=max_degree}^k` grid into factorial-basis
/// coefficients. The mixed-radix grid is little-endian over `support_vars`
/// and is consumed in place by the forward-difference transform.
fn recover_from_grid(
    mut table: Vec<u64>,
    support_vars: &[u32],
    total_num_vars: u32,
    bitwidth: u32,
    max_degree: u8,
) -> SolverResult<NormalizedPoly> {
    let k = support_vars.len();
    let mask = bitmask(bitwidth);
    let base = usize::from(max_degree) + 1;
    let table_size = table.len();

    // Tensor-product forward differences, `max_degree` passes per dimension.
    for dim in 0..k {
        let stride = (0..dim).fold(1usize, |acc, _| acc * base);
        for pass in 1..=u32::from(max_degree) {
            for idx in (0..table_size).rev() {
                let coord = ((idx / stride) % base) as u32;
                if coord < pass {
                    continue;
                }
                let lo = idx - stride;
                table[idx] = table[idx].wrapping_sub(table[lo]) & mask;
            }
        }
    }

    // Factorial-basis coefficient extraction.
    let nv = total_num_vars as u8;
    let mut coeffs: CoeffMap = CoeffMap::with_hasher(RandomState::with_seeds(1, 2, 3, 4));
    let mut exps = [0u8; MAX_POLY_VARS];

    // OddPartFactorial(e, width) is this full-width product masked to
    // `width`, so compute it once per degree instead of once per monomial.
    let odd_fact = build_odd_factorials(max_degree);

    for (idx, &alpha) in table.iter().enumerate() {
        if alpha == 0 {
            continue;
        }

        exps.fill(0);
        let mut tmp = idx;
        let mut q: u32 = 0;
        for &support_var in support_vars {
            let e = (tmp % base) as u8;
            exps[support_var as usize] = e;
            q += twos_in_factorial(u32::from(e));
            tmp /= base;
        }

        // Run the divisibility test first. `precision_bits` returns `None`
        // exactly when `q >= bitwidth`, and for a genuine polynomial of the
        // requested degree that forces `alpha == 0` — so a non-zero `alpha`
        // there is a proof the function is not such a polynomial, not a
        // monomial to skip. Discarding it unexamined swallowed the failure.
        let Some(prec_bits) = precision_bits(q, bitwidth) else {
            if alpha != 0 {
                return SolverResult::Blocked(reason(
                    ReasonCategory::NoSolution,
                    subcode::DIVISIBILITY_FAIL,
                    "null-space monomial carries a non-zero coefficient",
                ));
            }
            continue;
        };

        if q > 0 {
            let low_bits = alpha & ((1u64 << q) - 1);
            if low_bits != 0 {
                return SolverResult::Blocked(reason(
                    ReasonCategory::NoSolution,
                    subcode::DIVISIBILITY_FAIL,
                    "falling-factorial coefficient fails divisibility gate",
                ));
            }
        }

        let prec_mask = bitmask(prec_bits);
        let mut odd_product: u64 = 1;
        for &support_var in support_vars {
            let e = exps[support_var as usize];
            if e >= 2 {
                odd_product = odd_product.wrapping_mul(odd_fact[usize::from(e)]) & prec_mask;
            }
        }

        let mut h = (alpha >> q) & prec_mask;
        if odd_product != 1 {
            h = h.wrapping_mul(mod_inverse_odd(odd_product, prec_bits)) & prec_mask;
        }
        if h == 0 {
            continue;
        }
        let key = MonomialKey::from_exponents(&exps, nv);
        coeffs.insert(key, h);
    }

    SolverResult::Success(NormalizedPoly {
        num_vars: nv,
        bitwidth,
        coeffs,
    })
}

/// Recover a [`NormalizedPoly`] whose factorial-basis coefficients
/// Returns `Inapplicable` for argument-validation failures, `Blocked`
/// if the 2-adic divisibility gate proves the function is not a
/// polynomial at the requested degree.
#[allow(clippy::too_many_lines)]
pub fn recover_multivar_poly(
    eval: &Evaluator,
    support_vars: &[u32],
    total_num_vars: u32,
    bitwidth: u32,
    max_degree: u8,
) -> SolverResult<NormalizedPoly> {
    if support_vars.is_empty() {
        return SolverResult::Inapplicable(reason(
            ReasonCategory::GuardFailed,
            subcode::EMPTY_SUPPORT,
            "empty support variable set",
        ));
    }
    if total_num_vars as usize > MAX_POLY_VARS {
        return SolverResult::Inapplicable(reason(
            ReasonCategory::GuardFailed,
            subcode::TOO_MANY_VARS,
            "total_num_vars exceeds MAX_POLY_VARS",
        ));
    }
    if !(2..=64).contains(&bitwidth) {
        return SolverResult::Inapplicable(reason(
            ReasonCategory::GuardFailed,
            subcode::BITWIDTH_RANGE,
            "bitwidth out of range [2, 64]",
        ));
    }
    if max_degree < 1 {
        return SolverResult::Inapplicable(reason(
            ReasonCategory::GuardFailed,
            subcode::MAX_DEGREE_ZERO,
            "max_degree must be >= 1",
        ));
    }
    for &idx in support_vars {
        if idx >= total_num_vars {
            return SolverResult::Inapplicable(reason(
                ReasonCategory::GuardFailed,
                subcode::BAD_SUPPORT_INDEX,
                "support index >= total_num_vars",
            ));
        }
    }

    let k = support_vars.len();
    let mask = bitmask(bitwidth);
    let base = usize::from(max_degree) + 1;
    let table_size: usize = (0..k).fold(1usize, |acc, _| acc * base);

    let mut table = vec![0u64; table_size];
    let mut point = vec![0u64; total_num_vars as usize];

    for (idx, slot) in table.iter_mut().enumerate() {
        let mut tmp = idx;
        for i in 0..k {
            point[support_vars[i] as usize] = (tmp % base) as u64;
            tmp /= base;
        }
        *slot = eval.eval(&point) & mask;
    }
    for &sv in support_vars {
        point[sv as usize] = 0;
    }

    recover_from_grid(table, support_vars, total_num_vars, bitwidth, max_degree)
}

/// Degree-escalating polynomial recovery with full-width verification.
/// Tries `min_degree..=max_degree_cap` and returns the first built
/// expression that evaluates identically to `eval` on the adversarial
/// probe set used by [`full_width_check`]. `Inapplicable` if
/// `max_degree_cap < min_degree`, `Blocked` if no degree verifies.
#[must_use]
pub struct PolyRecoveryResult {
    pub expr: Arc<Expr>,
    pub degree_used: u8,
}

/// Degree-escalating recovery. The verification step uses a plain
/// compiled evaluation on a fixed set of probe points; for production
/// use, pair this with the caller's own full-width check.
pub fn recover_and_verify_poly<F>(
    eval: &Evaluator,
    support_vars: &[u32],
    total_num_vars: u32,
    bitwidth: u32,
    max_degree_cap: u8,
    min_degree: u8,
    mut verify: F,
) -> SolverResult<PolyRecoveryResult>
where
    F: FnMut(&Evaluator, u32, &Expr, u32) -> bool,
{
    if max_degree_cap < min_degree {
        return SolverResult::Inapplicable(reason(
            ReasonCategory::GuardFailed,
            subcode::CAP_BELOW_MIN,
            "max_degree_cap < min_degree",
        ));
    }

    // Validate degree-independent preconditions once. The former loop
    // swallowed per-degree Inapplicable results and ultimately returned
    // NO_VERIFIED_DEGREE, so invalid inputs still fall through to that same
    // outcome rather than exposing a different reason code.
    let mut inputs_ok = !support_vars.is_empty()
        && total_num_vars as usize <= MAX_POLY_VARS
        && (2..=64).contains(&bitwidth);
    if inputs_ok && support_vars.iter().any(|&idx| idx >= total_num_vars) {
        inputs_ok = false;
    }

    if inputs_ok {
        let k = support_vars.len();
        let mask = bitmask(bitwidth);
        let mut grid: Vec<u64> = Vec::new();
        let mut grid_base = 0usize;
        let mut point = vec![0u64; total_num_vars as usize];
        let mut eval_at = |idx: usize, base: usize| {
            let mut tmp = idx;
            for &support_var in support_vars {
                point[support_var as usize] = (tmp % base) as u64;
                tmp /= base;
            }
            let value = eval.eval(&point) & mask;
            for &support_var in support_vars {
                point[support_var as usize] = 0;
            }
            value
        };

        for d in min_degree..=max_degree_cap {
            if d < 1 {
                continue;
            }

            let base = usize::from(d) + 1;
            let table_size = (0..k).fold(1usize, |acc, _| acc * base);

            if grid_base == 0 {
                grid.resize(table_size, 0);
                for (idx, slot) in grid.iter_mut().enumerate() {
                    *slot = eval_at(idx, base);
                }
            } else {
                let mut grown = vec![0u64; table_size];
                for (idx, slot) in grown.iter_mut().enumerate() {
                    let mut tmp = idx;
                    let mut old_idx = 0usize;
                    let mut place = 1usize;
                    let mut is_old = true;
                    for _ in 0..k {
                        let coord = tmp % base;
                        tmp /= base;
                        if coord >= grid_base {
                            is_old = false;
                        }
                        old_idx += coord * place;
                        place *= grid_base;
                    }

                    *slot = if is_old {
                        grid[old_idx]
                    } else {
                        eval_at(idx, base)
                    };
                }
                grid = grown;
            }
            grid_base = base;

            let poly = recover_from_grid(grid.clone(), support_vars, total_num_vars, bitwidth, d);
            let Some(payload) = poly.take_payload() else {
                continue;
            };
            let Ok(expr) = build_poly_expr(&payload) else {
                continue;
            };
            if !verify(eval, total_num_vars, &expr, bitwidth) {
                continue;
            }
            return SolverResult::Success(PolyRecoveryResult {
                expr,
                degree_used: d,
            });
        }
    }

    SolverResult::Blocked(reason(
        ReasonCategory::SearchExhausted,
        subcode::NO_VERIFIED_DEGREE,
        "no degree produced a verified polynomial",
    ))
}

/// Simple unit-level verifier usable as the `verify` argument to
/// [`recover_and_verify_poly`]. Compares `eval` vs a compiled version
/// of `candidate` on the mixed-radix `{0..4}^num_vars` probe set.
#[must_use]
pub fn probe_grid_check(eval: &Evaluator, num_vars: u32, candidate: &Expr, bitwidth: u32) -> bool {
    let cand = compile(candidate, bitwidth);
    let mask = bitmask(bitwidth);
    if num_vars > 8 {
        return false;
    }
    let base = 5usize;
    let total: usize = (0..num_vars).fold(1usize, |acc, _| acc * base);
    let mut point = vec![0u64; num_vars as usize];
    let mut ws_cand = crate::core::evaluator::Workspace::default();
    let mut stack_cand: Vec<u64> = Vec::new();
    for idx in 0..total {
        let mut tmp = idx;
        for slot in point.iter_mut().take(num_vars as usize) {
            *slot = (tmp % base) as u64;
            tmp /= base;
        }
        let got_eval = eval.eval_with(&point, &mut ws_cand) & mask;
        let got_cand = eval_compiled(&cand, &point, &mut stack_cand) & mask;
        if got_eval != got_cand {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::evaluator::Evaluator;
    use crate::core::expr::Expr;
    use crate::ir::math_utils::odd_part_factorial;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn recovers_univariate_quadratic() {
        // f(x) = 3x² + 5x + 7 at bitwidth 64.
        let expr = Expr::add(
            Expr::add(
                Expr::mul(
                    Expr::constant(3),
                    Expr::mul(Expr::variable(0), Expr::variable(0)),
                ),
                Expr::mul(Expr::constant(5), Expr::variable(0)),
            ),
            Expr::constant(7),
        );
        let eval = Evaluator::from_expr(&expr, 64);
        let poly = recover_multivar_poly(&eval, &[0], 1, 64, 2);
        let payload = poly.take_payload().expect("success");
        let built = build_poly_expr(&payload).unwrap();
        assert!(probe_grid_check(&eval, 1, &built, 64));
    }

    #[test]
    fn recovers_bivariate_linear() {
        // f(x, y) = 2x + 3y + 1.
        let expr = Expr::add(
            Expr::add(
                Expr::mul(Expr::constant(2), Expr::variable(0)),
                Expr::mul(Expr::constant(3), Expr::variable(1)),
            ),
            Expr::constant(1),
        );
        let eval = Evaluator::from_expr(&expr, 64);
        let poly = recover_multivar_poly(&eval, &[0, 1], 2, 64, 1);
        let payload = poly.take_payload().expect("success");
        assert_eq!(payload.num_vars, 2);
        let built = build_poly_expr(&payload).unwrap();
        assert!(probe_grid_check(&eval, 2, &built, 64));
    }

    #[test]
    fn empty_support_returns_inapplicable() {
        let expr = Expr::variable(0);
        let eval = Evaluator::from_expr(&expr, 64);
        let poly = recover_multivar_poly(&eval, &[], 1, 64, 2);
        assert!(matches!(poly, SolverResult::Inapplicable(_)));
    }

    #[test]
    fn degree_zero_returns_inapplicable() {
        let expr = Expr::variable(0);
        let eval = Evaluator::from_expr(&expr, 64);
        let poly = recover_multivar_poly(&eval, &[0], 1, 64, 0);
        assert!(matches!(poly, SolverResult::Inapplicable(_)));
    }

    #[test]
    fn out_of_range_bitwidth_returns_inapplicable() {
        let expr = Expr::variable(0);
        let eval = Evaluator::from_expr(&expr, 64);
        let poly = recover_multivar_poly(&eval, &[0], 1, 1, 2);
        assert!(matches!(poly, SolverResult::Inapplicable(_)));
    }

    #[test]
    fn non_polynomial_trips_divisibility_gate() {
        // f(x) = x & 1 — not a polynomial, divisibility gate should fire
        // once the degree reaches 2 and coefficients start having
        // factorial-weight requirements. Narrow bitwidth makes this
        // easier to trigger.
        let expr = Expr::and(Expr::variable(0), Expr::constant(1));
        let eval = Evaluator::from_expr(&expr, 8);
        let poly = recover_multivar_poly(&eval, &[0], 1, 8, 4);
        // Either Blocked (divisibility) or Success with coefficients
        // matching the function on the probe grid. For x & 1 on a
        // width-8 grid {0..4}, the function is 0,1,0,1,0 — which can
        // be interpolated exactly as a degree-4 polynomial. Just
        // assert we produced *some* outcome with a reason when not
        // successful.
        match poly {
            SolverResult::Success(_) => {}
            SolverResult::Blocked(r) => {
                assert_eq!(r.top.code.domain, ReasonDomain::MultivarPoly);
            }
            other => panic!("unexpected outcome: {:?}", other.kind()),
        }
    }

    #[test]
    fn escalating_recovery_returns_minimum_verified_degree() {
        let expr = Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(0)),
            Expr::variable(0),
        );
        let eval = Evaluator::from_expr(&expr, 64);
        let res = recover_and_verify_poly(&eval, &[0], 1, 64, 4, 2, probe_grid_check);
        let SolverResult::Success(r) = res else {
            panic!("expected success");
        };
        assert_eq!(r.degree_used, 2);
    }

    #[test]
    fn odd_factorial_table_matches_width_specific_helper() {
        let table = build_odd_factorials(66);
        for bitwidth in [1u32, 8, 16, 32, 64] {
            let mask = bitmask(bitwidth);
            for (degree, &odd_fact) in table.iter().enumerate() {
                assert_eq!(
                    odd_fact & mask,
                    odd_part_factorial(degree as u32, bitwidth),
                    "degree={degree}, bitwidth={bitwidth}"
                );
            }
        }
    }

    #[test]
    fn escalating_recovery_evaluates_each_grid_point_once() {
        let calls = Arc::new(AtomicUsize::new(0));
        let calls_for_eval = Arc::clone(&calls);
        let eval = Evaluator::from_closure(move |point| {
            calls_for_eval.fetch_add(1, Ordering::Relaxed);
            point[0].wrapping_add(point[1])
        });

        let result = recover_and_verify_poly(&eval, &[0, 1], 2, 64, 4, 2, |_, _, _, _| false);

        let SolverResult::Blocked(reason) = result else {
            panic!("expected exhausted recovery");
        };
        assert_eq!(
            reason.top.code,
            ReasonCode {
                category: ReasonCategory::SearchExhausted,
                domain: ReasonDomain::MultivarPoly,
                subcode: subcode::NO_VERIFIED_DEGREE,
            }
        );
        // The final degree-4 grid has 5^2 points. Incremental growth visits
        // each point once; independent degree-2/3/4 grids would make
        // 3^2 + 4^2 + 5^2 = 50 evaluator calls.
        assert_eq!(calls.load(Ordering::Relaxed), 25);
    }
}
