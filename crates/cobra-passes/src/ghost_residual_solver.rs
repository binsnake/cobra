//! Solve a Boolean-null residual as `c * ghost(x_{i_1}, ..., x_{i_a})`
//! for some constant `c` and ghost primitive, discovered by probing
//! at a fixed mixed-parity probe bank and inferring the 2-adic
//! coefficient.
//!
//! The probe bank is deterministic — `SplitMix64`-style seeded
//! sequence — so a successful match at byte-for-byte parity with the
//! C++ implementation is guaranteed for identical residual evaluators.

use cobra_core::arith::bitmask;
use cobra_core::evaluator::Evaluator;
use cobra_core::expr::Expr;
use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, SolverResult,
};

use cobra_ir::mod_inverse_odd;
use cobra_ir::poly_expr_builder::build_poly_expr;

use crate::ghost_basis::{get_ghost_basis, GhostPrimitive};
use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};
use crate::weighted_poly_fit::{recover_weighted_poly, WeightFn};

pub struct GhostSolveResult {
    pub expr: Box<Expr>,
    pub primitives_used: Vec<&'static str>,
    pub num_terms: u8,
}

const NUM_PROBES: usize = 8;

#[derive(Copy, Clone, Default)]
struct ProbePoint {
    values: [u64; 6],
}

/// Fixed mixed-parity probe seeds — byte-for-byte match with the C++
/// `GhostResidualSolver` to keep coefficient-inference parity.
const PROBE_SEEDS: [u64; 48] = [
    3, 4, 7, 10, 13, 18, 23, 28, 37, 42, 51, 60, 71, 80, 97, 106, 5, 6, 11, 14, 19, 22, 29, 34, 41,
    50, 59, 66, 73, 82, 91, 100, 9, 12, 17, 20, 25, 30, 35, 40, 47, 56, 63, 70, 79, 86, 95, 102,
];

fn generate_probe_bank(num_vars: u32, bitwidth: u32) -> [ProbePoint; NUM_PROBES] {
    let mask = bitmask(bitwidth);
    let mut bank = [ProbePoint::default(); NUM_PROBES];
    for (p, probe) in bank.iter_mut().enumerate() {
        for v in 0..num_vars.min(6) {
            probe.values[v as usize] = PROBE_SEEDS[(p * 6) + v as usize] & mask;
        }
    }
    bank
}

fn next_combo(combo: &mut [u32], support_size: u32) -> bool {
    let arity = combo.len();
    for step in 0..arity {
        let i = arity - 1 - step;
        combo[i] += 1;
        if combo[i] <= support_size - arity as u32 + i as u32 {
            for j in (i + 1)..arity {
                combo[j] = combo[j - 1] + 1;
            }
            return true;
        }
    }
    false
}

/// Classify whether the residual is zero on every Boolean assignment
/// but nonzero on at least one mixed-parity probe.
#[must_use]
pub fn is_boolean_null_residual(
    residual_eval: &Evaluator,
    support: &[u32],
    num_vars: u32,
    bitwidth: u32,
    boolean_sig: &[u64],
) -> bool {
    if !boolean_sig.iter().all(|&v| v == 0) {
        return false;
    }
    let support_size = support.len() as u32;
    if support_size > 6 {
        return false;
    }
    let bank = generate_probe_bank(support_size, bitwidth);
    let mask = bitmask(bitwidth);
    let mut point = vec![0u64; num_vars as usize];
    for probe in &bank {
        for (v, &idx) in support.iter().enumerate() {
            point[idx as usize] = probe.values[v];
        }
        let val = residual_eval.eval(&point) & mask;
        for &idx in support {
            point[idx as usize] = 0;
        }
        if val != 0 {
            return true;
        }
    }
    false
}

fn reason(msg: &'static str, subcode: u16) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category: ReasonCategory::SearchExhausted,
                domain: ReasonDomain::GhostResidual,
                subcode,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

#[allow(clippy::too_many_lines)]
fn try_primitive(
    prim: &GhostPrimitive,
    residual_eval: &Evaluator,
    support: &[u32],
    num_vars: u32,
    bitwidth: u32,
    bank: &[ProbePoint; NUM_PROBES],
    r_vals: &[u64; NUM_PROBES],
) -> Option<GhostSolveResult> {
    let support_size = support.len() as u32;
    let mask = bitmask(bitwidth);
    if u32::from(prim.arity) > support_size {
        return None;
    }

    let mut combo: [u32; 6] = [0; 6];
    for i in 0..prim.arity {
        combo[i as usize] = u32::from(i);
    }

    loop {
        // Ghost evaluation at each probe point.
        let mut g_vals = [0u64; NUM_PROBES];
        let mut args = [0u64; 6];
        for (p, probe) in bank.iter().enumerate() {
            for a in 0..prim.arity {
                args[a as usize] = probe.values[combo[a as usize] as usize];
            }
            g_vals[p] = (prim.eval)(&args[..prim.arity as usize], bitwidth);
        }

        // 2-adic coefficient inference.
        let mut best_probe: Option<usize> = None;
        let mut best_t: u32 = bitwidth;
        let mut best_c: u64 = 0;
        let mut tuple_reject = false;

        for p in 0..NUM_PROBES {
            if g_vals[p] == 0 {
                continue;
            }
            let t = g_vals[p].trailing_zeros();
            if t > 0 && (r_vals[p] & ((1u64 << t) - 1)) != 0 {
                tuple_reject = true;
                break;
            }
            if t < best_t {
                best_t = t;
                let prec = bitwidth - t;
                if prec == 0 {
                    continue;
                }
                let g_odd = g_vals[p] >> t;
                let r_shifted = r_vals[p] >> t;
                let inv = mod_inverse_odd(g_odd, prec);
                let prec_mask = if prec >= 64 {
                    u64::MAX
                } else {
                    (1u64 << prec) - 1
                };
                best_c = r_shifted.wrapping_mul(inv) & prec_mask;
                best_probe = Some(p);
            }
        }

        if !tuple_reject && best_probe.is_some() {
            // Cross-check.
            let mut cross_ok = true;
            for p in 0..NUM_PROBES {
                let expected = best_c.wrapping_mul(g_vals[p]) & mask;
                if expected != r_vals[p] {
                    cross_ok = false;
                    break;
                }
            }
            if cross_ok {
                let mut var_indices = [0u32; 6];
                for a in 0..prim.arity {
                    var_indices[a as usize] = support[combo[a as usize] as usize];
                }
                let ghost_expr = (prim.build)(&var_indices[..prim.arity as usize]);
                let result_expr = if best_c == 1 {
                    ghost_expr
                } else {
                    Expr::mul(Expr::constant(best_c), ghost_expr)
                };
                let check = full_width_check_eval(
                    residual_eval,
                    num_vars,
                    &result_expr,
                    bitwidth,
                    DEFAULT_NUM_SAMPLES,
                );
                if check.passed {
                    return Some(GhostSolveResult {
                        expr: result_expr,
                        primitives_used: vec![prim.name],
                        num_terms: 1,
                    });
                }
            }
        }

        if !next_combo(&mut combo[..prim.arity as usize], support_size) {
            break;
        }
    }
    None
}

/// Attempt to solve a Boolean-null residual as `c * ghost(...)`.
pub fn solve_ghost_residual(
    residual_eval: &Evaluator,
    support: &[u32],
    num_vars: u32,
    bitwidth: u32,
) -> SolverResult<GhostSolveResult> {
    let mask = bitmask(bitwidth);
    let support_size = support.len() as u32;
    let bank = generate_probe_bank(support_size, bitwidth);

    let mut r_vals = [0u64; NUM_PROBES];
    let mut full = vec![0u64; num_vars as usize];
    for (p, probe) in bank.iter().enumerate() {
        for (v, &idx) in support.iter().enumerate() {
            full[idx as usize] = probe.values[v];
        }
        r_vals[p] = residual_eval.eval(&full) & mask;
        for &idx in support {
            full[idx as usize] = 0;
        }
    }

    for prim in get_ghost_basis() {
        if let Some(r) = try_primitive(
            prim,
            residual_eval,
            support,
            num_vars,
            bitwidth,
            &bank,
            &r_vals,
        ) {
            return SolverResult::Success(r);
        }
    }

    SolverResult::Blocked(reason("no single ghost primitive matched", 1))
}

/// Factored ghost residual solver. Tries to recover residual ≡ Q(x)·g(x)
/// for some polynomial Q and ghost primitive g, via the weighted
/// falling-factorial 2-adic solve.
pub fn solve_factored_ghost_residual(
    residual_eval: &Evaluator,
    support: &[u32],
    num_vars: u32,
    bitwidth: u32,
    max_degree: u8,
    grid_degree: u8,
) -> SolverResult<GhostSolveResult> {
    let support_size = support.len() as u32;
    for prim in get_ghost_basis() {
        if u32::from(prim.arity) > support_size {
            continue;
        }
        let mut combo: [u32; 6] = [0; 6];
        for i in 0..prim.arity {
            combo[i as usize] = u32::from(i);
        }
        let arity = prim.arity as usize;

        loop {
            let mut var_indices = [0u32; 6];
            for a in 0..arity {
                var_indices[a] = support[combo[a] as usize];
            }
            let combo_snapshot: [u32; 6] = combo;
            let prim_eval = prim.eval;
            let weight: WeightFn<'_> = Box::new(move |args: &[u64], bw: u32| {
                let mut ghost_args = [0u64; 6];
                for a in 0..arity {
                    ghost_args[a] = args[combo_snapshot[a] as usize];
                }
                prim_eval(&ghost_args[..arity], bw)
            });

            let fit = recover_weighted_poly(
                residual_eval,
                &weight,
                support,
                num_vars,
                bitwidth,
                max_degree,
                grid_degree,
            );
            if let SolverResult::Success(payload) = fit {
                if let Ok(q_expr) = build_poly_expr(&payload.poly) {
                    let g_expr = (prim.build)(&var_indices[..arity]);
                    let combined = Expr::mul(q_expr, g_expr);
                    let check = full_width_check_eval(
                        residual_eval,
                        num_vars,
                        &combined,
                        bitwidth,
                        DEFAULT_NUM_SAMPLES,
                    );
                    if check.passed {
                        return SolverResult::Success(GhostSolveResult {
                            expr: combined,
                            primitives_used: vec![prim.name],
                            num_terms: 1,
                        });
                    }
                }
            }

            if !next_combo(&mut combo[..arity], support_size) {
                break;
            }
        }
    }

    SolverResult::Blocked(reason("no factored ghost primitive matched", 2))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decomposition_helpers::build_remainder_evaluator;

    #[test]
    fn solves_single_mul_sub_and_residual() {
        // f = x*y; core = x&y. Residual = x*y - (x&y) = mul_sub_and(x,y).
        // Expect the solver to recover coefficient 1 and primitive mul_sub_and.
        let f = Expr::mul(Expr::variable(0), Expr::variable(1));
        let core = Expr::and(Expr::variable(0), Expr::variable(1));
        let eval = Evaluator::from_expr(&f, 64);
        let residual = build_remainder_evaluator(&eval, &core, 64);

        let SolverResult::Success(result) = solve_ghost_residual(&residual, &[0, 1], 2, 64) else {
            panic!("expected success");
        };
        assert_eq!(result.primitives_used, vec!["mul_sub_and"]);
        assert_eq!(result.num_terms, 1);
    }

    #[test]
    fn rejects_when_residual_not_ghost_shaped() {
        let f = Expr::and(Expr::variable(0), Expr::variable(1));
        let core = Expr::constant(0);
        let eval = Evaluator::from_expr(&f, 64);
        let residual = build_remainder_evaluator(&eval, &core, 64);
        let out = solve_ghost_residual(&residual, &[0, 1], 2, 64);
        assert!(matches!(out, SolverResult::Blocked(_)));
    }
}
