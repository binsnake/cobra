//! Per-variable univariate recovery. For each variable `v`, evaluates
//! the slice `g_v(t) = f(0, …, 0, t, 0, …, 0)` at `t = 0, 1, …, d-1`
//! where `d = degree_cap(bitwidth)`, then extracts the falling-factorial
//! coefficients via forward differences and a 2-adic divisibility gate.
//!
//! The per-variable polynomial lives at its own node in the arithmetic-
//! lowering pipeline: the outer solver assembles them with the bitwise
//! residual to form a full recovered expression.

use cobra_core::arith::bitmask;
use cobra_core::evaluator::Evaluator;
use cobra_core::result::{err, CobraError, Result};

use crate::math_utils::{degree_cap, mod_inverse_odd, odd_part_factorial, twos_in_factorial};
use crate::singleton_power::{SingletonPowerResult, UnivariateNormalizedPoly, UnivariateTerm};

#[derive(Copy, Clone)]
struct DegreeInfo {
    twos: u32,
    odd_inverse: u64,
    precision_bits: u32,
}

/// Recover the per-variable univariate factorial-basis coefficients.
/// Returns an error if `bitwidth` is out of range, or if the 2-adic
/// divisibility check fails for any variable (meaning that variable's
/// slice is not a genuine polynomial at the requested degree cap).
pub fn recover_singleton_powers(
    eval: &Evaluator,
    num_vars: u32,
    bitwidth: u32,
) -> Result<SingletonPowerResult> {
    if !(2..=64).contains(&bitwidth) {
        return Err(err(
            CobraError::NoReduction,
            format!("recover_singleton_powers: bitwidth must be 2..64, got {bitwidth}"),
        ));
    }

    let max_degree = degree_cap(bitwidth);
    let mask = bitmask(bitwidth);

    let info: Vec<DegreeInfo> = (0..max_degree)
        .map(|k| {
            if k == 0 {
                DegreeInfo {
                    twos: 0,
                    odd_inverse: 1,
                    precision_bits: bitwidth,
                }
            } else {
                let twos = twos_in_factorial(k);
                let prec = bitwidth - twos;
                let odd = odd_part_factorial(k, prec);
                DegreeInfo {
                    twos,
                    odd_inverse: mod_inverse_odd(odd, prec),
                    precision_bits: prec,
                }
            }
        })
        .collect();

    let mut result = SingletonPowerResult {
        num_vars,
        bitwidth,
        per_var: vec![
            UnivariateNormalizedPoly {
                bitwidth,
                terms: Vec::new()
            };
            num_vars as usize
        ],
    };

    let mut point = vec![0u64; num_vars as usize];
    let mut table = vec![0u64; max_degree as usize];

    for var in 0..num_vars as usize {
        for t in 0..max_degree {
            point[var] = u64::from(t);
            table[t as usize] = eval.eval(&point) & mask;
        }
        point[var] = 0;

        // In-place forward differences: `max_degree` passes, each shrinking
        // the live range by one from the right.
        for k in 1..max_degree {
            let mut t = max_degree - 1;
            while t >= k {
                let hi = table[t as usize];
                let lo = table[(t - 1) as usize];
                table[t as usize] = hi.wrapping_sub(lo) & mask;
                t -= 1;
            }
        }

        let mut terms: Vec<UnivariateTerm> = Vec::new();
        for k in 1..max_degree {
            let dk = table[k as usize];
            let v = info[k as usize].twos;

            if v > 0 && (dk & ((1u64 << v) - 1)) != 0 {
                return Err(err(
                    CobraError::NoReduction,
                    format!(
                        "singleton-power recovery failed: variable {var}, degree {k} — divisibility check failed"
                    ),
                ));
            }

            let shifted = dk >> v;
            let prec_mask = bitmask(info[k as usize].precision_bits);
            let factorial_coeff = shifted.wrapping_mul(info[k as usize].odd_inverse) & prec_mask;

            if factorial_coeff != 0 {
                terms.push(UnivariateTerm {
                    degree: u16::try_from(k).expect("degree fits in u16"),
                    coeff: factorial_coeff,
                });
            }
        }

        result.per_var[var].terms = terms;
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::expr::Expr;

    #[test]
    fn recovers_univariate_quadratic() {
        // f(x) = x² = x + x·(x-1) in falling-factorial basis (S₂(2,1)=1, S₂(2,2)=1).
        let expr = Expr::mul(Expr::variable(0), Expr::variable(0));
        let eval = Evaluator::from_expr(&expr, 64);
        let res = recover_singleton_powers(&eval, 1, 64).unwrap();
        assert_eq!(res.per_var[0].terms.len(), 2);
        // Both terms coefficient 1 (monomial x² = x^(1) + x^(2))
        assert!(res.per_var[0].terms.iter().all(|t| t.coeff == 1));
    }

    #[test]
    fn recovers_two_var_quadratic_slices() {
        // f(x, y) = x² + y. Per-variable: g_x(t) = t², g_y(t) = t.
        let expr = Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(0)),
            Expr::variable(1),
        );
        let eval = Evaluator::from_expr(&expr, 64);
        let res = recover_singleton_powers(&eval, 2, 64).unwrap();
        // x slice: two falling-factorial terms (x + x^(2)).
        assert_eq!(res.per_var[0].terms.len(), 2);
        // y slice: one linear term.
        assert_eq!(res.per_var[1].terms.len(), 1);
        assert_eq!(res.per_var[1].terms[0].degree, 1);
        assert_eq!(res.per_var[1].terms[0].coeff, 1);
    }

    #[test]
    fn rejects_out_of_range_bitwidth() {
        let expr = Expr::variable(0);
        let eval = Evaluator::from_expr(&expr, 64);
        assert!(recover_singleton_powers(&eval, 1, 1).is_err());
        assert!(recover_singleton_powers(&eval, 1, 65).is_err());
    }

    #[test]
    fn linear_has_one_term() {
        let expr = Expr::mul(Expr::constant(7), Expr::variable(0));
        let eval = Evaluator::from_expr(&expr, 64);
        let res = recover_singleton_powers(&eval, 1, 64).unwrap();
        assert_eq!(res.per_var[0].terms.len(), 1);
        assert_eq!(res.per_var[0].terms[0].degree, 1);
        assert_eq!(res.per_var[0].terms[0].coeff, 7);
    }
}
