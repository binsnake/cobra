//! Build an `Expr` tree from a per-variable singleton-power
//! decomposition. For each variable, the univariate factorial-basis
//! polynomial is converted to monomial coefficients via signed
//! Stirling numbers of the first kind, then emitted as a balanced
//! Add-tree of `coeff * x^j` terms. Per-variable trees are then
//! combined into a single balanced Add-tree.
//!
//! Output is `None` if no variable contributes a non-zero monomial
//! (caller interprets `None` as "no singleton-power lift applicable").

use cobra_core::arith::bitmask;
use cobra_core::expr::Expr;
use cobra_core::expr_rewrite::apply_coefficient;

use cobra_ir::{SingletonPowerResult, UnivariateTerm};

/// Convert a factorial-basis univariate polynomial into its monomial
/// coefficient vector: `mono[j] = Σ h[k] * s(k, j)` where `s` is the
/// signed Stirling number of the first kind.
#[must_use]
pub fn factorial_to_monomial(terms: &[UnivariateTerm], bitwidth: u32) -> Vec<u64> {
    if terms.is_empty() {
        return Vec::new();
    }
    let d_max = terms.iter().map(|t| t.degree).max().unwrap_or(0);
    let mask = bitmask(bitwidth);

    let mut h = vec![0u64; usize::from(d_max) + 1];
    for t in terms {
        h[usize::from(t.degree)] = t.coeff;
    }

    let mut mono = vec![0u64; usize::from(d_max) + 1];
    let mut s_prev = vec![0u64; usize::from(d_max) + 1];
    let mut s_curr = vec![0u64; usize::from(d_max) + 1];
    s_prev[0] = 1;

    for k in 1..=d_max {
        s_curr.iter_mut().for_each(|v| *v = 0);
        let km1 = u64::from(k - 1);
        for j in 0..=k {
            let from_left = if j > 0 { s_prev[usize::from(j) - 1] } else { 0 };
            let from_diag = s_prev[usize::from(j)];
            s_curr[usize::from(j)] =
                from_left.wrapping_sub(km1.wrapping_mul(from_diag) & mask) & mask;
        }

        if h[usize::from(k)] != 0 {
            for j in 1..=k {
                mono[usize::from(j)] = mono[usize::from(j)]
                    .wrapping_add(h[usize::from(k)].wrapping_mul(s_curr[usize::from(j)]))
                    & mask;
            }
        }

        std::mem::swap(&mut s_prev, &mut s_curr);
    }

    mono
}

#[allow(clippy::vec_box)]
fn reduce_add_tree(mut terms: Vec<Box<Expr>>) -> Box<Expr> {
    while terms.len() > 1 {
        let mut next: Vec<Box<Expr>> = Vec::with_capacity(terms.len().div_ceil(2));
        let mut it = terms.into_iter();
        while let Some(a) = it.next() {
            match it.next() {
                Some(b) => next.push(Expr::add(a, b)),
                None => next.push(a),
            }
        }
        terms = next;
    }
    terms.pop().expect("at least one term")
}

/// Build a full singleton-power Expr tree, or `None` if no variable
/// contributes. Per-variable degrees are emitted as `coeff * x^j` with
/// `x^j` built as a left-leaning product chain.
#[must_use]
pub fn build_singleton_power_expr(powers: &SingletonPowerResult) -> Option<Box<Expr>> {
    let w = powers.bitwidth;
    let mut var_exprs: Vec<Box<Expr>> = Vec::new();

    for (i, uni) in powers.per_var.iter().enumerate() {
        if uni.terms.is_empty() {
            continue;
        }
        let mono = factorial_to_monomial(&uni.terms, w);

        let mut degree_exprs: Vec<Box<Expr>> = Vec::new();
        let mut power: Option<Box<Expr>> = None;
        for (j, &coeff) in mono.iter().enumerate().skip(1) {
            let var_expr = Expr::variable(i as u32);
            power = Some(match power {
                None => var_expr,
                Some(p) => Expr::mul(p, var_expr),
            });
            if coeff != 0 {
                let p = power.as_ref().expect("set above").clone_tree();
                degree_exprs.push(apply_coefficient(p, coeff, w));
            }
            let _ = j;
        }
        if degree_exprs.is_empty() {
            continue;
        }
        var_exprs.push(reduce_add_tree(degree_exprs));
    }

    if var_exprs.is_empty() {
        return None;
    }
    Some(reduce_add_tree(var_exprs))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluator::Evaluator;
    use cobra_ir::{recover_singleton_powers, UnivariateNormalizedPoly};

    #[test]
    fn x_squared_factorial_to_monomial_is_x_squared() {
        // h[1] = 1, h[2] = 1 → mono = [0, 0, 1] (x² contributes at degree 2 only).
        let terms = vec![
            UnivariateTerm {
                degree: 1,
                coeff: 1,
            },
            UnivariateTerm {
                degree: 2,
                coeff: 1,
            },
        ];
        let mono = factorial_to_monomial(&terms, 64);
        assert_eq!(mono, vec![0u64, 0, 1]);
    }

    #[test]
    fn build_expr_recovers_x_squared() {
        let orig = Expr::mul(Expr::variable(0), Expr::variable(0));
        let eval = Evaluator::from_expr(&orig, 64);
        let powers = recover_singleton_powers(&eval, 1, 64).unwrap();
        let expr = build_singleton_power_expr(&powers).expect("non-empty");
        // Evaluate at x=5 — expect 25.
        let built_eval = Evaluator::from_expr(&expr, 64);
        assert_eq!(built_eval.eval(&[5]), 25);
    }

    #[test]
    fn empty_powers_returns_none() {
        let powers = SingletonPowerResult {
            num_vars: 2,
            bitwidth: 64,
            per_var: vec![UnivariateNormalizedPoly::default(); 2],
        };
        assert!(build_singleton_power_expr(&powers).is_none());
    }

    #[test]
    fn two_var_linear_builds_add_tree() {
        let orig = Expr::add(
            Expr::mul(Expr::constant(3), Expr::variable(0)),
            Expr::mul(Expr::constant(5), Expr::variable(1)),
        );
        let eval = Evaluator::from_expr(&orig, 64);
        let powers = recover_singleton_powers(&eval, 2, 64).unwrap();
        let expr = build_singleton_power_expr(&powers).expect("non-empty");
        let built_eval = Evaluator::from_expr(&expr, 64);
        // f(2, 3) = 6 + 15 = 21.
        assert_eq!(built_eval.eval(&[2, 3]), 21);
    }
}
