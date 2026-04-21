//! Build an [`Expr`] tree from a [`NormalizedPoly`]. The transform is
//! one factorial-basis → monomial-basis rewrite followed by a pairwise
//! tree-build to keep the Add / Mul chains balanced.
//!
//! Monomials are emitted in lexicographic order of their exponent keys
//! so the output is deterministic for a given input.

use cobra_core::arith::bitmask;
use cobra_core::expr::Expr;
use cobra_core::expr_rewrite::apply_coefficient;
use cobra_core::result::{err, CobraError, Result};

use crate::basis_transform::to_monomial_basis;
use crate::mono::{MonomialKey, MAX_POLY_VARS};
use crate::poly::NormalizedPoly;

fn build_power_expr(var_index: u32, exponent: u8) -> Box<Expr> {
    debug_assert!(exponent >= 2);
    let mut factors: Vec<Box<Expr>> = (0..exponent).map(|_| Expr::variable(var_index)).collect();
    while factors.len() > 1 {
        let mut next: Vec<Box<Expr>> = Vec::with_capacity(factors.len().div_ceil(2));
        let mut i = 0;
        while i < factors.len() {
            if i + 1 < factors.len() {
                let a = factors[i].clone_tree();
                let b = factors[i + 1].clone_tree();
                next.push(Expr::mul(a, b));
            } else {
                next.push(factors[i].clone_tree());
            }
            i += 2;
        }
        factors = next;
    }
    factors.pop().expect("factors non-empty")
}

#[allow(clippy::vec_box)]
fn reduce_add_tree(mut terms: Vec<Box<Expr>>) -> Box<Expr> {
    while terms.len() > 1 {
        let mut next: Vec<Box<Expr>> = Vec::with_capacity(terms.len().div_ceil(2));
        let mut i = 0;
        while i < terms.len() {
            if i + 1 < terms.len() {
                let a = terms[i].clone_tree();
                let b = terms[i + 1].clone_tree();
                next.push(Expr::add(a, b));
            } else {
                next.push(terms[i].clone_tree());
            }
            i += 2;
        }
        terms = next;
    }
    terms.pop().expect("at least one term")
}

/// Build an `Expr` from a `NormalizedPoly`. Returns `Ok(Constant(0))`
/// for the empty-polynomial case. Fails with `TooManyVariables` if the
/// polynomial's `num_vars` exceeds `MAX_POLY_VARS`.
pub fn build_poly_expr(poly: &NormalizedPoly) -> Result<Box<Expr>> {
    let n = poly.num_vars;
    if usize::from(n) > MAX_POLY_VARS {
        return Err(err(
            CobraError::TooManyVariables,
            format!("build_poly_expr: num_vars ({n}) exceeds MAX_POLY_VARS ({MAX_POLY_VARS})"),
        ));
    }
    let w = poly.bitwidth;

    if poly.coeffs.is_empty() {
        return Ok(Expr::constant(0));
    }

    let monomial = to_monomial_basis(&poly.coeffs, n, w);
    if monomial.is_empty() {
        return Ok(Expr::constant(0));
    }

    let mask = bitmask(w);
    let mut sorted: Vec<(MonomialKey, u64)> = monomial.into_iter().collect();
    sorted.sort_by(|a, b| a.0.cmp(&b.0));

    let mut term_exprs: Vec<Box<Expr>> = Vec::with_capacity(sorted.len());
    for (tuple, coeff) in sorted {
        let c = coeff & mask;
        if c == 0 {
            continue;
        }
        let mut product: Option<Box<Expr>> = None;
        for i in 0..n {
            let e = tuple.exponent_at(i);
            if e == 0 {
                continue;
            }
            let factor = if e == 1 {
                Expr::variable(u32::from(i))
            } else {
                build_power_expr(u32::from(i), e)
            };
            product = Some(match product {
                Some(acc) => Expr::mul(acc, factor),
                None => factor,
            });
        }
        let term = match product {
            None => Expr::constant(c),
            Some(p) => apply_coefficient(p, c, w),
        };
        term_exprs.push(term);
    }

    if term_exprs.is_empty() {
        return Ok(Expr::constant(0));
    }
    Ok(reduce_add_tree(term_exprs))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poly::CoeffMap;
    use cobra_core::compile;
    use cobra_core::evaluator::Evaluator;
    use cobra_core::expr::Kind;

    fn poly_from(entries: &[(&[u8], u64)], num_vars: u8, bitwidth: u32) -> NormalizedPoly {
        let mut p = NormalizedPoly::empty(num_vars, bitwidth);
        let mut coeffs: CoeffMap =
            CoeffMap::with_hasher(ahash::RandomState::with_seeds(1, 2, 3, 4));
        for &(exps, c) in entries {
            coeffs.insert(MonomialKey::from_exponents(exps, num_vars), c);
        }
        p.coeffs = coeffs;
        p
    }

    #[test]
    fn empty_poly_builds_zero_constant() {
        let p = NormalizedPoly::empty(2, 64);
        let expr = build_poly_expr(&p).unwrap();
        assert!(matches!(expr.kind, Kind::Constant(0)));
    }

    #[test]
    fn linear_polynomial_produces_add_tree() {
        // 3x + 5y in monomial basis = same in factorial basis (degree ≤ 1).
        let p = poly_from(&[(&[1, 0], 3), (&[0, 1], 5)], 2, 64);
        let expr = build_poly_expr(&p).unwrap();
        // Evaluate at (1, 2) — expect 3 + 10 = 13.
        let prog = compile(&expr, 64);
        let ev = Evaluator::from_compiled(
            std::sync::Arc::new(prog),
            cobra_core::evaluator::TraceKind::None,
        );
        assert_eq!(ev.eval(&[1, 2]), 13);
    }

    #[test]
    fn quadratic_polynomial_round_trips_via_evaluator() {
        // Factorial-basis coefficient c at exponent (2, 0) represents
        // c · x · (x - 1) — to produce "2·x²" in factorial basis we'd
        // need coefficients at exp=1 and exp=2 (since x² = x^(1) + x^(2)).
        // Easier: start from a purely quadratic monomial input, push
        // through to_factorial_basis then build_poly_expr, compare to
        // evaluating the raw polynomial.
        let mono = poly_from(&[(&[2, 0], 1), (&[1, 1], 3)], 2, 64);
        let factorial_form = crate::basis_transform::to_factorial_basis(&mono.coeffs, 2, 64);
        let mut fp = NormalizedPoly::empty(2, 64);
        fp.coeffs = factorial_form;

        let expr = build_poly_expr(&fp).unwrap();
        let prog = compile(&expr, 64);
        let ev = Evaluator::from_compiled(
            std::sync::Arc::new(prog),
            cobra_core::evaluator::TraceKind::None,
        );
        // f(x, y) = x² + 3xy → f(2, 3) = 4 + 18 = 22.
        assert_eq!(ev.eval(&[2, 3]), 22);
    }
}
