//! Build an [`Expr`] tree from a [`NormalizedPoly`]. The transform is
//! one factorial-basis → monomial-basis rewrite followed by a pairwise
//! tree-build to keep the Add / Mul chains balanced.
//!
//! Monomials are emitted in lexicographic order of their exponent keys
//! so the output is deterministic for a given input.

use crate::core::arith::bitmask;
use crate::core::expr::Expr;
use crate::core::expr_rewrite::apply_coefficient;
use crate::core::result::{err, CobraError, Result};
use std::sync::Arc;

use crate::ir::basis_transform::to_monomial_basis;
use crate::ir::mono::{MonomialKey, MAX_POLY_VARS};
use crate::ir::poly::NormalizedPoly;

fn build_power_expr(var_index: u32, exponent: u8) -> Arc<Expr> {
    debug_assert!(exponent >= 2);
    let factors: Vec<Arc<Expr>> = (0..exponent).map(|_| Expr::variable(var_index)).collect();
    reduce_pairwise(factors, Expr::mul).expect("factors non-empty")
}

#[allow(clippy::vec_box)]
fn reduce_add_tree(terms: Vec<Arc<Expr>>) -> Arc<Expr> {
    reduce_pairwise(terms, Expr::add).expect("at least one term")
}

/// Balanced pairwise reduction of `items` under `combine`. Operands are
/// moved (never cloned): each level consumes its vec via `into_iter`,
/// pairing adjacent elements and carrying any odd tail forward.
#[allow(clippy::vec_box)]
fn reduce_pairwise(
    mut items: Vec<Arc<Expr>>,
    combine: fn(Arc<Expr>, Arc<Expr>) -> Arc<Expr>,
) -> Option<Arc<Expr>> {
    while items.len() > 1 {
        let mut next: Vec<Arc<Expr>> = Vec::with_capacity(items.len().div_ceil(2));
        let mut it = items.into_iter();
        while let Some(a) = it.next() {
            match it.next() {
                Some(b) => next.push(combine(a, b)),
                None => next.push(a),
            }
        }
        items = next;
    }
    items.pop()
}

/// Build an `Expr` from a `NormalizedPoly`. Returns `Ok(Constant(0))`
/// for the empty-polynomial case. Fails with `TooManyVariables` if the
/// polynomial's `num_vars` exceeds `MAX_POLY_VARS`.
pub fn build_poly_expr(poly: &NormalizedPoly) -> Result<Arc<Expr>> {
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

    let mut term_exprs: Vec<Arc<Expr>> = Vec::with_capacity(sorted.len());
    for (tuple, coeff) in sorted {
        let c = coeff & mask;
        if c == 0 {
            continue;
        }
        let mut product: Option<Arc<Expr>> = None;
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
    use crate::core::compile;
    use crate::core::evaluator::Evaluator;
    use crate::core::expr::Kind;
    use crate::ir::poly::CoeffMap;

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
            crate::core::evaluator::TraceKind::None,
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
        let factorial_form = crate::ir::basis_transform::to_factorial_basis(&mono.coeffs, 2, 64);
        let mut fp = NormalizedPoly::empty(2, 64);
        fp.coeffs = factorial_form;

        let expr = build_poly_expr(&fp).unwrap();
        let prog = compile(&expr, 64);
        let ev = Evaluator::from_compiled(
            std::sync::Arc::new(prog),
            crate::core::evaluator::TraceKind::None,
        );
        // f(x, y) = x² + 3xy → f(2, 3) = 4 + 18 = 22.
        assert_eq!(ev.eval(&[2, 3]), 22);
    }
}
