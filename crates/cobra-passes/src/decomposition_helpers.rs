//! Shared plumbing for the decomposition engine: remainder evaluator
//! construction, AST walkers that split an Add-tree into
//! product-addends vs. residual, and the probe-based `AcceptCore`
//! check.
//!
//! These helpers don't fit the `trait Extractor` shape — they're
//! utilities used by extractor implementations and by the residual-
//! solver passes.

use std::sync::Arc;

use cobra_core::arith::bitmask;
use cobra_core::compile;
use cobra_core::evaluator::{Evaluator, TraceKind};
use cobra_core::expr::{Expr, Kind};

/// `true` if `e` is `Mul(non-const, non-const)`.
#[must_use]
pub fn is_var_product(e: &Expr) -> bool {
    if !matches!(e.kind, Kind::Mul) || e.children.len() != 2 {
        return false;
    }
    let lhs_const = matches!(e.children[0].kind, Kind::Constant(_));
    let rhs_const = matches!(e.children[1].kind, Kind::Constant(_));
    !lhs_const && !rhs_const
}

/// `true` if `e` is a scaled var-product: `Mul(Const, Mul(var, var))`
/// or `Mul(Mul(var, var), Const)`. The constant coefficient rides
/// with the core into the extracted product.
#[must_use]
pub fn is_scaled_var_product(e: &Expr) -> bool {
    if !matches!(e.kind, Kind::Mul) || e.children.len() != 2 {
        return false;
    }
    let (c, other) = match (
        matches!(e.children[0].kind, Kind::Constant(_)),
        matches!(e.children[1].kind, Kind::Constant(_)),
    ) {
        (true, false) => (&e.children[0], &e.children[1]),
        (false, true) => (&e.children[1], &e.children[0]),
        _ => return false,
    };
    let _ = c;
    is_var_product(other)
}

/// `true` if `e` is a product addend: a var-product `Mul(a, b)`, a
/// scaled var-product `Mul(Const, Mul(a, b))`, or one of the sign-wrap
/// variants `Neg(...)` / `Not(...)` around either.
#[must_use]
pub fn is_product_addend(e: &Expr) -> bool {
    if is_var_product(e) || is_scaled_var_product(e) {
        return true;
    }
    if matches!(e.kind, Kind::Neg) && e.children.len() == 1 {
        let c = &e.children[0];
        if is_var_product(c) || is_scaled_var_product(c) {
            return true;
        }
    }
    if matches!(e.kind, Kind::Not) && e.children.len() == 1 {
        let c = &e.children[0];
        if is_var_product(c) || is_scaled_var_product(c) {
            return true;
        }
    }
    false
}

/// Walk an `Add` tree; push product-addends into `products`, every
/// other leaf into `residual`.
pub fn split_add_tree<'a>(
    e: &'a Expr,
    products: &mut Vec<&'a Expr>,
    residual: &mut Vec<Box<Expr>>,
) {
    if matches!(e.kind, Kind::Add) && e.children.len() == 2 {
        split_add_tree(&e.children[0], products, residual);
        let rhs = &e.children[1];
        if is_product_addend(rhs) {
            products.push(rhs);
        } else {
            residual.push(rhs.clone_tree());
        }
        return;
    }
    if is_product_addend(e) {
        products.push(e);
    } else {
        residual.push(e.clone_tree());
    }
}

/// Build `r(x) = (f(x) - core(x)) mod 2^bitwidth`. The returned
/// evaluator is a closure wrapping the supplied `original` evaluator
/// plus a freshly-compiled `core`. `core` is cloned so the caller's
/// ownership isn't disturbed.
#[must_use]
pub fn build_remainder_evaluator(original: &Evaluator, core: &Expr, bitwidth: u32) -> Evaluator {
    let mask = bitmask(bitwidth);
    let compiled_core = Arc::new(compile(core, bitwidth));
    let original_clone = original.clone();
    Evaluator::from_closure(move |v: &[u64]| {
        let f = original_clone.eval(v);
        let mut stack: Vec<u64> = Vec::new();
        let p = cobra_core::compiled::eval(&compiled_core, v, &mut stack);
        f.wrapping_sub(p) & mask
    })
    .with_trace(TraceKind::Remainder)
}

/// Five-probe `AcceptCore` check: the core is accepted iff it is
/// non-trivial — i.e. its removal produces a residual that is neither
/// identically zero nor identically the original function on a fixed
/// set of pseudo-random probes.
#[must_use]
pub fn accept_core(evaluator: &Evaluator, core: &Expr, num_vars: u32, bitwidth: u32) -> bool {
    if matches!(core.kind, Kind::Constant(_)) {
        return false;
    }
    let mask = bitmask(bitwidth);
    let residual_eval = build_remainder_evaluator(evaluator, core, bitwidth);

    // SplitMix64 with the same seed as C++ `mt19937_64(0xDECAF)` — close
    // enough for determinism; the probe count is fixed at 5.
    let mut state: u64 = 0x0000_0000_000D_ECAF;
    let mut next = || -> u64 {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };

    let mut all_same_as_orig = true;
    let mut all_zero = true;
    let mut point = vec![0u64; num_vars as usize];
    for _ in 0..5 {
        for slot in &mut point {
            *slot = next() & mask;
        }
        let orig = evaluator.eval(&point) & mask;
        let res = residual_eval.eval(&point);
        if res != orig {
            all_same_as_orig = false;
        }
        if res != 0 {
            all_zero = false;
        }
    }
    !all_same_as_orig && !all_zero
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn is_product_addend_recognises_neg_and_not() {
        let m = Expr::mul(Expr::variable(0), Expr::variable(1));
        assert!(is_product_addend(&m));
        assert!(is_product_addend(&Expr::neg(m.clone_tree())));
        assert!(is_product_addend(&Expr::not(m)));
    }

    #[test]
    fn is_product_addend_rejects_const_factor() {
        let m = Expr::mul(Expr::constant(3), Expr::variable(0));
        assert!(!is_product_addend(&m));
    }

    #[test]
    fn split_add_tree_separates_products_and_residual() {
        // f = x*y + 3 + z*w
        let expr = Expr::add(
            Expr::add(
                Expr::mul(Expr::variable(0), Expr::variable(1)),
                Expr::constant(3),
            ),
            Expr::mul(Expr::variable(2), Expr::variable(3)),
        );
        let mut products = Vec::new();
        let mut residual = Vec::new();
        split_add_tree(&expr, &mut products, &mut residual);
        assert_eq!(products.len(), 2);
        assert_eq!(residual.len(), 1);
    }

    #[test]
    fn build_remainder_evaluator_zero_on_identity() {
        let expr = Expr::mul(Expr::variable(0), Expr::variable(1));
        let eval = Evaluator::from_expr(&expr, 64);
        let residual = build_remainder_evaluator(&eval, &expr, 64);
        assert_eq!(residual.eval(&[3, 5]), 0);
    }

    #[test]
    fn accept_core_rejects_constant_and_equal_core() {
        let expr = Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::constant(7),
        );
        let eval = Evaluator::from_expr(&expr, 64);
        // Accept a real core (just the Mul).
        let core = Expr::mul(Expr::variable(0), Expr::variable(1));
        assert!(accept_core(&eval, &core, 2, 64));
        // Reject the full expression as its own "core" (residual ≡ 0).
        assert!(!accept_core(&eval, &expr, 2, 64));
    }
}
