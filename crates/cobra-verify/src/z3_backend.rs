//! Z3-backed [`Verifier`] implementation.
//!
//! version's `Z3_mk_context` / `Z3_del_context` around each verification.
//!
//! Enabled via the `z3` Cargo feature. Without that feature, this module
//! is not compiled and downstream crates link against [`NullVerifier`]
//! instead.

use cobra_core::expr::{Expr, Kind};
use z3::ast::{Ast, Bool, BV};
use z3::{Config, Context, SatResult, Solver};

use crate::{Verifier, VerifyOpts, VerifyOutcome};

/// Z3 SMT backend. Zero internal state — each `prove_*` call is
/// self-contained.
#[derive(Copy, Clone, Debug, Default)]
pub struct Z3Verifier;

impl Verifier for Z3Verifier {
    fn prove_equiv(
        &self,
        original: &Expr,
        simplified: &Expr,
        var_names: &[String],
        opts: VerifyOpts,
    ) -> VerifyOutcome {
        let cfg = make_config(opts.timeout_ms);
        let ctx = Context::new(&cfg);
        let var_asts = make_var_asts(&ctx, var_names, opts.bitwidth);

        let lhs = build_bv(&ctx, original, &var_asts, opts.bitwidth);
        let rhs = build_bv(&ctx, simplified, &var_asts, opts.bitwidth);
        run_equiv_check(&ctx, &lhs, &rhs)
    }

    fn prove_reconstruction(
        &self,
        cob_coeffs: &[u64],
        simplified: &Expr,
        var_names: &[String],
        num_vars: u32,
        opts: VerifyOpts,
    ) -> VerifyOutcome {
        let cfg = make_config(opts.timeout_ms);
        let ctx = Context::new(&cfg);
        let var_asts = make_var_asts(&ctx, var_names, opts.bitwidth);

        let reconstructed = build_from_coeffs(&ctx, cob_coeffs, &var_asts, num_vars, opts.bitwidth);
        let simpl = build_bv(&ctx, simplified, &var_asts, opts.bitwidth);
        run_equiv_check(&ctx, &reconstructed, &simpl)
    }
}

fn make_config(timeout_ms: u32) -> Config {
    let mut cfg = Config::new();
    cfg.set_param_value("timeout", &timeout_ms.to_string());
    cfg
}

fn make_var_asts<'c>(ctx: &'c Context, var_names: &[String], bitwidth: u32) -> Vec<BV<'c>> {
    var_names
        .iter()
        .map(|name| BV::new_const(ctx, name.as_str(), bitwidth))
        .collect()
}

/// `BuildZ3Expr`.
fn build_bv<'c>(ctx: &'c Context, expr: &Expr, var_asts: &[BV<'c>], bitwidth: u32) -> BV<'c> {
    match &expr.kind {
        Kind::Constant(v) => BV::from_u64(ctx, *v, bitwidth),
        Kind::Variable(idx) => var_asts[*idx as usize].clone(),
        Kind::Add => {
            let l = build_bv(ctx, &expr.children[0], var_asts, bitwidth);
            let r = build_bv(ctx, &expr.children[1], var_asts, bitwidth);
            l.bvadd(&r)
        }
        Kind::Mul => {
            let l = build_bv(ctx, &expr.children[0], var_asts, bitwidth);
            let r = build_bv(ctx, &expr.children[1], var_asts, bitwidth);
            l.bvmul(&r)
        }
        Kind::And => {
            let l = build_bv(ctx, &expr.children[0], var_asts, bitwidth);
            let r = build_bv(ctx, &expr.children[1], var_asts, bitwidth);
            l.bvand(&r)
        }
        Kind::Or => {
            let l = build_bv(ctx, &expr.children[0], var_asts, bitwidth);
            let r = build_bv(ctx, &expr.children[1], var_asts, bitwidth);
            l.bvor(&r)
        }
        Kind::Xor => {
            let l = build_bv(ctx, &expr.children[0], var_asts, bitwidth);
            let r = build_bv(ctx, &expr.children[1], var_asts, bitwidth);
            l.bvxor(&r)
        }
        Kind::Not => build_bv(ctx, &expr.children[0], var_asts, bitwidth).bvnot(),
        Kind::Neg => build_bv(ctx, &expr.children[0], var_asts, bitwidth).bvneg(),
        Kind::Shr(k) => {
            let child = build_bv(ctx, &expr.children[0], var_asts, bitwidth);
            let shift = BV::from_u64(ctx, u64::from(*k), bitwidth);
            child.bvlshr(&shift)
        }
    }
}

/// Rebuild the expression from its CoB coefficients as a bitvector sum.
/// Index 0 is the constant term; index `i > 0` is the coefficient of the
/// AND-product of variables whose bit is set in `i`.
fn build_from_coeffs<'c>(
    ctx: &'c Context,
    coeffs: &[u64],
    var_asts: &[BV<'c>],
    num_vars: u32,
    bitwidth: u32,
) -> BV<'c> {
    let mut result = BV::from_u64(ctx, coeffs[0], bitwidth);
    let len = 1usize << num_vars;
    for i in 1..len {
        if coeffs[i] == 0 {
            continue;
        }
        // AND-product over set bits of `i`.
        let mut product: Option<BV<'c>> = None;
        for v in 0..num_vars {
            if i & (1usize << v) == 0 {
                continue;
            }
            let var = var_asts[v as usize].clone();
            product = Some(match product {
                None => var,
                Some(acc) => acc.bvand(&var),
            });
        }
        let product = product.expect("popcount(i) >= 1 for i > 0");
        let coeff = BV::from_u64(ctx, coeffs[i], bitwidth);
        let term = coeff.bvmul(&product);
        result = result.bvadd(&term);
    }
    result
}

/// Assert `lhs != rhs` and return the verification outcome.
fn run_equiv_check<'c>(ctx: &'c Context, lhs: &BV<'c>, rhs: &BV<'c>) -> VerifyOutcome {
    let solver = Solver::new(ctx);
    let neq: Bool<'c> = lhs._eq(rhs).not();
    solver.assert(&neq);

    match solver.check() {
        SatResult::Unsat => VerifyOutcome::Equivalent,
        SatResult::Sat => {
            let counterexample = match solver.get_model() {
                Some(m) => format!("{m}"),
                None => String::from("<no model available>"),
            };
            VerifyOutcome::Disproved { counterexample }
        }
        SatResult::Unknown => VerifyOutcome::TimedOut,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(n: usize) -> Vec<String> {
        ('a'..).take(n).map(|c| c.to_string()).collect()
    }

    #[test]
    fn commutative_add_is_proven() {
        let v = Z3Verifier;
        let lhs = Expr::add(Expr::variable(0), Expr::variable(1));
        let rhs = Expr::add(Expr::variable(1), Expr::variable(0));
        let out = v.prove_equiv(&lhs, &rhs, &names(2), VerifyOpts::default());
        assert_eq!(out, VerifyOutcome::Equivalent);
    }

    #[test]
    fn classic_mba_identity_is_proven() {
        // (x & y) + (x | y) == x + y
        let v = Z3Verifier;
        let lhs = Expr::add(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::or(Expr::variable(0), Expr::variable(1)),
        );
        let rhs = Expr::add(Expr::variable(0), Expr::variable(1));
        let out = v.prove_equiv(&lhs, &rhs, &names(2), VerifyOpts::default());
        assert_eq!(out, VerifyOutcome::Equivalent);
    }

    #[test]
    fn disproves_non_equivalence() {
        // x + y vs x * y — not equivalent
        let v = Z3Verifier;
        let lhs = Expr::add(Expr::variable(0), Expr::variable(1));
        let rhs = Expr::mul(Expr::variable(0), Expr::variable(1));
        let out = v.prove_equiv(&lhs, &rhs, &names(2), VerifyOpts::default());
        match out {
            VerifyOutcome::Disproved { counterexample } => assert!(!counterexample.is_empty()),
            other => panic!("expected Disproved, got {other:?}"),
        }
    }

    #[test]
    fn reconstruction_from_coeffs() {
        // CoB coefficients for x + y on 2 vars:
        //   [0, 1, 1, 0]  (const=0, x=1, y=1, x&y=0)
        // Simplified form: x + y
        let v = Z3Verifier;
        let simplified = Expr::add(Expr::variable(0), Expr::variable(1));
        let out = v.prove_reconstruction(
            &[0, 1, 1, 0],
            &simplified,
            &names(2),
            2,
            VerifyOpts::default(),
        );
        assert_eq!(out, VerifyOutcome::Equivalent);
    }
}
