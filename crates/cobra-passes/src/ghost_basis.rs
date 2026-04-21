//! Ghost primitives: arithmetic identities that vanish on the
//! Boolean corners but not at full width, used as building blocks for
//! residual reconstruction.
//!
//! Each primitive provides an evaluator (for probe-based coefficient
//! recovery) and a builder that materialises it as an `Expr` tree
//! given the variable indices to substitute.

use cobra_core::arith::bitmask;
use cobra_core::expr::Expr;

/// Evaluate the primitive at the given argument vector.
pub type GhostEval = fn(&[u64], u32) -> u64;
/// Build an Expr tree for the primitive given the original-space
/// variable indices its operands map to.
pub type GhostBuilder = fn(&[u32]) -> Box<Expr>;

#[derive(Copy, Clone)]
pub struct GhostPrimitive {
    pub name: &'static str,
    pub arity: u8,
    pub symmetric: bool,
    pub eval: GhostEval,
    pub build: GhostBuilder,
}

fn eval_mul_sub_and(args: &[u64], bw: u32) -> u64 {
    let mask = bitmask(bw);
    (args[0]
        .wrapping_mul(args[1])
        .wrapping_sub(args[0] & args[1]))
        & mask
}

fn build_mul_sub_and(vars: &[u32]) -> Box<Expr> {
    Expr::add(
        Expr::mul(Expr::variable(vars[0]), Expr::variable(vars[1])),
        Expr::neg(Expr::and(Expr::variable(vars[0]), Expr::variable(vars[1]))),
    )
}

fn eval_mul3_sub_and3(args: &[u64], bw: u32) -> u64 {
    let mask = bitmask(bw);
    let prod = args[0].wrapping_mul(args[1]).wrapping_mul(args[2]);
    let and3 = args[0] & args[1] & args[2];
    prod.wrapping_sub(and3) & mask
}

fn build_mul3_sub_and3(vars: &[u32]) -> Box<Expr> {
    Expr::add(
        Expr::mul(
            Expr::mul(Expr::variable(vars[0]), Expr::variable(vars[1])),
            Expr::variable(vars[2]),
        ),
        Expr::neg(Expr::and(
            Expr::and(Expr::variable(vars[0]), Expr::variable(vars[1])),
            Expr::variable(vars[2]),
        )),
    )
}

/// the ghost residual solver.
#[must_use]
pub fn get_ghost_basis() -> &'static [GhostPrimitive] {
    &GHOST_BASIS
}

static GHOST_BASIS: [GhostPrimitive; 2] = [
    GhostPrimitive {
        name: "mul_sub_and",
        arity: 2,
        symmetric: true,
        eval: eval_mul_sub_and,
        build: build_mul_sub_and,
    },
    GhostPrimitive {
        name: "mul3_sub_and3",
        arity: 3,
        symmetric: true,
        eval: eval_mul3_sub_and3,
        build: build_mul3_sub_and3,
    },
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mul_sub_and_zero_on_boolean_corners() {
        for a in 0..=1u64 {
            for b in 0..=1u64 {
                assert_eq!(eval_mul_sub_and(&[a, b], 64), 0);
            }
        }
    }

    #[test]
    fn mul_sub_and_nonzero_at_full_width() {
        assert_ne!(eval_mul_sub_and(&[3, 5], 64), 0);
    }

    #[test]
    fn basis_list_has_expected_primitives() {
        let basis = get_ghost_basis();
        assert_eq!(basis.len(), 2);
        assert_eq!(basis[0].name, "mul_sub_and");
        assert_eq!(basis[0].arity, 2);
        assert_eq!(basis[1].name, "mul3_sub_and3");
        assert_eq!(basis[1].arity, 3);
    }
}
