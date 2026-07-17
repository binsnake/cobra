//! that other crates need without the heavier AST-rewrite helpers
//! (those belong in `cobra-ir` / `cobra-passes`).

use crate::core::arith::{bitmask, mod_add, mod_mul, mod_neg, mod_not, mod_shr, sext, trunc, zext};
use crate::core::expr::{Expr, Kind};
use crate::core::width::width_of;

/// Returns true if `expr` contains no `Variable` leaf.
#[must_use]
pub fn is_constant_subtree(expr: &Expr) -> bool {
    match &expr.kind {
        Kind::Constant(_) => true,
        Kind::Variable(_) => false,
        _ => expr.children.iter().all(|c| is_constant_subtree(c)),
    }
}

/// Evaluate a constant-only `Expr` subtree at the given `bitwidth`.
/// `EvalConstantExpr`'s `std::unreachable()`).
#[must_use]
pub fn eval_constant(expr: &Expr, bitwidth: u32) -> u64 {
    let mask = bitmask(bitwidth);
    match &expr.kind {
        Kind::Constant(v) => *v & mask,
        Kind::Variable(_) => panic!("eval_constant: variable in constant-only subtree"),
        Kind::Not => mod_not(eval_constant(&expr.children[0], bitwidth), bitwidth),
        Kind::Neg => mod_neg(eval_constant(&expr.children[0], bitwidth), bitwidth),
        Kind::And => {
            eval_constant(&expr.children[0], bitwidth) & eval_constant(&expr.children[1], bitwidth)
        }
        Kind::Or => {
            eval_constant(&expr.children[0], bitwidth) | eval_constant(&expr.children[1], bitwidth)
        }
        Kind::Xor => {
            eval_constant(&expr.children[0], bitwidth) ^ eval_constant(&expr.children[1], bitwidth)
        }
        Kind::Add => mod_add(
            eval_constant(&expr.children[0], bitwidth),
            eval_constant(&expr.children[1], bitwidth),
            bitwidth,
        ),
        Kind::Mul => mod_mul(
            eval_constant(&expr.children[0], bitwidth),
            eval_constant(&expr.children[1], bitwidth),
            bitwidth,
        ),
        Kind::Shr(k) => mod_shr(
            eval_constant(&expr.children[0], bitwidth),
            u64::from(*k),
            bitwidth,
        ),
        // Casts produce a `w`-wide value from a child evaluated at the context
        // width. The child's source width drives sign-extension.
        Kind::ZExt(w) => zext(eval_constant(&expr.children[0], bitwidth), *w),
        Kind::SExt(w) => {
            let from = width_of(&expr.children[0], &[], bitwidth);
            sext(eval_constant(&expr.children[0], bitwidth), from, *w)
        }
        Kind::Trunc(w) => trunc(eval_constant(&expr.children[0], bitwidth), *w),
        // Concat: high child shifted left by the low child's width, OR'd with
        // the low child masked to its own width.
        Kind::Concat => {
            let low_w = width_of(&expr.children[1], &[], bitwidth);
            let high = eval_constant(&expr.children[0], bitwidth);
            let low = eval_constant(&expr.children[1], bitwidth) & bitmask(low_w);
            (high.wrapping_shl(low_w) | low) & bitmask(width_of(expr, &[], bitwidth))
        }
    }
}

#[must_use]
pub fn has_var_dep(expr: &Expr) -> bool {
    if matches!(expr.kind, Kind::Variable(_)) {
        return true;
    }
    expr.children.iter().any(|c| has_var_dep(c))
}

/// Duplicates are preserved (the caller sorts/dedupes).
pub fn collect_vars(expr: &Expr, out: &mut Vec<u32>) {
    if let Kind::Variable(idx) = &expr.kind {
        out.push(*idx);
        return;
    }
    for child in &expr.children {
        collect_vars(child, out);
    }
}

/// Rewrite every `Variable(idx)` node in-place as `Variable(index_map[idx])`.
/// `at()` behaviour).
pub fn remap_var_indices(expr: &mut Expr, index_map: &[u32]) {
    if let Kind::Variable(idx) = &mut expr.kind {
        let new = index_map[*idx as usize];
        *idx = new;
        return;
    }
    for child in &mut expr.children {
        remap_var_indices(std::sync::Arc::make_mut(child), index_map);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn is_constant_subtree_distinguishes_leaves() {
        assert!(is_constant_subtree(&Expr::constant(42)));
        assert!(!is_constant_subtree(&Expr::variable(0)));
        assert!(is_constant_subtree(&Expr::add(
            Expr::constant(1),
            Expr::constant(2)
        )));
        assert!(!is_constant_subtree(&Expr::add(
            Expr::constant(1),
            Expr::variable(0)
        )));
    }

    #[test]
    fn eval_constant_covers_all_kinds() {
        // (~(3) + -5) * 2, bitwidth 8
        // ~3 = 0xFC, -5 = 0xFB, sum = 0xF7, * 2 = 0xEE
        let e = Expr::mul(
            Expr::add(Expr::not(Expr::constant(3)), Expr::neg(Expr::constant(5))),
            Expr::constant(2),
        );
        assert_eq!(eval_constant(&e, 8), 0xEE);

        // (1 | 6) & 3 = 7 & 3 = 3
        let e = Expr::and(
            Expr::or(Expr::constant(1), Expr::constant(6)),
            Expr::constant(3),
        );
        assert_eq!(eval_constant(&e, 64), 3);

        // 5 ^ 6 = 3
        assert_eq!(
            eval_constant(&Expr::xor(Expr::constant(5), Expr::constant(6)), 64),
            3
        );

        // 0xFF >> 4 = 0x0F at bitwidth 8
        assert_eq!(eval_constant(&Expr::shr(Expr::constant(0xFF), 4), 8), 0x0F);
    }

    #[test]
    fn eval_constant_casts_and_concat() {
        // zext: 0xAB (8-bit constant) extended to 16 -> 0x00AB.
        // The constant subtree is a u8 value; context bitwidth 16 so the
        // child masks to 0x00AB, and zext keeps it.
        let e = Expr::zext(Expr::constant(0xAB), 16);
        assert_eq!(eval_constant(&e, 16), 0x00AB);

        // sext: an 8-bit constant 0xFF is -1; sign-extend to 16 -> 0xFFFF.
        // Use bitwidth 8 so the child's intrinsic width is 8.
        let e = Expr::sext(Expr::constant(0xFF), 16);
        assert_eq!(eval_constant(&e, 8), 0xFFFF);

        // sext positive: 0x7F at width 8 stays 0x007F.
        let e = Expr::sext(Expr::constant(0x7F), 16);
        assert_eq!(eval_constant(&e, 8), 0x007F);

        // trunc: 0xABCD truncated to 8 -> 0xCD.
        let e = Expr::trunc(Expr::constant(0xABCD), 8);
        assert_eq!(eval_constant(&e, 16), 0xCD);

        // concat: 0x12 (high, 8-bit) ++ 0x34 (low, 8-bit) -> 0x1234.
        let e = Expr::concat(Expr::constant(0x12), Expr::constant(0x34));
        assert_eq!(eval_constant(&e, 8), 0x1234);
    }

    #[test]
    #[should_panic(expected = "variable in constant-only subtree")]
    fn eval_constant_panics_on_variable() {
        let _ = eval_constant(&Expr::variable(0), 64);
    }

    #[test]
    fn has_var_dep_walks() {
        assert!(!has_var_dep(&Expr::constant(1)));
        assert!(has_var_dep(&Expr::variable(0)));
        assert!(has_var_dep(&Expr::and(
            Expr::constant(1),
            Expr::variable(0)
        )));
        assert!(!has_var_dep(&Expr::and(
            Expr::constant(1),
            Expr::constant(2)
        )));
    }

    #[test]
    fn collect_vars_preserves_preorder_with_dupes() {
        // (x0 + x1) * (x0 & x2) — indices seen in order: 0, 1, 0, 2
        let e = Expr::mul(
            Expr::add(Expr::variable(0), Expr::variable(1)),
            Expr::and(Expr::variable(0), Expr::variable(2)),
        );
        let mut out = Vec::new();
        collect_vars(&e, &mut out);
        assert_eq!(out, vec![0, 1, 0, 2]);
    }

    #[test]
    fn remap_var_indices_rewrites_leaves() {
        let mut e = Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        // Map 0->10, 1->11, 2->12
        remap_var_indices(std::sync::Arc::make_mut(&mut e), &[10, 11, 12]);
        let mut out = Vec::new();
        collect_vars(&e, &mut out);
        assert_eq!(out, vec![10, 11, 12]);
    }
}
