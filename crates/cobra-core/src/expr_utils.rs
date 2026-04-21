//! Small, general-purpose utilities on `Expr` trees. Ported from the
//! subset of `include/cobra/core/ExprUtils.h` and `lib/core/ExprUtils.cpp`
//! that other crates need without the heavier AST-rewrite helpers
//! (those belong in `cobra-ir` / `cobra-passes`).

use crate::arith::{bitmask, mod_add, mod_mul, mod_neg, mod_not, mod_shr};
use crate::expr::{Expr, Kind};

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
/// Panics if a `Variable` leaf is encountered (matches C++
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
    }
}

/// Returns true if `expr` references any `Variable` leaf.
#[must_use]
pub fn has_var_dep(expr: &Expr) -> bool {
    if matches!(expr.kind, Kind::Variable(_)) {
        return true;
    }
    expr.children.iter().any(|c| has_var_dep(c))
}

/// Append every variable index referenced in `expr` to `out` in preorder.
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
/// Panics if a variable index is out of range of `index_map` (matches C++
/// `at()` behaviour).
pub fn remap_var_indices(expr: &mut Expr, index_map: &[u32]) {
    if let Kind::Variable(idx) = &mut expr.kind {
        let new = index_map[*idx as usize];
        *idx = new;
        return;
    }
    for child in &mut expr.children {
        remap_var_indices(child, index_map);
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
        let mut e = *Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        // Map 0->10, 1->11, 2->12
        remap_var_indices(&mut e, &[10, 11, 12]);
        let mut out = Vec::new();
        collect_vars(&e, &mut out);
        assert_eq!(out, vec![10, 11, 12]);
    }
}
