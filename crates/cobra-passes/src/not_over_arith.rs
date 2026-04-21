//! `Not`-over-arith detection and lowering.
//!
//! In modular 2's-complement arithmetic, `~x = -x + (2^w - 1)`. When a
//! `~` applies to a purely-arithmetic subtree, rewriting it into the
//! arithmetic form lets downstream signature-based passes ingest the
//! expression without a special-case bitwise-over-arith path. Ported
//! `HasNotOverArith`, `LowerNotOverArith`).

use cobra_core::arith::bitmask;
use cobra_core::expr::{Expr, Kind};

/// True if every node in `e` is `Constant`, `Variable`, `Add`, `Mul`,
/// or `Neg` — i.e. the subtree has no bitwise or shift operators.
#[must_use]
pub fn is_purely_arithmetic(e: &Expr) -> bool {
    match &e.kind {
        Kind::Constant(_) | Kind::Variable(_) | Kind::Add | Kind::Mul | Kind::Neg => {}
        _ => return false,
    }
    e.children.iter().all(|c| is_purely_arithmetic(c))
}

/// True if any `Not` node in `e` has a purely-arithmetic child.
#[must_use]
pub fn has_not_over_arith(e: &Expr) -> bool {
    if matches!(e.kind, Kind::Not) && !e.children.is_empty() && is_purely_arithmetic(&e.children[0])
    {
        return true;
    }
    e.children.iter().any(|c| has_not_over_arith(c))
}

/// Bottom-up rewrite: replace each `Not(arith)` node with
#[must_use]
pub fn lower_not_over_arith(mut e: Box<Expr>, bitwidth: u32) -> Box<Expr> {
    // Rewrite children first (post-order).
    let rewritten: Vec<Box<Expr>> = e
        .children
        .drain(..)
        .map(|c| lower_not_over_arith(c, bitwidth))
        .collect();
    e.children = rewritten.into_iter().collect();

    if matches!(e.kind, Kind::Not) && e.children.len() == 1 && is_purely_arithmetic(&e.children[0])
    {
        let mask = bitmask(bitwidth);
        let inner = e.children.remove(0);
        return Expr::add(Expr::neg(inner), Expr::constant(mask));
    }
    e
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluate_boolean_signature;

    #[test]
    fn pure_arith_subtree_predicate() {
        assert!(is_purely_arithmetic(&Expr::constant(3)));
        assert!(is_purely_arithmetic(&Expr::variable(0)));
        assert!(is_purely_arithmetic(&Expr::add(
            Expr::variable(0),
            Expr::constant(2)
        )));
        assert!(is_purely_arithmetic(&Expr::mul(
            Expr::variable(0),
            Expr::neg(Expr::variable(1))
        )));
        // Bitwise anywhere → false.
        assert!(!is_purely_arithmetic(&Expr::and(
            Expr::variable(0),
            Expr::constant(1)
        )));
        assert!(!is_purely_arithmetic(&Expr::add(
            Expr::variable(0),
            Expr::xor(Expr::variable(1), Expr::constant(1))
        )));
    }

    #[test]
    fn has_not_over_arith_detects_root_and_nested() {
        // ~(x + y)
        let e = Expr::not(Expr::add(Expr::variable(0), Expr::variable(1)));
        assert!(has_not_over_arith(&e));

        // (a & ~(x * 3))  — Not(arith) nested inside And
        let e = Expr::and(
            Expr::variable(0),
            Expr::not(Expr::mul(Expr::variable(1), Expr::constant(3))),
        );
        assert!(has_not_over_arith(&e));

        // No Not anywhere.
        assert!(!has_not_over_arith(&Expr::add(
            Expr::variable(0),
            Expr::variable(1)
        )));

        // Not of bitwise — doesn't match.
        assert!(!has_not_over_arith(&Expr::not(Expr::and(
            Expr::variable(0),
            Expr::variable(1)
        ))));
    }

    #[test]
    fn lowering_rewrites_not_arith_to_add_neg_mask() {
        // ~(x + 1) at bitwidth 8 → Add(Neg(x + 1), 0xFF)
        let e = Expr::not(Expr::add(Expr::variable(0), Expr::constant(1)));
        let lowered = lower_not_over_arith(e, 8);
        assert!(matches!(lowered.kind, Kind::Add));
        assert!(matches!(lowered.children[0].kind, Kind::Neg));
        if let Kind::Constant(v) = lowered.children[1].kind {
            assert_eq!(v, 0xFF);
        } else {
            panic!("expected Constant on RHS");
        }
    }

    #[test]
    fn lowering_preserves_semantics() {
        // ~(x + y + 1) at bitwidth 8 must match the original at every
        // 1-variable Boolean assignment.
        let original = Expr::not(Expr::add(
            Expr::add(Expr::variable(0), Expr::variable(1)),
            Expr::constant(1),
        ));
        let lowered = lower_not_over_arith(original.clone_tree(), 8);
        let a = evaluate_boolean_signature(&original, 2, 8);
        let b = evaluate_boolean_signature(&lowered, 2, 8);
        assert_eq!(a, b);
    }

    #[test]
    fn lowering_leaves_bitwise_not_untouched() {
        // ~(x & y) — child is bitwise, not arith. Stay unchanged.
        let original = Expr::not(Expr::and(Expr::variable(0), Expr::variable(1)));
        let after = lower_not_over_arith(original.clone_tree(), 8);
        assert_eq!(original, after);
    }

    #[test]
    fn lowering_handles_nested_not_arith_inside_bitwise() {
        // x & ~(y + 1) at bw 8 — inner Not-over-arith rewrites to
        // Add(Neg(y + 1), 0xFF) while the outer And is preserved.
        let e = Expr::and(
            Expr::variable(0),
            Expr::not(Expr::add(Expr::variable(1), Expr::constant(1))),
        );
        let lowered = lower_not_over_arith(e.clone_tree(), 8);
        // Outer is still And.
        assert!(matches!(lowered.kind, Kind::And));
        // Right child is now an Add(Neg(...), Constant(0xFF)).
        assert!(matches!(lowered.children[1].kind, Kind::Add));
        // Semantic equivalence.
        let a = evaluate_boolean_signature(&e, 2, 8);
        let b = evaluate_boolean_signature(&lowered, 2, 8);
        assert_eq!(a, b);
    }
}
