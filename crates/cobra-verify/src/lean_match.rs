//! Shared structural pattern matchers for the Lean certificate layer.
//!
//! This module is the **single source of truth** for the structural shape of
//! every theorem-backed local rewrite. Two sites consume it and they MUST stay
//! in lock-step:
//!
//! * [`crate::verify::lean_cert::identify_rewrite_theorem_64`] uses these matchers to
//!   *decide* which `LeanTheorem` fires for a `(before, after)` pair.
//! * [`crate::verify::lean_emit`]'s `theorem_eval_args` uses the same matchers to
//!   *extract* the operands that instantiate that theorem in emitted Lean.
//!
//! If the decision matcher and the extraction matcher ever disagreed, the
//! emitter would hand a Lean theorem arguments that don't match the rewrite —
//! a silently vacuous / wrong "passing" proof. Keeping the operand-extraction
//! logic here (and nowhere else) makes that divergence impossible.
//!
//! Every matcher returns borrowed sub-`Expr`s of its input; none allocate.
//! The binary matchers all self-guard on arity (`children.len() == 2`) and
//! kind, so they are safe to call on an arbitrary node, not just one already
//! known to be the expected shape.

use crate::core::expr::{Expr, Kind};

// --- leaf predicates -------------------------------------------------------

#[must_use]
pub(crate) fn expr_eq(lhs: &Expr, rhs: &Expr) -> bool {
    lhs == rhs
}

#[must_use]
pub(crate) fn unordered_pair_eq(a: &Expr, b: &Expr, x: &Expr, y: &Expr) -> bool {
    (expr_eq(a, x) && expr_eq(b, y)) || (expr_eq(a, y) && expr_eq(b, x))
}

#[must_use]
pub(crate) fn is_const_value(expr: &Expr, value: u64) -> bool {
    matches!(expr.kind, Kind::Constant(v) if v == value)
}

#[must_use]
pub(crate) fn is_zero(expr: &Expr) -> bool {
    is_const_value(expr, 0)
}

#[must_use]
pub(crate) fn is_one(expr: &Expr) -> bool {
    is_const_value(expr, 1)
}

/// All-ones at `bitwidth`, not just at 64.
///
/// The hard-coded `u64::MAX` form meant `x | ~x -> -1` was recognized only at
/// bitwidth 64: at 8 the all-ones constant is `0xFF`, so the match failed and
/// no certificate was issued.
#[must_use]
pub(crate) fn is_all_ones_at(expr: &Expr, bitwidth: u32) -> bool {
    matches!(expr.kind, Kind::Constant(v) if v == crate::core::arith::bitmask(bitwidth))
}

#[must_use]
pub(crate) fn is_not_of(expr: &Expr, inner: &Expr) -> bool {
    matches!(expr.kind, Kind::Not) && expr.children.len() == 1 && expr_eq(&expr.children[0], inner)
}

// --- binary/unary child accessors -----------------------------------------

/// `index`-th child of `expr` iff `expr` is the given binary `kind` with
/// exactly two children. Self-guards on arity and kind.
#[must_use]
pub(crate) fn binary_child<'a>(expr: &'a Expr, kind: &Kind, index: usize) -> Option<&'a Expr> {
    if expr.children.len() != 2 || !kind_matches(&expr.kind, kind) {
        return None;
    }
    expr.children.get(index).map(|c| &**c)
}

/// Sole child of `expr` iff `expr` is the given unary `kind` with exactly one
/// child. Self-guards on arity and kind.
#[must_use]
pub(crate) fn unary_child<'a>(expr: &'a Expr, kind: &Kind) -> Option<&'a Expr> {
    if expr.children.len() != 1 || !kind_matches(&expr.kind, kind) {
        return None;
    }
    expr.children.first().map(|c| &**c)
}

/// Kind equality up to payload: `Shr(_)` matches any shift amount; all other
/// kinds compare by discriminant. Used so a single `Kind::Shr(0)` template can
/// gate any `Shr` node.
fn kind_matches(actual: &Kind, expected: &Kind) -> bool {
    match (actual, expected) {
        (Kind::Shr(_), Kind::Shr(_)) => true,
        _ => std::mem::discriminant(actual) == std::mem::discriminant(expected),
    }
}

// --- operand-extraction matchers ------------------------------------------

/// `x + (-y)` (either order) → `(x, y)`. Requires `expr` to be a binary `Add`.
#[must_use]
pub(crate) fn add_with_neg_operands(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let lhs = binary_child(expr, &Kind::Add, 0)?;
    let rhs = binary_child(expr, &Kind::Add, 1)?;
    if let Some(inner) = unary_child(rhs, &Kind::Neg) {
        Some((lhs, inner))
    } else {
        unary_child(lhs, &Kind::Neg).map(|inner| (rhs, inner))
    }
}

/// `x ^ (x & y)` (either XOR operand order, either AND operand order) →
/// `(x, y)`. Used to recognise the `XorAndEqAndNot64` rewrite
/// `x ^ (x & y) = x & ~y`.
#[must_use]
#[allow(clippy::items_after_statements)]
pub(crate) fn xor_and_absorb_operands(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let lhs = binary_child(expr, &Kind::Xor, 0)?;
    let rhs = binary_child(expr, &Kind::Xor, 1)?;
    fn split<'a>(x: &'a Expr, and_node: &'a Expr) -> Option<(&'a Expr, &'a Expr)> {
        let a = binary_child(and_node, &Kind::And, 0)?;
        let b = binary_child(and_node, &Kind::And, 1)?;
        if expr_eq(a, x) {
            Some((x, b))
        } else if expr_eq(b, x) {
            Some((x, a))
        } else {
            None
        }
    }
    split(lhs, rhs).or_else(|| split(rhs, lhs))
}

/// `after == x & ~y` (either AND operand order; the complemented side must be
/// `~y`). Companion check for [`xor_and_absorb_operands`].
#[must_use]
pub(crate) fn is_and_not_of(after: &Expr, x: &Expr, y: &Expr) -> bool {
    let Some(a) = binary_child(after, &Kind::And, 0) else {
        return false;
    };
    let Some(b) = binary_child(after, &Kind::And, 1) else {
        return false;
    };
    let is_not_y = |e: &Expr| unary_child(e, &Kind::Not).is_some_and(|inner| expr_eq(inner, y));
    (expr_eq(a, x) && is_not_y(b)) || (expr_eq(b, x) && is_not_y(a))
}

/// `(a | b)` and `(a & b)` over the same unordered operand pair → `(a, b)`.
#[must_use]
pub(crate) fn same_or_and_operands<'a>(
    or_node: &'a Expr,
    and_node: &'a Expr,
) -> Option<(&'a Expr, &'a Expr)> {
    let or_lhs = binary_child(or_node, &Kind::Or, 0)?;
    let or_rhs = binary_child(or_node, &Kind::Or, 1)?;
    let and_lhs = binary_child(and_node, &Kind::And, 0)?;
    let and_rhs = binary_child(and_node, &Kind::And, 1)?;
    if unordered_pair_eq(or_lhs, or_rhs, and_lhs, and_rhs) {
        Some((or_lhs, or_rhs))
    } else {
        None
    }
}

/// [`same_or_and_operands`] tolerant of which side is the `Or` vs `And`.
#[must_use]
pub(crate) fn and_or_sum_operands<'a>(
    lhs: &'a Expr,
    rhs: &'a Expr,
) -> Option<(&'a Expr, &'a Expr)> {
    same_or_and_operands(lhs, rhs).or_else(|| same_or_and_operands(rhs, lhs))
}

/// `(coeff*(a|b)) + (coeff*(a&b))` → `(a, b)`; `lhs`/`rhs` are the two `Add`
/// operands.
#[must_use]
pub(crate) fn scaled_and_or_sum_operands<'a>(
    lhs: &'a Expr,
    rhs: &'a Expr,
    coeff: u64,
) -> Option<(&'a Expr, &'a Expr)> {
    let lhs = scaled_child(lhs, coeff)?;
    let rhs = scaled_child(rhs, coeff)?;
    and_or_sum_operands(lhs, rhs)
}

/// The non-constant factor of `coeff * x` (either factor order) → `x`.
#[must_use]
pub(crate) fn scaled_child(expr: &Expr, coeff: u64) -> Option<&Expr> {
    let lhs = binary_child(expr, &Kind::Mul, 0)?;
    let rhs = binary_child(expr, &Kind::Mul, 1)?;
    if is_const_value(lhs, coeff) {
        Some(rhs)
    } else if is_const_value(rhs, coeff) {
        Some(lhs)
    } else {
        None
    }
}

/// `(~a | b)` paired with `~a` (the `not_node`) → `(a, b)`. `or_node` is the
/// `Or`; `not_node` is the standalone `Not` whose inner is the shared operand.
#[must_use]
pub(crate) fn not_or_minus_not_operands<'a>(
    or_node: &'a Expr,
    not_node: &'a Expr,
) -> Option<(&'a Expr, &'a Expr)> {
    let a = unary_child(not_node, &Kind::Not)?;
    let lhs = binary_child(or_node, &Kind::Or, 0)?;
    let rhs = binary_child(or_node, &Kind::Or, 1)?;
    if is_not_of(lhs, a) {
        Some((a, rhs))
    } else if is_not_of(rhs, a) {
        Some((a, lhs))
    } else {
        None
    }
}

struct SignedAddend<'a> {
    expr: &'a Expr,
    negated: bool,
}

/// Flatten a nested `Add`/`Neg` tree into a list of signed leaves, tracking the
/// accumulated sign for each leaf.
fn flatten_signed_addends<'a>(expr: &'a Expr, negated: bool, out: &mut Vec<SignedAddend<'a>>) {
    match expr.kind {
        Kind::Add if expr.children.len() == 2 => {
            flatten_signed_addends(&expr.children[0], negated, out);
            flatten_signed_addends(&expr.children[1], negated, out);
        }
        Kind::Neg if expr.children.len() == 1 => {
            flatten_signed_addends(&expr.children[0], !negated, out);
        }
        _ => out.push(SignedAddend { expr, negated }),
    }
}

/// `a + (~a | b) + 1` (in any flattening order, all positive) → `(a, b)`.
#[must_use]
pub(crate) fn not_or_add_self_add_one_operands(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let mut addends = Vec::new();
    flatten_signed_addends(expr, false, &mut addends);
    if addends.len() != 3 || addends.iter().any(|a| a.negated) {
        return None;
    }

    let one_idx = addends.iter().position(|a| is_one(a.expr))?;
    let or_idx = addends
        .iter()
        .enumerate()
        .find(|(idx, a)| *idx != one_idx && matches!(a.expr.kind, Kind::Or))
        .map(|(idx, _)| idx)?;
    let a_idx = (0..3).find(|idx| *idx != one_idx && *idx != or_idx)?;

    let a = addends[a_idx].expr;
    let lhs = binary_child(addends[or_idx].expr, &Kind::Or, 0)?;
    let rhs = binary_child(addends[or_idx].expr, &Kind::Or, 1)?;
    if is_not_of(lhs, a) {
        Some((a, rhs))
    } else if is_not_of(rhs, a) {
        Some((a, lhs))
    } else {
        None
    }
}

/// XOR-via-OR-NOT lowering over the flattened signed addends → `(a, b)`.
#[must_use]
pub(crate) fn xor_via_or_not_operands(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let mut addends = Vec::new();
    flatten_signed_addends(expr, false, &mut addends);
    if addends.len() != 4 {
        return None;
    }

    let neg_two_idx = addends
        .iter()
        .position(|a| a.negated && is_const_value(a.expr, 2))?;
    let (mul_idx, or_node) = addends.iter().enumerate().find_map(|(idx, a)| {
        if idx == neg_two_idx || !a.negated || !matches!(a.expr.kind, Kind::Mul) {
            return None;
        }
        let lhs = binary_child(a.expr, &Kind::Mul, 0)?;
        let rhs = binary_child(a.expr, &Kind::Mul, 1)?;
        if is_const_value(lhs, 2) && matches!(rhs.kind, Kind::Or) {
            Some((idx, rhs))
        } else if is_const_value(rhs, 2) && matches!(lhs.kind, Kind::Or) {
            Some((idx, lhs))
        } else {
            None
        }
    })?;

    let remaining: Vec<_> = (0..4)
        .filter(|idx| *idx != neg_two_idx && *idx != mul_idx)
        .collect();
    if remaining.len() != 2 {
        return None;
    }
    let (a_idx, b_idx) = match (addends[remaining[0]].negated, addends[remaining[1]].negated) {
        (false, true) => (remaining[0], remaining[1]),
        (true, false) => (remaining[1], remaining[0]),
        _ => return None,
    };
    let a = addends[a_idx].expr;
    let b = addends[b_idx].expr;
    let lhs = binary_child(or_node, &Kind::Or, 0)?;
    let rhs = binary_child(or_node, &Kind::Or, 1)?;
    if (expr_eq(lhs, a) && is_not_of(rhs, b)) || (expr_eq(rhs, a) && is_not_of(lhs, b)) {
        Some((a, b))
    } else {
        None
    }
}
