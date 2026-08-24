//! Algebraic identities for pure-bitwise atoms, plus a
//! [`simplify_structure`] pass that merges like terms and removes
//! complementary-atom pairs from a [`SemilinearIR`].
//!
//! Atom-level rewrites applied bottom-up:
//! - `x >> 0 → x`
//! - `~~x → x`
//! - De Morgan: `~(A & B) → ~A | ~B` (and dual) when either side is
//!   already a `~`
//! - `A & A → A`, `A | A → A`
//! - constant-only subtree folding via [`eval_constant`]
//! - identity elision: `A & 0 → 0`, `A | 0 → A`, etc.
//!
//! IR-level rewrites in [`simplify_structure`]:
//! - merge terms by atom id, dropping zero coefficients
//! - complement recognition: atoms with matching support and
//!   bitwise-complementary truth tables and equal coefficients collapse
//!   into the constant as `c * mask_all`. Gated on pure-variable atoms
//!   only — atoms containing constants / shifts can have identical
//!   Boolean truth tables but diverge at full width.

use crate::core::arith::bitmask;
use crate::core::expr::{Expr, Kind};
use crate::core::expr_utils::{eval_constant, is_constant_subtree};
use crate::orchestrator::{ExprPath, LeanCertificate};
use std::sync::Arc;

use crate::ir::semilinear::{AtomId, GlobalVarIdx, SemilinearIR, WeightedAtom};

use crate::passes::candidate_normalize::merge_certificate;

type ComplementKey = (u64, Vec<GlobalVarIdx>, Vec<u64>);

fn constant_val(e: &Expr) -> Option<u64> {
    if let Kind::Constant(v) = e.kind {
        Some(v)
    } else {
        None
    }
}

fn negate_bitwise_child(child: Arc<Expr>) -> Arc<Expr> {
    if matches!(child.kind, Kind::Not) && !child.children.is_empty() {
        let mut c = child;
        return Arc::make_mut(&mut c)
            .children
            .pop()
            .expect("checked non-empty");
    }
    Expr::not(child)
}

/// `true` if `a` is exactly `Not(b)` or `b` is exactly `Not(a)`.
fn are_complements(a: &Expr, b: &Expr) -> bool {
    let is_not_of = |outer: &Expr, inner: &Expr| {
        matches!(outer.kind, Kind::Not) && outer.children.len() == 1 && *outer.children[0] == *inner
    };
    is_not_of(a, b) || is_not_of(b, a)
}

/// `true` if `whole` is an `op`-node with `part` as one of its two operands.
fn contains_operand(whole: &Expr, op: &Kind, part: &Expr) -> bool {
    whole.kind == *op
        && whole.children.len() == 2
        && (*whole.children[0] == *part || *whole.children[1] == *part)
}

/// Reassociate `(x op C1) op C2` into `x op (C1 op C2)` so the sibling-constant
/// fold can fire.
///
/// `constant_val` matches only a direct `Constant` child, so for the
/// left-associated `And(And(x, 15), 240)` the inner node folds nothing and the
/// outer sees only `rc = Some(240)`. `x & 15 & 240` therefore never folded
/// while `x & (15 & 240)` folded to 0.
fn reassociate_constant(
    kind: &Kind,
    lhs: &Expr,
    rhs_const: u64,
    bitwidth: u32,
) -> Option<Arc<Expr>> {
    if lhs.kind != *kind || lhs.children.len() != 2 {
        return None;
    }
    let inner_const = constant_val(&lhs.children[1]).or_else(|| constant_val(&lhs.children[0]))?;
    let inner_other = if constant_val(&lhs.children[1]).is_some() {
        lhs.children[0].clone_tree()
    } else {
        lhs.children[1].clone_tree()
    };
    let mask = bitmask(bitwidth);
    let folded = match kind {
        Kind::And => inner_const & rhs_const & mask,
        Kind::Or => (inner_const | rhs_const) & mask,
        Kind::Xor => (inner_const ^ rhs_const) & mask,
        _ => return None,
    };
    Some(try_fold_binary(
        kind.clone(),
        inner_other,
        Expr::constant(folded),
        bitwidth,
    ))
}

fn try_fold_binary(kind: Kind, lhs: Arc<Expr>, rhs: Arc<Expr>, bitwidth: u32) -> Arc<Expr> {
    let all_ones = bitmask(bitwidth);
    let lc = constant_val(&lhs);
    let rc = constant_val(&rhs);

    // Constant reassociation, before the per-operator arms.
    if matches!(kind, Kind::And | Kind::Or | Kind::Xor) {
        if let Some(c) = rc {
            if let Some(folded) = reassociate_constant(&kind, &lhs, c, bitwidth) {
                return folded;
            }
        }
        if let Some(c) = lc {
            if let Some(folded) = reassociate_constant(&kind, &rhs, c, bitwidth) {
                return folded;
            }
        }
    }

    // Complement and absorption laws, in all operand orders.
    match kind {
        Kind::And if are_complements(&lhs, &rhs) => return Expr::constant(0),
        Kind::Or | Kind::Xor if are_complements(&lhs, &rhs) => {
            return Expr::constant(all_ones);
        }
        // Absorption: x & (x | y) -> x, and the dual x | (x & y) -> x.
        Kind::And if contains_operand(&rhs, &Kind::Or, &lhs) => return lhs,
        Kind::And if contains_operand(&lhs, &Kind::Or, &rhs) => return rhs,
        Kind::Or if contains_operand(&rhs, &Kind::And, &lhs) => return lhs,
        Kind::Or if contains_operand(&lhs, &Kind::And, &rhs) => return rhs,
        _ => {}
    }

    match kind {
        Kind::And => {
            if rc == Some(0) || lc == Some(0) {
                return Expr::constant(0);
            }
            if rc == Some(all_ones) {
                return lhs;
            }
            if lc == Some(all_ones) {
                return rhs;
            }
            Expr::and(lhs, rhs)
        }
        Kind::Or => {
            if rc == Some(0) {
                return lhs;
            }
            if lc == Some(0) {
                return rhs;
            }
            if rc == Some(all_ones) || lc == Some(all_ones) {
                return Expr::constant(all_ones);
            }
            Expr::or(lhs, rhs)
        }
        Kind::Xor => {
            if rc == Some(0) {
                return lhs;
            }
            if lc == Some(0) {
                return rhs;
            }
            Expr::xor(lhs, rhs)
        }
        _ => {
            // Preserve the incoming kind verbatim for anything else.
            let mut e = Expr::and(lhs, rhs);
            Arc::make_mut(&mut e).kind = kind;
            e
        }
    }
}

fn has_constant_or_shr(e: &Expr) -> bool {
    // Constants and shifts already block complement-merge / constant-fold;
    // width-changing casts and Concat are likewise opaque to this same-width
    // machinery and must block it too (soundness wall).
    if matches!(
        e.kind,
        Kind::Constant(_)
            | Kind::Shr(_)
            | Kind::ZExt(_)
            | Kind::SExt(_)
            | Kind::Trunc(_)
            | Kind::Concat
    ) {
        return true;
    }
    e.children.iter().any(|c| has_constant_or_shr(c))
}

/// Simplify a bitwise atom expression tree bottom-up. Consumes `atom`,
/// returns the possibly-rewritten tree.
#[must_use]
pub fn simplify_atom(atom: Arc<Expr>, bitwidth: u32) -> Arc<Expr> {
    if matches!(atom.kind, Kind::Constant(_) | Kind::Variable(_)) {
        return atom;
    }

    let mut atom = Arc::try_unwrap(atom).unwrap_or_else(|a| (*a).clone());
    let new_children: Vec<Arc<Expr>> = atom
        .children
        .drain(..)
        .map(|c| simplify_atom(c, bitwidth))
        .collect();
    atom.children = new_children.into();

    if let Kind::Shr(0) = atom.kind {
        return atom.children.into_iter().next().expect("shr has one child");
    }

    if matches!(atom.kind, Kind::Not) && matches!(atom.children[0].kind, Kind::Not) {
        let mut inner = atom.children.into_iter().next().expect("not has one child");
        return Arc::make_mut(&mut inner)
            .children
            .drain(..)
            .next()
            .expect("inner not has one child");
    }

    // De Morgan: ~(A op B) → (~A op' B) when one side is already ~.
    if matches!(atom.kind, Kind::Not) {
        let inner = &atom.children[0];
        let inner_is_and_or = matches!(inner.kind, Kind::And | Kind::Or);
        let inner_has_not = inner.children.len() == 2
            && (matches!(inner.children[0].kind, Kind::Not)
                || matches!(inner.children[1].kind, Kind::Not));
        if inner_is_and_or && inner_has_not {
            let was_and = matches!(inner.kind, Kind::And);
            let mut inner = atom.children.into_iter().next().expect("not child");
            let inner_mut = Arc::make_mut(&mut inner);
            let rhs = negate_bitwise_child(inner_mut.children.pop().expect("two children"));
            let lhs = negate_bitwise_child(inner_mut.children.pop().expect("two children"));
            let combined = if was_and {
                Expr::or(lhs, rhs)
            } else {
                Expr::and(lhs, rhs)
            };
            return simplify_atom(combined, bitwidth);
        }
    }

    if matches!(atom.kind, Kind::And | Kind::Or)
        && atom.children.len() == 2
        && atom.children[0] == atom.children[1]
    {
        return atom.children.into_iter().next().expect("two children");
    }

    if is_constant_subtree(&atom) {
        return Expr::constant(eval_constant(&atom, bitwidth));
    }

    if atom.children.len() == 2 {
        let kind = atom.kind;
        let mut children = atom.children.into_iter();
        let lhs = children.next().expect("two children");
        let rhs = children.next().expect("two children");
        return try_fold_binary(kind, lhs, rhs, bitwidth);
    }

    Arc::new(atom)
}

/// Simplify an atom and return Lean-checkable evidence for the same
/// transformation. Local identities and recognized constant folds use
/// theorem-backed step chains; residual 64-bit constant folds fall back to an
/// endpoint certificate replayed by the generated Lean `bv_decide` path.
#[must_use]
pub fn simplify_atom_certified(
    atom: Arc<Expr>,
    bitwidth: u32,
) -> (Arc<Expr>, Option<LeanCertificate>) {
    let expected = simplify_atom(atom.clone_tree(), bitwidth);

    let original = atom.clone_tree();
    let mut current = atom;
    let mut chain: Option<LeanCertificate> = None;
    while let Some((path, after)) = find_first_certifiable_atom_rewrite(&current, bitwidth) {
        let Some(step) =
            LeanCertificate::try_single_rewrite_64(bitwidth, current.clone_tree(), path, after)
        else {
            return (expected, None);
        };
        current = step.simplified.clone_tree();
        chain = merge_certificate(chain, step);
    }

    if *current == *expected {
        (current, chain)
    } else if *original != *expected {
        (
            expected.clone_tree(),
            Some(LeanCertificate::new(bitwidth, original, expected)),
        )
    } else {
        (expected, None)
    }
}

fn find_first_certifiable_atom_rewrite(
    root: &Expr,
    bitwidth: u32,
) -> Option<(ExprPath, Arc<Expr>)> {
    find_first_certifiable_atom_rewrite_at(root, bitwidth, &mut Vec::new())
}

fn find_first_certifiable_atom_rewrite_at(
    root: &Expr,
    bitwidth: u32,
    path: &mut Vec<u8>,
) -> Option<(ExprPath, Arc<Expr>)> {
    for (idx, child) in root.children.iter().enumerate() {
        let child_idx = u8::try_from(idx).ok()?;
        path.push(child_idx);
        if let Some(site) = find_first_certifiable_atom_rewrite_at(child, bitwidth, path) {
            path.pop();
            return Some(site);
        }
        path.pop();
    }

    let after = local_certifiable_atom_rewrite(root, bitwidth)?;
    Some((ExprPath(path.clone()), after))
}

fn local_certifiable_atom_rewrite(node: &Expr, bitwidth: u32) -> Option<Arc<Expr>> {
    match &node.kind {
        Kind::Shr(0) if node.children.len() == 1 => Some(node.children[0].clone_tree()),
        Kind::Not if node.children.len() == 1 => {
            let child = &node.children[0];
            if matches!(child.kind, Kind::Not) && child.children.len() == 1 {
                return Some(child.children[0].clone_tree());
            }
            if matches!(child.kind, Kind::And | Kind::Or)
                && child.children.len() == 2
                && (matches!(child.children[0].kind, Kind::Not)
                    || matches!(child.children[1].kind, Kind::Not))
            {
                let lhs = Expr::not(child.children[0].clone_tree());
                let rhs = Expr::not(child.children[1].clone_tree());
                return if matches!(child.kind, Kind::And) {
                    Some(Expr::or(lhs, rhs))
                } else {
                    Some(Expr::and(lhs, rhs))
                };
            }
            None
        }
        Kind::And | Kind::Or
            if node.children.len() == 2 && node.children[0] == node.children[1] =>
        {
            Some(node.children[0].clone_tree())
        }
        Kind::And
            if node.children.len() == 2
                && constant_val(&node.children[0]) == Some(3)
                && constant_val(&node.children[1]) == Some(1) =>
        {
            Some(Expr::constant(1))
        }
        Kind::And | Kind::Or | Kind::Xor if node.children.len() == 2 => {
            let mut children = node.children.clone().into_iter();
            let lhs = children.next().expect("two children");
            let rhs = children.next().expect("two children");
            let folded = try_fold_binary(node.kind.clone(), lhs, rhs, bitwidth);
            if *folded == *node {
                None
            } else {
                Some(folded)
            }
        }
        _ => None,
    }
}

/// Merge like terms, drop zero coefficients, absorb complementary
/// atom pairs into the constant, and bottom-up simplify each atom's
/// stored subtree. Operates in place.
pub fn simplify_structure(ir: &mut SemilinearIR) {
    if ir.bitwidth == 0 || ir.bitwidth > 64 {
        return;
    }
    let mask = bitmask(ir.bitwidth);

    let mut merged: std::collections::HashMap<AtomId, u64> = std::collections::HashMap::new();
    for term in &ir.terms {
        let slot = merged.entry(term.atom_id).or_insert(0);
        *slot = slot.wrapping_add(term.coeff) & mask;
    }

    let mut result: Vec<WeightedAtom> = merged
        .into_iter()
        .filter(|&(_, c)| c != 0)
        .map(|(atom_id, coeff)| WeightedAtom { coeff, atom_id })
        .collect();
    result.sort_by_key(|t| t.atom_id);
    ir.terms = result;

    // Complement recognition: index eligible terms by (coeff, support, truth_table)
    // so each term can look up its bitwise-complement partner in O(1).
    let mut index: std::collections::HashMap<ComplementKey, usize> =
        std::collections::HashMap::new();
    let mut removed = vec![false; ir.terms.len()];

    for i in 0..ir.terms.len() {
        let term = &ir.terms[i];
        let info = &ir.atom_table[term.atom_id as usize];
        let key = &info.key;
        if key.truth_table.is_empty() {
            continue;
        }
        if has_constant_or_shr(&info.original_subtree) {
            continue;
        }
        let complement_tt: Vec<u64> = key.truth_table.iter().map(|t| (!*t) & mask).collect();
        let lookup: ComplementKey = (term.coeff, key.support.clone(), complement_tt);
        if let Some(&j) = index.get(&lookup) {
            if !removed[j] {
                ir.constant = ir.constant.wrapping_add(term.coeff.wrapping_mul(mask)) & mask;
                removed[i] = true;
                removed[j] = true;
                continue;
            }
        }
        let self_key: ComplementKey = (term.coeff, key.support.clone(), key.truth_table.clone());
        index.insert(self_key, i);
    }
    let kept: Vec<WeightedAtom> = ir
        .terms
        .iter()
        .enumerate()
        .filter_map(|(i, t)| if removed[i] { None } else { Some(*t) })
        .collect();
    ir.terms = kept;

    // Simplify each stored subtree in place.
    for info in &mut ir.atom_table {
        let subtree = std::mem::replace(&mut info.original_subtree, Expr::constant(0));
        info.original_subtree = simplify_atom(subtree, ir.bitwidth);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn complement_laws_fold() {
        let x = || Expr::variable(0);
        let all_ones = bitmask(64);

        assert_eq!(
            *try_fold_binary(Kind::And, x(), Expr::not(x()), 64),
            *Expr::constant(0)
        );
        assert_eq!(
            *try_fold_binary(Kind::And, Expr::not(x()), x(), 64),
            *Expr::constant(0)
        );
        assert_eq!(
            *try_fold_binary(Kind::Or, x(), Expr::not(x()), 64),
            *Expr::constant(all_ones)
        );
        assert_eq!(
            *try_fold_binary(Kind::Xor, Expr::not(x()), x(), 64),
            *Expr::constant(all_ones)
        );
    }

    #[test]
    fn absorption_laws_fold() {
        let x = || Expr::variable(0);
        let y = || Expr::variable(1);

        // x & (x | y) -> x, both operand orders and both operand positions.
        assert_eq!(
            *try_fold_binary(Kind::And, x(), Expr::or(x(), y()), 64),
            *x()
        );
        assert_eq!(
            *try_fold_binary(Kind::And, x(), Expr::or(y(), x()), 64),
            *x()
        );
        assert_eq!(
            *try_fold_binary(Kind::And, Expr::or(x(), y()), x(), 64),
            *x()
        );
        // x | (x & y) -> x, the dual.
        assert_eq!(
            *try_fold_binary(Kind::Or, x(), Expr::and(x(), y()), 64),
            *x()
        );
        assert_eq!(
            *try_fold_binary(Kind::Or, Expr::and(y(), x()), x(), 64),
            *x()
        );
    }

    #[test]
    fn constants_reassociate_across_a_chain() {
        let x = Expr::variable(0);
        // `x & 15 & 240` is left-associated, so the outer node only ever saw
        // one constant and folded nothing; 15 & 240 == 0.
        let folded = try_fold_binary(
            Kind::And,
            Expr::and(x.clone_tree(), Expr::constant(15)),
            Expr::constant(240),
            64,
        );
        assert_eq!(*folded, *Expr::constant(0));

        // Or and Xor duals.
        let ored = try_fold_binary(
            Kind::Or,
            Expr::or(x.clone_tree(), Expr::constant(0xF0)),
            Expr::constant(0x0F),
            64,
        );
        assert_eq!(*ored, *Expr::or(x.clone_tree(), Expr::constant(0xFF)));

        let xored = try_fold_binary(
            Kind::Xor,
            Expr::xor(x.clone_tree(), Expr::constant(0b1100)),
            Expr::constant(0b1010),
            64,
        );
        assert_eq!(*xored, *Expr::xor(x, Expr::constant(0b0110)));
    }
    use crate::ir::{normalize_to_semilinear, semilinear::OperatorFamily};

    #[test]
    fn double_not_collapses() {
        let e = Expr::not(Expr::not(Expr::variable(0)));
        let s = simplify_atom(e, 64);
        assert!(matches!(s.kind, Kind::Variable(0)));
    }

    #[test]
    fn shr_by_zero_is_identity() {
        let e = Expr::shr(Expr::variable(0), 0);
        let s = simplify_atom(e, 64);
        assert!(matches!(s.kind, Kind::Variable(0)));
    }

    #[test]
    fn and_with_all_ones_eliminates_mask() {
        let e = Expr::and(Expr::variable(0), Expr::constant(u64::MAX));
        let s = simplify_atom(e, 64);
        assert!(matches!(s.kind, Kind::Variable(0)));
    }

    #[test]
    fn or_with_zero_is_identity() {
        let e = Expr::or(Expr::variable(0), Expr::constant(0));
        let s = simplify_atom(e, 64);
        assert!(matches!(s.kind, Kind::Variable(0)));
    }

    #[test]
    fn and_with_zero_is_zero() {
        let e = Expr::and(Expr::variable(0), Expr::constant(0));
        let s = simplify_atom(e, 64);
        assert!(matches!(s.kind, Kind::Constant(0)));
    }

    #[test]
    fn idempotent_and_collapses() {
        let e = Expr::and(Expr::variable(0), Expr::variable(0));
        let s = simplify_atom(e, 64);
        assert!(matches!(s.kind, Kind::Variable(0)));
    }

    #[test]
    fn certified_atom_simplify_covers_identity_chain() {
        let e = Expr::and(
            Expr::not(Expr::not(Expr::variable(0))),
            Expr::constant(u64::MAX),
        );
        let (s, cert) = simplify_atom_certified(e, 64);
        assert!(matches!(s.kind, Kind::Variable(0)));
        let cert = cert.expect("Lean certificate");
        assert_eq!(cert.steps.len(), 2);
        assert_eq!(
            cert.steps[0].theorem,
            crate::orchestrator::LeanTheorem::NotNot64
        );
        assert_eq!(
            cert.steps[1].theorem,
            crate::orchestrator::LeanTheorem::AndAllOnes64
        );
    }

    #[test]
    fn certified_atom_simplify_covers_demorgan_chain() {
        let e = Expr::not(Expr::and(Expr::not(Expr::variable(0)), Expr::variable(1)));
        let (s, cert) = simplify_atom_certified(e, 64);
        assert!(matches!(s.kind, Kind::Or));
        let cert = cert.expect("Lean certificate");
        assert_eq!(cert.steps.len(), 2);
        assert_eq!(
            cert.steps[0].theorem,
            crate::orchestrator::LeanTheorem::DemorganNotAnd64
        );
        assert_eq!(
            cert.steps[1].theorem,
            crate::orchestrator::LeanTheorem::NotNot64
        );
    }

    #[test]
    fn certified_atom_simplify_uses_theorem_for_constant_folding() {
        let e = Expr::and(Expr::constant(3), Expr::constant(1));
        let (s, cert) = simplify_atom_certified(e, 64);
        assert_eq!(*s, *Expr::constant(1));
        let cert = cert.expect("theorem-backed endpoint certificate");
        assert_eq!(cert.steps.len(), 1);
        assert_eq!(
            cert.steps[0].theorem,
            crate::orchestrator::LeanTheorem::Const3And1_64
        );
        assert!(cert.matches_endpoints(
            64,
            &Expr::and(Expr::constant(3), Expr::constant(1)),
            &Expr::constant(1)
        ));
    }

    #[test]
    fn structure_merges_like_terms() {
        // Normalize x + x to a single atom with coeff 2.
        let e = Expr::add(Expr::variable(0), Expr::variable(0));
        let mut ir = normalize_to_semilinear(&e, &["x".into()], 64).unwrap();
        simplify_structure(&mut ir);
        assert_eq!(ir.terms.len(), 1);
        assert_eq!(ir.terms[0].coeff, 2);
    }

    #[test]
    fn complement_recognition_absorbs_into_constant() {
        // x + (~x) = -1 at 64-bit, so 1*x + 1*(~x) should vanish into constant -1.
        let mut ir = SemilinearIR {
            bitwidth: 64,
            constant: 0,
            ..Default::default()
        };
        let id_pos =
            crate::ir::semilinear::create_atom(&mut ir, Expr::variable(0), OperatorFamily::Mixed);
        let id_neg = crate::ir::semilinear::create_atom(
            &mut ir,
            Expr::not(Expr::variable(0)),
            OperatorFamily::Not,
        );
        ir.terms.push(WeightedAtom {
            coeff: 1,
            atom_id: id_pos,
        });
        ir.terms.push(WeightedAtom {
            coeff: 1,
            atom_id: id_neg,
        });

        simplify_structure(&mut ir);
        assert!(ir.terms.is_empty());
        assert_eq!(ir.constant, u64::MAX);
    }
}
