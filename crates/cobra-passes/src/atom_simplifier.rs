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

use cobra_core::arith::bitmask;
use cobra_core::expr::{Expr, Kind};
use cobra_core::expr_utils::{eval_constant, is_constant_subtree};

use cobra_ir::semilinear::{AtomId, SemilinearIR, WeightedAtom};

fn is_const(e: &Expr) -> bool {
    matches!(e.kind, Kind::Constant(_))
}

fn constant_val(e: &Expr) -> Option<u64> {
    if let Kind::Constant(v) = e.kind {
        Some(v)
    } else {
        None
    }
}

fn negate_bitwise_child(child: Box<Expr>) -> Box<Expr> {
    if matches!(child.kind, Kind::Not) && !child.children.is_empty() {
        let mut c = child;
        return c.children.pop().expect("checked non-empty");
    }
    Expr::not(child)
}

fn try_fold_binary(kind: Kind, lhs: Box<Expr>, rhs: Box<Expr>, bitwidth: u32) -> Box<Expr> {
    let all_ones = bitmask(bitwidth);
    let lc = constant_val(&lhs);
    let rc = constant_val(&rhs);

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
            e.kind = kind;
            e
        }
    }
}

fn exprs_equal(a: &Expr, b: &Expr) -> bool {
    if std::mem::discriminant(&a.kind) != std::mem::discriminant(&b.kind) {
        return false;
    }
    match (&a.kind, &b.kind) {
        (Kind::Constant(x), Kind::Constant(y)) => x == y,
        (Kind::Variable(x), Kind::Variable(y)) | (Kind::Shr(x), Kind::Shr(y)) => x == y,
        _ => {
            if a.children.len() != b.children.len() {
                return false;
            }
            a.children
                .iter()
                .zip(b.children.iter())
                .all(|(c1, c2)| exprs_equal(c1, c2))
        }
    }
}

fn has_constant_or_shr(e: &Expr) -> bool {
    if matches!(e.kind, Kind::Constant(_) | Kind::Shr(_)) {
        return true;
    }
    e.children.iter().any(|c| has_constant_or_shr(c))
}

/// Simplify a bitwise atom expression tree bottom-up. Consumes `atom`,
/// returns the possibly-rewritten tree.
#[must_use]
pub fn simplify_atom(atom: Box<Expr>, bitwidth: u32) -> Box<Expr> {
    if matches!(atom.kind, Kind::Constant(_) | Kind::Variable(_)) {
        return atom;
    }

    let mut atom = atom;
    let new_children: Vec<Box<Expr>> = atom
        .children
        .drain(..)
        .map(|c| simplify_atom(c, bitwidth))
        .collect();
    atom.children = new_children.into();

    if let Kind::Shr(0) = atom.kind {
        return atom.children.into_iter().next().expect("shr has one child");
    }

    if matches!(atom.kind, Kind::Not) && matches!(atom.children[0].kind, Kind::Not) {
        let inner = atom.children.into_iter().next().expect("not has one child");
        return inner
            .children
            .into_iter()
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
            let rhs = negate_bitwise_child(inner.children.pop().expect("two children"));
            let lhs = negate_bitwise_child(inner.children.pop().expect("two children"));
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
        && exprs_equal(&atom.children[0], &atom.children[1])
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

    atom
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

    // Complement recognition.
    let mut removed = vec![false; ir.terms.len()];
    for i in 0..ir.terms.len() {
        if removed[i] {
            continue;
        }
        for j in (i + 1)..ir.terms.len() {
            if removed[j] {
                continue;
            }
            if ir.terms[i].coeff != ir.terms[j].coeff {
                continue;
            }
            let ki = &ir.atom_table[ir.terms[i].atom_id as usize].key;
            let kj = &ir.atom_table[ir.terms[j].atom_id as usize].key;
            if ki.truth_table.is_empty() || kj.truth_table.is_empty() {
                continue;
            }
            if ki.support != kj.support {
                continue;
            }
            if ki.truth_table.len() != kj.truth_table.len() {
                continue;
            }
            let si = &ir.atom_table[ir.terms[i].atom_id as usize];
            let sj = &ir.atom_table[ir.terms[j].atom_id as usize];
            if has_constant_or_shr(&si.original_subtree)
                || has_constant_or_shr(&sj.original_subtree)
            {
                continue;
            }
            let complementary = ki
                .truth_table
                .iter()
                .zip(kj.truth_table.iter())
                .all(|(a, b)| *a == ((!*b) & mask));
            if !complementary {
                continue;
            }
            ir.constant = ir
                .constant
                .wrapping_add(ir.terms[i].coeff.wrapping_mul(mask))
                & mask;
            removed[i] = true;
            removed[j] = true;
            break;
        }
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
    // Touch the unused helper to avoid dead_code warnings in debug builds.
    let _ = is_const;
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_ir::{normalize_to_semilinear, semilinear::OperatorFamily};

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
            cobra_ir::semilinear::create_atom(&mut ir, Expr::variable(0), OperatorFamily::Mixed);
        let id_neg = cobra_ir::semilinear::create_atom(
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
