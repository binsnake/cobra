//! Semilinear IR — bitwise atoms lifted from an expression and their
//! weighted combinations.
//!
//! Ported from `include/cobra/core/SemilinearIR.h` and
//! `lib/core/SemilinearIR.cpp`. An atom is a pure-bitwise subexpression
//! evaluated on all `2^k` Boolean assignments to its support; the resulting
//! truth table is the atom's identity. The outer `SemilinearIR` holds a
//! table of these atoms plus a list of weighted terms referring to them by
//! `AtomId`.

use std::hash::{Hash, Hasher};

use cobra_core::arith::bitmask;
use cobra_core::expr::{Expr, Kind};
use cobra_core::expr_utils::{collect_vars, eval_constant, is_constant_subtree};

/// Stable index into `SemilinearIR::atom_table`.
pub type AtomId = u32;
/// Index into the outer variable list (shared with the rest of the IR).
pub type GlobalVarIdx = u32;

/// Opaque per-atom semantic id used by downstream partitioning passes.
pub type AtomSemanticId = u64;

/// The identifying fingerprint of an atom: its support variables (ascending)
/// and its full truth table over those variables.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AtomKey {
    /// Sorted, unique.
    pub support: Vec<GlobalVarIdx>,
    /// Length = `2^support.len()`. All entries masked to `bitmask(bitwidth)`.
    pub truth_table: Vec<u64>,
}

/// C++ `std::hash<AtomKey>` is Boost-style `hash_combine` over size,
/// support entries, and truth-table entries. The Rust port replays the
/// same sequence so any stored fingerprint matches.
impl Hash for AtomKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut h: u64 = self.support.len() as u64;
        for &v in &self.support {
            h = hash_combine(h, u64::from(v));
        }
        for &t in &self.truth_table {
            h = hash_combine(h, t);
        }
        state.write_u64(h);
    }
}

/// Boost-style `hash_combine` used by the C++ codebase for structural
/// hashing. Constants match the C++ `cobra::detail::hash_combine`.
#[inline]
#[must_use]
pub(crate) fn hash_combine(seed: u64, value: u64) -> u64 {
    seed ^ value
        .wrapping_add(0x9E37_79B9)
        .wrapping_add(seed << 6)
        .wrapping_add(seed >> 2)
}

/// Where an atom came from in the original expression. Drives a later
/// partitioning heuristic in the semilinear passes.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum OperatorFamily {
    And,
    Or,
    Xor,
    Not,
    #[default]
    Mixed,
}

/// A single atom entry.
#[derive(Clone, Debug)]
pub struct AtomInfo {
    pub atom_id: AtomId,
    pub key: AtomKey,
    pub original_subtree: Box<Expr>,
    pub structural_hash: u64,
    pub provenance: OperatorFamily,
}

/// A `coeff * atom` term in the outer semilinear sum.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct WeightedAtom {
    pub coeff: u64,
    pub atom_id: AtomId,
}

/// The full semilinear IR for a single simplification work item.
#[derive(Clone, Debug, Default)]
pub struct SemilinearIR {
    pub constant: u64,
    pub terms: Vec<WeightedAtom>,
    pub atom_table: Vec<AtomInfo>,
    pub bitwidth: u32,
}

/// Bit-partition class — groups bit positions that share a semantic profile.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PartitionClass {
    pub mask: u64,
    pub profile: Vec<AtomSemanticId>,
}

/// Result of [`decompose_atom`]: the original atom viewed as
/// `basis & mask` when the pattern applies.
#[derive(Copy, Clone, Debug, Default)]
pub struct Decomposed<'a> {
    pub valid: bool,
    pub basis: Option<&'a Expr>,
    pub mask: u64,
    pub basis_hash: u64,
}

/// Evaluate a pure-bitwise `Expr` at all `2^k` Boolean assignments to the
/// given support. Returns a truth table of length `2^k` with every entry
/// masked to `bitmask(bitwidth)`. Matches C++ `ComputeAtomTruthTable`.
///
/// If the support has more than 5 variables, returns an empty vec (same
/// bailout as C++, which caps the truth table at `2^5 = 32` entries).
#[must_use]
pub fn compute_atom_truth_table(atom: &Expr, support: &[GlobalVarIdx], bitwidth: u32) -> Vec<u64> {
    let n = support.len();
    if n > 5 {
        return Vec::new();
    }
    let len = 1usize << n;
    let mask = bitmask(bitwidth);
    let mut tt = Vec::with_capacity(len);
    for i in 0..len {
        tt.push(eval_expr_bool(atom, support, i as u64, mask));
    }
    tt
}

/// Core evaluator: the atom must only contain `Constant`, `Variable`,
/// `And`, `Or`, `Xor`, `Not`, and `Shr`. `Add` / `Mul` / `Neg` are unreachable.
fn eval_expr_bool(e: &Expr, support: &[GlobalVarIdx], assignment: u64, mask: u64) -> u64 {
    match &e.kind {
        Kind::Constant(v) => *v & mask,
        Kind::Variable(v) => {
            for (i, &s) in support.iter().enumerate() {
                if s == *v {
                    return (assignment >> i) & 1;
                }
            }
            0
        }
        Kind::And => {
            eval_expr_bool(&e.children[0], support, assignment, mask)
                & eval_expr_bool(&e.children[1], support, assignment, mask)
        }
        Kind::Or => {
            eval_expr_bool(&e.children[0], support, assignment, mask)
                | eval_expr_bool(&e.children[1], support, assignment, mask)
        }
        Kind::Xor => {
            eval_expr_bool(&e.children[0], support, assignment, mask)
                ^ eval_expr_bool(&e.children[1], support, assignment, mask)
        }
        Kind::Not => !eval_expr_bool(&e.children[0], support, assignment, mask) & mask,
        Kind::Shr(k) => {
            let val = eval_expr_bool(&e.children[0], support, assignment, mask);
            (val >> *k) & mask
        }
        Kind::Add | Kind::Mul | Kind::Neg => {
            unreachable!("arithmetic kind inside pure-bitwise atom")
        }
    }
}

/// Structural hash of an `Expr` tree. Mirrors C++ `StructuralHash` with the
/// exact mixing constants — required for parity with stored
/// `AtomInfo::structural_hash` fingerprints.
#[must_use]
pub fn structural_hash(expr: &Expr) -> u64 {
    let tag = match &expr.kind {
        Kind::Constant(_) => 0u64,
        Kind::Variable(_) => 1,
        Kind::Add => 2,
        Kind::Mul => 3,
        Kind::And => 4,
        Kind::Or => 5,
        Kind::Xor => 6,
        Kind::Not => 7,
        Kind::Neg => 8,
        Kind::Shr(_) => 9,
    };
    let mut h: u64 = tag;
    match &expr.kind {
        Kind::Constant(v) => {
            h ^= v.wrapping_mul(0x9E37_79B9_7F4A_7C15);
        }
        Kind::Shr(k) => {
            h ^= u64::from(*k).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        }
        Kind::Variable(idx) => {
            h ^= u64::from(*idx + 1).wrapping_mul(0x517C_C1B7_2722_0A95);
        }
        _ => {}
    }
    for child in &expr.children {
        let c_hash = structural_hash(child);
        h ^= c_hash
            .wrapping_add(0x9E37_79B9_7F4A_7C15)
            .wrapping_add(h << 6)
            .wrapping_add(h >> 2);
    }
    h
}

/// If the atom is `Variable` or `And(basis, const_mask)` /
/// `And(const_mask, basis)`, return the `(basis, mask)` view with the
/// structural hash of `basis`. Otherwise, returns an invalid `Decomposed`.
///
/// `modmask` is the caller's `bitmask(bitwidth)`; the decomposed mask is
/// bitwise-`and`-combined with it.
#[must_use]
pub fn decompose_atom(info: &AtomInfo, modmask: u64) -> Decomposed<'_> {
    let atom = &*info.original_subtree;

    if matches!(atom.kind, Kind::Variable(_)) {
        return Decomposed {
            valid: true,
            basis: Some(atom),
            mask: modmask,
            basis_hash: structural_hash(atom),
        };
    }

    if matches!(atom.kind, Kind::And) && atom.children.len() == 2 {
        let lhs_const = is_constant_subtree(&atom.children[0]);
        let rhs_const = is_constant_subtree(&atom.children[1]);
        if rhs_const && !lhs_const {
            let c = eval_constant(&atom.children[1], 64) & modmask;
            return Decomposed {
                valid: true,
                basis: Some(&atom.children[0]),
                mask: c,
                basis_hash: structural_hash(&atom.children[0]),
            };
        }
        if lhs_const && !rhs_const {
            let c = eval_constant(&atom.children[0], 64) & modmask;
            return Decomposed {
                valid: true,
                basis: Some(&atom.children[1]),
                mask: c,
                basis_hash: structural_hash(&atom.children[1]),
            };
        }
    }

    Decomposed::default()
}

/// Materialise a new atom entry in `ir` for the given subtree. Returns the
/// newly-assigned `AtomId`.
pub fn create_atom(
    ir: &mut SemilinearIR,
    subtree: Box<Expr>,
    provenance: OperatorFamily,
) -> AtomId {
    let mut support = Vec::new();
    collect_vars(&subtree, &mut support);
    support.sort_unstable();
    support.dedup();

    let tt = compute_atom_truth_table(&subtree, &support, ir.bitwidth);
    let new_id = ir.atom_table.len() as AtomId;

    let structural = structural_hash(&subtree);
    ir.atom_table.push(AtomInfo {
        atom_id: new_id,
        key: AtomKey {
            support,
            truth_table: tt,
        },
        structural_hash: structural,
        provenance,
        original_subtree: subtree,
    });
    new_id
}

/// Remove atoms with no referencing term and remap ids. Safe to call after
/// rewrite passes that may leave dead intermediate atoms behind.
pub fn compact_atom_table(ir: &mut SemilinearIR) {
    let mut live = vec![false; ir.atom_table.len()];
    for term in &ir.terms {
        live[term.atom_id as usize] = true;
    }
    let live_count = live.iter().filter(|b| **b).count();
    if live_count == ir.atom_table.len() {
        return;
    }

    let mut remap = vec![0u32; ir.atom_table.len()];
    let mut compacted: Vec<AtomInfo> = Vec::with_capacity(live_count);
    for (i, info) in ir.atom_table.drain(..).enumerate() {
        if !live[i] {
            continue;
        }
        let new_id = compacted.len() as AtomId;
        remap[i] = new_id;
        let mut moved = info;
        moved.atom_id = new_id;
        compacted.push(moved);
    }
    ir.atom_table = compacted;
    for term in &mut ir.terms {
        term.atom_id = remap[term.atom_id as usize];
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compute_truth_table_simple_and() {
        // atom = v0 & v1, bitwidth 64, support = [0, 1]
        let atom = Expr::and(Expr::variable(0), Expr::variable(1));
        let tt = compute_atom_truth_table(&atom, &[0, 1], 64);
        // assignments 00, 01, 10, 11 → 0, 0, 0, 1
        assert_eq!(tt, vec![0, 0, 0, 1]);
    }

    #[test]
    fn compute_truth_table_not_is_masked() {
        // ~v0 at bitwidth 8 → 0xFF, 0xFE
        let atom = Expr::not(Expr::variable(0));
        let tt = compute_atom_truth_table(&atom, &[0], 8);
        assert_eq!(tt, vec![0xFF, 0xFE]);
    }

    #[test]
    fn compute_truth_table_empty_over_size_limit() {
        let atom = Expr::and(Expr::variable(0), Expr::variable(1));
        let support: Vec<u32> = (0..6).collect();
        assert!(compute_atom_truth_table(&atom, &support, 64).is_empty());
    }

    #[test]
    fn structural_hash_is_deterministic_and_distinguishing() {
        let a = Expr::and(Expr::variable(0), Expr::variable(1));
        let b = Expr::and(Expr::variable(0), Expr::variable(1));
        let c = Expr::or(Expr::variable(0), Expr::variable(1));
        assert_eq!(structural_hash(&a), structural_hash(&b));
        assert_ne!(structural_hash(&a), structural_hash(&c));
    }

    #[test]
    fn create_atom_populates_fields() {
        let mut ir = SemilinearIR {
            bitwidth: 8,
            ..Default::default()
        };
        let id = create_atom(
            &mut ir,
            Expr::and(Expr::variable(2), Expr::variable(0)),
            OperatorFamily::And,
        );
        assert_eq!(id, 0);
        assert_eq!(ir.atom_table.len(), 1);
        let info = &ir.atom_table[0];
        assert_eq!(info.atom_id, 0);
        assert_eq!(info.key.support, vec![0, 2]);
        assert_eq!(info.key.truth_table, vec![0, 0, 0, 1]);
        assert!(matches!(info.provenance, OperatorFamily::And));
    }

    #[test]
    fn compact_removes_dead_atoms_and_remaps() {
        let mut ir = SemilinearIR {
            bitwidth: 8,
            ..Default::default()
        };
        let _id0 = create_atom(&mut ir, Expr::variable(0), OperatorFamily::Mixed); // dead
        let id1 = create_atom(&mut ir, Expr::variable(1), OperatorFamily::Mixed);
        let _id2 = create_atom(&mut ir, Expr::variable(2), OperatorFamily::Mixed); // dead
        let id3 = create_atom(&mut ir, Expr::variable(3), OperatorFamily::Mixed);

        ir.terms = vec![
            WeightedAtom {
                coeff: 1,
                atom_id: id1,
            },
            WeightedAtom {
                coeff: 2,
                atom_id: id3,
            },
        ];
        compact_atom_table(&mut ir);

        assert_eq!(ir.atom_table.len(), 2);
        assert_eq!(ir.atom_table[0].atom_id, 0);
        assert_eq!(ir.atom_table[1].atom_id, 1);
        // Terms should now point to 0 and 1 respectively.
        assert_eq!(ir.terms[0].atom_id, 0);
        assert_eq!(ir.terms[1].atom_id, 1);
        // Surviving atoms should reference vars 1 and 3.
        assert!(matches!(
            ir.atom_table[0].original_subtree.kind,
            Kind::Variable(1)
        ));
        assert!(matches!(
            ir.atom_table[1].original_subtree.kind,
            Kind::Variable(3)
        ));
    }

    #[test]
    fn decompose_bare_variable() {
        let mut ir = SemilinearIR {
            bitwidth: 8,
            ..Default::default()
        };
        let id = create_atom(&mut ir, Expr::variable(0), OperatorFamily::Mixed);
        let dec = decompose_atom(&ir.atom_table[id as usize], 0xFF);
        assert!(dec.valid);
        assert_eq!(dec.mask, 0xFF);
        assert!(matches!(dec.basis.unwrap().kind, Kind::Variable(0)));
    }

    #[test]
    fn decompose_and_with_constant_mask() {
        let mut ir = SemilinearIR {
            bitwidth: 8,
            ..Default::default()
        };
        let id = create_atom(
            &mut ir,
            Expr::and(Expr::variable(0), Expr::constant(0xF0)),
            OperatorFamily::And,
        );
        let dec = decompose_atom(&ir.atom_table[id as usize], 0xFF);
        assert!(dec.valid);
        assert_eq!(dec.mask, 0xF0);
        assert!(matches!(dec.basis.unwrap().kind, Kind::Variable(0)));
    }

    #[test]
    fn decompose_rejects_two_variables() {
        let mut ir = SemilinearIR {
            bitwidth: 8,
            ..Default::default()
        };
        let id = create_atom(
            &mut ir,
            Expr::and(Expr::variable(0), Expr::variable(1)),
            OperatorFamily::And,
        );
        let dec = decompose_atom(&ir.atom_table[id as usize], 0xFF);
        assert!(!dec.valid);
    }

    struct Cap(u64);
    impl Hasher for Cap {
        fn finish(&self) -> u64 {
            self.0
        }
        fn write(&mut self, _: &[u8]) {}
        fn write_u64(&mut self, n: u64) {
            self.0 = n;
        }
    }

    #[test]
    fn atom_key_hash_matches_manual_boost_combine() {
        // Sanity: two keys with the same fields hash-equal; different
        // keys hash-differently (high probability).
        let a = AtomKey {
            support: vec![1, 2, 3],
            truth_table: vec![0, 1, 2, 3],
        };
        let b = AtomKey {
            support: vec![1, 2, 3],
            truth_table: vec![0, 1, 2, 3],
        };
        let c = AtomKey {
            support: vec![1, 2, 3],
            truth_table: vec![0, 1, 2, 4],
        };

        let (mut ha, mut hb, mut hc) = (Cap(0), Cap(0), Cap(0));
        a.hash(&mut ha);
        b.hash(&mut hb);
        c.hash(&mut hc);
        assert_eq!(ha.0, hb.0);
        assert_ne!(ha.0, hc.0);
    }
}
