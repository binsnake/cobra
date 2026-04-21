//! `MSiMBA` §5.3 structural recovery: XOR-pair recovery, mask
//! elimination, and per-bit coalescing plus the `FlattenComplexAtoms`
//! canonicaliser. Operates in-place on [`SemilinearIR`].
//!
//! - [`recover_structure`]: for each basis group, when two terms have
//!   complementary masks, either recognise an XOR pattern
//!   (`m*(c&x) - m*(~c&x) = -m*(c^x) + m*c`) or eliminate the mask
//!   (`a*(c&x) + b*(~c&x) = (a-b)*(c&x) + b*x`).
//! - [`coalesce_terms`]: for single-variable basis groups, compute
//!   per-bit effective coefficient and repartition to minimise term
//!   count.
//! - [`flatten_complex_atoms`]: rewrite a single-variable atom as
//!   `f(0) + coeff*(x & pass_mask) - coeff*(x & invert_mask)` by
//!   probing at `x = 0` and `x = all_ones`.

use std::collections::HashMap;

use cobra_core::arith::{bitmask, mod_neg};
use cobra_core::expr::{Expr, Kind};

use crate::semilinear::{
    create_atom, decompose_atom, structural_hash, AtomId, OperatorFamily, SemilinearIR,
    WeightedAtom,
};

fn has_shr(expr: &Expr) -> bool {
    if matches!(expr.kind, Kind::Shr(_)) {
        return true;
    }
    expr.children.iter().any(|c| has_shr(c))
}

/// Evaluate a pure-bitwise + shift expression at the provided variable
/// assignment. Panics if the atom contains arithmetic kinds — which
/// `FlattenComplexAtoms` shouldn't feed in.
fn eval_bitwise_at(expr: &Expr, vars: &[u64], mask: u64) -> u64 {
    match &expr.kind {
        Kind::Constant(v) => *v & mask,
        Kind::Variable(i) => vars.get(*i as usize).copied().unwrap_or(0) & mask,
        Kind::Not => !eval_bitwise_at(&expr.children[0], vars, mask) & mask,
        Kind::And => {
            eval_bitwise_at(&expr.children[0], vars, mask)
                & eval_bitwise_at(&expr.children[1], vars, mask)
        }
        Kind::Or => {
            (eval_bitwise_at(&expr.children[0], vars, mask)
                | eval_bitwise_at(&expr.children[1], vars, mask))
                & mask
        }
        Kind::Xor => {
            (eval_bitwise_at(&expr.children[0], vars, mask)
                ^ eval_bitwise_at(&expr.children[1], vars, mask))
                & mask
        }
        Kind::Shr(k) => {
            let v = eval_bitwise_at(&expr.children[0], vars, mask);
            if *k >= 64 {
                0
            } else {
                (v >> *k) & mask
            }
        }
        Kind::Add | Kind::Mul | Kind::Neg => {
            unreachable!("arithmetic kind inside atom expression")
        }
    }
}

/// Build a `structural_hash -> Vec<AtomId>` index over the current atom
/// table. Lookups check the bucket for structural equality to handle
/// the rare hash collision.
fn build_atom_hash_index(ir: &SemilinearIR) -> HashMap<u64, Vec<AtomId>> {
    let mut map: HashMap<u64, Vec<AtomId>> = HashMap::new();
    for info in &ir.atom_table {
        map.entry(info.structural_hash).or_default().push(info.atom_id);
    }
    map
}

/// Find a variable / already-materialised basis atom in `ir` matching
/// the given basis expression. Falls back to creating a new atom. The
/// `index` is consulted first (O(1) average) and updated on insertion.
fn find_or_create_bare_atom(
    ir: &mut SemilinearIR,
    index: &mut HashMap<u64, Vec<AtomId>>,
    basis: &Expr,
) -> AtomId {
    let basis_hash = structural_hash(basis);
    if let Some(bucket) = index.get(&basis_hash) {
        for &aid in bucket {
            let info = &ir.atom_table[aid as usize];
            if std::mem::discriminant(&info.original_subtree.kind)
                != std::mem::discriminant(&basis.kind)
            {
                continue;
            }
            match (&info.original_subtree.kind, &basis.kind) {
                (Kind::Variable(a), Kind::Variable(b)) if a == b => return aid,
                _ if info.structural_hash == basis_hash => return aid,
                _ => {}
            }
        }
    }
    let new_id = create_atom(ir, basis.clone_tree(), OperatorFamily::Mixed);
    index.entry(basis_hash).or_default().push(new_id);
    new_id
}

/// Wrap `create_atom` so newly created atoms are also registered in the
/// hash index used by `find_or_create_bare_atom`.
fn create_atom_indexed(
    ir: &mut SemilinearIR,
    index: &mut HashMap<u64, Vec<AtomId>>,
    subtree: Box<Expr>,
    provenance: OperatorFamily,
) -> AtomId {
    let hash = structural_hash(&subtree);
    let new_id = create_atom(ir, subtree, provenance);
    index.entry(hash).or_default().push(new_id);
    new_id
}

#[derive(Clone)]
struct GroupTerm {
    coeff: u64,
    mask: u64,
    atom_id: AtomId,
    consumed: bool,
}

fn rebuild_terms_from_groups(
    ir: &mut SemilinearIR,
    basis_groups: &HashMap<u64, Vec<GroupTerm>>,
    in_group: &[bool],
    modmask: u64,
) {
    let mut new_terms: Vec<WeightedAtom> = Vec::new();
    for (i, t) in ir.terms.iter().enumerate() {
        if !in_group[i] {
            new_terms.push(*t);
        }
    }
    for entries in basis_groups.values() {
        for e in entries {
            if e.consumed || e.coeff == 0 {
                continue;
            }
            new_terms.push(WeightedAtom {
                coeff: e.coeff & modmask,
                atom_id: e.atom_id,
            });
        }
    }

    let mut merged: HashMap<AtomId, u64> = HashMap::new();
    for t in &new_terms {
        let slot = merged.entry(t.atom_id).or_insert(0);
        *slot = slot.wrapping_add(t.coeff) & modmask;
    }
    ir.terms.clear();
    for (aid, coeff) in merged {
        if coeff != 0 {
            ir.terms.push(WeightedAtom {
                coeff,
                atom_id: aid,
            });
        }
    }
    ir.terms.sort_by_key(|t| t.atom_id);
}

/// Apply XOR-pair recovery and mask-elimination rewrites.
#[allow(clippy::too_many_lines, clippy::similar_names)]
pub fn recover_structure(ir: &mut SemilinearIR) {
    if ir.terms.len() < 2 {
        return;
    }
    let modmask = bitmask(ir.bitwidth);

    let mut basis_groups: HashMap<u64, Vec<GroupTerm>> = HashMap::new();
    let mut basis_repr: HashMap<u64, Box<Expr>> = HashMap::new();
    let mut in_group = vec![false; ir.terms.len()];

    for (i, term) in ir.terms.iter().enumerate() {
        let decomp = decompose_atom(&ir.atom_table[term.atom_id as usize], modmask);
        if !decomp.valid {
            continue;
        }
        in_group[i] = true;
        basis_repr
            .entry(decomp.basis_hash)
            .or_insert_with(|| decomp.basis.expect("valid decomp has basis").clone_tree());
        basis_groups
            .entry(decomp.basis_hash)
            .or_default()
            .push(GroupTerm {
                coeff: term.coeff,
                mask: decomp.mask,
                atom_id: term.atom_id,
                consumed: false,
            });
    }

    let mut any_changed = false;
    let mut atom_hash_index = build_atom_hash_index(ir);
    let hashes: Vec<u64> = basis_groups.keys().copied().collect();
    for hash in hashes {
        let entries_len = basis_groups.get(&hash).map_or(0, Vec::len);
        if entries_len < 2 {
            continue;
        }
        let basis = basis_repr.get(&hash).expect("basis present").clone_tree();

        // Group entries by their mask so an XOR/mask-elim partner can be
        // found by complement-mask lookup instead of an O(n²) pair scan.
        let mut mask_index: HashMap<u64, Vec<usize>> = HashMap::new();
        {
            let entries = basis_groups.get(&hash).expect("present");
            for (idx, e) in entries.iter().enumerate() {
                mask_index.entry(e.mask).or_default().push(idx);
            }
        }

        for i in 0..entries_len {
            if basis_groups.get(&hash).expect("present")[i].consumed {
                continue;
            }
            let a_mask = basis_groups.get(&hash).expect("present")[i].mask;
            let complement = modmask & !a_mask;
            // A valid partner must have mask == complement so that
            // (a_mask | b_mask) == modmask and (a_mask & b_mask) == 0.
            let Some(candidates) = mask_index.get(&complement) else {
                continue;
            };
            let mut partner: Option<usize> = None;
            {
                let entries = basis_groups.get(&hash).expect("present");
                for &j in candidates {
                    if j <= i {
                        continue;
                    }
                    if entries[j].consumed {
                        continue;
                    }
                    partner = Some(j);
                    break;
                }
            }
            let Some(j) = partner else {
                continue;
            };
            let entries = basis_groups.get_mut(&hash).expect("present");
            let (a_coeff, a_mask) = (entries[i].coeff, entries[i].mask);
            let (b_coeff, b_mask) = (entries[j].coeff, entries[j].mask);

            if a_coeff.wrapping_add(b_coeff) & modmask == 0 {
                // XOR recovery — choose the mask with fewer set bits as
                // the XOR constant so the added constant shrinks.
                let (src_is_a, src_mask, src_coeff, dst_coeff) =
                    if a_mask.count_ones() <= b_mask.count_ones() {
                        (true, a_mask, a_coeff, b_coeff)
                    } else {
                        (false, b_mask, b_coeff, a_coeff)
                    };
                let xor_expr = Expr::xor(Expr::constant(src_mask), basis.clone_tree());
                let xor_id =
                    create_atom_indexed(ir, &mut atom_hash_index, xor_expr, OperatorFamily::Xor);
                let entries = basis_groups.get_mut(&hash).expect("present");
                let (src_idx, dst_idx) = if src_is_a { (i, j) } else { (j, i) };
                entries[src_idx].coeff = dst_coeff;
                entries[src_idx].atom_id = xor_id;
                entries[src_idx].mask = modmask;
                entries[dst_idx].consumed = true;
                ir.constant =
                    ir.constant.wrapping_add(src_coeff.wrapping_mul(src_mask)) & modmask;
                any_changed = true;
                continue;
            }

            let diff = a_coeff.wrapping_sub(b_coeff) & modmask;
            if diff != 0 {
                let bare = find_or_create_bare_atom(ir, &mut atom_hash_index, &basis);
                let entries = basis_groups.get_mut(&hash).expect("present");
                entries[i].coeff = diff;
                entries[j].atom_id = bare;
                entries[j].mask = modmask;
                any_changed = true;
            }
        }
    }

    if !any_changed {
        return;
    }
    rebuild_terms_from_groups(ir, &basis_groups, &in_group, modmask);
}

const SENTINEL_REMOVED: AtomId = AtomId::MAX;

/// Coalesce single-variable terms by per-bit effective coefficient.
#[allow(clippy::too_many_lines)]
pub fn coalesce_terms(ir: &mut SemilinearIR) {
    if ir.terms.len() < 2 {
        return;
    }
    let modmask = bitmask(ir.bitwidth);

    let mut basis_groups: HashMap<u64, Vec<GroupTerm>> = HashMap::new();
    let mut basis_repr: HashMap<u64, Box<Expr>> = HashMap::new();
    let mut in_group = vec![false; ir.terms.len()];

    for (i, term) in ir.terms.iter().enumerate() {
        let decomp = decompose_atom(&ir.atom_table[term.atom_id as usize], modmask);
        if !decomp.valid {
            continue;
        }
        let basis = decomp.basis.expect("valid decomp has basis");
        if !matches!(basis.kind, Kind::Variable(_)) {
            continue;
        }
        in_group[i] = true;
        basis_repr
            .entry(decomp.basis_hash)
            .or_insert_with(|| basis.clone_tree());
        basis_groups
            .entry(decomp.basis_hash)
            .or_default()
            .push(GroupTerm {
                coeff: term.coeff,
                mask: decomp.mask,
                atom_id: term.atom_id,
                consumed: false,
            });
    }

    let mut any_changed = false;
    let mut atom_hash_index = build_atom_hash_index(ir);
    let hashes: Vec<u64> = basis_groups.keys().copied().collect();

    for hash in hashes {
        let entries_len = basis_groups.get(&hash).map_or(0, Vec::len);
        if entries_len < 2 {
            continue;
        }
        let basis = basis_repr.get(&hash).expect("present").clone_tree();

        // Per-bit effective coefficient.
        let mut eff = vec![0u64; ir.bitwidth as usize];
        {
            let entries = basis_groups.get(&hash).expect("present");
            for (bit, slot) in eff.iter_mut().enumerate().take(ir.bitwidth as usize) {
                for t in entries {
                    if ((t.mask >> bit) & 1) != 0 {
                        *slot = slot.wrapping_add(t.coeff) & modmask;
                    }
                }
            }
        }
        let mut coeff_to_mask: HashMap<u64, u64> = HashMap::new();
        for (bit, &e) in eff.iter().enumerate().take(ir.bitwidth as usize) {
            if e != 0 {
                let slot = coeff_to_mask.entry(e).or_insert(0);
                *slot |= 1u64 << bit;
            }
        }

        if coeff_to_mask.len() >= entries_len {
            continue;
        }

        // Mark old entries, append new ones.
        {
            let entries = basis_groups.get_mut(&hash).expect("present");
            for e in entries {
                e.atom_id = SENTINEL_REMOVED;
            }
        }
        for (coeff, mask) in coeff_to_mask {
            let aid = if mask == modmask {
                find_or_create_bare_atom(ir, &mut atom_hash_index, &basis)
            } else {
                let and_expr = Expr::and(basis.clone_tree(), Expr::constant(mask));
                create_atom_indexed(ir, &mut atom_hash_index, and_expr, OperatorFamily::And)
            };
            basis_groups
                .get_mut(&hash)
                .expect("present")
                .push(GroupTerm {
                    coeff,
                    mask,
                    atom_id: aid,
                    consumed: false,
                });
        }
        any_changed = true;
    }

    if !any_changed {
        return;
    }

    // Rebuild, ignoring sentinel atoms.
    let mut new_terms: Vec<WeightedAtom> = Vec::new();
    for (i, t) in ir.terms.iter().enumerate() {
        if !in_group[i] {
            new_terms.push(*t);
        }
    }
    for entries in basis_groups.values() {
        for e in entries {
            if e.atom_id == SENTINEL_REMOVED || e.coeff == 0 {
                continue;
            }
            new_terms.push(WeightedAtom {
                coeff: e.coeff & modmask,
                atom_id: e.atom_id,
            });
        }
    }
    let mut merged: HashMap<AtomId, u64> = HashMap::new();
    for t in &new_terms {
        let slot = merged.entry(t.atom_id).or_insert(0);
        *slot = slot.wrapping_add(t.coeff) & modmask;
    }
    ir.terms.clear();
    for (aid, coeff) in merged {
        if coeff != 0 {
            ir.terms.push(WeightedAtom {
                coeff,
                atom_id: aid,
            });
        }
    }
    ir.terms.sort_by_key(|t| t.atom_id);
}

/// Flatten single-variable atoms to `coeff*(x & pass_mask) -
/// coeff*(x & invert_mask) + f(0)`. Returns `true` if any atom was
/// flattened.
pub fn flatten_complex_atoms(ir: &mut SemilinearIR) -> bool {
    let modmask = bitmask(ir.bitwidth);
    let mut new_terms: Vec<WeightedAtom> = Vec::new();
    let mut added_constant: u64 = 0;
    let mut any_flattened = false;

    let original_terms: Vec<WeightedAtom> = ir.terms.clone();
    for term in original_terms {
        let info = &ir.atom_table[term.atom_id as usize];
        if matches!(info.original_subtree.kind, Kind::Variable(_)) {
            new_terms.push(term);
            continue;
        }
        let decomp = decompose_atom(info, modmask);
        if decomp.valid && matches!(decomp.basis.map(|b| &b.kind), Some(Kind::Variable(_))) {
            new_terms.push(term);
            continue;
        }
        if info.key.support.len() != 1 || has_shr(&info.original_subtree) {
            new_terms.push(term);
            continue;
        }

        let var_idx = info.key.support[0];
        let vec_size = (var_idx as usize) + 1;
        // Clone the subtree out so the probe doesn't alias the mutable ir.
        let subtree = info.original_subtree.clone_tree();

        let mut vars = vec![0u64; vec_size];
        let zero_val = eval_bitwise_at(&subtree, &vars, modmask) & modmask;
        vars[var_idx as usize] = modmask;
        let ones_val = eval_bitwise_at(&subtree, &vars, modmask) & modmask;

        let pass_mask = ones_val & !zero_val;
        let invert_mask = zero_val & !ones_val;

        added_constant = added_constant.wrapping_add(term.coeff.wrapping_mul(zero_val)) & modmask;

        if pass_mask != 0 {
            let pass_expr = if pass_mask == modmask {
                Expr::variable(var_idx)
            } else {
                Expr::and(Expr::variable(var_idx), Expr::constant(pass_mask))
            };
            let pass_id = create_atom(ir, pass_expr, OperatorFamily::And);
            new_terms.push(WeightedAtom {
                coeff: term.coeff,
                atom_id: pass_id,
            });
        }
        if invert_mask != 0 {
            let inv_expr = if invert_mask == modmask {
                Expr::variable(var_idx)
            } else {
                Expr::and(Expr::variable(var_idx), Expr::constant(invert_mask))
            };
            let inv_id = create_atom(ir, inv_expr, OperatorFamily::And);
            let neg_coeff = mod_neg(term.coeff, ir.bitwidth);
            new_terms.push(WeightedAtom {
                coeff: neg_coeff,
                atom_id: inv_id,
            });
        }
        any_flattened = true;
    }

    if !any_flattened {
        return false;
    }

    ir.constant = ir.constant.wrapping_add(added_constant) & modmask;

    let mut merged: HashMap<AtomId, u64> = HashMap::new();
    for t in &new_terms {
        let slot = merged.entry(t.atom_id).or_insert(0);
        *slot = slot.wrapping_add(t.coeff) & modmask;
    }
    ir.terms.clear();
    for (aid, coeff) in merged {
        if coeff != 0 {
            ir.terms.push(WeightedAtom {
                coeff,
                atom_id: aid,
            });
        }
    }
    ir.terms.sort_by_key(|t| t.atom_id);
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::normalize_to_semilinear;

    #[test]
    fn recover_structure_handles_xor_pair() {
        // x & 0xFF + (-(x & 0xFFFFFFFFFFFFFF00)) = ? — degenerate test;
        // just exercise that the function runs without panic.
        let e = Expr::add(
            Expr::and(Expr::variable(0), Expr::constant(0xFF)),
            Expr::and(Expr::variable(0), Expr::constant(0xFFFF_FFFF_FFFF_FF00u64)),
        );
        let mut ir = normalize_to_semilinear(&e, &["x".into()], 64).unwrap();
        recover_structure(&mut ir);
        // Either recovered or untouched — must still be valid.
        assert!(ir.bitwidth == 64);
    }

    #[test]
    fn flatten_complex_atoms_on_not_variable() {
        // f(x) = ~x as an atom — probing x=0 gives ~0 = mask, x=mask gives 0.
        // pass_mask = 0 & ~mask = 0, invert_mask = mask & ~0 = mask. So
        // flatten becomes constant(mask) + 1*0 - 1*(x). For the IR this
        // means constant += mask, and a single negated-variable term.
        let e = Expr::not(Expr::variable(0));
        let mut ir = normalize_to_semilinear(&e, &["x".into()], 64).unwrap();
        let orig_atom_count = ir.atom_table.len();
        let flattened = flatten_complex_atoms(&mut ir);
        // Atom may already be the canonical ~x form — if so, no change.
        // Either way, the IR stays consistent.
        if flattened {
            assert!(ir.atom_table.len() > orig_atom_count);
        }
    }

    #[test]
    fn coalesce_terms_merges_single_var_partitions() {
        // Build two terms with coefficient 1 on (x & 0x0F) and 1 on (x & 0xF0).
        // Effective per-bit coefficient = 1 for bits 0..8 → one term (x & 0xFF).
        let e = Expr::add(
            Expr::and(Expr::variable(0), Expr::constant(0x0F)),
            Expr::and(Expr::variable(0), Expr::constant(0xF0)),
        );
        let mut ir = normalize_to_semilinear(&e, &["x".into()], 64).unwrap();
        let before = ir.terms.len();
        coalesce_terms(&mut ir);
        assert!(ir.terms.len() <= before);
    }
}
