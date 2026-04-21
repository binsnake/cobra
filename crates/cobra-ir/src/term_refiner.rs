//! `MSiMBA` §5.2 per-group term refinement: mask reduction, zero-term
//! elimination, disjoint-mask merging, coefficient matching, `-1`
//! normalisation, and three-term collapse.
//!
//! All predicates work modulo `2^bitwidth`. The entry point
//! [`refine_terms`] groups [`SemilinearIR`] terms by basis and applies
//! the six-step refinement to each group.

use std::collections::HashMap;

use cobra_core::arith::bitmask;
use cobra_core::expr::Expr;

use crate::semilinear::{
    create_atom, decompose_atom, AtomId, OperatorFamily, SemilinearIR, WeightedAtom,
};

/// Mask of bits of `x` that survive `coeff.wrapping_mul(x)` modulo
/// `2^bitwidth`. Bit `i` survives iff `i + coeff.trailing_zeros() < bitwidth`.
#[must_use]
fn effective_mask(coeff: u64, bitwidth: u32) -> u64 {
    let tz = coeff.trailing_zeros();
    if tz >= bitwidth {
        0
    } else {
        bitmask(bitwidth - tz)
    }
}

/// True iff `old_coeff * (bit & bitmask) == new_coeff * (bit & bitmask)`
/// mod `2^bitwidth` for every single-bit `bit`.
#[must_use]
pub fn can_change_coefficient_to(
    old_coeff: u64,
    new_coeff: u64,
    bitmask_val: u64,
    bitwidth: u32,
) -> bool {
    // Equivalent to `(old_coeff - new_coeff) * (bit & bitmask_val) == 0`
    // for every single bit. That holds iff every set bit of
    // `bitmask_val` lies at position `>= bitwidth - tz(d)`.
    let modmask = bitmask(bitwidth);
    let d = old_coeff.wrapping_sub(new_coeff) & modmask;
    (bitmask_val & effective_mask(d, bitwidth)) == 0
}

/// True iff `coeff * (old_mask & x) == coeff * (new_mask & x)` mod
/// `2^bitwidth` for all `x`.
#[must_use]
pub fn can_change_mask_to(coeff: u64, old_mask: u64, new_mask: u64, bitwidth: u32) -> bool {
    // Differing bits must all be zeroed by `coeff`.
    ((old_mask ^ new_mask) & effective_mask(coeff, bitwidth)) == 0
}

/// Strip bits from `mask` whose contribution is zeroed by `coeff`.
#[must_use]
pub fn reduce_mask(coeff: u64, mask: u64, bitwidth: u32) -> u64 {
    mask & effective_mask(coeff, bitwidth)
}

#[derive(Clone)]
struct RefineTerm {
    coeff: u64,
    mask: u64,
    atom_id: AtomId,
    consumed: bool,
}

fn create_masked_atom(ir: &mut SemilinearIR, basis: &Expr, mask: u64) -> AtomId {
    let expr = Expr::and(basis.clone_tree(), Expr::constant(mask));
    create_atom(ir, expr, OperatorFamily::And)
}

fn try_merge_pair(
    group: &mut [RefineTerm],
    i: usize,
    j: usize,
    ir: &mut SemilinearIR,
    basis: &Expr,
    modmask: u64,
) -> bool {
    if group[i].consumed || group[j].consumed {
        return false;
    }
    if (group[i].mask & group[j].mask) != 0 {
        return false;
    }

    let (a_coeff, a_mask, b_coeff, b_mask) =
        (group[i].coeff, group[i].mask, group[j].coeff, group[j].mask);

    if a_coeff == b_coeff {
        let merged_mask = (a_mask | b_mask) & modmask;
        let aid = create_masked_atom(ir, basis, merged_mask);
        group[i].atom_id = aid;
        group[i].mask = merged_mask;
        group[j].consumed = true;
        return true;
    }

    if can_change_coefficient_to(b_coeff, a_coeff, b_mask, ir.bitwidth) {
        let merged_mask = (a_mask | b_mask) & modmask;
        let aid = create_masked_atom(ir, basis, merged_mask);
        group[j].coeff = a_coeff;
        group[i].atom_id = aid;
        group[i].mask = merged_mask;
        group[j].consumed = true;
        return true;
    }
    if can_change_coefficient_to(a_coeff, b_coeff, a_mask, ir.bitwidth) {
        let merged_mask = (a_mask | b_mask) & modmask;
        let aid = create_masked_atom(ir, basis, merged_mask);
        group[i].coeff = b_coeff;
        group[i].atom_id = aid;
        group[i].mask = merged_mask;
        group[j].consumed = true;
        return true;
    }
    false
}

#[allow(clippy::similar_names)]
fn try_three_term_collapse(
    group: &mut [RefineTerm],
    ir: &mut SemilinearIR,
    basis: &Expr,
    modmask: u64,
) -> bool {
    let modn = bitmask(ir.bitwidth);
    // Index live terms by coefficient so for each pair (i, j) we can
    // O(1)-locate a candidate k whose coeff equals (c_i + c_j) mod 2^bw.
    let mut by_coeff: HashMap<u64, Vec<usize>> = HashMap::new();
    for (idx, t) in group.iter().enumerate() {
        if !t.consumed {
            by_coeff.entry(t.coeff).or_default().push(idx);
        }
    }
    for i in 0..group.len() {
        if group[i].consumed {
            continue;
        }
        for j in (i + 1)..group.len() {
            if group[j].consumed {
                continue;
            }
            let target = group[i].coeff.wrapping_add(group[j].coeff) & modn;
            let Some(cands) = by_coeff.get(&target) else {
                continue;
            };
            let (a_mask, b_mask) = (group[i].mask, group[j].mask);
            for &k in cands {
                if k == i || k == j || group[k].consumed {
                    continue;
                }
                let c_mask = group[k].mask;
                if (a_mask & c_mask) != 0 || (b_mask & c_mask) != 0 {
                    continue;
                }
                let mask_ac = (a_mask | c_mask) & modmask;
                let mask_bc = (b_mask | c_mask) & modmask;
                let aid_ac = create_masked_atom(ir, basis, mask_ac);
                let aid_bc = create_masked_atom(ir, basis, mask_bc);
                group[i].atom_id = aid_ac;
                group[i].mask = mask_ac;
                group[j].atom_id = aid_bc;
                group[j].mask = mask_bc;
                group[k].consumed = true;
                return true;
            }
        }
    }
    false
}

#[allow(clippy::too_many_lines)]
fn refine_group(group: &mut [RefineTerm], ir: &mut SemilinearIR, basis: &Expr, modmask: u64) {
    let bw = ir.bitwidth;

    // Step 0: reduce masks.
    for t in group.iter_mut() {
        if t.consumed {
            continue;
        }
        let reduced = reduce_mask(t.coeff, t.mask, bw);
        if reduced != t.mask {
            t.mask = reduced;
        }
    }
    // Rebuild atoms for any reduced masks after the loop to avoid
    // overlapping &mut borrows.
    for t in group.iter_mut() {
        if t.consumed {
            continue;
        }
        let new_id = create_masked_atom(ir, basis, t.mask);
        t.atom_id = new_id;
    }

    // Step 3: zero-effective elimination.
    for t in group.iter_mut() {
        if t.consumed {
            continue;
        }
        if can_change_coefficient_to(t.coeff, 0, t.mask, bw) {
            t.consumed = true;
        }
    }

    // Step 1: disjoint-mask merge with matching coefficient.
    // Bucket live terms by coefficient; within each bucket greedily
    // merge terms whose masks are disjoint from an accumulator slot.
    // Because (A|B) & C == 0 iff A & C == 0 and B & C == 0, a single
    // pass reaches the same fixed point as the naive restart loop.
    let mut buckets: HashMap<u64, Vec<usize>> = HashMap::new();
    for (idx, t) in group.iter().enumerate() {
        if !t.consumed {
            buckets.entry(t.coeff).or_default().push(idx);
        }
    }
    for indices in buckets.values() {
        if indices.len() < 2 {
            continue;
        }
        // Slots: (representative_idx, accumulated_mask).
        let mut slots: Vec<(usize, u64)> = Vec::new();
        for &idx in indices {
            let m = group[idx].mask;
            let mut placed = false;
            for slot in slots.iter_mut() {
                if (slot.1 & m) == 0 {
                    let rep = slot.0;
                    let merged_mask = (slot.1 | m) & modmask;
                    let aid = create_masked_atom(ir, basis, merged_mask);
                    group[rep].atom_id = aid;
                    group[rep].mask = merged_mask;
                    group[idx].consumed = true;
                    slot.1 = merged_mask;
                    placed = true;
                    break;
                }
            }
            if !placed {
                slots.push((idx, m));
            }
        }
    }

    // Step 2: coefficient matching + merge.
    for i in 0..group.len() {
        for j in (i + 1)..group.len() {
            try_merge_pair(group, i, j, ir, basis, modmask);
        }
    }

    // Step 4: normalise coefficient to -1 where possible.
    let neg_one = bitmask(bw);
    for t in group.iter_mut() {
        if t.consumed {
            continue;
        }
        if t.coeff != neg_one && can_change_coefficient_to(t.coeff, neg_one, t.mask, bw) {
            t.coeff = neg_one;
        }
    }

    // Step 5: second merge pass after normalisation.
    for i in 0..group.len() {
        for j in (i + 1)..group.len() {
            try_merge_pair(group, i, j, ir, basis, modmask);
        }
    }

    // Step 6: three-term collapse.
    try_three_term_collapse(group, ir, basis, modmask);
}

/// Run the §5.2 refinement on the whole IR. Operates in place.
pub fn refine_terms(ir: &mut SemilinearIR) {
    if ir.terms.is_empty() {
        return;
    }
    let modmask = bitmask(ir.bitwidth);

    let mut basis_groups: HashMap<u64, Vec<RefineTerm>> = HashMap::new();
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
            .push(RefineTerm {
                coeff: term.coeff,
                mask: decomp.mask,
                atom_id: term.atom_id,
                consumed: false,
            });
    }

    let hashes: Vec<u64> = basis_groups.keys().copied().collect();
    for hash in hashes {
        let basis = basis_repr.get(&hash).expect("present").clone_tree();
        let mut group = basis_groups.remove(&hash).expect("present");
        refine_group(&mut group, ir, &basis, modmask);
        basis_groups.insert(hash, group);
    }

    // Rebuild terms.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reduce_mask_strips_zero_bits_under_coefficient_2() {
        // At bitwidth 8, coefficient 2 zeroes bit 7 (2 * 0x80 = 0x100 mod 256 = 0).
        let reduced = reduce_mask(2, 0xFF, 8);
        assert_eq!(reduced, 0x7F);
    }

    #[test]
    fn can_change_coefficient_to_catches_scale_change() {
        // With narrow bitwidth the test is meaningful — at bw=4,
        // coeff 1 and 17 agree mod 16 on every single bit.
        assert!(can_change_coefficient_to(1, 17, 0x0F, 4));
        assert!(!can_change_coefficient_to(1, 2, 0x0F, 8));
    }

    #[test]
    fn can_change_mask_to_with_equivalent_reduction() {
        // At bitwidth 8, coefficient 2 makes bit 7 dead, so the mask can
        // safely drop bit 7.
        assert!(can_change_mask_to(2, 0xFF, 0x7F, 8));
        assert!(!can_change_mask_to(1, 0xFF, 0x7F, 8));
    }

    #[test]
    fn refine_terms_is_idempotent_on_empty_ir() {
        let mut ir = SemilinearIR {
            bitwidth: 64,
            ..Default::default()
        };
        refine_terms(&mut ir);
        assert!(ir.terms.is_empty());
    }
}
