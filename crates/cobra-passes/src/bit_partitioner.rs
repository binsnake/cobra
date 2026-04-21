//! Per-bit semantic-ID profiling: group bit positions into
//! [`PartitionClass`]es where the packed 1-bit truth table of every
//! atom agrees across bits in the class.
//!
//! For each bit `b` we build a length-`atom_count` profile vector
//! whose entry `a` is the atom's Boolean truth table packed into a
//! `u64` with bit `i` set when the atom's 1-bit evaluation at bit `b`
//! and Boolean assignment `i` is one. Bits whose profile vectors
//! agree belong to the same partition class — the class's `mask` is
//! the OR of those bit positions.
//!
//! Atoms with support larger than 5 are collapsed to a per-atom
//! opaque sentinel to keep the packed table in a `u64`.

use std::collections::HashMap;

use cobra_core::expr::{Expr, Kind};

use cobra_ir::semilinear::{AtomSemanticId, GlobalVarIdx, PartitionClass, SemilinearIR};

const OPAQUE_SENTINEL_BASE: u64 = 0xDEAD_0000_0000_0000;

#[derive(Clone)]
struct AtomMeta {
    opaque: bool,
    sentinel: u64,
}

fn eval_atom_at_bit_impl(
    e: &Expr,
    support: &[GlobalVarIdx],
    assignment: u64,
    bit_pos: u32,
    bitwidth: u32,
) -> u64 {
    match &e.kind {
        Kind::Constant(v) => (v >> bit_pos) & 1,
        Kind::Variable(idx) => {
            for (i, &s) in support.iter().enumerate() {
                if s == *idx {
                    return (assignment >> i) & 1;
                }
            }
            0
        }
        Kind::And => {
            eval_atom_at_bit_impl(&e.children[0], support, assignment, bit_pos, bitwidth)
                & eval_atom_at_bit_impl(&e.children[1], support, assignment, bit_pos, bitwidth)
        }
        Kind::Or => {
            eval_atom_at_bit_impl(&e.children[0], support, assignment, bit_pos, bitwidth)
                | eval_atom_at_bit_impl(&e.children[1], support, assignment, bit_pos, bitwidth)
        }
        Kind::Xor => {
            eval_atom_at_bit_impl(&e.children[0], support, assignment, bit_pos, bitwidth)
                ^ eval_atom_at_bit_impl(&e.children[1], support, assignment, bit_pos, bitwidth)
        }
        Kind::Not => {
            eval_atom_at_bit_impl(&e.children[0], support, assignment, bit_pos, bitwidth) ^ 1
        }
        Kind::Shr(k) => {
            let src = bit_pos.saturating_add(*k);
            if src >= bitwidth {
                0
            } else {
                eval_atom_at_bit_impl(&e.children[0], support, assignment, src, bitwidth)
            }
        }
        Kind::Add | Kind::Mul | Kind::Neg => {
            unreachable!("arithmetic inside pure-bitwise atom")
        }
    }
}

fn eval_atom_at_bit(atom: &Expr, support: &[GlobalVarIdx], bit_pos: u32, bitwidth: u32) -> u64 {
    let n = support.len();
    let len = 1usize << n;
    let mut packed: u64 = 0;
    for i in 0..len {
        let v = eval_atom_at_bit_impl(atom, support, i as u64, bit_pos, bitwidth);
        packed |= (v & 1) << i;
    }
    packed
}

/// Group bit positions by their per-atom truth-table profile.
#[must_use]
pub fn compute_partitions(ir: &SemilinearIR) -> Vec<PartitionClass> {
    if ir.atom_table.is_empty() {
        return Vec::new();
    }
    if ir.bitwidth == 0 || ir.bitwidth > 64 {
        return Vec::new();
    }

    let atom_count = ir.atom_table.len();

    let meta: Vec<AtomMeta> = ir
        .atom_table
        .iter()
        .enumerate()
        .map(|(a, info)| {
            if info.key.support.len() > 5 {
                AtomMeta {
                    opaque: true,
                    sentinel: OPAQUE_SENTINEL_BASE | a as u64,
                }
            } else {
                AtomMeta {
                    opaque: false,
                    sentinel: 0,
                }
            }
        })
        .collect();

    let mut profile_to_mask: HashMap<Vec<AtomSemanticId>, u64> = HashMap::new();
    let mut profile: Vec<AtomSemanticId> = vec![0; atom_count];

    for b in 0..ir.bitwidth {
        for (a, info) in ir.atom_table.iter().enumerate() {
            profile[a] = if meta[a].opaque {
                meta[a].sentinel
            } else {
                eval_atom_at_bit(&info.original_subtree, &info.key.support, b, ir.bitwidth)
            };
        }
        let slot = profile_to_mask.entry(profile.clone()).or_insert(0);
        *slot |= 1u64 << b;
    }

    profile_to_mask
        .into_iter()
        .map(|(profile, mask)| PartitionClass { mask, profile })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_ir::normalize_to_semilinear;

    #[test]
    fn empty_ir_produces_no_partitions() {
        let ir = SemilinearIR {
            bitwidth: 64,
            ..Default::default()
        };
        assert!(compute_partitions(&ir).is_empty());
    }

    #[test]
    fn single_variable_ir_has_one_partition() {
        // f = x — all bits produce the same 1-bit profile `[assignment]`,
        // so a single partition covers all bitwidth bits.
        let e = Expr::variable(0);
        let ir = normalize_to_semilinear(&e, &["x".into()], 64).unwrap();
        let parts = compute_partitions(&ir);
        assert_eq!(parts.len(), 1);
        assert_eq!(parts[0].mask, u64::MAX);
    }

    #[test]
    fn high_support_atom_gets_opaque_sentinel() {
        // 6-variable AND saturates the 5-var support cap and is treated
        // as opaque across all bit positions. Resulting partition has
        // a single class covering the full mask.
        let e = (0..6)
            .map(|i| Expr::variable(i as u32))
            .reduce(Expr::and)
            .unwrap();
        let vars: Vec<String> = (0..6).map(|i| format!("v{i}")).collect();
        let ir = normalize_to_semilinear(&e, &vars, 64).unwrap();
        let parts = compute_partitions(&ir);
        assert_eq!(parts.len(), 1);
        assert_eq!(parts[0].mask, u64::MAX);
    }
}
