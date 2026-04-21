//! Rebuild an `Expr` from a [`SemilinearIR`], merging coefficient-1
//! atom pairs whose partition-class "active masks" are disjoint into
//! a single `OR` node. Output shape:
//!
//! ```text
//! constant + (OR-merged pairs) + (remaining coeff * atom terms)
//! ```
//!
//! Partitions come from `cobra-passes::bit_partitioner::compute_partitions`;
//! an empty partition list disables the OR-merging step and reduces to
//! a straight weighted sum.

use cobra_core::expr::Expr;
use cobra_core::expr_rewrite::apply_coefficient;

use crate::semilinear::{AtomId, PartitionClass, SemilinearIR};

struct ReconstructEntry {
    expr: Box<Expr>,
    coeff: u64,
    atom_id: AtomId,
}

fn compute_active_mask(atom_id: AtomId, partitions: &[PartitionClass]) -> u64 {
    let mut mask = 0u64;
    for pc in partitions {
        if (atom_id as usize) < pc.profile.len() && pc.profile[atom_id as usize] != 0 {
            mask |= pc.mask;
        }
    }
    mask
}

/// Produce an `Expr` tree equivalent to `constant + Σ coeff_i * atom_i`
/// with coefficient-1 pairs fused into `OR` nodes when their active
/// masks are disjoint.
#[must_use]
pub fn reconstruct_masked_atoms(ir: &SemilinearIR, partitions: &[PartitionClass]) -> Box<Expr> {
    if ir.terms.is_empty() {
        return Expr::constant(ir.constant);
    }

    let mut entries: Vec<ReconstructEntry> = ir
        .terms
        .iter()
        .map(|term| {
            let atom_clone = ir.atom_table[term.atom_id as usize]
                .original_subtree
                .clone_tree();
            let applied = apply_coefficient(atom_clone, term.coeff, ir.bitwidth);
            ReconstructEntry {
                expr: applied,
                coeff: term.coeff,
                atom_id: term.atom_id,
            }
        })
        .collect();

    let mut consumed = vec![false; entries.len()];
    let mut combined: Vec<Box<Expr>> = Vec::new();

    if !partitions.is_empty() {
        for i in 0..entries.len() {
            if consumed[i] || entries[i].coeff != 1 {
                continue;
            }
            let mask_i = compute_active_mask(entries[i].atom_id, partitions);
            for j in (i + 1)..entries.len() {
                if consumed[j] || entries[j].coeff != 1 {
                    continue;
                }
                let mask_j = compute_active_mask(entries[j].atom_id, partitions);
                if (mask_i & mask_j) == 0 {
                    // Take ownership of the two expressions without leaving
                    // invalid temp values behind.
                    let e_i = std::mem::replace(&mut entries[i].expr, Expr::constant(0));
                    let e_j = std::mem::replace(&mut entries[j].expr, Expr::constant(0));
                    combined.push(Expr::or(e_i, e_j));
                    consumed[i] = true;
                    consumed[j] = true;
                    break;
                }
            }
        }
    }

    let mut all_terms: Vec<Box<Expr>> = combined;
    for (i, e) in entries.into_iter().enumerate() {
        if !consumed[i] {
            all_terms.push(e.expr);
        }
    }

    let mut result = all_terms.remove(0);
    for t in all_terms {
        result = Expr::add(result, t);
    }
    if ir.constant != 0 {
        result = Expr::add(Expr::constant(ir.constant), result);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{normalize_to_semilinear, semilinear::PartitionClass};
    use cobra_core::evaluator::Evaluator;

    #[test]
    fn empty_ir_returns_constant() {
        let ir = SemilinearIR {
            bitwidth: 64,
            constant: 42,
            ..Default::default()
        };
        let expr = reconstruct_masked_atoms(&ir, &[]);
        match expr.kind {
            cobra_core::expr::Kind::Constant(42) => {}
            _ => panic!("expected constant 42"),
        }
    }

    #[test]
    fn reconstruction_preserves_evaluation() {
        // f = x + y — no OR-merge opportunity without partitions.
        let e = Expr::add(Expr::variable(0), Expr::variable(1));
        let ir = normalize_to_semilinear(&e, &["x".into(), "y".into()], 64).unwrap();
        let expr = reconstruct_masked_atoms(&ir, &[]);
        let eval = Evaluator::from_expr(&expr, 64);
        // f(3, 5) = 8
        assert_eq!(eval.eval(&[3, 5]), 8);
    }

    #[test]
    fn disjoint_mask_pair_fuses_into_or() {
        // Two bare atoms (x & y) and (~x & ~y) — different coefficients
        // would normally keep them separate; here both are coefficient 1
        // and their active masks can be made disjoint via a crafted
        // partition list. The test just exercises the OR fusion path.
        let e = Expr::add(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::and(Expr::not(Expr::variable(0)), Expr::not(Expr::variable(1))),
        );
        let ir = normalize_to_semilinear(&e, &["x".into(), "y".into()], 64).unwrap();

        // Build a partition where atom 0 has profile=1, atom 1 has
        // profile=2 — non-overlapping masks.
        let partitions = vec![
            PartitionClass {
                mask: 0x00FF_FFFF_FFFF_FFFF,
                profile: vec![1, 0],
            },
            PartitionClass {
                mask: 0xFF00_0000_0000_0000,
                profile: vec![0, 1],
            },
        ];

        let expr = reconstruct_masked_atoms(&ir, &partitions);
        // Confirm the result evaluates to the same thing as the original.
        let eval = Evaluator::from_expr(&expr, 64);
        let orig = Evaluator::from_expr(&e, 64);
        assert_eq!(eval.eval(&[3, 5]), orig.eval(&[3, 5]));
    }
}
