//! Boost-style `hash_combine` for structural hashing, keeping the exact
//! same mix constants for structural consistency across hash computations.

use cobra_ir::semilinear::SemilinearIR;

use crate::context::expr_identity_hash;
use crate::state::StateData;
use crate::work_item::{SemilinearFingerprintKey, SemilinearTermKey, StateFingerprint, WorkItem};

/// Boost-style hash combination: structurally identical inputs produce identical combined hashes.
#[inline]
#[must_use]
pub fn hash_combine(seed: u64, value: u64) -> u64 {
    seed ^ value
        .wrapping_add(0x9E37_79B9)
        .wrapping_add(seed << 6)
        .wrapping_add(seed >> 2)
}

/// `ComputeFingerprint`.
#[must_use]
pub fn compute_fingerprint(item: &WorkItem, bitwidth: u32) -> StateFingerprint {
    let kind = item.payload.kind();
    let provenance = item.features.provenance;

    // Fold Phase-3 control state into signature-family hashes so that
    // the pass-attempt cache distinguishes subproblems that share the
    // same signature but differ in group, recursion depth, or
    // evaluator presence.
    let fold_control = |h: u64| -> u64 {
        let mut h = hash_combine(h, u64::from(item.group_id.unwrap_or(u32::MAX)));
        h = hash_combine(h, u64::from(item.signature_recursion_depth));
        hash_combine(h, u64::from(item.evaluator_override.is_some()))
    };

    let (payload_hash, vars_hash) = match &item.payload {
        StateData::FoldedAst(p) => {
            let mut h = expr_identity_hash(&p.expr);
            if let Some(ctx) = &p.solve_ctx {
                for v in &ctx.vars {
                    h = hash_combine(h, hash_string(v));
                }
                h = hash_combine(h, u64::from(ctx.evaluator.is_some()));
                for s in &ctx.input_sig {
                    h = hash_combine(h, *s);
                }
            }
            h = hash_combine(h, u64::from(item.group_id.unwrap_or(u32::MAX)));
            (h, 0u64)
        }
        StateData::Signature(p) => {
            let mut h = p.ctx.sig.len() as u64;
            for v in &p.ctx.sig {
                h = hash_combine(h, *v);
            }
            (fold_control(h), hash_var_list(&p.ctx.real_vars))
        }
        StateData::SignatureCoeff(p) => {
            let mut h = p.ctx.sig.len() as u64;
            for v in &p.ctx.sig {
                h = hash_combine(h, *v);
            }
            for c in &p.coeffs {
                h = hash_combine(h, *c);
            }
            (fold_control(h), hash_var_list(&p.ctx.real_vars))
        }
        StateData::CoreCandidate(p) => {
            let mut h = expr_identity_hash(&p.core_expr);
            h = hash_combine(h, p.extractor_kind as u64);
            h = hash_combine(h, u64::from(p.degree_used));
            for v in &p.target.vars {
                h = hash_combine(h, hash_string(v));
            }
            for r in &p.target.remap_support {
                h = hash_combine(h, u64::from(*r));
            }
            (h, 0u64)
        }
        StateData::Remainder(p) => {
            let mut h = p.origin as u64;
            h = hash_combine(h, expr_identity_hash(&p.prefix_expr));
            for v in &p.remainder_sig {
                h = hash_combine(h, *v);
            }
            for s in &p.remainder_support {
                h = hash_combine(h, u64::from(*s));
            }
            h = hash_combine(h, u64::from(p.is_boolean_null));
            h = hash_combine(h, u64::from(p.degree_floor));
            for v in &p.target.vars {
                h = hash_combine(h, hash_string(v));
            }
            for r in &p.target.remap_support {
                h = hash_combine(h, u64::from(*r));
            }
            h = hash_combine(h, u64::from(item.group_id.unwrap_or(u32::MAX)));
            (h, 0u64)
        }
        StateData::SemilinearNormalized(p) => (
            hash_semilinear_fingerprint_key(&build_semilinear_fingerprint_key(&p.ctx.ir)),
            0u64,
        ),
        StateData::SemilinearChecked(p) => (
            hash_semilinear_fingerprint_key(&build_semilinear_fingerprint_key(&p.ctx.ir)),
            0u64,
        ),
        StateData::SemilinearRewritten(p) => (
            hash_semilinear_fingerprint_key(&build_semilinear_fingerprint_key(&p.ctx.ir)),
            0u64,
        ),
        StateData::LiftedSkeleton(p) => {
            let mut h = expr_identity_hash(&p.outer_expr);
            for v in &p.outer_ctx.vars {
                h = hash_combine(h, hash_string(v));
            }
            for s in &p.outer_ctx.input_sig {
                h = hash_combine(h, *s);
            }
            for v in &p.original_ctx.vars {
                h = hash_combine(h, hash_string(v));
            }
            h = hash_combine(h, u64::from(p.original_ctx.evaluator.is_some()));
            h = hash_combine(h, u64::from(p.original_var_count));
            for b in &p.bindings {
                h = hash_combine(h, b.kind as u64);
                h = hash_combine(h, u64::from(b.outer_var_index));
                h = hash_combine(h, b.structural_hash);
            }
            (h, 0u64)
        }
        StateData::Candidate(p) => {
            let h = hash_combine(
                expr_identity_hash(&p.expr),
                u64::from(p.needs_original_space_verification),
            );
            (h, hash_var_list(&p.real_vars))
        }
        StateData::CompetitionResolved(p) => (u64::from(p.group_id), 0u64),
    };

    StateFingerprint {
        kind,
        payload_hash,
        vars_hash,
        bitwidth,
        provenance,
    }
}

/// Build the content-keyed fingerprint of a [`SemilinearIR`]. Terms are
/// structural_hash, provenance)` so that two IRs with the same set of
#[must_use]
pub fn build_semilinear_fingerprint_key(ir: &SemilinearIR) -> SemilinearFingerprintKey {
    let mut terms: Vec<SemilinearTermKey> = Vec::with_capacity(ir.terms.len());
    for t in &ir.terms {
        let info = &ir.atom_table[t.atom_id as usize];
        terms.push(SemilinearTermKey {
            coeff: t.coeff,
            support: info.key.support.clone(),
            truth_table: info.key.truth_table.clone(),
            structural_hash: info.structural_hash,
            provenance: info.provenance,
        });
    }
    terms.sort_by(|a, b| {
        a.coeff
            .cmp(&b.coeff)
            .then_with(|| a.support.cmp(&b.support))
            .then_with(|| a.truth_table.cmp(&b.truth_table))
            .then_with(|| a.structural_hash.cmp(&b.structural_hash))
            .then_with(|| (a.provenance as u8).cmp(&(b.provenance as u8)))
    });
    SemilinearFingerprintKey {
        constant: ir.constant,
        bitwidth: ir.bitwidth,
        terms,
    }
}

/// Canonical u64 hash of a fingerprint key. Internal helper; exposed
/// for tests.
#[must_use]
pub fn hash_semilinear_fingerprint_key(key: &SemilinearFingerprintKey) -> u64 {
    let mut h = key.constant;
    h = hash_combine(h, u64::from(key.bitwidth));
    for t in &key.terms {
        h = hash_combine(h, t.coeff);
        for s in &t.support {
            h = hash_combine(h, u64::from(*s));
        }
        for v in &t.truth_table {
            h = hash_combine(h, *v);
        }
        h = hash_combine(h, t.structural_hash);
        h = hash_combine(h, t.provenance as u64);
    }
    h
}

fn hash_string(s: &str) -> u64 {
    use std::sync::OnceLock;
    static STATE: OnceLock<ahash::RandomState> = OnceLock::new();
    STATE
        .get_or_init(crate::context::determinism_seeds_ahash)
        .hash_one(s)
}

/// Order-sensitive hash of a variable-name list. Used by
/// `StateFingerprint::vars_hash` to replace the old `Vec<String>`
/// clones on every fingerprint computation.
fn hash_var_list(vars: &[String]) -> u64 {
    let mut h = vars.len() as u64;
    for v in vars {
        h = hash_combine(h, hash_string(v));
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::enums::{Provenance, StateKind};
    use crate::state::{AstPayload, CandidatePayload, CompetitionResolvedPayload};
    use cobra_core::expr::Expr;
    use cobra_core::expr_cost::ExprCost;

    fn mk_ast_item(expr: Box<Expr>) -> WorkItem {
        WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
            expr,
            classification: None,
            provenance: Provenance::Original,
            solve_ctx: None,
        })))
    }

    #[test]
    fn fingerprint_kind_follows_payload() {
        let item = mk_ast_item(Expr::variable(0));
        let fp = compute_fingerprint(&item, 64);
        assert_eq!(fp.kind, StateKind::FoldedAst);
        assert_eq!(fp.bitwidth, 64);
        assert_eq!(fp.provenance, Provenance::Original);
    }

    #[test]
    fn same_payload_produces_same_fingerprint() {
        let a = mk_ast_item(Expr::add(Expr::variable(0), Expr::variable(1)));
        let b = mk_ast_item(Expr::add(Expr::variable(0), Expr::variable(1)));
        assert_eq!(compute_fingerprint(&a, 64), compute_fingerprint(&b, 64));
    }

    #[test]
    fn different_expressions_yield_different_payload_hashes() {
        let a = mk_ast_item(Expr::variable(0));
        let b = mk_ast_item(Expr::variable(1));
        let fa = compute_fingerprint(&a, 64);
        let fb = compute_fingerprint(&b, 64);
        assert_ne!(fa.payload_hash, fb.payload_hash);
    }

    #[test]
    fn candidate_fingerprint_carries_real_vars() {
        let item = WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
            expr: Expr::variable(0),
            real_vars: vec!["x".into(), "y".into()],
            cost: ExprCost::default(),
            producing_pass: crate::enums::PassId::VerifyCandidate,
            needs_original_space_verification: true,
        })));
        let fp = compute_fingerprint(&item, 64);
        assert_eq!(fp.vars_hash, hash_var_list(&["x".into(), "y".into()]));
        assert_ne!(fp.vars_hash, 0);
        assert_eq!(fp.kind, StateKind::CandidateExpr);
        // Different real_vars produce different vars_hash.
        let other = WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
            expr: Expr::variable(0),
            real_vars: vec!["a".into(), "b".into()],
            cost: ExprCost::default(),
            producing_pass: crate::enums::PassId::VerifyCandidate,
            needs_original_space_verification: true,
        })));
        let fp2 = compute_fingerprint(&other, 64);
        assert_ne!(fp.vars_hash, fp2.vars_hash);
    }

    #[test]
    fn group_id_changes_fingerprint_for_folded_ast() {
        let mut a = mk_ast_item(Expr::variable(0));
        let mut b = mk_ast_item(Expr::variable(0));
        a.group_id = Some(1);
        b.group_id = Some(2);
        assert_ne!(
            compute_fingerprint(&a, 64).payload_hash,
            compute_fingerprint(&b, 64).payload_hash,
        );
    }

    #[test]
    fn competition_resolved_fingerprint_uses_group_id() {
        let a = WorkItem::new(StateData::CompetitionResolved(CompetitionResolvedPayload {
            group_id: 1,
        }));
        let b = WorkItem::new(StateData::CompetitionResolved(CompetitionResolvedPayload {
            group_id: 2,
        }));
        assert_ne!(
            compute_fingerprint(&a, 64).payload_hash,
            compute_fingerprint(&b, 64).payload_hash,
        );
    }

    #[test]
    fn hash_combine_is_deterministic() {
        let h = hash_combine(hash_combine(0, 1), 2);
        assert_eq!(h, hash_combine(hash_combine(0, 1), 2));
        // Order-sensitive — (1 then 2) ≠ (2 then 1).
        assert_ne!(h, hash_combine(hash_combine(0, 2), 1));
    }

    #[test]
    fn semilinear_fingerprint_key_sorts_terms() {
        use cobra_ir::semilinear::{create_atom, OperatorFamily, SemilinearIR, WeightedAtom};

        let mut ir = SemilinearIR {
            bitwidth: 8,
            ..Default::default()
        };
        let a0 = create_atom(&mut ir, Expr::variable(0), OperatorFamily::Mixed);
        let a1 = create_atom(&mut ir, Expr::variable(1), OperatorFamily::Mixed);

        // Insert out-of-order to exercise the sort.
        ir.terms = vec![
            WeightedAtom {
                coeff: 3,
                atom_id: a1,
            },
            WeightedAtom {
                coeff: 1,
                atom_id: a0,
            },
        ];
        let key = build_semilinear_fingerprint_key(&ir);
        assert_eq!(key.terms.len(), 2);
        assert_eq!(key.terms[0].coeff, 1); // sorted ascending
        assert_eq!(key.terms[1].coeff, 3);
    }

    #[test]
    fn semilinear_fingerprint_key_order_independent() {
        use cobra_ir::semilinear::{create_atom, OperatorFamily, SemilinearIR, WeightedAtom};

        let mut ir_a = SemilinearIR {
            bitwidth: 8,
            ..Default::default()
        };
        let xa = create_atom(&mut ir_a, Expr::variable(0), OperatorFamily::Mixed);
        let ya = create_atom(&mut ir_a, Expr::variable(1), OperatorFamily::Mixed);
        ir_a.terms = vec![
            WeightedAtom {
                coeff: 2,
                atom_id: xa,
            },
            WeightedAtom {
                coeff: 5,
                atom_id: ya,
            },
        ];

        let mut ir_b = SemilinearIR {
            bitwidth: 8,
            ..Default::default()
        };
        let yb = create_atom(&mut ir_b, Expr::variable(1), OperatorFamily::Mixed);
        let xb = create_atom(&mut ir_b, Expr::variable(0), OperatorFamily::Mixed);
        ir_b.terms = vec![
            WeightedAtom {
                coeff: 5,
                atom_id: yb,
            },
            WeightedAtom {
                coeff: 2,
                atom_id: xb,
            },
        ];

        let ka = build_semilinear_fingerprint_key(&ir_a);
        let kb = build_semilinear_fingerprint_key(&ir_b);
        assert_eq!(ka, kb);
        assert_eq!(
            hash_semilinear_fingerprint_key(&ka),
            hash_semilinear_fingerprint_key(&kb)
        );
    }
}
