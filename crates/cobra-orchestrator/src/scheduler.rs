//! DAG-aware pass scheduler: `select_next_pass` picks the next
//! applicable pass for a given work item, honouring the per-item
//! attempted-mask, the global pass-attempt cache, and prerequisite
//! bitmasks carried in the `FoldedAst` pass table. Ported from the
//! `SelectNextPass` section of `lib/core/Orchestrator.cpp`.

use cobra_core::classification::{
    is_folded_ast_exploration_candidate, SemanticClass, StructuralFlag,
};

use crate::attempt_cache::PassAttemptCache;
use crate::context::OrchestratorPolicy;
use crate::enums::{PassId, Provenance, RemainderOrigin, StateKind};
use crate::fingerprint::compute_fingerprint;
use crate::state::StateData;
use crate::work_item::WorkItem;

/// Shorthand for "which bit does this `PassId` occupy in
/// `WorkItem::attempted_mask`?".
#[inline]
const fn bit(p: PassId) -> u64 {
    1u64 << (p as u8)
}

// ---------- pass tables ----------

#[derive(Copy, Clone)]
struct FoldedAstEntry {
    id: PassId,
    prereq_mask: u64,
    _priority: u8,
    is_structural_transform: bool,
}

// Priority order matches C++ `kFoldedAstPasses` exactly. The
// `is_structural_transform` arms are gated by `rewrite_gen`.
const FOLDED_AST_PASSES: &[FoldedAstEntry] = &[
    FoldedAstEntry {
        id: PassId::BuildSignatureState,
        prereq_mask: 0,
        _priority: 0,
        is_structural_transform: false,
    },
    FoldedAstEntry {
        id: PassId::PrepareDirectRemainder,
        prereq_mask: 0,
        _priority: 1,
        is_structural_transform: false,
    },
    // Masked-product collapse before direct product extraction.
    FoldedAstEntry {
        id: PassId::ProductIdentityCollapse,
        prereq_mask: 0,
        _priority: 2,
        is_structural_transform: true,
    },
    // Atom-level bitwise identities (`(A|B)-(A&B) -> A^B`, etc.).
    // Runs after PIC so that PIC's collapse of inner product shapes
    // can expose outer atom-level identities in nested forms.
    FoldedAstEntry {
        id: PassId::AtomIdentityRewrite,
        prereq_mask: 0,
        _priority: 3,
        is_structural_transform: true,
    },
    FoldedAstEntry {
        id: PassId::ExtractProductCore,
        prereq_mask: 0,
        _priority: 4,
        is_structural_transform: false,
    },
    FoldedAstEntry {
        id: PassId::ExtractPolyCoreD2,
        prereq_mask: 0,
        _priority: 4,
        is_structural_transform: false,
    },
    FoldedAstEntry {
        id: PassId::ExtractTemplateCore,
        prereq_mask: 0,
        _priority: 5,
        is_structural_transform: false,
    },
    FoldedAstEntry {
        id: PassId::ExtractPolyCoreD3,
        prereq_mask: 0,
        _priority: 6,
        is_structural_transform: false,
    },
    FoldedAstEntry {
        id: PassId::ExtractPolyCoreD4,
        prereq_mask: 0,
        _priority: 7,
        is_structural_transform: false,
    },
    FoldedAstEntry {
        id: PassId::LiftArithmeticAtoms,
        prereq_mask: 0,
        _priority: 8,
        is_structural_transform: false,
    },
    FoldedAstEntry {
        id: PassId::LiftRepeatedSubexpressions,
        prereq_mask: 0,
        _priority: 9,
        is_structural_transform: false,
    },
    FoldedAstEntry {
        id: PassId::OperandSimplify,
        prereq_mask: bit(PassId::ExtractProductCore),
        _priority: 10,
        is_structural_transform: true,
    },
    FoldedAstEntry {
        id: PassId::XorLowering,
        prereq_mask: 0,
        _priority: 11,
        is_structural_transform: true,
    },
];

#[derive(Copy, Clone)]
struct ResidualEntry {
    id: PassId,
}

// Direct boolean-null: ghost-first (C++ `kDirectBooleanNullSolvers`).
const DIRECT_BOOLEAN_NULL_SOLVERS: &[ResidualEntry] = &[
    ResidualEntry {
        id: PassId::ResidualGhost,
    },
    ResidualEntry {
        id: PassId::ResidualFactoredGhost,
    },
    ResidualEntry {
        id: PassId::ResidualFactoredGhostEscalated,
    },
    ResidualEntry {
        id: PassId::ResidualPolyRecovery,
    },
    ResidualEntry {
        id: PassId::ResidualTemplate,
    },
];

// Core-derived boolean-null: poly-first (C++ `kCoreBooleanNullSolvers`).
const CORE_BOOLEAN_NULL_SOLVERS: &[ResidualEntry] = &[
    ResidualEntry {
        id: PassId::ResidualPolyRecovery,
    },
    ResidualEntry {
        id: PassId::ResidualGhost,
    },
    ResidualEntry {
        id: PassId::ResidualFactoredGhost,
    },
    ResidualEntry {
        id: PassId::ResidualTemplate,
    },
];

// Core-derived standard: supported-first (C++ `kCoreStandardSolvers`).
const CORE_STANDARD_SOLVERS: &[ResidualEntry] = &[
    ResidualEntry {
        id: PassId::ResidualSupported,
    },
    ResidualEntry {
        id: PassId::ResidualPolyRecovery,
    },
    ResidualEntry {
        id: PassId::ResidualTemplate,
    },
];

// Signature-state technique DAG (C++ `kSignatureStatePasses`).
const SIGNATURE_STATE_PASSES: &[PassId] = &[
    PassId::SignaturePatternMatch,
    PassId::SignatureAnf,
    PassId::PrepareCoeffModel,
    PassId::SignatureMultivarPolyRecovery,
    PassId::SignatureBitwiseDecompose,
    PassId::SignatureHybridDecompose,
];

// Signature-coeff technique passes (C++ `kSignatureCoeffPasses`).
const SIGNATURE_COEFF_PASSES: &[PassId] = &[
    PassId::SignatureCobCandidate,
    PassId::SignatureSingletonPolyRecovery,
];

// ---------- scheduler ----------

/// Pick the next applicable pass for `item`, or `None` if the item is
/// exhausted. Matches C++ `SelectNextPass`. Bitwidth is fixed at 64 for
/// fingerprint computation to match the C++ call site.
#[must_use]
#[allow(clippy::too_many_lines)] // direct port; splitting would diverge from C++
pub fn select_next_pass(
    item: &WorkItem,
    policy: &OrchestratorPolicy,
    verifications_used: u32,
    cache: &PassAttemptCache,
) -> Option<PassId> {
    let kind = item.payload.kind();
    let fp = compute_fingerprint(item, 64);

    // 1. Candidate → VerifyCandidate (budgeted)
    if kind == StateKind::CandidateExpr {
        let pass = PassId::VerifyCandidate;
        if verifications_used >= policy.max_candidates {
            return None;
        }
        return if eligible(item, cache, &fp, pass) {
            Some(pass)
        } else {
            None
        };
    }

    // 2. SignatureState → technique DAG
    if kind == StateKind::SignatureState {
        for &p in SIGNATURE_STATE_PASSES {
            if eligible(item, cache, &fp, p) {
                return Some(p);
            }
        }
        return None;
    }

    // 2b. SignatureCoeffState
    if kind == StateKind::SignatureCoeffState {
        for &p in SIGNATURE_COEFF_PASSES {
            if eligible(item, cache, &fp, p) {
                return Some(p);
            }
        }
        return None;
    }

    // 3. CoreCandidate → PrepareRemainderFromCore
    if kind == StateKind::CoreCandidate {
        let pass = PassId::PrepareRemainderFromCore;
        return if eligible(item, cache, &fp, pass) {
            Some(pass)
        } else {
            None
        };
    }

    // 4. RemainderState → residual-solver routing
    if kind == StateKind::RemainderState {
        let StateData::Remainder(residual) = &item.payload else {
            return None;
        };
        let table: &[ResidualEntry] = if residual.origin == RemainderOrigin::DirectBooleanNull {
            DIRECT_BOOLEAN_NULL_SOLVERS
        } else if residual.is_boolean_null {
            CORE_BOOLEAN_NULL_SOLVERS
        } else {
            CORE_STANDARD_SOLVERS
        };
        for entry in table {
            if eligible(item, cache, &fp, entry.id) {
                return Some(entry.id);
            }
        }
        return None;
    }

    // 5. Semilinear chain (Normalize → Check → Rewrite → Reconstruct)
    match kind {
        StateKind::SemilinearNormalizedIr => {
            let pass = PassId::SemilinearCheck;
            return if eligible(item, cache, &fp, pass) {
                Some(pass)
            } else {
                None
            };
        }
        StateKind::SemilinearCheckedIr => {
            let pass = PassId::SemilinearRewrite;
            return if eligible(item, cache, &fp, pass) {
                Some(pass)
            } else {
                None
            };
        }
        StateKind::SemilinearRewrittenIr => {
            let pass = PassId::SemilinearReconstruct;
            return if eligible(item, cache, &fp, pass) {
                Some(pass)
            } else {
                None
            };
        }
        StateKind::CompetitionResolved => {
            let pass = PassId::ResolveCompetition;
            return if eligible(item, cache, &fp, pass) {
                Some(pass)
            } else {
                None
            };
        }
        StateKind::LiftedSkeleton => {
            let pass = PassId::PrepareLiftedOuterSolve;
            return if eligible(item, cache, &fp, pass) {
                Some(pass)
            } else {
                None
            };
        }
        _ => {}
    }

    // 6. FoldedAst routing

    // 6a. Semilinear eligibility: original OR rewritten-with-solve_ctx
    let classification = item.features.classification;
    let is_semilinear_eligible = match classification {
        Some(c) if c.semantic == SemanticClass::Semilinear => match item.features.provenance {
            Provenance::Original => true,
            Provenance::Rewritten => {
                if let StateData::FoldedAst(ast) = &item.payload {
                    ast.solve_ctx.is_some()
                } else {
                    false
                }
            }
            Provenance::Lowered => false,
        },
        _ => false,
    };
    if is_semilinear_eligible {
        let pass = PassId::SemilinearNormalize;
        return if eligible(item, cache, &fp, pass) {
            Some(pass)
        } else {
            None
        };
    }
    // Original items that aren't semilinear can't proceed through this
    // arm of the scheduler — lower routes handle them elsewhere.
    if item.features.provenance == Provenance::Original {
        return None;
    }

    // 6b. Non-original items: must carry a classification, no unknown shape.
    let cls = classification?;
    if cls.flags.contains(StructuralFlag::HAS_UNKNOWN_SHAPE) {
        return None;
    }

    // 6c. Non-exploration candidates → BuildSignatureState only.
    if !is_folded_ast_exploration_candidate(cls.flags) {
        let pass = PassId::BuildSignatureState;
        return if eligible(item, cache, &fp, pass) {
            Some(pass)
        } else {
            None
        };
    }

    // 6d. Exploration candidates → iterate the FoldedAst pass table.
    for entry in FOLDED_AST_PASSES {
        if item.has_attempted(entry.id) {
            continue;
        }
        if (item.attempted_mask & entry.prereq_mask) != entry.prereq_mask {
            continue;
        }
        if entry.is_structural_transform && item.rewrite_gen >= policy.max_rewrite_gen {
            continue;
        }
        if cache.has_attempted(&fp, entry.id) {
            continue;
        }
        return Some(entry.id);
    }

    None
}

/// Eligibility check shared across the single-pass arms: not yet
/// attempted on this item and not yet attempted (for this fingerprint)
/// in the global cache.
#[inline]
fn eligible(
    item: &WorkItem,
    cache: &PassAttemptCache,
    fp: &crate::work_item::StateFingerprint,
    pass: PassId,
) -> bool {
    !item.has_attempted(pass) && !cache.has_attempted(fp, pass)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::RemainderTargetContext;
    use crate::state::{AstPayload, CandidatePayload, RemainderStatePayload};
    use crate::stubs::EliminationResult;
    use cobra_core::classification::{Classification, SemanticClass, StructuralFlag};
    use cobra_core::evaluator::Evaluator;
    use cobra_core::expr::Expr;
    use cobra_core::expr_cost::ExprCost;

    fn policy() -> OrchestratorPolicy {
        OrchestratorPolicy::default()
    }

    fn empty_cache() -> PassAttemptCache {
        PassAttemptCache::new()
    }

    fn mk_candidate() -> WorkItem {
        WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
            expr: Expr::variable(0),
            real_vars: vec![],
            cost: ExprCost::default(),
            producing_pass: PassId::VerifyCandidate,
            needs_original_space_verification: true,
        })))
    }

    fn mk_folded(ast: Box<Expr>, prov: Provenance, cls: Option<Classification>) -> WorkItem {
        let mut item = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
            expr: ast,
            classification: None,
            provenance: prov,
            solve_ctx: None,
        })));
        item.features.provenance = prov;
        item.features.classification = cls;
        item
    }

    fn mk_remainder(origin: RemainderOrigin, is_boolean_null: bool) -> WorkItem {
        WorkItem::new(StateData::Remainder(Box::new(RemainderStatePayload {
            origin,
            prefix_expr: Expr::variable(0),
            prefix_degree: 0,
            remainder_eval: Evaluator::default(),
            source_sig: vec![],
            remainder_sig: vec![],
            remainder_elim: EliminationResult::default(),
            remainder_support: vec![],
            is_boolean_null,
            degree_floor: 2,
            target: RemainderTargetContext::default(),
        })))
    }

    #[test]
    fn candidate_picks_verify_candidate() {
        let item = mk_candidate();
        let p = select_next_pass(&item, &policy(), 0, &empty_cache());
        assert_eq!(p, Some(PassId::VerifyCandidate));
    }

    #[test]
    fn candidate_stops_when_verification_budget_exhausted() {
        let item = mk_candidate();
        let p = select_next_pass(&item, &policy(), policy().max_candidates, &empty_cache());
        assert_eq!(p, None);
    }

    #[test]
    fn candidate_skips_when_already_attempted() {
        let mut item = mk_candidate();
        item.record_attempt(PassId::VerifyCandidate);
        let p = select_next_pass(&item, &policy(), 0, &empty_cache());
        assert_eq!(p, None);
    }

    #[test]
    fn remainder_direct_boolean_null_routes_ghost_first() {
        let item = mk_remainder(RemainderOrigin::DirectBooleanNull, true);
        let p = select_next_pass(&item, &policy(), 0, &empty_cache());
        assert_eq!(p, Some(PassId::ResidualGhost));
    }

    #[test]
    fn remainder_core_boolean_null_routes_poly_first() {
        let item = mk_remainder(RemainderOrigin::ProductCore, true);
        let p = select_next_pass(&item, &policy(), 0, &empty_cache());
        assert_eq!(p, Some(PassId::ResidualPolyRecovery));
    }

    #[test]
    fn remainder_core_standard_routes_supported_first() {
        let item = mk_remainder(RemainderOrigin::ProductCore, false);
        let p = select_next_pass(&item, &policy(), 0, &empty_cache());
        assert_eq!(p, Some(PassId::ResidualSupported));
    }

    #[test]
    fn original_ast_without_classification_returns_none() {
        let item = mk_folded(Expr::variable(0), Provenance::Original, None);
        assert_eq!(select_next_pass(&item, &policy(), 0, &empty_cache()), None);
    }

    #[test]
    fn original_ast_with_semilinear_classification_picks_normalize() {
        let cls = Classification {
            semantic: SemanticClass::Semilinear,
            flags: StructuralFlag::NONE,
        };
        let item = mk_folded(Expr::variable(0), Provenance::Original, Some(cls));
        let p = select_next_pass(&item, &policy(), 0, &empty_cache());
        assert_eq!(p, Some(PassId::SemilinearNormalize));
    }

    #[test]
    fn non_exploration_ast_goes_to_build_signature_state() {
        // Rewritten, linear, no exploration flags → BuildSignatureState
        let cls = Classification {
            semantic: SemanticClass::Linear,
            flags: StructuralFlag::HAS_ARITHMETIC,
        };
        let item = mk_folded(Expr::variable(0), Provenance::Rewritten, Some(cls));
        let p = select_next_pass(&item, &policy(), 0, &empty_cache());
        assert_eq!(p, Some(PassId::BuildSignatureState));
    }

    #[test]
    fn exploration_candidate_iterates_folded_ast_table() {
        // Mixed product → exploration candidate; BuildSignatureState is
        // first in the table and should be picked.
        let cls = Classification {
            semantic: SemanticClass::Polynomial,
            flags: StructuralFlag::HAS_MIXED_PRODUCT,
        };
        let item = mk_folded(Expr::variable(0), Provenance::Rewritten, Some(cls));
        let p = select_next_pass(&item, &policy(), 0, &empty_cache());
        assert_eq!(p, Some(PassId::BuildSignatureState));
    }

    #[test]
    fn operand_simplify_blocked_without_extract_product_core_prereq() {
        // Mark every folded-ast pass attempted EXCEPT OperandSimplify
        // and its prereq ExtractProductCore. The scheduler should pick
        // ExtractProductCore (earlier in the table) rather than
        // OperandSimplify, because OperandSimplify's prereq isn't met.
        let cls = Classification {
            semantic: SemanticClass::Polynomial,
            flags: StructuralFlag::HAS_MIXED_PRODUCT,
        };
        let mut item = mk_folded(Expr::variable(0), Provenance::Rewritten, Some(cls));
        for p in [
            PassId::BuildSignatureState,
            PassId::PrepareDirectRemainder,
            PassId::ProductIdentityCollapse,
            PassId::AtomIdentityRewrite,
            PassId::ExtractPolyCoreD2,
            PassId::ExtractTemplateCore,
            PassId::ExtractPolyCoreD3,
            PassId::ExtractPolyCoreD4,
            PassId::LiftArithmeticAtoms,
            PassId::LiftRepeatedSubexpressions,
            PassId::XorLowering,
        ] {
            item.record_attempt(p);
        }
        let p = select_next_pass(&item, &policy(), 0, &empty_cache());
        assert_eq!(p, Some(PassId::ExtractProductCore));
    }

    #[test]
    fn operand_simplify_picks_after_prereq_met() {
        let cls = Classification {
            semantic: SemanticClass::Polynomial,
            flags: StructuralFlag::HAS_MIXED_PRODUCT,
        };
        let mut item = mk_folded(Expr::variable(0), Provenance::Rewritten, Some(cls));
        for p in [
            PassId::BuildSignatureState,
            PassId::PrepareDirectRemainder,
            PassId::ProductIdentityCollapse,
            PassId::AtomIdentityRewrite,
            PassId::ExtractProductCore,
            PassId::ExtractPolyCoreD2,
            PassId::ExtractTemplateCore,
            PassId::ExtractPolyCoreD3,
            PassId::ExtractPolyCoreD4,
            PassId::LiftArithmeticAtoms,
            PassId::LiftRepeatedSubexpressions,
        ] {
            item.record_attempt(p);
        }
        let p = select_next_pass(&item, &policy(), 0, &empty_cache());
        assert_eq!(p, Some(PassId::OperandSimplify));
    }

    #[test]
    fn structural_transforms_blocked_by_rewrite_gen() {
        let cls = Classification {
            semantic: SemanticClass::Polynomial,
            flags: StructuralFlag::HAS_MIXED_PRODUCT,
        };
        let mut item = mk_folded(Expr::variable(0), Provenance::Rewritten, Some(cls));
        item.rewrite_gen = policy().max_rewrite_gen;
        // All non-structural passes exhausted; only XorLowering (structural)
        // and ProductIdentityCollapse (structural) remain eligible — both
        // blocked by rewrite_gen. Expect None.
        for p in [
            PassId::BuildSignatureState,
            PassId::PrepareDirectRemainder,
            PassId::ExtractProductCore,
            PassId::ExtractPolyCoreD2,
            PassId::ExtractTemplateCore,
            PassId::ExtractPolyCoreD3,
            PassId::ExtractPolyCoreD4,
            PassId::LiftArithmeticAtoms,
            PassId::LiftRepeatedSubexpressions,
        ] {
            item.record_attempt(p);
        }
        let p = select_next_pass(&item, &policy(), 0, &empty_cache());
        assert_eq!(p, None);
    }

    #[test]
    fn unknown_shape_blocks_folded_ast_routing() {
        let cls = Classification {
            semantic: SemanticClass::NonPolynomial,
            flags: StructuralFlag::HAS_UNKNOWN_SHAPE,
        };
        let item = mk_folded(Expr::variable(0), Provenance::Rewritten, Some(cls));
        assert_eq!(select_next_pass(&item, &policy(), 0, &empty_cache()), None);
    }
}
