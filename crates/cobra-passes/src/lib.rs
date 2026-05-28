//! `CoBRA` simplification passes. Each pass is a free function matching
//! [`cobra_orchestrator::PassFn`] plus an applicability predicate
//! matching [`cobra_orchestrator::ApplicabilityFn`]. Registration is
//! done via [`PASS_REGISTRY`] — a `'static` slice of
//! [`PassDescriptor`] entries ordered by [`PassId`] value.
//!
//! Currently ported passes:
//! - [`classify_ast::run_classify_ast`] — structural classifier
//! - [`lower_not_over_arith::run_lower_not_over_arith`] —
//!   `~(arith)` → `Add(Neg, mask)` rewrite
//!
//! Many more are stubbed out / pending. The registry's current length
//! orchestrator treats missing entries as "skip" without error, so
//! enabling more passes is purely additive.

#![forbid(unsafe_code)]
// Expr-building helpers return `Box<Expr>` to match the ownership shape
// of `cobra_core::Expr` factories.
#![allow(clippy::unnecessary_box_returns)]

pub mod atom_identity_rewrite;
pub mod atom_simplifier;
pub mod aux_var;
pub mod bit_partitioner;
pub mod bitwise_decomposer;
pub mod candidate_normalize;
pub mod classifier;
pub mod cob_expr_builder;
pub mod decomposition_engine;
pub mod decomposition_helpers;
pub mod entry;
pub mod extract_poly_core;
pub mod extract_product_core;
pub mod extract_template_core;
pub mod ghost_basis;
pub mod ghost_residual_solver;
pub mod hybrid_decomposer;
pub mod lift_arithmetic_atoms;
pub mod lift_repeated_subexpressions;
pub mod lifting;
pub mod mapped_evaluator;
pub mod mixed_product_rewriter;
pub mod not_over_arith;
pub mod npn4_canonical;
pub mod npn4_table;
pub mod operand_simplify;
pub mod pattern_matcher;
pub mod prepare_lifted_outer_solve;
pub mod product_identity_collapse;
pub mod proof_coverage;
pub mod self_check;
pub mod spot_check;
pub mod template_decomposer;
pub mod weighted_poly_fit;
pub mod xor_lowering;

pub mod build_signature_state;
pub mod classify_ast;
pub mod lower_not_over_arith;
pub mod prepare_coeff_model;
pub mod prepare_direct_remainder;
pub mod prepare_remainder_from_core;
pub mod residual_common;
pub mod residual_factored_ghost;
pub mod residual_ghost;
pub mod residual_poly_recovery;
pub mod residual_supported;
pub mod residual_template;
pub mod resolve_competition;
pub mod seed;
pub mod semilinear_check;
pub mod semilinear_normalize;
pub mod semilinear_reconstruct;
pub mod semilinear_rewrite;
pub mod signature_anf;
pub mod signature_bitwise_decompose;
pub mod signature_cob_candidate;
pub mod signature_hybrid_decompose;
pub mod signature_multivar_poly_recovery;
pub mod signature_pattern_match;
pub mod signature_singleton_poly_recovery;
pub mod singleton_power_expr_builder;
pub mod verify_candidate;

use cobra_orchestrator::{PassDescriptor, PassId, PassTag, StateKind};

/// iterating the slice encounters passes in canonical priority.
pub const PASS_REGISTRY: &[PassDescriptor] = &[
    PassDescriptor {
        id: PassId::LowerNotOverArith,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Rewrite,
        applicable: lower_not_over_arith::applicable,
        run: lower_not_over_arith::run_lower_not_over_arith,
    },
    PassDescriptor {
        id: PassId::ClassifyAst,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Analysis,
        applicable: classify_ast::applicable,
        run: classify_ast::run_classify_ast,
    },
    PassDescriptor {
        id: PassId::BuildSignatureState,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Analysis,
        applicable: build_signature_state::applicable,
        run: build_signature_state::run_build_signature_state,
    },
    PassDescriptor {
        id: PassId::VerifyCandidate,
        consumes: StateKind::CandidateExpr,
        tag: PassTag::Verifier,
        applicable: verify_candidate::applicable,
        run: verify_candidate::run_verify_candidate,
    },
    PassDescriptor {
        id: PassId::SignaturePatternMatch,
        consumes: StateKind::SignatureState,
        tag: PassTag::Solver,
        applicable: signature_pattern_match::applicable,
        run: signature_pattern_match::run_signature_pattern_match,
    },
    PassDescriptor {
        id: PassId::SignatureAnf,
        consumes: StateKind::SignatureState,
        tag: PassTag::Solver,
        applicable: signature_anf::applicable,
        run: signature_anf::run_signature_anf,
    },
    PassDescriptor {
        id: PassId::PrepareCoeffModel,
        consumes: StateKind::SignatureState,
        tag: PassTag::Analysis,
        applicable: prepare_coeff_model::applicable,
        run: prepare_coeff_model::run_prepare_coeff_model,
    },
    PassDescriptor {
        id: PassId::SignatureCobCandidate,
        consumes: StateKind::SignatureCoeffState,
        tag: PassTag::Solver,
        applicable: signature_cob_candidate::applicable,
        run: signature_cob_candidate::run_signature_cob_candidate,
    },
    PassDescriptor {
        id: PassId::SignatureMultivarPolyRecovery,
        consumes: StateKind::SignatureState,
        tag: PassTag::Solver,
        applicable: signature_multivar_poly_recovery::applicable,
        run: signature_multivar_poly_recovery::run_signature_multivar_poly_recovery,
    },
    PassDescriptor {
        id: PassId::SignatureSingletonPolyRecovery,
        consumes: StateKind::SignatureCoeffState,
        tag: PassTag::Solver,
        applicable: signature_singleton_poly_recovery::applicable,
        run: signature_singleton_poly_recovery::run_signature_singleton_poly_recovery,
    },
    PassDescriptor {
        id: PassId::SemilinearNormalize,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Analysis,
        applicable: semilinear_normalize::applicable,
        run: semilinear_normalize::run_semilinear_normalize,
    },
    PassDescriptor {
        id: PassId::SemilinearCheck,
        consumes: StateKind::SemilinearNormalizedIr,
        tag: PassTag::Analysis,
        applicable: semilinear_check::applicable,
        run: semilinear_check::run_semilinear_check,
    },
    PassDescriptor {
        id: PassId::SemilinearRewrite,
        consumes: StateKind::SemilinearCheckedIr,
        tag: PassTag::Rewrite,
        applicable: semilinear_rewrite::applicable,
        run: semilinear_rewrite::run_semilinear_rewrite,
    },
    PassDescriptor {
        id: PassId::SemilinearReconstruct,
        consumes: StateKind::SemilinearRewrittenIr,
        tag: PassTag::Solver,
        applicable: semilinear_reconstruct::applicable,
        run: semilinear_reconstruct::run_semilinear_reconstruct,
    },
    PassDescriptor {
        id: PassId::PrepareDirectRemainder,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Analysis,
        applicable: prepare_direct_remainder::applicable,
        run: prepare_direct_remainder::run_prepare_direct_remainder,
    },
    PassDescriptor {
        id: PassId::PrepareRemainderFromCore,
        consumes: StateKind::CoreCandidate,
        tag: PassTag::Analysis,
        applicable: prepare_remainder_from_core::applicable,
        run: prepare_remainder_from_core::run_prepare_remainder_from_core,
    },
    PassDescriptor {
        id: PassId::ExtractProductCore,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Solver,
        applicable: extract_product_core::applicable,
        run: extract_product_core::run_extract_product_core,
    },
    PassDescriptor {
        id: PassId::ExtractPolyCoreD2,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Solver,
        applicable: extract_poly_core::applicable,
        run: extract_poly_core::run_extract_poly_core_d2,
    },
    PassDescriptor {
        id: PassId::ExtractPolyCoreD3,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Solver,
        applicable: extract_poly_core::applicable,
        run: extract_poly_core::run_extract_poly_core_d3,
    },
    PassDescriptor {
        id: PassId::ExtractPolyCoreD4,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Solver,
        applicable: extract_poly_core::applicable,
        run: extract_poly_core::run_extract_poly_core_d4,
    },
    PassDescriptor {
        id: PassId::ExtractTemplateCore,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Solver,
        applicable: extract_template_core::applicable,
        run: extract_template_core::run_extract_template_core,
    },
    PassDescriptor {
        id: PassId::ResidualSupported,
        consumes: StateKind::RemainderState,
        tag: PassTag::Solver,
        applicable: residual_supported::applicable,
        run: residual_supported::run_residual_supported,
    },
    PassDescriptor {
        id: PassId::ResidualPolyRecovery,
        consumes: StateKind::RemainderState,
        tag: PassTag::Solver,
        applicable: residual_poly_recovery::applicable,
        run: residual_poly_recovery::run_residual_poly_recovery,
    },
    PassDescriptor {
        id: PassId::ResidualGhost,
        consumes: StateKind::RemainderState,
        tag: PassTag::Solver,
        applicable: residual_ghost::applicable,
        run: residual_ghost::run_residual_ghost,
    },
    PassDescriptor {
        id: PassId::ResidualFactoredGhost,
        consumes: StateKind::RemainderState,
        tag: PassTag::Solver,
        applicable: residual_factored_ghost::applicable,
        run: residual_factored_ghost::run_residual_factored_ghost,
    },
    PassDescriptor {
        id: PassId::ResidualFactoredGhostEscalated,
        consumes: StateKind::RemainderState,
        tag: PassTag::Solver,
        applicable: residual_factored_ghost::applicable,
        run: residual_factored_ghost::run_residual_factored_ghost_escalated,
    },
    PassDescriptor {
        id: PassId::ResidualTemplate,
        consumes: StateKind::RemainderState,
        tag: PassTag::Solver,
        applicable: residual_template::applicable,
        run: residual_template::run_residual_template,
    },
    PassDescriptor {
        id: PassId::SignatureBitwiseDecompose,
        consumes: StateKind::SignatureState,
        tag: PassTag::Solver,
        applicable: signature_bitwise_decompose::applicable,
        run: signature_bitwise_decompose::run_signature_bitwise_decompose,
    },
    PassDescriptor {
        id: PassId::SignatureHybridDecompose,
        consumes: StateKind::SignatureState,
        tag: PassTag::Solver,
        applicable: signature_hybrid_decompose::applicable,
        run: signature_hybrid_decompose::run_signature_hybrid_decompose,
    },
    PassDescriptor {
        id: PassId::ResolveCompetition,
        consumes: StateKind::CompetitionResolved,
        tag: PassTag::Solver,
        applicable: resolve_competition::applicable,
        run: resolve_competition::run_resolve_competition,
    },
    PassDescriptor {
        id: PassId::OperandSimplify,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Rewrite,
        applicable: operand_simplify::applicable,
        run: operand_simplify::run_operand_simplify,
    },
    PassDescriptor {
        id: PassId::ProductIdentityCollapse,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Rewrite,
        applicable: product_identity_collapse::applicable,
        run: product_identity_collapse::run_product_identity_collapse,
    },
    PassDescriptor {
        id: PassId::AtomIdentityRewrite,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Rewrite,
        applicable: atom_identity_rewrite::applicable,
        run: atom_identity_rewrite::run_atom_identity_rewrite,
    },
    PassDescriptor {
        id: PassId::XorLowering,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Rewrite,
        applicable: xor_lowering::applicable,
        run: xor_lowering::run_xor_lowering,
    },
    PassDescriptor {
        id: PassId::LiftArithmeticAtoms,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Rewrite,
        applicable: lift_arithmetic_atoms::applicable,
        run: lift_arithmetic_atoms::run_lift_arithmetic_atoms,
    },
    PassDescriptor {
        id: PassId::LiftRepeatedSubexpressions,
        consumes: StateKind::FoldedAst,
        tag: PassTag::Rewrite,
        applicable: lift_repeated_subexpressions::applicable,
        run: lift_repeated_subexpressions::run_lift_repeated_subexpressions,
    },
    PassDescriptor {
        id: PassId::PrepareLiftedOuterSolve,
        consumes: StateKind::LiftedSkeleton,
        tag: PassTag::Analysis,
        applicable: prepare_lifted_outer_solve::applicable,
        run: prepare_lifted_outer_solve::run_prepare_lifted_outer_solve,
    },
];

pub use crate::aux_var::eliminate_aux_vars;
pub use crate::classifier::classify_structural;
pub use crate::entry::{simplify, simplify_expr, MAX_INPUT_VARS};
pub use crate::not_over_arith::{has_not_over_arith, is_purely_arithmetic, lower_not_over_arith};
pub use crate::pattern_matcher::{
    match_1var, match_2var_boolean, match_pattern, pack_bool_sig, simplify_pattern_subtrees,
    simplify_pattern_subtrees_certified, try_simplify_pattern_subtree,
    try_simplify_two_var_pattern_sum,
};
pub use crate::seed::seed_with_ast;
pub use crate::spot_check::{full_width_check_eval, verify_in_original_space, CheckResult};
