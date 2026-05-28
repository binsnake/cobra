//! Registry-level Lean proof coverage declarations.
//!
//! This is a drift guard, not a substitute for Lean proofs.  Every
//! registered pass must have one entry here so a new simplification path
//! cannot appear without an explicit statement of how proof metadata is
//! produced, preserved, or invalidated.

use cobra_orchestrator::PassId;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LeanProofCoverage {
    /// The pass only annotates or routes the same expression endpoint.
    AnalysisSameEndpoint,
    /// The pass emits a Lean endpoint semantic-equivalence certificate, or a
    /// verifier-generated endpoint certificate when one is missing.
    EndpointCertificate,
    /// The pass emits a Lean finite-signature certificate for a candidate.
    SignatureCertificate,
    /// The pass composes subproblem results and emits fresh parent signature
    /// evidence, or carries only certificates that still match the winner.
    RecomposeOrCarryCheckedCertificate,
    /// The pass crosses through an internal state whose semantic endpoint is
    /// discharged by a later reconstruction/substitution pass with fresh
    /// Lean-checkable endpoint or signature evidence.
    CoveredByDownstreamCertificate,
}

impl LeanProofCoverage {
    #[must_use]
    pub const fn is_lean_checked(self) -> bool {
        matches!(
            self,
            Self::EndpointCertificate
                | Self::SignatureCertificate
                | Self::RecomposeOrCarryCheckedCertificate
                | Self::CoveredByDownstreamCertificate
        )
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct PassProofCoverage {
    pub pass: PassId,
    pub coverage: LeanProofCoverage,
    pub note: &'static str,
}

pub const PASS_PROOF_COVERAGE: &[PassProofCoverage] = &[
    PassProofCoverage {
        pass: PassId::LowerNotOverArith,
        coverage: LeanProofCoverage::EndpointCertificate,
        note: "local 64-bit not-over-arithmetic rewrites chain endpoint certificates",
    },
    PassProofCoverage {
        pass: PassId::ClassifyAst,
        coverage: LeanProofCoverage::AnalysisSameEndpoint,
        note: "classification annotates the same AST endpoint",
    },
    PassProofCoverage {
        pass: PassId::BuildSignatureState,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "signature-state seed clears stale metadata and downstream signature solvers emit source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::VerifyCandidate,
        coverage: LeanProofCoverage::EndpointCertificate,
        note: "verified candidates receive endpoint certificates when possible",
    },
    PassProofCoverage {
        pass: PassId::SignaturePatternMatch,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "truth-table signature certificate covers produced candidate",
    },
    PassProofCoverage {
        pass: PassId::SignatureAnf,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "truth-table signature certificate covers produced ANF candidate",
    },
    PassProofCoverage {
        pass: PassId::PrepareCoeffModel,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "coefficient-model state clears stale metadata and downstream coefficient solvers emit source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::SignatureCobCandidate,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "truth-table signature certificate covers produced COB candidate",
    },
    PassProofCoverage {
        pass: PassId::SignatureMultivarPolyRecovery,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "truth-table signature certificate covers recovered polynomial candidate",
    },
    PassProofCoverage {
        pass: PassId::SignatureSingletonPolyRecovery,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "truth-table signature certificate covers singleton polynomial candidate",
    },
    PassProofCoverage {
        pass: PassId::SemilinearNormalize,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "semilinear normalized IR is covered when reconstruction emits source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::SemilinearCheck,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "semilinear checked IR is covered when reconstruction emits source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::SemilinearRewrite,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "semilinear rewritten IR is covered when reconstruction emits source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::SemilinearReconstruct,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "reconstructed candidate gets source-signature truth-table evidence",
    },
    PassProofCoverage {
        pass: PassId::PrepareDirectRemainder,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "direct remainder state is covered when residual recombination emits source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::PrepareRemainderFromCore,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "constant residual short-circuit emits source-signature evidence; remainder state clears stale metadata",
    },
    PassProofCoverage {
        pass: PassId::ExtractProductCore,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "direct extractor candidates get source-signature evidence; core candidates clear stale metadata",
    },
    PassProofCoverage {
        pass: PassId::ExtractPolyCoreD2,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "direct extractor candidates get source-signature evidence; core candidates clear stale metadata",
    },
    PassProofCoverage {
        pass: PassId::ExtractPolyCoreD3,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "direct extractor candidates get source-signature evidence; core candidates clear stale metadata",
    },
    PassProofCoverage {
        pass: PassId::ExtractPolyCoreD4,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "direct extractor candidates get source-signature evidence; core candidates clear stale metadata",
    },
    PassProofCoverage {
        pass: PassId::ExtractTemplateCore,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "direct extractor candidates get source-signature evidence; core candidates clear stale metadata",
    },
    PassProofCoverage {
        pass: PassId::ResidualSupported,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "supported residual subproblem is covered when residual recombination emits source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::ResidualPolyRecovery,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "residual recombination emits source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::ResidualGhost,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "residual recombination emits source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::ResidualFactoredGhost,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "residual recombination emits source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::ResidualFactoredGhostEscalated,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "residual recombination emits source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::ResidualTemplate,
        coverage: LeanProofCoverage::SignatureCertificate,
        note: "residual recombination emits source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::SignatureBitwiseDecompose,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "bitwise decomposition children are covered when resolve recomposes fresh parent signature evidence",
    },
    PassProofCoverage {
        pass: PassId::SignatureHybridDecompose,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "hybrid decomposition children are covered when resolve recomposes fresh parent signature evidence",
    },
    PassProofCoverage {
        pass: PassId::ResolveCompetition,
        coverage: LeanProofCoverage::RecomposeOrCarryCheckedCertificate,
        note: "winner carry is endpoint-checked; recomposition/substitution emits fresh signature evidence",
    },
    PassProofCoverage {
        pass: PassId::OperandSimplify,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "operand subproblems are covered when resolved join rewrites emit endpoint evidence",
    },
    PassProofCoverage {
        pass: PassId::ProductIdentityCollapse,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "product-collapse subproblems clear stale metadata and resolved recomposition emits source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::AtomIdentityRewrite,
        coverage: LeanProofCoverage::EndpointCertificate,
        note: "atom identity rewrites chain local endpoint certificates when theorem-supported",
    },
    PassProofCoverage {
        pass: PassId::XorLowering,
        coverage: LeanProofCoverage::EndpointCertificate,
        note: "xor-lowered AST replacements emit theorem-backed endpoint step chains when structurally reconstructed",
    },
    PassProofCoverage {
        pass: PassId::LiftArithmeticAtoms,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "lifted arithmetic skeleton is covered when lifted substitution emits source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::LiftRepeatedSubexpressions,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "lifted repeated-subexpression skeleton is covered when lifted substitution emits source-signature evidence",
    },
    PassProofCoverage {
        pass: PassId::PrepareLiftedOuterSolve,
        coverage: LeanProofCoverage::CoveredByDownstreamCertificate,
        note: "outer lifted solve is covered when lifted substitution emits source-signature evidence",
    },
];

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct PassReplayEvidence {
    pub pass: PassId,
    pub replay_tests: &'static [&'static str],
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum InternalProofTarget {
    LeanEmitterFallbacks,
    LeanContextFrameMatrix,
    LeanTheoremExports,
    LocalRewriteTheoremMatrix,
    PublicCleanupFamily,
    ProductShadowRepairGuard,
    PatternSubtreeRewrite,
    AtomSimplifierConstantFold,
    SemilinearReconstructionFamily,
    ResidualRecompositionFamily,
    BitwiseRecompositionFamily,
    HybridRecompositionFamily,
    LiftedSubstitution,
    OperandJoinRewrite,
    ProductJoinRewrite,
    DirectExtractorFamilies,
    SignatureSolverFamilies,
    XorLoweringFamily,
    VerifyCandidateEndpoint,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct InternalProofCoverage {
    pub target: InternalProofTarget,
    pub replay_tests: &'static [&'static str],
    pub note: &'static str,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EndpointFallbackInventory {
    pub file: &'static str,
    pub lean_certificate_new_count: usize,
    pub class: EndpointFallbackClass,
    pub note: &'static str,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum EndpointFallbackClass {
    TestOnly,
    ProductionFallback,
    MixedProductionAndTest,
    RemovedProductionFallback,
}

pub const ENDPOINT_FALLBACK_INVENTORY: &[EndpointFallbackInventory] = &[
    EndpointFallbackInventory {
        file: "crates/cobra-orchestrator/src/competition.rs",
        lean_certificate_new_count: 2,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificates for competition acceptance guards",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-orchestrator/src/entry.rs",
        lean_certificate_new_count: 3,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificates for public proof-level acceptance",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-orchestrator/src/main_loop.rs",
        lean_certificate_new_count: 2,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificates for group verification acceptance",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/atom_simplifier.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::ProductionFallback,
        note: "residual atom simplifier fallback when a theorem-backed local rewrite chain cannot be assembled",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/candidate_normalize.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificate for normalized candidate rejection guards",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/atom_identity_rewrite.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificate for stale metadata clearing",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/build_signature_state.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificate proving stale metadata is cleared",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/decomposition_engine.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificate proving stale metadata is cleared",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/xor_lowering.rs",
        lean_certificate_new_count: 0,
        class: EndpointFallbackClass::RemovedProductionFallback,
        note: "production fallback removed; xor lowering attaches endpoint evidence only when theorem-chain reconstruction succeeds",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/verify_candidate.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::ProductionFallback,
        note: "production verifier fallback after full-width acceptance when no theorem-backed endpoint chain exists",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/signature_pattern_match.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificate proving stale metadata is cleared",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/prepare_lifted_outer_solve.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificate proving stale metadata is cleared",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/prepare_coeff_model.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificate proving stale metadata is cleared",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/signature_anf.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificate proving stale metadata is cleared",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/pattern_matcher.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::ProductionFallback,
        note: "residual pattern matcher fallback when a theorem-backed local rewrite chain cannot be assembled",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/seed.rs",
        lean_certificate_new_count: 0,
        class: EndpointFallbackClass::RemovedProductionFallback,
        note: "production fallback removed; seed rewrites attach endpoint evidence only when theorem-chain composition succeeds",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/resolve_competition.rs",
        lean_certificate_new_count: 8,
        class: EndpointFallbackClass::MixedProductionAndTest,
        note: "mixed production/test endpoint fallbacks for competition resolution and recomposition guards",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/product_identity_collapse.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificate proving stale metadata is cleared",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/residual_supported.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificate proving stale metadata is cleared",
    },
    EndpointFallbackInventory {
        file: "crates/cobra-passes/src/lift_arithmetic_atoms.rs",
        lean_certificate_new_count: 1,
        class: EndpointFallbackClass::TestOnly,
        note: "test-only endpoint certificate proving stale metadata is cleared",
    },
];

pub const INTERNAL_PROOF_COVERAGE: &[InternalProofCoverage] = &[
    InternalProofCoverage {
        target: InternalProofTarget::LeanEmitterFallbacks,
        replay_tests: &["lean_emitter_fallbacks_replays_in_lean"],
        note: "fallback endpoint and constant-signature Lean emitters produce source accepted by Lean",
    },
    InternalProofCoverage {
        target: InternalProofTarget::LeanContextFrameMatrix,
        replay_tests: &["lean_context_frame_matrix_replays_in_lean"],
        note: "every generated Lean context frame shape replays through step-chain certificates",
    },
    InternalProofCoverage {
        target: InternalProofTarget::LeanTheoremExports,
        replay_tests: &["lean_theorem_exports_replays_in_lean"],
        note: "every theorem named by Rust certificate generation is exported by the Lean verification layer",
    },
    InternalProofCoverage {
        target: InternalProofTarget::LocalRewriteTheoremMatrix,
        replay_tests: &["local_rewrite_theorem_matrix_replays_in_lean"],
        note: "every theorem recognized by 64-bit local rewrite certificate generation replays in Lean",
    },
    InternalProofCoverage {
        target: InternalProofTarget::PublicCleanupFamily,
        replay_tests: &[
            "public_cleanup_generated_certificate_replays_in_lean",
            "public_cleanup_after_certified_endpoint_replays_in_lean",
        ],
        note: "final public-output cleanup rewrites replay as endpoint certificates and composes with prior certified pass endpoints",
    },
    InternalProofCoverage {
        target: InternalProofTarget::ProductShadowRepairGuard,
        replay_tests: &["signature_anf_product_shadow_repair_generated_certificate_replays_in_lean"],
        note: "product-shadow repair is not a general endpoint rewrite; the guarded ANF route replays a Lean signature certificate for the repaired candidate",
    },
    InternalProofCoverage {
        target: InternalProofTarget::PatternSubtreeRewrite,
        replay_tests: &[
            "seed_pattern_rewrite_generated_certificate_replays_in_lean",
            "pattern_matcher_scaled_pattern_sum_theorem_replays_in_lean",
            "pattern_matcher_demorgan_table_theorem_replays_in_lean",
            "pattern_matcher_demorgan_dual_table_theorem_replays_in_lean",
        ],
        note: "pattern-subtree simplification emits theorem-backed endpoint certificates for local, bidirectional De Morgan table, and scaled pattern-sum rewrites",
    },
    InternalProofCoverage {
        target: InternalProofTarget::AtomSimplifierConstantFold,
        replay_tests: &["atom_simplifier_constant_fold_generated_certificate_replays_in_lean"],
        note: "constant-folded atoms produce endpoint certificates against the source expression",
    },
    InternalProofCoverage {
        target: InternalProofTarget::SemilinearReconstructionFamily,
        replay_tests: &[
            "semilinear_reconstruct_generated_certificate_replays_in_lean",
            "semilinear_flow_generated_certificate_replays_in_lean",
            "semilinear_family_generated_certificate_replays_in_lean",
        ],
        note: "semilinear normalize/check/rewrite paths are discharged by source-signature reconstruction certificates",
    },
    InternalProofCoverage {
        target: InternalProofTarget::ResidualRecompositionFamily,
        replay_tests: &[
            "residual_recombine_generated_certificate_replays_in_lean",
            "residual_recombine_context_target_generated_certificate_replays_in_lean",
            "residual_recombine_remapped_vars_generated_certificate_replays_in_lean",
            "residual_poly_recovery_generated_certificate_replays_in_lean",
            "residual_poly_recovery_family_generated_certificate_replays_in_lean",
            "residual_ghost_generated_certificate_replays_in_lean",
            "residual_ghost_family_generated_certificate_replays_in_lean",
            "residual_factored_ghost_generated_certificate_replays_in_lean",
            "residual_factored_ghost_family_generated_certificate_replays_in_lean",
            "residual_template_generated_certificate_replays_in_lean",
            "residual_template_family_generated_certificate_replays_in_lean",
        ],
        note: "residual solvers and recomposition emit source-signature certificates for the recombined candidate",
    },
    InternalProofCoverage {
        target: InternalProofTarget::BitwiseRecompositionFamily,
        replay_tests: &[
            "bitwise_compose_generated_certificate_replays_in_lean",
            "bitwise_compose_without_parent_eval_generated_certificate_replays_in_lean",
            "bitwise_compose_family_generated_certificate_replays_in_lean",
            "signature_bitwise_decompose_direct_generated_certificate_replays_in_lean",
            "signature_bitwise_decompose_child_flow_generated_certificate_replays_in_lean",
        ],
        note: "bitwise decomposition is discharged by direct candidate or parent recomposition signature certificates",
    },
    InternalProofCoverage {
        target: InternalProofTarget::HybridRecompositionFamily,
        replay_tests: &[
            "hybrid_compose_generated_certificate_replays_in_lean",
            "hybrid_compose_without_parent_eval_generated_certificate_replays_in_lean",
            "hybrid_compose_family_generated_certificate_replays_in_lean",
            "signature_hybrid_decompose_flow_generated_certificate_replays_in_lean",
        ],
        note: "hybrid decomposition is discharged by parent recomposition signature certificates",
    },
    InternalProofCoverage {
        target: InternalProofTarget::LiftedSubstitution,
        replay_tests: &[
            "lifted_substitute_generated_certificate_replays_in_lean",
            "lift_arithmetic_atoms_flow_generated_certificate_replays_in_lean",
            "lift_arithmetic_atoms_family_generated_certificate_replays_in_lean",
            "lift_repeated_subexpressions_flow_generated_certificate_replays_in_lean",
            "lift_repeated_subexpressions_family_generated_certificate_replays_in_lean",
            "prepare_lifted_outer_pattern_certificate_replays_in_lean",
        ],
        note: "lifted skeleton and outer-solve paths are discharged by substitution or pattern endpoint/signature certificates",
    },
    InternalProofCoverage {
        target: InternalProofTarget::OperandJoinRewrite,
        replay_tests: &[
            "operand_join_rewrite_generated_certificate_replays_in_lean",
            "operand_simplify_flow_generated_certificate_replays_in_lean",
            "operand_simplify_family_generated_certificate_replays_in_lean",
        ],
        note: "resolved operand simplifications emit endpoint certificates for the joined rewrite",
    },
    InternalProofCoverage {
        target: InternalProofTarget::ProductJoinRewrite,
        replay_tests: &[
            "product_join_rewrite_generated_certificate_replays_in_lean",
            "product_identity_collapse_flow_generated_certificate_replays_in_lean",
            "product_identity_collapse_pattern_flow_generated_certificate_replays_in_lean",
            "product_identity_collapse_family_generated_certificate_replays_in_lean",
        ],
        note: "product identity collapse is discharged by joined source-signature certificates",
    },
    InternalProofCoverage {
        target: InternalProofTarget::DirectExtractorFamilies,
        replay_tests: &[
            "extract_product_core_generated_certificate_replays_in_lean",
            "extract_product_core_family_generated_certificate_replays_in_lean",
            "extract_poly_core_d2_generated_certificate_replays_in_lean",
            "extract_poly_core_d2_family_generated_certificate_replays_in_lean",
            "extract_poly_core_d3_generated_certificate_replays_in_lean",
            "extract_poly_core_d3_family_generated_certificate_replays_in_lean",
            "extract_poly_core_d4_generated_certificate_replays_in_lean",
            "extract_poly_core_d4_family_generated_certificate_replays_in_lean",
            "extract_template_core_generated_certificate_replays_in_lean",
            "extract_template_core_family_generated_certificate_replays_in_lean",
        ],
        note: "extractor direct-candidate paths emit source-signature certificates; internal core states are downstream-covered",
    },
    InternalProofCoverage {
        target: InternalProofTarget::SignatureSolverFamilies,
        replay_tests: &[
            "signature_pattern_match_generated_certificate_replays_in_lean",
            "signature_pattern_match_grouped_candidate_generated_certificate_replays_in_lean",
            "signature_pattern_match_family_generated_certificate_replays_in_lean",
            "signature_anf_generated_certificate_replays_in_lean",
            "signature_anf_grouped_candidate_generated_certificate_replays_in_lean",
            "signature_anf_family_generated_certificate_replays_in_lean",
            "signature_cob_candidate_generated_certificate_replays_in_lean",
            "signature_cob_candidate_override_generated_certificate_replays_in_lean",
            "signature_cob_candidate_family_generated_certificate_replays_in_lean",
            "signature_multivar_poly_generated_certificate_replays_in_lean",
            "signature_multivar_poly_override_generated_certificate_replays_in_lean",
            "signature_multivar_poly_family_generated_certificate_replays_in_lean",
            "signature_singleton_poly_generated_certificate_replays_in_lean",
            "signature_singleton_poly_inline_override_generated_certificate_replays_in_lean",
            "signature_singleton_poly_family_generated_certificate_replays_in_lean",
        ],
        note: "signature candidate families emit finite truth-table certificates for accepted verified candidates",
    },
    InternalProofCoverage {
        target: InternalProofTarget::XorLoweringFamily,
        replay_tests: &[
            "xor_lowering_generated_certificate_replays_in_lean",
            "xor_lowering_family_generated_certificate_replays_in_lean",
        ],
        note: "xor lowering emits theorem-backed endpoint step chains for reconstructed arithmetic forms",
    },
    InternalProofCoverage {
        target: InternalProofTarget::VerifyCandidateEndpoint,
        replay_tests: &[
            "verify_candidate_generated_certificate_replays_in_lean",
            "verify_candidate_family_generated_certificate_replays_in_lean",
        ],
        note: "candidate verification emits endpoint certificates for accepted original-space candidates",
    },
];

pub const PASS_REPLAY_EVIDENCE: &[PassReplayEvidence] = &[
    PassReplayEvidence {
        pass: PassId::LowerNotOverArith,
        replay_tests: &[
            "lower_not_over_arith_generated_certificate_replays_in_lean",
            "lower_not_over_arith_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::BuildSignatureState,
        replay_tests: &["build_signature_state_flow_generated_certificate_replays_in_lean"],
    },
    PassReplayEvidence {
        pass: PassId::PatternSubtreeRewrite,
        replay_tests: &[
            "seed_pattern_rewrite_generated_certificate_replays_in_lean",
            "pattern_matcher_scaled_pattern_sum_theorem_replays_in_lean",
            "pattern_matcher_demorgan_table_theorem_replays_in_lean",
            "pattern_matcher_demorgan_dual_table_theorem_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::VerifyCandidate,
        replay_tests: &[
            "verify_candidate_generated_certificate_replays_in_lean",
            "verify_candidate_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::SignaturePatternMatch,
        replay_tests: &[
            "signature_pattern_match_generated_certificate_replays_in_lean",
            "signature_pattern_match_grouped_candidate_generated_certificate_replays_in_lean",
            "signature_pattern_match_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::SignatureAnf,
        replay_tests: &[
            "signature_anf_generated_certificate_replays_in_lean",
            "signature_anf_grouped_candidate_generated_certificate_replays_in_lean",
            "signature_anf_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::PrepareCoeffModel,
        replay_tests: &["prepare_coeff_model_flow_generated_certificate_replays_in_lean"],
    },
    PassReplayEvidence {
        pass: PassId::SignatureCobCandidate,
        replay_tests: &[
            "signature_cob_candidate_generated_certificate_replays_in_lean",
            "signature_cob_candidate_override_generated_certificate_replays_in_lean",
            "signature_cob_candidate_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::SignatureMultivarPolyRecovery,
        replay_tests: &[
            "signature_multivar_poly_generated_certificate_replays_in_lean",
            "signature_multivar_poly_override_generated_certificate_replays_in_lean",
            "signature_multivar_poly_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::SignatureSingletonPolyRecovery,
        replay_tests: &[
            "signature_singleton_poly_generated_certificate_replays_in_lean",
            "signature_singleton_poly_inline_override_generated_certificate_replays_in_lean",
            "signature_singleton_poly_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::SemilinearNormalize,
        replay_tests: &[
            "semilinear_reconstruct_generated_certificate_replays_in_lean",
            "semilinear_flow_generated_certificate_replays_in_lean",
            "semilinear_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::SemilinearCheck,
        replay_tests: &[
            "semilinear_reconstruct_generated_certificate_replays_in_lean",
            "semilinear_flow_generated_certificate_replays_in_lean",
            "semilinear_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::SemilinearRewrite,
        replay_tests: &[
            "semilinear_reconstruct_generated_certificate_replays_in_lean",
            "semilinear_flow_generated_certificate_replays_in_lean",
            "semilinear_family_generated_certificate_replays_in_lean",
            "atom_simplifier_constant_fold_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::SemilinearReconstruct,
        replay_tests: &[
            "semilinear_reconstruct_generated_certificate_replays_in_lean",
            "semilinear_flow_generated_certificate_replays_in_lean",
            "semilinear_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::PrepareDirectRemainder,
        replay_tests: &[
            "residual_recombine_generated_certificate_replays_in_lean",
            "prepare_direct_remainder_recombine_generated_certificate_replays_in_lean",
            "prepare_direct_remainder_ghost_flow_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::PrepareRemainderFromCore,
        replay_tests: &[
            "prepare_remainder_constant_generated_certificate_replays_in_lean",
            "prepare_remainder_supported_flow_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::ExtractProductCore,
        replay_tests: &[
            "extract_product_core_generated_certificate_replays_in_lean",
            "extract_product_core_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::ExtractPolyCoreD2,
        replay_tests: &[
            "extract_poly_core_d2_generated_certificate_replays_in_lean",
            "extract_poly_core_d2_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::ExtractPolyCoreD3,
        replay_tests: &[
            "extract_poly_core_d3_generated_certificate_replays_in_lean",
            "extract_poly_core_d3_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::ExtractPolyCoreD4,
        replay_tests: &[
            "extract_poly_core_d4_generated_certificate_replays_in_lean",
            "extract_poly_core_d4_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::ExtractTemplateCore,
        replay_tests: &[
            "extract_template_core_generated_certificate_replays_in_lean",
            "extract_template_core_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::ResidualSupported,
        replay_tests: &[
            "residual_recombine_generated_certificate_replays_in_lean",
            "prepare_remainder_supported_flow_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::ResidualPolyRecovery,
        replay_tests: &[
            "residual_poly_recovery_generated_certificate_replays_in_lean",
            "residual_poly_recovery_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::ResidualGhost,
        replay_tests: &[
            "residual_ghost_generated_certificate_replays_in_lean",
            "residual_ghost_family_generated_certificate_replays_in_lean",
            "prepare_direct_remainder_ghost_flow_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::ResidualFactoredGhost,
        replay_tests: &["residual_factored_ghost_generated_certificate_replays_in_lean"],
    },
    PassReplayEvidence {
        pass: PassId::ResidualFactoredGhostEscalated,
        replay_tests: &[
            "residual_factored_ghost_generated_certificate_replays_in_lean",
            "residual_factored_ghost_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::ResidualTemplate,
        replay_tests: &[
            "residual_template_generated_certificate_replays_in_lean",
            "residual_template_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::SignatureBitwiseDecompose,
        replay_tests: &[
            "signature_bitwise_decompose_direct_generated_certificate_replays_in_lean",
            "signature_bitwise_decompose_child_flow_generated_certificate_replays_in_lean",
            "bitwise_compose_generated_certificate_replays_in_lean",
            "bitwise_compose_without_parent_eval_generated_certificate_replays_in_lean",
            "bitwise_compose_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::SignatureHybridDecompose,
        replay_tests: &[
            "signature_hybrid_decompose_flow_generated_certificate_replays_in_lean",
            "hybrid_compose_generated_certificate_replays_in_lean",
            "hybrid_compose_without_parent_eval_generated_certificate_replays_in_lean",
            "hybrid_compose_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::ResolveCompetition,
        replay_tests: &[
            "resolve_none_carry_generated_certificate_replays_in_lean",
            "resolve_none_endpoint_carry_generated_certificate_replays_in_lean",
            "signature_bitwise_decompose_child_flow_generated_certificate_replays_in_lean",
            "bitwise_compose_generated_certificate_replays_in_lean",
            "bitwise_compose_without_parent_eval_generated_certificate_replays_in_lean",
            "bitwise_compose_family_generated_certificate_replays_in_lean",
            "hybrid_compose_generated_certificate_replays_in_lean",
            "hybrid_compose_without_parent_eval_generated_certificate_replays_in_lean",
            "hybrid_compose_family_generated_certificate_replays_in_lean",
            "lifted_substitute_generated_certificate_replays_in_lean",
            "operand_join_rewrite_generated_certificate_replays_in_lean",
            "product_join_rewrite_generated_certificate_replays_in_lean",
            "residual_recombine_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::OperandSimplify,
        replay_tests: &[
            "operand_join_rewrite_generated_certificate_replays_in_lean",
            "operand_simplify_flow_generated_certificate_replays_in_lean",
            "operand_simplify_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::ProductIdentityCollapse,
        replay_tests: &[
            "product_identity_collapse_flow_generated_certificate_replays_in_lean",
            "product_identity_collapse_pattern_flow_generated_certificate_replays_in_lean",
            "product_identity_collapse_family_generated_certificate_replays_in_lean",
            "product_join_rewrite_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::AtomIdentityRewrite,
        replay_tests: &[
            "atom_identity_rewrite_generated_certificate_replays_in_lean",
            "atom_identity_rewrite_family_generated_certificate_replays_in_lean",
            "local_rewrite_theorem_matrix_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::XorLowering,
        replay_tests: &[
            "xor_lowering_generated_certificate_replays_in_lean",
            "xor_lowering_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::LiftArithmeticAtoms,
        replay_tests: &[
            "lift_arithmetic_atoms_flow_generated_certificate_replays_in_lean",
            "lift_arithmetic_atoms_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::LiftRepeatedSubexpressions,
        replay_tests: &[
            "lift_repeated_subexpressions_flow_generated_certificate_replays_in_lean",
            "lift_repeated_subexpressions_family_generated_certificate_replays_in_lean",
        ],
    },
    PassReplayEvidence {
        pass: PassId::PrepareLiftedOuterSolve,
        replay_tests: &[
            "lift_arithmetic_atoms_flow_generated_certificate_replays_in_lean",
            "lift_arithmetic_atoms_family_generated_certificate_replays_in_lean",
            "lift_repeated_subexpressions_flow_generated_certificate_replays_in_lean",
            "lift_repeated_subexpressions_family_generated_certificate_replays_in_lean",
            "prepare_lifted_outer_pattern_certificate_replays_in_lean",
        ],
    },
];

#[must_use]
pub fn proof_coverage_for(pass: PassId) -> Option<&'static PassProofCoverage> {
    PASS_PROOF_COVERAGE.iter().find(|entry| entry.pass == pass)
}

#[must_use]
pub fn replay_evidence_for(pass: PassId) -> Option<&'static PassReplayEvidence> {
    PASS_REPLAY_EVIDENCE.iter().find(|entry| entry.pass == pass)
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use cobra_orchestrator::PassTag;

    use super::*;
    use crate::PASS_REGISTRY;

    const ALL_PASS_IDS: [PassId; PassId::COUNT as usize] = [
        PassId::LowerNotOverArith,
        PassId::ClassifyAst,
        PassId::BuildSignatureState,
        PassId::SemilinearNormalize,
        PassId::SemilinearCheck,
        PassId::SemilinearRewrite,
        PassId::SemilinearReconstruct,
        PassId::ExtractProductCore,
        PassId::ExtractPolyCoreD2,
        PassId::ExtractTemplateCore,
        PassId::ExtractPolyCoreD3,
        PassId::ExtractPolyCoreD4,
        PassId::PrepareDirectRemainder,
        PassId::PrepareRemainderFromCore,
        PassId::ResidualSupported,
        PassId::ResidualPolyRecovery,
        PassId::ResidualGhost,
        PassId::ResidualFactoredGhost,
        PassId::ResidualFactoredGhostEscalated,
        PassId::ResidualTemplate,
        PassId::ResolveCompetition,
        PassId::SignaturePatternMatch,
        PassId::SignatureAnf,
        PassId::PrepareCoeffModel,
        PassId::SignatureCobCandidate,
        PassId::SignatureSingletonPolyRecovery,
        PassId::SignatureMultivarPolyRecovery,
        PassId::SignatureBitwiseDecompose,
        PassId::SignatureHybridDecompose,
        PassId::OperandSimplify,
        PassId::ProductIdentityCollapse,
        PassId::XorLowering,
        PassId::VerifyCandidate,
        PassId::LiftArithmeticAtoms,
        PassId::LiftRepeatedSubexpressions,
        PassId::PrepareLiftedOuterSolve,
        PassId::PatternSubtreeRewrite,
        PassId::AtomIdentityRewrite,
    ];

    const PSEUDO_PASS_IDS_WITH_REPLAY_EVIDENCE: &[PassId] = &[PassId::PatternSubtreeRewrite];

    fn source_for_inventory_file(file: &str) -> &'static str {
        match file {
            "crates/cobra-orchestrator/src/competition.rs" => {
                include_str!("../../cobra-orchestrator/src/competition.rs")
            }
            "crates/cobra-orchestrator/src/entry.rs" => {
                include_str!("../../cobra-orchestrator/src/entry.rs")
            }
            "crates/cobra-orchestrator/src/main_loop.rs" => {
                include_str!("../../cobra-orchestrator/src/main_loop.rs")
            }
            "crates/cobra-passes/src/atom_simplifier.rs" => include_str!("atom_simplifier.rs"),
            "crates/cobra-passes/src/candidate_normalize.rs" => {
                include_str!("candidate_normalize.rs")
            }
            "crates/cobra-passes/src/atom_identity_rewrite.rs" => {
                include_str!("atom_identity_rewrite.rs")
            }
            "crates/cobra-passes/src/build_signature_state.rs" => {
                include_str!("build_signature_state.rs")
            }
            "crates/cobra-passes/src/decomposition_engine.rs" => {
                include_str!("decomposition_engine.rs")
            }
            "crates/cobra-passes/src/xor_lowering.rs" => include_str!("xor_lowering.rs"),
            "crates/cobra-passes/src/verify_candidate.rs" => include_str!("verify_candidate.rs"),
            "crates/cobra-passes/src/signature_pattern_match.rs" => {
                include_str!("signature_pattern_match.rs")
            }
            "crates/cobra-passes/src/prepare_lifted_outer_solve.rs" => {
                include_str!("prepare_lifted_outer_solve.rs")
            }
            "crates/cobra-passes/src/prepare_coeff_model.rs" => {
                include_str!("prepare_coeff_model.rs")
            }
            "crates/cobra-passes/src/signature_anf.rs" => include_str!("signature_anf.rs"),
            "crates/cobra-passes/src/pattern_matcher.rs" => include_str!("pattern_matcher.rs"),
            "crates/cobra-passes/src/seed.rs" => include_str!("seed.rs"),
            "crates/cobra-passes/src/resolve_competition.rs" => {
                include_str!("resolve_competition.rs")
            }
            "crates/cobra-passes/src/product_identity_collapse.rs" => {
                include_str!("product_identity_collapse.rs")
            }
            "crates/cobra-passes/src/residual_supported.rs" => {
                include_str!("residual_supported.rs")
            }
            "crates/cobra-passes/src/lift_arithmetic_atoms.rs" => {
                include_str!("lift_arithmetic_atoms.rs")
            }
            other => panic!("missing endpoint fallback inventory source for {other}"),
        }
    }

    #[test]
    fn every_registered_pass_has_proof_coverage_entry() {
        let mut declared = HashSet::new();
        for entry in PASS_PROOF_COVERAGE {
            assert!(
                declared.insert(entry.pass),
                "duplicate proof coverage entry for {:?}",
                entry.pass
            );
            assert!(
                !entry.note.is_empty(),
                "proof coverage entry for {:?} needs a note",
                entry.pass
            );
        }

        for desc in PASS_REGISTRY {
            assert!(
                declared.remove(&desc.id),
                "missing proof coverage entry for {:?}",
                desc.id
            );
        }

        assert!(
            declared.is_empty(),
            "proof coverage declares unregistered passes: {:?}",
            declared
        );
    }

    #[test]
    fn endpoint_fallback_certificate_sites_are_inventoried() {
        let mut declared = HashSet::new();
        let mut production_files = Vec::new();
        for entry in ENDPOINT_FALLBACK_INVENTORY {
            assert!(
                declared.insert(entry.file),
                "duplicate endpoint fallback inventory entry for {}",
                entry.file
            );
            assert!(
                !entry.note.is_empty(),
                "endpoint fallback inventory entry for {} must explain why the fallback remains",
                entry.file
            );
            let actual = source_for_inventory_file(entry.file)
                .matches("LeanCertificate::new(")
                .count();
            assert_eq!(
                actual, entry.lean_certificate_new_count,
                "{} changed its LeanCertificate::new count; classify the new or removed endpoint fallback site before updating the inventory",
                entry.file
            );
            match entry.class {
                EndpointFallbackClass::TestOnly => {
                    assert!(
                        entry.note.contains("test-only"),
                        "{} is classified test-only but its note does not say so",
                        entry.file
                    );
                }
                EndpointFallbackClass::ProductionFallback
                | EndpointFallbackClass::MixedProductionAndTest => {
                    production_files.push(entry.file);
                    assert!(
                        !entry.note.contains("test-only"),
                        "{} has production fallback behavior but is described as test-only",
                        entry.file
                    );
                }
                EndpointFallbackClass::RemovedProductionFallback => {
                    assert_eq!(
                        entry.lean_certificate_new_count, 0,
                        "{} is marked as removed production fallback but still has endpoint fallback constructors",
                        entry.file
                    );
                    assert!(
                        entry.note.contains("removed"),
                        "{} is marked as removed production fallback but its note does not say so",
                        entry.file
                    );
                }
            }
        }

        let total: usize = ENDPOINT_FALLBACK_INVENTORY
            .iter()
            .map(|entry| entry.lean_certificate_new_count)
            .sum();
        assert!(
            total > 0,
            "endpoint fallback inventory should not be empty while fallback constructors remain"
        );
        assert_eq!(
            production_files,
            vec![
                "crates/cobra-passes/src/atom_simplifier.rs",
                "crates/cobra-passes/src/verify_candidate.rs",
                "crates/cobra-passes/src/pattern_matcher.rs",
                "crates/cobra-passes/src/resolve_competition.rs",
            ],
            "production endpoint fallback inventory changed; prioritize these sites for theorem-chain replacement"
        );
    }

    #[test]
    fn every_pass_id_is_registered_or_explicit_pseudo_with_replay_evidence() {
        let registered: HashSet<_> = PASS_REGISTRY.iter().map(|desc| desc.id).collect();
        let pseudo: HashSet<_> = PSEUDO_PASS_IDS_WITH_REPLAY_EVIDENCE
            .iter()
            .copied()
            .collect();
        let mut seen = HashSet::new();

        for (idx, pass) in ALL_PASS_IDS.iter().copied().enumerate() {
            assert_eq!(
                pass.as_u8(),
                idx as u8,
                "ALL_PASS_IDS must stay in PassId discriminant order"
            );
            assert!(
                seen.insert(pass),
                "duplicate PassId inventory entry {pass:?}"
            );
            assert!(
                registered.contains(&pass) || pseudo.contains(&pass),
                "{pass:?} is a PassId but is neither a registered pass nor an explicit pseudo-pass"
            );
        }

        assert_eq!(
            seen.len(),
            PassId::COUNT as usize,
            "ALL_PASS_IDS must enumerate every PassId variant"
        );

        for pass in pseudo {
            assert!(
                !registered.contains(&pass),
                "pseudo-pass {pass:?} must not also be a runtime registered pass"
            );
            assert!(
                replay_evidence_for(pass).is_some(),
                "pseudo-pass {pass:?} must have generated Lean replay evidence"
            );
        }
    }

    #[test]
    fn semantic_result_passes_have_explicit_checked_or_invalidating_coverage() {
        for desc in PASS_REGISTRY {
            let coverage = proof_coverage_for(desc.id)
                .unwrap_or_else(|| panic!("missing proof coverage for {:?}", desc.id));
            match desc.tag {
                PassTag::Rewrite | PassTag::Solver | PassTag::Verifier => assert_ne!(
                    coverage.coverage,
                    LeanProofCoverage::AnalysisSameEndpoint,
                    "{:?} changes or solves semantics and cannot be same-endpoint analysis",
                    desc.id
                ),
                PassTag::Analysis => {}
            }
        }
    }

    #[test]
    fn rewrite_solver_and_verifier_passes_are_lean_checked_or_downstream_covered() {
        for desc in PASS_REGISTRY {
            let coverage = proof_coverage_for(desc.id)
                .unwrap_or_else(|| panic!("missing proof coverage for {:?}", desc.id));
            match desc.tag {
                PassTag::Rewrite | PassTag::Solver | PassTag::Verifier => assert!(
                    coverage.coverage.is_lean_checked(),
                    "{:?} is a semantic-result pass but is only {:?}",
                    desc.id,
                    coverage.coverage
                ),
                PassTag::Analysis => {}
            }
        }
    }

    #[test]
    fn only_non_simplifying_analysis_passes_may_be_unchecked() {
        let unchecked: Vec<_> = PASS_REGISTRY
            .iter()
            .filter_map(|desc| {
                let coverage = proof_coverage_for(desc.id)?;
                (!coverage.coverage.is_lean_checked()).then_some(desc.id)
            })
            .collect();

        assert_eq!(
            unchecked,
            vec![PassId::ClassifyAst],
            "unchecked proof coverage is allowed only for non-simplifying analysis passes"
        );
    }

    #[test]
    fn every_lean_checked_pass_has_named_generated_replay_evidence() {
        let replay_source = include_str!("../tests/generated_lean_replay.rs");
        let mut named_replay_tests = HashSet::new();
        let mut declared = HashSet::new();
        let pseudo: HashSet<_> = PSEUDO_PASS_IDS_WITH_REPLAY_EVIDENCE
            .iter()
            .copied()
            .collect();
        for entry in PASS_REPLAY_EVIDENCE {
            assert!(
                declared.insert(entry.pass),
                "duplicate replay evidence entry for {:?}",
                entry.pass
            );
            if let Some(coverage) = proof_coverage_for(entry.pass) {
                assert!(
                    coverage.coverage.is_lean_checked(),
                    "replay evidence for {:?} is meaningless because coverage is {:?}",
                    entry.pass,
                    coverage.coverage
                );
            } else {
                assert!(
                    pseudo.contains(&entry.pass),
                    "replay evidence for {:?} is neither registered coverage nor explicit pseudo-pass evidence",
                    entry.pass
                );
            }
            assert!(
                !entry.replay_tests.is_empty(),
                "replay evidence for {:?} must name at least one generated replay test",
                entry.pass
            );
            for test in entry.replay_tests {
                assert!(
                    test.ends_with("_replays_in_lean"),
                    "replay evidence {:?} for {:?} must name a generated Lean replay test",
                    test,
                    entry.pass
                );
                named_replay_tests.insert(*test);
                let fn_decl = format!("fn {test}(");
                assert!(
                    replay_source.contains(&fn_decl),
                    "replay evidence {:?} for {:?} does not exist in generated_lean_replay.rs",
                    test,
                    entry.pass
                );
            }
        }
        for entry in INTERNAL_PROOF_COVERAGE {
            for test in entry.replay_tests {
                named_replay_tests.insert(*test);
            }
        }

        let mut previous_nonempty = "";
        for line in replay_source.lines().map(str::trim) {
            if line.starts_with("fn ") && line.contains("_replays_in_lean(") {
                let name = line
                    .strip_prefix("fn ")
                    .and_then(|rest| rest.split_once('(').map(|(name, _)| name))
                    .expect("generated replay function name");
                assert_eq!(
                    previous_nonempty, "#[test]",
                    "generated replay function {name:?} must be a Rust test"
                );
                assert!(
                    named_replay_tests.contains(name),
                    "generated replay test {name:?} is not linked from PASS_REPLAY_EVIDENCE"
                );
            }
            if !line.is_empty() {
                previous_nonempty = line;
            }
        }

        for desc in PASS_REGISTRY {
            let coverage = proof_coverage_for(desc.id)
                .unwrap_or_else(|| panic!("missing proof coverage for {:?}", desc.id));
            if coverage.coverage.is_lean_checked() {
                assert!(
                    replay_evidence_for(desc.id).is_some(),
                    "{:?} is {:?} but has no named generated Lean replay evidence",
                    desc.id,
                    coverage.coverage
                );
            }
        }
    }

    #[test]
    fn internal_transform_targets_have_generated_replay_evidence() {
        let replay_source = include_str!("../tests/generated_lean_replay.rs");
        let mut declared = HashSet::new();

        for entry in INTERNAL_PROOF_COVERAGE {
            assert!(
                declared.insert(entry.target),
                "duplicate internal proof target {:?}",
                entry.target
            );
            assert!(
                !entry.note.is_empty(),
                "internal proof target {:?} needs a note",
                entry.target
            );
            assert!(
                !entry.replay_tests.is_empty(),
                "internal proof target {:?} needs generated replay evidence",
                entry.target
            );
            for test in entry.replay_tests {
                assert!(
                    test.ends_with("_replays_in_lean"),
                    "internal proof evidence {:?} for {:?} must name a generated Lean replay test",
                    test,
                    entry.target
                );
                let fn_decl = format!("fn {test}(");
                assert!(
                    replay_source.contains(&fn_decl),
                    "internal proof evidence {:?} for {:?} does not exist in generated_lean_replay.rs",
                    test,
                    entry.target
                );
            }
        }
    }

    #[test]
    fn internal_transform_targets_cover_distinct_architectural_gaps() {
        let targets: HashSet<_> = INTERNAL_PROOF_COVERAGE
            .iter()
            .map(|entry| entry.target)
            .collect();
        let expected: HashSet<_> = [
            InternalProofTarget::LeanEmitterFallbacks,
            InternalProofTarget::LeanContextFrameMatrix,
            InternalProofTarget::LeanTheoremExports,
            InternalProofTarget::LocalRewriteTheoremMatrix,
            InternalProofTarget::PublicCleanupFamily,
            InternalProofTarget::ProductShadowRepairGuard,
            InternalProofTarget::PatternSubtreeRewrite,
            InternalProofTarget::AtomSimplifierConstantFold,
            InternalProofTarget::SemilinearReconstructionFamily,
            InternalProofTarget::ResidualRecompositionFamily,
            InternalProofTarget::BitwiseRecompositionFamily,
            InternalProofTarget::HybridRecompositionFamily,
            InternalProofTarget::LiftedSubstitution,
            InternalProofTarget::OperandJoinRewrite,
            InternalProofTarget::ProductJoinRewrite,
            InternalProofTarget::DirectExtractorFamilies,
            InternalProofTarget::SignatureSolverFamilies,
            InternalProofTarget::XorLoweringFamily,
            InternalProofTarget::VerifyCandidateEndpoint,
        ]
        .into_iter()
        .collect();

        assert_eq!(
            targets, expected,
            "internal proof target inventory drifted without an explicit coverage decision"
        );
    }
}
