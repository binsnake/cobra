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
    /// The pass crosses into an internal state representation and clears
    /// endpoint/signature certificates that no longer describe the payload.
    ClearsStaleProofMetadata,
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
        coverage: LeanProofCoverage::ClearsStaleProofMetadata,
        note: "signature-state seed no longer carries endpoint proof metadata",
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
        coverage: LeanProofCoverage::ClearsStaleProofMetadata,
        note: "coefficient-model state clears stale endpoint/signature proof metadata",
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
        coverage: LeanProofCoverage::EndpointCertificate,
        note: "direct product-collapse rewrites emit endpoint certificates; child subproblems clear stale metadata until resolved",
    },
    PassProofCoverage {
        pass: PassId::AtomIdentityRewrite,
        coverage: LeanProofCoverage::EndpointCertificate,
        note: "atom identity rewrites chain local endpoint certificates when theorem-supported",
    },
    PassProofCoverage {
        pass: PassId::XorLowering,
        coverage: LeanProofCoverage::EndpointCertificate,
        note: "xor-lowered AST replacements emit endpoint certificates",
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

#[must_use]
pub fn proof_coverage_for(pass: PassId) -> Option<&'static PassProofCoverage> {
    PASS_PROOF_COVERAGE.iter().find(|entry| entry.pass == pass)
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use cobra_orchestrator::PassTag;

    use super::*;
    use crate::PASS_REGISTRY;

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
            vec![
                PassId::ClassifyAst,
                PassId::BuildSignatureState,
                PassId::PrepareCoeffModel
            ],
            "unchecked proof coverage is allowed only for non-simplifying analysis passes"
        );
    }
}
