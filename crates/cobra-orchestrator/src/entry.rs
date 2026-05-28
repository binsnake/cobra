//! Top-level convenience entry points over [`crate::main_loop`]. A full
//! public `simplify(sig, vars, input_expr, opts)` that performs its own
//! seeding lands once the classifier and pattern-match passes are
//! ported; until then, `simplify_from_worklist` lets tests and early
//! integration exercise the dispatch end-to-end.

use cobra_core::expr::Expr;
use cobra_core::expr_rewrite::{cleanup_final_expr, try_build_var_support};
use cobra_core::expr_utils::remap_var_indices;
use cobra_core::pass_contract::{PassOutcome, VerificationState};
use cobra_core::result::Result;
use cobra_core::simplify_outcome::{
    Diagnostic, ProofLevel, SimplifyOutcome, SimplifyOutcomeKind, SimplifyTelemetry,
};

use crate::context::{OrchestratorContext, OrchestratorPolicy};
use crate::main_loop::{run_main_loop, LoopResult};
use crate::registry::PassDescriptor;
use crate::worklist::Worklist;

/// Run the main loop against a pre-seeded worklist and convert the
/// result to a public [`SimplifyOutcome`].
///
/// `original_expr`, when supplied, is cloned into the outcome's `expr`
/// `expr` as `None`.
pub fn simplify_from_worklist(
    ctx: &mut OrchestratorContext,
    mut worklist: Worklist,
    mut policy: OrchestratorPolicy,
    registry: &[PassDescriptor],
    original_expr: Option<&Expr>,
) -> Result<SimplifyOutcome> {
    let result = run_main_loop(ctx, &mut worklist, &mut policy, registry, original_expr)?;
    Ok(to_simplify_outcome(
        result,
        original_expr,
        ctx.bitwidth,
        &ctx.original_vars,
    ))
}

/// `ToSimplifyOutcome`: success runs `cleanup_final_expr` on the expr,
/// failure either echoes the input or leaves `expr = None`.
pub fn to_simplify_outcome(
    result: LoopResult,
    original_expr: Option<&Expr>,
    bitwidth: u32,
    original_vars: &[String],
) -> SimplifyOutcome {
    let mut outcome = SimplifyOutcome::default();

    match result.outcome {
        PassOutcome::Success {
            expr,
            real_vars,
            verification,
            ..
        } => {
            outcome.kind = SimplifyOutcomeKind::Simplified;
            let cleaned_expr = cleanup_final_expr(expr, bitwidth);
            let has_matching_lean_certificate = result
                .metadata
                .lean_certificate
                .as_ref()
                .is_some_and(|cert| {
                    original_expr.is_some_and(|original| {
                        certificate_matches_public_output(
                            cert,
                            bitwidth,
                            original,
                            &cleaned_expr,
                            &real_vars,
                            original_vars,
                        )
                    })
                });
            let has_matching_signature_certificate = original_expr.is_none()
                && result
                    .metadata
                    .lean_signature_certificate
                    .as_ref()
                    .is_some_and(|cert| {
                        cert.matches_signature(
                            bitwidth,
                            real_vars.len() as u32,
                            &result.metadata.sig_vector,
                            &cleaned_expr,
                        )
                    });
            let has_matching_lean_evidence =
                has_matching_lean_certificate || has_matching_signature_certificate;
            outcome.expr = Some(cleaned_expr);
            outcome.real_vars = real_vars;
            outcome.verified =
                verification == VerificationState::Verified && has_matching_lean_evidence;
            outcome.proof_level =
                proof_level_for_verification(verification, has_matching_lean_evidence);
            outcome.sig_vector = result.metadata.sig_vector;
        }
        other => {
            outcome.kind = SimplifyOutcomeKind::UnchangedUnsupported;
            outcome.expr = original_expr.map(|e| Box::new(e.clone()));
            // Pull the reason's top-level message into the diagnostic.
            if let PassOutcome::Blocked(reason) | PassOutcome::Inapplicable(reason) = &other {
                outcome.diag.reason.clone_from(&reason.top.message);
            }
        }
    }

    let existing_reason = std::mem::take(&mut outcome.diag.reason);
    outcome.diag = Diagnostic {
        classification: result.run_metadata.input_classification,
        structural_transform_rounds: result.metadata.structural_transform_rounds,
        transform_produced_candidate: result.metadata.transform_produced_candidate,
        candidate_failed_verification: result.metadata.candidate_failed_verification,
        reason: existing_reason,
        reason_code: result.metadata.reason_code,
        cause_chain: result.metadata.cause_chain,
    };

    outcome.telemetry = SimplifyTelemetry {
        total_expansions: result.telemetry.total_expansions,
        max_depth_reached: result.telemetry.max_depth_reached,
        candidates_verified: result.telemetry.candidates_verified,
        queue_high_water: result.telemetry.queue_high_water,
    };

    outcome
}

fn certificate_matches_public_output(
    cert: &cobra_verify::LeanCertificate,
    bitwidth: u32,
    original: &Expr,
    public_expr: &Expr,
    real_vars: &[String],
    original_vars: &[String],
) -> bool {
    let public_candidates = public_output_candidates(public_expr, real_vars, original_vars);
    public_candidates.iter().any(|candidate| {
        cert.matches_endpoints(bitwidth, original, candidate)
            || certificate_matches_cleanup_of_public_output(cert, bitwidth, original, candidate)
    })
}

fn public_output_candidates(
    public_expr: &Expr,
    real_vars: &[String],
    original_vars: &[String],
) -> Vec<Box<Expr>> {
    let mut candidates = vec![public_expr.clone_tree()];
    let Some(idx_map) = try_build_var_support(original_vars, real_vars) else {
        return candidates;
    };
    let mut remapped = public_expr.clone_tree();
    remap_var_indices(&mut remapped, &idx_map);
    if *remapped != *public_expr {
        candidates.push(remapped);
    }
    candidates
}

fn certificate_matches_cleanup_of_public_output(
    cert: &cobra_verify::LeanCertificate,
    bitwidth: u32,
    original: &Expr,
    public_expr: &Expr,
) -> bool {
    if cert.bitwidth != bitwidth || *cert.original != *original {
        return false;
    }
    let cleaned_cert_endpoint = cleanup_final_expr(cert.simplified.clone_tree(), bitwidth);
    *cleaned_cert_endpoint == *public_expr
}

fn proof_level_for_verification(
    verification: VerificationState,
    has_lean_certificate: bool,
) -> ProofLevel {
    match (verification, has_lean_certificate) {
        (VerificationState::Verified, true) => ProofLevel::LeanCertified,
        (VerificationState::Unverified | VerificationState::Rejected, _) => ProofLevel::Unverified,
        (VerificationState::Verified, false) => ProofLevel::SpotChecked,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::{OrchestratorTelemetry, RunMetadata};
    use crate::work_item::ItemMetadata;

    #[test]
    fn lean_certificate_upgrades_public_proof_level() {
        let expr = Expr::variable(0);
        let mut metadata = ItemMetadata::default();
        metadata.lean_certificate = Some(cobra_verify::LeanCertificate::new(
            64,
            expr.clone_tree(),
            expr.clone_tree(),
        ));
        let result = LoopResult {
            outcome: PassOutcome::success(
                expr.clone_tree(),
                vec!["x".into()],
                VerificationState::Verified,
            ),
            metadata,
            run_metadata: RunMetadata::default(),
            telemetry: OrchestratorTelemetry::default(),
        };

        let outcome = to_simplify_outcome(result, Some(&expr), 64, &["x".into()]);
        assert_eq!(outcome.proof_level, ProofLevel::LeanCertified);
        assert!(outcome.verified);
    }

    #[test]
    fn mismatched_lean_certificate_does_not_upgrade_public_proof_level() {
        let original = Expr::variable(0);
        let simplified = Expr::variable(1);
        let mut metadata = ItemMetadata::default();
        metadata.lean_certificate = Some(cobra_verify::LeanCertificate::new(
            64,
            original.clone_tree(),
            Expr::constant(0),
        ));
        let result = LoopResult {
            outcome: PassOutcome::success(
                simplified,
                vec!["x".into(), "y".into()],
                VerificationState::Verified,
            ),
            metadata,
            run_metadata: RunMetadata::default(),
            telemetry: OrchestratorTelemetry::default(),
        };

        let outcome = to_simplify_outcome(result, Some(&original), 64, &["x".into()]);
        assert_eq!(outcome.proof_level, ProofLevel::SpotChecked);
        assert!(!outcome.verified);
    }

    #[test]
    fn cleanup_of_certified_endpoint_preserves_public_proof_level() {
        let original = Expr::add(
            Expr::add(Expr::variable(0), Expr::constant(0)),
            Expr::constant(0),
        );
        let precleaned = Expr::add(Expr::variable(0), Expr::constant(0));
        let mut metadata = ItemMetadata::default();
        metadata.lean_certificate = Some(cobra_verify::LeanCertificate::new(
            64,
            original.clone_tree(),
            precleaned.clone_tree(),
        ));
        let result = LoopResult {
            outcome: PassOutcome::success(
                precleaned,
                vec!["x".into()],
                VerificationState::Verified,
            ),
            metadata,
            run_metadata: RunMetadata::default(),
            telemetry: OrchestratorTelemetry::default(),
        };

        let outcome = to_simplify_outcome(result, Some(&original), 64, &["x".into()]);
        assert_eq!(outcome.expr, Some(Expr::variable(0)));
        assert_eq!(outcome.proof_level, ProofLevel::LeanCertified);
        assert!(outcome.verified);
    }

    #[test]
    fn signature_certificate_does_not_upgrade_public_proof_level() {
        let expr = Expr::variable(0);
        let mut metadata = ItemMetadata {
            verification: VerificationState::Verified,
            lean_signature_certificate: cobra_verify::LeanSignatureCertificate::new(
                64,
                1,
                vec![0, 1],
                expr.clone_tree(),
            ),
            ..ItemMetadata::default()
        };
        metadata.sig_vector = vec![0, 1];
        let result = LoopResult {
            outcome: PassOutcome::success(
                expr.clone_tree(),
                vec!["x".into()],
                VerificationState::Verified,
            ),
            metadata,
            run_metadata: RunMetadata::default(),
            telemetry: OrchestratorTelemetry::default(),
        };

        let outcome = to_simplify_outcome(result, Some(&expr), 64, &["x".into()]);
        assert_eq!(outcome.proof_level, ProofLevel::SpotChecked);
        assert!(!outcome.verified);
    }

    #[test]
    fn signature_certificate_upgrades_signature_only_public_proof_level() {
        let expr = Expr::variable(0);
        let mut metadata = ItemMetadata {
            verification: VerificationState::Verified,
            lean_signature_certificate: cobra_verify::LeanSignatureCertificate::new(
                64,
                1,
                vec![0, 1],
                expr.clone_tree(),
            ),
            ..ItemMetadata::default()
        };
        metadata.sig_vector = vec![0, 1];
        let result = LoopResult {
            outcome: PassOutcome::success(
                expr.clone_tree(),
                vec!["x".into()],
                VerificationState::Verified,
            ),
            metadata,
            run_metadata: RunMetadata::default(),
            telemetry: OrchestratorTelemetry::default(),
        };

        let outcome = to_simplify_outcome(result, None, 64, &["x".into()]);
        assert_eq!(outcome.proof_level, ProofLevel::LeanCertified);
        assert!(outcome.verified);
    }
}
