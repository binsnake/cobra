//! Top-level conversion helpers over [`crate::orchestrator::main_loop`].
//! Public seeding is implemented by `crate::passes::entry`; this module owns
//! the seeded-worklist dispatch and conversion into the public outcome type.

use crate::core::expr::Expr;
use crate::core::expr_cost::{compute_cost, is_cost_blowup};
use crate::core::expr_rewrite::{cleanup_final_expr, try_build_var_support};
use crate::core::expr_utils::{collect_vars, remap_var_indices};
use crate::core::pass_contract::{
    PassOutcome, ReasonCategory, ReasonCode, ReasonDomain, VerificationState,
};
use crate::core::result::Result;
use crate::core::simplify_outcome::{
    Diagnostic, ProofLevel, SimplifyOutcome, SimplifyOutcomeKind, SimplifyTelemetry,
};
use std::sync::Arc;

use crate::orchestrator::context::{OrchestratorContext, OrchestratorPolicy};
use crate::orchestrator::main_loop::{run_main_loop, LoopResult};
use crate::orchestrator::registry::PassDescriptor;
use crate::orchestrator::worklist::Worklist;

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
    let require_lean_certificate = ctx.opts.require_lean_certificate;
    Ok(to_simplify_outcome(
        result,
        original_expr,
        ctx.bitwidth,
        &ctx.original_vars,
        require_lean_certificate,
    ))
}

/// `ToSimplifyOutcome`: success runs `cleanup_final_expr` on the expr,
/// failure either echoes the input or leaves `expr = None`.
#[allow(clippy::too_many_lines)]
pub fn to_simplify_outcome(
    mut result: LoopResult,
    original_expr: Option<&Expr>,
    bitwidth: u32,
    original_vars: &[String],
    require_lean_certificate: bool,
) -> SimplifyOutcome {
    let mut outcome = SimplifyOutcome::default();
    let mut cost_rejected = false;

    match result.outcome {
        PassOutcome::Success {
            expr,
            real_vars,
            verification,
            ..
        } => {
            let cleaned = cleanup_final_expr(expr.clone_tree(), bitwidth);
            if let Some(original) = original_expr {
                let existing_proves_cleaned = result
                    .metadata
                    .lean_certificate
                    .as_ref()
                    .is_some_and(|cert| cert.replays_between(bitwidth, original, &cleaned));
                if !existing_proves_cleaned {
                    if let Some(cert) =
                        crate::verify::LeanCertificate::try_single_rewrite_between_64(
                            bitwidth,
                            original.clone_tree(),
                            cleaned.clone_tree(),
                        )
                    {
                        result.metadata.lean_certificate = Some(cert);
                    }
                }
            }
            // Cleanup is a transformation too. Prefer the exact cleaned
            // endpoint when it is certified; otherwise preserve a certified
            // pre-cleanup endpoint rather than detaching proof metadata from
            // the expression it actually proves.
            let cleaned_expr = if original_expr.is_some_and(|original| {
                result
                    .metadata
                    .lean_certificate
                    .as_ref()
                    .is_some_and(|cert| {
                        certificate_matches_public_output(
                            cert,
                            bitwidth,
                            original,
                            &cleaned,
                            &real_vars,
                            original_vars,
                        )
                    })
            }) {
                cleaned
            } else if original_expr.is_some_and(|original| {
                result
                    .metadata
                    .lean_certificate
                    .as_ref()
                    .is_some_and(|cert| {
                        certificate_matches_public_output(
                            cert,
                            bitwidth,
                            original,
                            &expr,
                            &real_vars,
                            original_vars,
                        )
                    })
            }) {
                expr
            } else {
                cleaned
            };
            // Match upstream's observable rejection contract: a candidate's
            // signature remains available even if a later public-output guard
            // rejects the expression.
            outcome.sig_vector = std::mem::take(&mut result.metadata.sig_vector);
            // Defense-in-depth: the public output's variables must be a
            // subset of the original problem's input variables. A surviving
            // lifted/aux var (index >= number of original input vars) means a
            // nested-lift leak (see resolve_lifted_substitute); rather than
            // returning a leaked-var expression, reject this candidate and
            // fall through to the echo-input path with a clear diagnostic.
            let original_var_count = original_vars.len() as u32;
            let mut output_vars = Vec::new();
            collect_vars(&cleaned_expr, &mut output_vars);
            if output_vars.iter().any(|&v| v >= original_var_count) {
                outcome.kind = SimplifyOutcomeKind::UnchangedUnsupported;
                outcome.expr = original_expr.map(|e| Arc::new(e.clone()));
                "rejected: simplified expression references a lifted/aux variable \
                 not present in the original input (nested-lift leak)"
                    .clone_into(&mut outcome.diag.reason);
            } else if reject_cost_blowup(&mut outcome, original_expr, &cleaned_expr) {
                cost_rejected = true;
            } else {
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
                                &outcome.sig_vector,
                                &cleaned_expr,
                            )
                        });
                let has_matching_lean_evidence =
                    has_matching_lean_certificate || has_matching_signature_certificate;
                // Only an explicit opt-in discards a correct rewrite for
                // lacking a certificate. Otherwise a missing proof lowers
                // `verified` / `proof_level` below and the simplification is
                // still returned. Correctness is carried by full-width
                // verification, not by certificate presence.
                let changed_ast_without_proof = require_lean_certificate
                    && original_expr.is_some_and(|original| *cleaned_expr != *original)
                    && !has_matching_lean_certificate;
                if changed_ast_without_proof {
                    outcome.kind = SimplifyOutcomeKind::UnchangedUnsupported;
                    outcome.expr = original_expr.map(Expr::clone_tree);
                    "rejected: final AST rewrite lacks a replayable proof for the exact output"
                        .clone_into(&mut outcome.diag.reason);
                } else {
                    outcome.kind = SimplifyOutcomeKind::Simplified;
                    outcome.expr = Some(cleaned_expr);
                    outcome.real_vars = real_vars;
                    outcome.verified =
                        verification == VerificationState::Verified && has_matching_lean_evidence;
                    outcome.proof_level =
                        proof_level_for_verification(verification, has_matching_lean_evidence);
                }
            }
        }
        other => {
            outcome.kind = SimplifyOutcomeKind::UnchangedUnsupported;
            outcome.expr = original_expr.map(|e| Arc::new(e.clone()));
            // Pull the reason's top-level message into the diagnostic.
            if let PassOutcome::Blocked(reason) | PassOutcome::Inapplicable(reason) = &other {
                outcome.diag.reason.clone_from(&reason.top.message);
            }
        }
    }

    if outcome.kind == SimplifyOutcomeKind::UnchangedUnsupported && original_expr.is_some() {
        outcome.real_vars = original_vars.to_vec();
        outcome.verified = false;
        outcome.proof_level = ProofLevel::Unverified;
    }

    let existing_reason = std::mem::take(&mut outcome.diag.reason);
    outcome.diag = Diagnostic {
        classification: result.run_metadata.input_classification,
        structural_transform_rounds: result.metadata.structural_transform_rounds,
        transform_produced_candidate: result.metadata.transform_produced_candidate,
        candidate_failed_verification: result.metadata.candidate_failed_verification,
        reason: existing_reason,
        reason_code: if cost_rejected {
            Some(ReasonCode {
                category: ReasonCategory::CostRejected,
                domain: ReasonDomain::Orchestrator,
                subcode: 0,
            })
        } else {
            result.metadata.reason_code
        },
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

fn reject_cost_blowup(
    outcome: &mut SimplifyOutcome,
    original_expr: Option<&Expr>,
    candidate: &Expr,
) -> bool {
    let Some(original) = original_expr else {
        return false;
    };
    if !is_cost_blowup(&compute_cost(candidate).cost, &compute_cost(original).cost) {
        return false;
    }

    // A Boolean-signature change of basis can be equivalent while expanding
    // an already-small input into an exponential AND-monomial sum. Reject only
    // candidates that are both >2x the input and >32 weighted nodes.
    outcome.kind = SimplifyOutcomeKind::UnchangedUnsupported;
    outcome.expr = Some(Arc::new(original.clone()));
    outcome.diag.reason =
        "rejected: simplified expression is a pathological size expansion".to_string();
    true
}

fn certificate_matches_public_output(
    cert: &crate::verify::LeanCertificate,
    bitwidth: u32,
    original: &Expr,
    public_expr: &Expr,
    real_vars: &[String],
    original_vars: &[String],
) -> bool {
    let public_candidates = public_output_candidates(public_expr, real_vars, original_vars);
    public_candidates
        .iter()
        .any(|candidate| cert.replays_between(bitwidth, original, candidate))
}

fn public_output_candidates(
    public_expr: &Expr,
    real_vars: &[String],
    original_vars: &[String],
) -> Vec<Arc<Expr>> {
    let mut candidates = vec![public_expr.clone_tree()];
    let Some(idx_map) = try_build_var_support(original_vars, real_vars) else {
        return candidates;
    };
    let mut remapped = public_expr.clone_tree();
    remap_var_indices(Arc::make_mut(&mut remapped), &idx_map);
    if *remapped != *public_expr {
        candidates.push(remapped);
    }
    candidates
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
    use crate::orchestrator::context::{OrchestratorTelemetry, RunMetadata};
    use crate::orchestrator::work_item::ItemMetadata;

    #[test]
    fn pathological_output_growth_is_rejected_globally() {
        let original = Expr::variable(0);
        let mut expanded = Expr::variable(0);
        for _ in 0..20 {
            expanded = Expr::add(expanded, Expr::variable(0));
        }
        assert!(is_cost_blowup(
            &compute_cost(&expanded).cost,
            &compute_cost(&original).cost
        ));

        let result = LoopResult {
            outcome: PassOutcome::success(expanded, vec!["x".into()], VerificationState::Verified),
            metadata: ItemMetadata {
                sig_vector: vec![0, 21],
                ..ItemMetadata::default()
            },
            run_metadata: RunMetadata::default(),
            telemetry: OrchestratorTelemetry::default(),
        };

        let outcome = to_simplify_outcome(result, Some(&original), 64, &["x".into()], true);
        assert_eq!(outcome.kind, SimplifyOutcomeKind::UnchangedUnsupported);
        assert_eq!(outcome.expr, Some(original));
        assert_eq!(outcome.sig_vector, vec![0, 21]);
        assert_eq!(
            outcome.diag.reason_code,
            Some(ReasonCode {
                category: ReasonCategory::CostRejected,
                domain: ReasonDomain::Orchestrator,
                subcode: 0,
            })
        );
    }

    #[test]
    fn lean_certificate_upgrades_public_proof_level() {
        let expr = Expr::variable(0);
        let metadata = ItemMetadata {
            lean_certificate: Some(crate::verify::LeanCertificate::new(
                64,
                expr.clone_tree(),
                expr.clone_tree(),
            )),
            ..ItemMetadata::default()
        };
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

        let outcome = to_simplify_outcome(result, Some(&expr), 64, &["x".into()], true);
        assert_eq!(outcome.proof_level, ProofLevel::LeanCertified);
        assert!(outcome.verified);
    }

    #[test]
    fn mismatched_lean_certificate_does_not_upgrade_public_proof_level() {
        let original = Expr::variable(0);
        let simplified = Expr::variable(1);
        let metadata = ItemMetadata {
            lean_certificate: Some(crate::verify::LeanCertificate::new(
                64,
                original.clone_tree(),
                Expr::constant(0),
            )),
            ..ItemMetadata::default()
        };
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

        // Use a two-variable input space so `Variable(1)` is a legitimate
        // input var (not a lifted/aux leak) — this test exercises
        // certificate-mismatch handling, not the nested-lift leak guard.
        let outcome =
            to_simplify_outcome(result, Some(&original), 64, &["x".into(), "y".into()], true);
        assert_eq!(outcome.kind, SimplifyOutcomeKind::UnchangedUnsupported);
        assert_eq!(outcome.expr, Some(original));
        assert_eq!(outcome.proof_level, ProofLevel::Unverified);
        assert!(!outcome.verified);
    }

    #[test]
    fn cleanup_requires_proof_for_the_exact_public_endpoint() {
        let original = Expr::add(
            Expr::add(Expr::variable(0), Expr::constant(0)),
            Expr::constant(0),
        );
        let precleaned = Expr::add(Expr::variable(0), Expr::constant(0));
        let metadata = ItemMetadata {
            lean_certificate: crate::verify::LeanCertificate::try_single_rewrite_between_64(
                64,
                original.clone_tree(),
                precleaned.clone_tree(),
            ),
            ..ItemMetadata::default()
        };
        let result = LoopResult {
            outcome: PassOutcome::success(
                precleaned.clone_tree(),
                vec!["x".into()],
                VerificationState::Verified,
            ),
            metadata,
            run_metadata: RunMetadata::default(),
            telemetry: OrchestratorTelemetry::default(),
        };

        let outcome = to_simplify_outcome(result, Some(&original), 64, &["x".into()], true);
        assert_eq!(outcome.expr, Some(precleaned));
        assert_eq!(outcome.proof_level, ProofLevel::LeanCertified);
        assert!(outcome.verified);
    }

    #[test]
    fn opting_out_of_the_certificate_gate_returns_the_uncertified_rewrite() {
        let original = Expr::add(Expr::variable(0), Expr::variable(1));
        let rewritten = Expr::mul(Expr::variable(0), Expr::variable(1));
        let result = LoopResult {
            outcome: PassOutcome::success(
                rewritten.clone_tree(),
                vec!["x".into(), "y".into()],
                VerificationState::Verified,
            ),
            metadata: ItemMetadata::default(),
            run_metadata: RunMetadata::default(),
            telemetry: OrchestratorTelemetry::default(),
        };
        let vars = ["x".to_string(), "y".to_string()];

        // Default (strict): no certificate, so the rewrite is discarded.
        let strict = to_simplify_outcome(result.clone(), Some(&original), 64, &vars, true);
        assert_eq!(strict.kind, SimplifyOutcomeKind::UnchangedUnsupported);
        assert_eq!(strict.expr, Some(original.clone_tree()));

        // Opted out: the rewrite is returned, and the absent proof shows up as
        // a lowered proof level rather than as a discarded result.
        let relaxed = to_simplify_outcome(result, Some(&original), 64, &vars, false);
        assert_eq!(relaxed.kind, SimplifyOutcomeKind::Simplified);
        assert_eq!(relaxed.expr, Some(rewritten));
        assert!(!relaxed.verified);
        assert_ne!(relaxed.proof_level, ProofLevel::LeanCertified);
    }

    #[test]
    fn signature_certificate_does_not_upgrade_public_proof_level() {
        let expr = Expr::variable(0);
        let mut metadata = ItemMetadata {
            verification: VerificationState::Verified,
            lean_signature_certificate: crate::verify::LeanSignatureCertificate::new(
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

        let outcome = to_simplify_outcome(result, Some(&expr), 64, &["x".into()], true);
        assert_eq!(outcome.proof_level, ProofLevel::SpotChecked);
        assert!(!outcome.verified);
    }

    #[test]
    fn signature_certificate_upgrades_signature_only_public_proof_level() {
        let expr = Expr::variable(0);
        let mut metadata = ItemMetadata {
            verification: VerificationState::Verified,
            lean_signature_certificate: crate::verify::LeanSignatureCertificate::new(
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

        let outcome = to_simplify_outcome(result, None, 64, &["x".into()], true);
        assert_eq!(outcome.proof_level, ProofLevel::LeanCertified);
        assert!(outcome.verified);
    }
}
