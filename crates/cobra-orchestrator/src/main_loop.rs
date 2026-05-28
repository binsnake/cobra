//! Orchestrator main loop: Rust port of the
//! `while (!worklist.empty() && expansions < policy.max_expansions)` body of
//! `Simplify`.
//!
//! Seeding (building the initial worklist from a signature or AST) is
//! intentionally *not* in this file — it depends on the classifier,
//! pattern matcher, and aux-var eliminator passes, none of which have
//! been ported yet. This module accepts a pre-seeded worklist and
//! runs it to either a verified candidate or an exhausted-worklist
//! result.

use cobra_core::expr::Expr;
use cobra_core::expr_cost::{compute_cost, is_better, ExprCost};
use cobra_core::expr_rewrite::try_build_var_support;
use cobra_core::expr_utils::remap_var_indices;
use cobra_core::pass_contract::{
    PassOutcome, ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame,
    VerificationState,
};
use cobra_core::result::Result;
use cobra_core::spot_check::full_width_check_eval;

use crate::attempt_cache::PassAttemptCache;
use crate::competition::{
    endpoint_certificate_matches_candidate_signature, release_handle, submit_candidate,
    CandidateRecord,
};
use crate::context::{OrchestratorContext, OrchestratorPolicy, OrchestratorTelemetry, RunMetadata};
use crate::enums::{ItemDisposition, PassDecision, PassId};
use crate::ranker::unsupported_rank_better;
use crate::registry::{build_pass_index, PassDescriptor};
use crate::scheduler::select_next_pass;
use crate::state::StateData;
use crate::work_item::{
    ItemMetadata, PassResult, TransformTerminalSignal, UnsupportedCandidate, WorkItem,
};
use crate::worklist::Worklist;

/// Result of one invocation of [`run_main_loop`]: either the outcome
/// emitted by a pass (typically `Success`) or a `Blocked` reason
/// describing why the worklist exhausted.
#[derive(Clone, Debug)]
pub struct LoopResult {
    pub outcome: PassOutcome,
    pub metadata: ItemMetadata,
    pub run_metadata: RunMetadata,
    pub telemetry: OrchestratorTelemetry,
}

/// Cheapest `FoldedAst` rewrite observed during the run that carries a
/// `ProductIdentityCollapse` step in its history. Used by the
/// exhaustion-path fallback to promote a verified cost-improving rewrite
/// to a final `Candidate` when the worklist drains without producing
/// one through the normal pipeline.
#[derive(Clone, Debug)]
struct BestRewrite {
    /// Expression already remapped to the original variable space when a
    /// `solve_ctx` sub-problem produced it.
    expr: Box<Expr>,
    cost: ExprCost,
    /// Real vars in original space (`ctx.original_vars` when present).
    real_vars: Vec<String>,
    /// Existing theorem-backed certificate for this rewrite, when the
    /// producing pass attached one.
    lean_certificate: Option<cobra_verify::LeanCertificate>,
}

/// Core dispatch loop. Mutates `ctx`, `worklist`, and `policy` in place;
/// returns a `LoopResult` summarising the run.
///
/// `policy.max_expansions` is mutable because the lifting passes bump
#[allow(clippy::too_many_lines)] // one-to-one port of the C++ main loop
pub fn run_main_loop(
    ctx: &mut OrchestratorContext,
    worklist: &mut Worklist,
    policy: &mut OrchestratorPolicy,
    registry: &[PassDescriptor],
    original_expr: Option<&Expr>,
) -> Result<LoopResult> {
    let mut cache = PassAttemptCache::new();
    let mut telemetry = OrchestratorTelemetry::default();
    let mut expansions: u32 = 0;
    let mut verifications: u32 = 0;
    let mut best_unsupported: Option<UnsupportedCandidate> = None;
    let mut strongest_transform_terminal: Option<TransformTerminalSignal> = None;
    // Tracker for the cheapest PIC-rewritten FoldedAst seen. On
    // exhaustion, used to promote a cost-improving, full-width-verified
    // rewrite instead of returning UnchangedUnsupported.
    let mut best_rewrite: Option<BestRewrite> = None;
    let original_cost: Option<ExprCost> = original_expr.map(|e| compute_cost(e).cost);

    let pass_index = build_pass_index(registry);

    while !worklist.is_empty() && expansions < policy.max_expansions {
        let mut item = worklist.pop().expect("non-empty worklist");
        expansions = expansions.saturating_add(1);
        telemetry.total_expansions = expansions;
        if item.depth > telemetry.max_depth_reached {
            telemetry.max_depth_reached = item.depth;
        }

        // Update best_unsupported tracking — we may promote this item's
        // snapshot now and refresh later if its metadata mutates.
        let mut current_was_best_snapshot = false;
        let current_snapshot = make_unsupported_candidate(&item);
        if best_unsupported
            .as_ref()
            .is_none_or(|b| unsupported_rank_better(&current_snapshot, b))
        {
            best_unsupported = Some(current_snapshot);
            current_was_best_snapshot = true;
        }

        // Promote any lineage-local structural-transform terminal to
        // the loop-level strongest-so-far tracker.
        if let Some(sig) = item.metadata.structural_transform_terminal {
            let keep = match strongest_transform_terminal {
                None => true,
                Some(prev) => terminal_rank(sig.category) > terminal_rank(prev.category),
            };
            if keep {
                strongest_transform_terminal = Some(sig);
            }
        }

        // Track cheapest PIC-rewritten FoldedAst for exhaustion-path
        // promotion. Only considers items strictly cheaper than the
        // current best; `is_better` is the lexicographic comparator
        // used across the rest of the pipeline.
        if original_cost.is_some() && item_is_pic_rewrite_candidate(&item) {
            maybe_update_best_rewrite(&mut best_rewrite, &item, ctx);
        }

        // Candidate acceptance: verified (needs_original_space_verification
        // = false) candidates either return immediately (top-level) or
        // submit into their owning competition group.
        if let StateData::Candidate(cand) = &item.payload {
            if !cand.needs_original_space_verification {
                let normalized_expr = cand.expr.clone_tree();
                let normalized_cost = compute_cost(&normalized_expr).cost;
                // Stamp `transform_produced_candidate` if any rewrite pass
                // is in the candidate's lineage.
                if item.history.iter().any(|h| {
                    matches!(
                        h,
                        PassId::OperandSimplify
                            | PassId::ProductIdentityCollapse
                            | PassId::XorLowering,
                    )
                }) {
                    item.metadata.transform_produced_candidate = true;
                }

                if let Some(gid) = item.group_id {
                    let verification = proof_backed_group_verification(
                        item.metadata.verification,
                        ctx.bitwidth,
                        &normalized_expr,
                        &cand.real_vars,
                        &item.metadata.sig_vector,
                        item.metadata.lean_certificate.as_ref(),
                        item.metadata.lean_signature_certificate.as_ref(),
                    );
                    submit_candidate(
                        &mut ctx.competition_groups,
                        gid,
                        CandidateRecord {
                            expr: normalized_expr,
                            cost: normalized_cost,
                            verification,
                            real_vars: cand.real_vars.clone(),
                            source_pass: cand.producing_pass,
                            needs_original_space_verification: false,
                            sig_vector: item.metadata.sig_vector.clone(),
                            lean_certificate: item.metadata.lean_certificate.clone(),
                            lean_signature_certificate: item
                                .metadata
                                .lean_signature_certificate
                                .clone(),
                        },
                        ctx.bitwidth,
                    );
                    if let Some(resolved) = release_handle(&mut ctx.competition_groups, gid) {
                        worklist.push(resolved);
                    }
                    continue;
                }

                telemetry.queue_high_water = worklist.high_water_mark() as u32;
                return Ok(LoopResult {
                    outcome: PassOutcome::success(
                        normalized_expr,
                        cand.real_vars.clone(),
                        item.metadata.verification,
                    ),
                    metadata: item.metadata,
                    run_metadata: ctx.run_metadata.clone(),
                    telemetry,
                });
            }
        }

        // Scheduler: pick a pass.
        let pass_id = select_next_pass(&item, policy, verifications, &cache);
        let Some(pass_id) = pass_id else {
            // No eligible pass — release the group handle if we own one.
            if let Some(gid) = item.group_id {
                if let Some(resolved) = release_handle(&mut ctx.competition_groups, gid) {
                    worklist.push(resolved);
                }
            }
            continue;
        };

        // Pre-attempt bookkeeping.
        let fp = item.fingerprint(ctx.bitwidth).into_owned();
        item.attempted_mask |= 1u64 << pass_id.as_u8();

        let Some(desc) = pass_index[pass_id.as_u8() as usize] else {
            continue;
        };
        telemetry.passes_attempted.push(pass_id);

        let pr = (desc.run)(&item, ctx)?;
        if std::env::var_os("COBRA_TRACE_PASSES").is_some() {
            eprintln!(
                "[trace] pass={:?} decision={:?} state_after={:?} reason={:?}",
                pass_id,
                pr.decision,
                pr.next.first().map(|w| w.payload.kind()),
                pr.reason.top.message,
            );
        }
        if pass_id == PassId::VerifyCandidate {
            verifications = verifications.saturating_add(1);
            telemetry.candidates_verified = verifications;
        }
        cache.record(fp, pass_id);

        handle_pass_result(
            item,
            pass_id,
            pr,
            worklist,
            ctx,
            policy,
            &mut best_unsupported,
            current_was_best_snapshot,
        );
    }

    telemetry.queue_high_water = worklist.high_water_mark() as u32;

    // Exhaustion-path fallback: if a PIC rewrite is strictly cheaper
    // than the input and passes a full-width spot check against the
    // original, promote it to a verified candidate instead of returning
    // UnchangedUnsupported. Narrowly scoped to PIC-in-history to keep
    // the regression surface small; extend once validated.
    if let (Some(best), Some(orig_cost), Some(orig_expr)) =
        (best_rewrite.as_ref(), original_cost, original_expr)
    {
        if let Some(promoted) =
            try_promote_best_rewrite(best, orig_cost, orig_expr, ctx, telemetry.clone())
        {
            return Ok(promoted);
        }
    }

    Ok(build_exhaustion_result(
        best_unsupported,
        strongest_transform_terminal,
        ctx,
        telemetry,
    ))
}

// ---------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------

fn make_unsupported_candidate(work: &WorkItem) -> UnsupportedCandidate {
    UnsupportedCandidate {
        metadata: work.metadata.clone(),
        depth: work.depth,
        rewrite_gen: work.rewrite_gen,
        history_size: work.history.len() as u32,
        last_pass: work.history.last().copied(),
        is_candidate_state: matches!(work.payload, StateData::Candidate(_)),
    }
}

fn terminal_rank(c: ReasonCategory) -> u8 {
    match c {
        ReasonCategory::VerifyFailed => 2,
        ReasonCategory::RepresentationGap => 1,
        _ => 0,
    }
}

/// Eligibility gate for the exhaustion-path "best rewrite" tracker. A
/// work item qualifies iff its payload is a `FoldedAst`, it has been
/// through at least one structural rewrite (`rewrite_gen > 0`), and its
/// history records a tracked source: `ProductIdentityCollapse` (direct
/// structural collapse), `PatternSubtreeRewrite` (seed-time fold that
/// couldn't be recovered downstream), or `AtomIdentityRewrite` (atom-
/// level bitwise identity rewrite). `OperandSimplify` and `XorLowering`
/// are deliberately excluded — their rewrites feed other stages that
/// are expected to produce their own Candidate.
fn item_is_pic_rewrite_candidate(item: &WorkItem) -> bool {
    matches!(item.payload, StateData::FoldedAst(_))
        && item.rewrite_gen > 0
        && item.history.iter().any(|p| {
            matches!(
                p,
                PassId::ProductIdentityCollapse
                    | PassId::PatternSubtreeRewrite
                    | PassId::AtomIdentityRewrite
            )
        })
}

/// Update the best-rewrite tracker with this `FoldedAst` item if it
/// beats the running best under `is_better`. Handles var-space
/// remapping when the AST came from a `solve_ctx` sub-problem.
fn maybe_update_best_rewrite(
    best: &mut Option<BestRewrite>,
    item: &WorkItem,
    ctx: &OrchestratorContext,
) {
    let StateData::FoldedAst(ast) = &item.payload else {
        return;
    };
    let raw_cost = compute_cost(&ast.expr).cost;
    if let Some(current) = best.as_ref() {
        if !is_better(&raw_cost, &current.cost) {
            return;
        }
    }

    // Remap into the original var space when a sub-problem produced
    // this AST. If the mapping can't be built, skip — we can't verify
    // against the original evaluator in a foreign namespace.
    let (expr, real_vars) = if let Some(sc) = ast.solve_ctx.as_ref() {
        if sc.vars == ctx.original_vars {
            (ast.expr.clone_tree(), ctx.original_vars.clone())
        } else {
            let Some(idx_map) = try_build_var_support(&ctx.original_vars, &sc.vars) else {
                return;
            };
            let mut remapped = ast.expr.clone_tree();
            remap_var_indices(&mut remapped, &idx_map);
            (remapped, ctx.original_vars.clone())
        }
    } else {
        (ast.expr.clone_tree(), ctx.original_vars.clone())
    };

    let cost = compute_cost(&expr).cost;
    if let Some(current) = best.as_ref() {
        if !is_better(&cost, &current.cost) {
            return;
        }
    }

    *best = Some(BestRewrite {
        expr,
        cost,
        real_vars,
        lean_certificate: item.metadata.lean_certificate.clone(),
    });
}

/// Try to turn a tracked best rewrite into a verified
/// `PassOutcome::Success`. Requires `ctx.evaluator` to be populated (so
/// we can check against the original at full width) and the rewrite's
/// cost to be strictly better than the input's. A 256-sample full-width
/// check is only a candidate filter; the promoted result is marked
/// verified only when a matching Lean certificate can be carried or
/// generated. Returns `None` when the check fails or the evaluator is
/// unavailable; caller then falls back to `build_exhaustion_result`.
fn try_promote_best_rewrite(
    best: &BestRewrite,
    original_cost: ExprCost,
    original_expr: &Expr,
    ctx: &OrchestratorContext,
    telemetry: OrchestratorTelemetry,
) -> Option<LoopResult> {
    if !is_better(&best.cost, &original_cost) {
        return None;
    }
    let eval = ctx.evaluator.as_ref()?;
    let num_vars = ctx.original_vars.len() as u32;
    let check = full_width_check_eval(eval, num_vars, &best.expr, ctx.bitwidth, 256);
    if !check.passed {
        return None;
    }
    // downstream callers do — cheap because both expressions are small
    // at this point.
    let lean_certificate = best
        .lean_certificate
        .as_ref()
        .filter(|cert| {
            cert.bitwidth == ctx.bitwidth
                && *cert.original == *original_expr
                && *cert.simplified == *best.expr
        })
        .cloned()
        .or_else(|| {
            cobra_verify::LeanCertificate::try_single_rewrite_between_64(
                ctx.bitwidth,
                original_expr.clone_tree(),
                best.expr.clone_tree(),
            )
        });

    let verification = if lean_certificate.is_some() {
        VerificationState::Verified
    } else {
        VerificationState::Unverified
    };

    let final_meta = ItemMetadata {
        verification,
        transform_produced_candidate: true,
        lean_certificate,
        reason_code: Some(ReasonCode {
            category: ReasonCategory::BestRewritePromoted,
            domain: ReasonDomain::StructuralTransform,
            subcode: 0,
        }),
        ..ItemMetadata::default()
    };

    Some(LoopResult {
        outcome: PassOutcome::success(best.expr.clone_tree(), best.real_vars.clone(), verification),
        metadata: final_meta,
        run_metadata: ctx.run_metadata.clone(),
        telemetry,
    })
}

/// Handle a pass result: push children, retain/consume the current
/// item, accumulate failure reasons, and release group handles when
/// the item is consumed with an outstanding group handle.
#[allow(clippy::too_many_arguments)]
fn handle_pass_result(
    mut item: WorkItem,
    pass_id: PassId,
    pr: PassResult,
    worklist: &mut Worklist,
    ctx: &mut OrchestratorContext,
    policy: &mut OrchestratorPolicy,
    best_unsupported: &mut Option<UnsupportedCandidate>,
    current_was_best_snapshot: bool,
) {
    match pr.decision {
        PassDecision::Advance | PassDecision::SolvedCandidate => {
            // Lifting passes get a 50% budget bump when they produce a
            // skeleton — gives the compact outer problem breathing room.
            if matches!(
                pass_id,
                PassId::LiftRepeatedSubexpressions | PassId::LiftArithmeticAtoms,
            ) && !pr.next.is_empty()
            {
                policy.max_expansions = policy
                    .max_expansions
                    .saturating_add(policy.max_expansions / 2);
            }
            for mut next in pr.next {
                next.depth = item.depth.saturating_add(1);
                next.history.push(pass_id);
                worklist.push(next);
            }
            if pr.disposition == ItemDisposition::RetainCurrent {
                item.depth = item.depth.saturating_add(2);
                worklist.push(item);
            }
        }
        _ => {
            // Blocked / NoProgress / NotApplicable.
            if !pr.reason.top.message.is_empty() {
                item.metadata.last_failure = pr.reason.clone();
            }
            if let Some(gid) = item.group_id {
                if !pr.reason.top.message.is_empty() {
                    if let Some(g) = ctx.competition_groups.get_mut(&gid) {
                        g.technique_failures.push(pr.reason.clone());
                    }
                }
            }
            // XorLowering terminal attribution.
            if pass_id == PassId::XorLowering {
                let cat = pr.reason.top.code.category;
                item.metadata.structural_transform_terminal = Some(TransformTerminalSignal {
                    source_pass: pass_id,
                    category: cat,
                });
                match cat {
                    ReasonCategory::RepresentationGap => {
                        item.metadata.transform_produced_candidate = true;
                    }
                    ReasonCategory::VerifyFailed => {
                        item.metadata.transform_produced_candidate = true;
                        item.metadata.candidate_failed_verification = true;
                    }
                    _ => {}
                }
            }
            // Verify failure after XorLowering in the lineage.
            if pass_id == PassId::VerifyCandidate
                && pr.reason.top.code.category == ReasonCategory::VerifyFailed
                && item.history.contains(&PassId::XorLowering)
            {
                item.metadata.structural_transform_terminal = Some(TransformTerminalSignal {
                    source_pass: PassId::XorLowering,
                    category: ReasonCategory::VerifyFailed,
                });
                item.metadata.transform_produced_candidate = true;
                item.metadata.candidate_failed_verification = true;
            }
            // Decomposition-family cause chain accumulation.
            if pass_id.is_decomposition_family() {
                item.metadata
                    .decomposition_causes
                    .push(pr.reason.top.clone());
                for c in &pr.reason.causes {
                    item.metadata.decomposition_causes.push(c.clone());
                }
            }
            // Populate reason_code for consumed semilinear passes.
            if is_semilinear_pass(pass_id) && pr.reason.top.code.category != ReasonCategory::None {
                item.metadata.reason_code = Some(pr.reason.top.code);
            }

            // Refresh best_unsupported since metadata may have mutated.
            let refreshed = make_unsupported_candidate(&item);
            if current_was_best_snapshot
                || best_unsupported
                    .as_ref()
                    .is_none_or(|b| unsupported_rank_better(&refreshed, b))
            {
                *best_unsupported = Some(refreshed);
            }

            // Retain on NotApplicable OR when the pass asks for it;
            // otherwise consume and release the group handle.
            if pr.disposition == ItemDisposition::RetainCurrent
                || pr.decision == PassDecision::NotApplicable
            {
                worklist.push(item);
            } else if let Some(gid) = item.group_id {
                if let Some(resolved) = release_handle(&mut ctx.competition_groups, gid) {
                    worklist.push(resolved);
                }
            }
        }
    }
}

fn is_semilinear_pass(id: PassId) -> bool {
    matches!(
        id,
        PassId::SemilinearNormalize
            | PassId::SemilinearCheck
            | PassId::SemilinearRewrite
            | PassId::SemilinearReconstruct,
    )
}

fn proof_backed_group_verification(
    verification: VerificationState,
    bitwidth: u32,
    expr: &Expr,
    real_vars: &[String],
    sig_vector: &[u64],
    lean_certificate: Option<&cobra_verify::LeanCertificate>,
    lean_signature_certificate: Option<&cobra_verify::LeanSignatureCertificate>,
) -> VerificationState {
    if verification != VerificationState::Verified {
        return verification;
    }

    let endpoint_ok = lean_certificate.is_some_and(|cert| {
        endpoint_certificate_matches_candidate_signature(
            cert, bitwidth, expr, real_vars, sig_vector,
        )
    });
    let signature_ok = lean_signature_certificate.is_some_and(|cert| {
        cert.matches_signature(bitwidth, real_vars.len() as u32, sig_vector, expr)
    });

    if endpoint_ok || signature_ok {
        VerificationState::Verified
    } else {
        VerificationState::Unverified
    }
}

/// Build the `LoopResult` returned when the worklist exhausts without
/// from the exhaustion comment to the final `ToSimplifyOutcome` call.
fn build_exhaustion_result(
    best_unsupported: Option<UnsupportedCandidate>,
    strongest_transform_terminal: Option<TransformTerminalSignal>,
    ctx: &OrchestratorContext,
    telemetry: OrchestratorTelemetry,
) -> LoopResult {
    let exhaustion_reason = match best_unsupported.as_ref() {
        Some(b) if !b.metadata.last_failure.top.message.is_empty() => {
            b.metadata.last_failure.clone()
        }
        _ => ReasonDetail {
            top: ReasonFrame {
                code: ReasonCode {
                    category: ReasonCategory::SearchExhausted,
                    domain: cobra_core::pass_contract::ReasonDomain::Orchestrator,
                    subcode: 0,
                },
                message: "Worklist exhausted".to_string(),
                fields: Vec::new(),
            },
            causes: Vec::new(),
        },
    };

    let mut final_meta = best_unsupported.map(|b| b.metadata).unwrap_or_default();

    // Derive structural-transform terminal reason code from
    let used_folded_ast_exploration =
        cobra_core::classification::is_folded_ast_exploration_candidate(
            ctx.run_metadata.input_classification.flags,
        ) || final_meta.structural_transform_rounds > 0
            || final_meta.transform_produced_candidate
            || strongest_transform_terminal.is_some();

    if used_folded_ast_exploration && final_meta.reason_code.is_none() {
        if let Some(sig) = strongest_transform_terminal {
            let cat = sig.category;
            final_meta.reason_code = Some(ReasonCode {
                category: cat,
                domain: cobra_core::pass_contract::ReasonDomain::StructuralTransform,
                subcode: 0,
            });
            match cat {
                ReasonCategory::VerifyFailed => {
                    final_meta.candidate_failed_verification = true;
                    final_meta.transform_produced_candidate = true;
                }
                ReasonCategory::RepresentationGap => {
                    final_meta.transform_produced_candidate = true;
                }
                _ => {}
            }
        }
    }

    // Propagate reason_code from the last failure if not already set.
    if final_meta.reason_code.is_none()
        && exhaustion_reason.top.code.category != ReasonCategory::None
    {
        final_meta.reason_code = Some(exhaustion_reason.top.code);
    }

    // Propagate accumulated decomposition cause chain.
    if final_meta.cause_chain.is_empty() && !final_meta.decomposition_causes.is_empty() {
        final_meta.cause_chain = std::mem::take(&mut final_meta.decomposition_causes);
    }

    // Non-exploration inputs: propagate semilinear failure as the cause.
    if final_meta.cause_chain.is_empty()
        && !cobra_core::classification::is_folded_ast_exploration_candidate(
            ctx.run_metadata.input_classification.flags,
        )
        && ctx.run_metadata.semilinear_failure.is_some()
    {
        let sf = ctx.run_metadata.semilinear_failure.as_ref().unwrap();
        final_meta.cause_chain.push(sf.top.clone());
        for c in &sf.causes {
            final_meta.cause_chain.push(c.clone());
        }
    }

    // Fallback: inherit causes from the exhaustion reason itself.
    if final_meta.cause_chain.is_empty() && !exhaustion_reason.causes.is_empty() {
        final_meta.cause_chain.clone_from(&exhaustion_reason.causes);
    }

    // `verification` must remain `Unverified` on the exhaustion path so
    // that `to_simplify_outcome` reports `verified = false` regardless
    // of any stale metadata left by earlier passes.
    final_meta.verification = VerificationState::Unverified;

    LoopResult {
        outcome: PassOutcome::blocked(exhaustion_reason),
        metadata: final_meta,
        run_metadata: ctx.run_metadata.clone(),
        telemetry,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_verify::LeanCertificate;

    #[test]
    fn proof_backed_group_verification_rejects_endpoint_with_wrong_source_signature() {
        let expr = Expr::variable(0);
        let cert = LeanCertificate::new(64, expr.clone_tree(), expr.clone_tree());
        let vars = vec!["x".to_owned()];

        let verification = proof_backed_group_verification(
            VerificationState::Verified,
            64,
            &expr,
            &vars,
            &[1, 0],
            Some(&cert),
            None,
        );

        assert_eq!(verification, VerificationState::Unverified);
    }

    #[test]
    fn proof_backed_group_verification_accepts_endpoint_with_matching_source_signature() {
        let expr = Expr::variable(0);
        let cert = LeanCertificate::new(64, expr.clone_tree(), expr.clone_tree());
        let vars = vec!["x".to_owned()];

        let verification = proof_backed_group_verification(
            VerificationState::Verified,
            64,
            &expr,
            &vars,
            &[0, 1],
            Some(&cert),
            None,
        );

        assert_eq!(verification, VerificationState::Verified);
    }
}
