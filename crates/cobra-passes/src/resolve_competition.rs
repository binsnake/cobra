//! `ResolveCompetition` — fires when a `CompetitionResolved` work item
//! reaches the scheduler. Per-continuation dispatch routes the winning
//! candidate (or accumulates failure reasons) into:
//!
//! - `None`: emit the winner straight through as a `Candidate`.
//! - `BitwiseCompose` / `HybridCompose`: stitch the recovered child
//!   expression back into the gate template that spawned it, then
//!   submit it to the parent group and release that group's handle.
//! - `OperandRewrite` / `ProductCollapse`: record the side that just
//!   resolved on the shared `JoinState`. Operand joins emit rewritten
//!   ASTs; product joins emit verified signature candidates because the
//!   recomposition is a Boolean-signature equivalence, not generally a
//!   full bit-vector endpoint identity.
//! - `RemainderRecombine`: verify and combine `prefix + solved` (or
//!   just `solved` for direct boolean-null residuals), submit to the
//!   parent group.
//! - `LiftedSubstitute`: substitute the lifted bindings back into the
//!   outer winner and emit a verified candidate in the original space.
//!
//! Group erasure happens unconditionally at the end so the registry
//! does not accumulate dead entries.

#![allow(
    clippy::similar_names,
    clippy::clone_on_copy,
    clippy::items_after_statements,
    clippy::too_many_lines
)]

use cobra_core::evaluate_boolean_signature;
use cobra_core::expr::Expr;
use cobra_core::expr_cost::{compute_cost, is_better, ExprCost};
use cobra_core::expr_utils::remap_var_indices;
use cobra_core::pass_contract::{
    DecompositionMeta, ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame,
    VerificationState,
};
use cobra_core::result::Result;

use cobra_orchestrator::{
    project_extractor_kind, release_handle, replace_by_hash, AstPayload, BitwiseComposeCont,
    CandidatePayload, CandidateRecord, CompetitionGroup, ContinuationData, FactorRole,
    HybridComposeCont, ItemDisposition, JoinState, LiftedBinding, LiftedSubstituteCont,
    OperandJoinState, OperandRewriteCont, OrchestratorContext, PassDecision, PassId, PassResult,
    ProductCollapseCont, ProductJoinState, Provenance, RemainderRecombineCont, ResidualSolverKind,
    StateData, WorkItem,
};

use crate::bitwise_decomposer::{compose, remap_vars};
use crate::candidate_normalize::{
    signature_certificate_for_candidate, submit_normalized_candidate,
};
use crate::classifier::classify_structural;
use crate::hybrid_decomposer::compose_extraction;
use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};

fn ast_reason(category: ReasonCategory, msg: &'static str) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category,
                domain: ReasonDomain::Orchestrator,
                subcode: 0,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

fn aggregate_failure(group: &CompetitionGroup, fallback: &'static str) -> ReasonDetail {
    if group.technique_failures.is_empty() {
        return ast_reason(ReasonCategory::SearchExhausted, fallback);
    }
    let mut reason = group.technique_failures[0].clone();
    for f in &group.technique_failures[1..] {
        reason.causes.push(f.top.clone());
    }
    reason
}

#[allow(clippy::unnecessary_wraps)]
pub fn run_resolve_competition(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::CompetitionResolved(resolved) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let group_id = resolved.group_id;
    let group = match ctx.competition_groups.get(&group_id) {
        Some(g) => g.clone(),
        None => {
            return Ok(PassResult {
                decision: PassDecision::Advance,
                disposition: ItemDisposition::ConsumeCurrent,
                next: Vec::new(),
                reason: ReasonDetail::default(),
            });
        }
    };

    let cont = group.continuation.clone().unwrap_or(ContinuationData::None);

    let result = match cont {
        ContinuationData::None => resolve_none(&group, item, ctx),
        ContinuationData::BitwiseCompose(c) => resolve_bitwise_compose(&c, &group, ctx),
        ContinuationData::HybridCompose(c) => resolve_hybrid_compose(&c, &group, ctx),
        ContinuationData::OperandRewrite(c) => resolve_operand_rewrite(c, &group, item, ctx),
        ContinuationData::ProductCollapse(c) => resolve_product_collapse(c, &group, item, ctx),
        ContinuationData::RemainderRecombine(c) => {
            resolve_residual_recombine(&c, &group, item, ctx)
        }
        ContinuationData::LiftedSubstitute(c) => resolve_lifted_substitute(&c, &group, item, ctx),
    };

    ctx.competition_groups.remove(&group_id);
    Ok(result)
}

#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::CompetitionResolved(_))
}

// ---------------------------------------------------------------
// None — pass the winner through as a Candidate.
// ---------------------------------------------------------------

fn resolve_none(
    group: &CompetitionGroup,
    item: &WorkItem,
    ctx: &OrchestratorContext,
) -> PassResult {
    if let Some(winner) = group.best.as_ref() {
        let mut cand_item = WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
            expr: winner.expr.clone_tree(),
            real_vars: winner.real_vars.clone(),
            cost: winner.cost,
            producing_pass: winner.source_pass,
            needs_original_space_verification: winner.needs_original_space_verification,
        })));
        cand_item.features = item.features.clone();
        cand_item.metadata = item.metadata.clone();
        cand_item.metadata.sig_vector.clone_from(&winner.sig_vector);
        cand_item.metadata.lean_certificate = winner
            .lean_certificate
            .as_ref()
            .filter(|cert| cert.bitwidth == ctx.bitwidth && *cert.simplified == *winner.expr)
            .cloned();
        cand_item.metadata.lean_signature_certificate = winner
            .lean_signature_certificate
            .as_ref()
            .filter(|cert| {
                cert.matches_signature(
                    ctx.bitwidth,
                    winner.real_vars.len() as u32,
                    &winner.sig_vector,
                    &winner.expr,
                )
            })
            .cloned();
        cand_item.metadata.verification = if winner.verification == VerificationState::Verified
            && (cand_item.metadata.lean_certificate.is_some()
                || cand_item.metadata.lean_signature_certificate.is_some())
        {
            VerificationState::Verified
        } else {
            VerificationState::Unverified
        };
        cand_item.depth = item.depth;
        cand_item.rewrite_gen = item.rewrite_gen;
        cand_item.attempted_mask = item.attempted_mask;
        cand_item.history.clone_from(&item.history);

        return PassResult {
            decision: PassDecision::SolvedCandidate,
            disposition: ItemDisposition::ConsumeCurrent,
            next: vec![cand_item],
            reason: ReasonDetail::default(),
        };
    }

    PassResult {
        decision: PassDecision::Blocked,
        disposition: ItemDisposition::ConsumeCurrent,
        next: Vec::new(),
        reason: aggregate_failure(group, "Competition group resolved with no winner"),
    }
}

// ---------------------------------------------------------------
// BitwiseCompose / HybridCompose — submit composed expr to parent.
// ---------------------------------------------------------------

fn submit_and_release_parent(
    parent_group_id: u32,
    record: CandidateRecord,
    ctx: &mut OrchestratorContext,
) -> Vec<WorkItem> {
    submit_normalized_candidate(
        &mut ctx.competition_groups,
        parent_group_id,
        record,
        ctx.bitwidth,
    );
    let mut next = Vec::new();
    if let Some(resolved) = release_handle(&mut ctx.competition_groups, parent_group_id) {
        next.push(resolved);
    }
    next
}

fn resolve_bitwise_compose(
    cont: &BitwiseComposeCont,
    group: &CompetitionGroup,
    ctx: &mut OrchestratorContext,
) -> PassResult {
    let mut next = Vec::new();
    if let Some(winner) = group.best.as_ref() {
        let remapped = remap_vars(&winner.expr, &cont.active_context_indices);
        let composed = compose(cont.gate, cont.var_k, remapped, cont.add_coeff);

        let fw_ok = if let Some(eval) = cont.parent_eval.as_ref() {
            full_width_check_eval(
                eval,
                cont.parent_num_vars,
                &composed,
                ctx.bitwidth,
                DEFAULT_NUM_SAMPLES,
            )
            .passed
        } else {
            true
        };

        if fw_ok {
            let cost = compute_cost(&composed).cost;
            let verification = if cont.parent_eval.is_some() {
                VerificationState::Verified
            } else {
                VerificationState::Unverified
            };
            let lean_signature_certificate = signature_certificate_for_candidate(
                ctx.bitwidth,
                &cont.parent_signature,
                &cont.parent_real_vars,
                &composed,
            );
            let record = CandidateRecord {
                expr: composed,
                cost,
                verification,
                real_vars: cont.parent_real_vars.clone(),
                source_pass: PassId::SignatureBitwiseDecompose,
                needs_original_space_verification: cont.parent_needs_original_space_verification,
                sig_vector: cont.parent_signature.clone(),
                lean_certificate: None,
                lean_signature_certificate,
            };
            next = submit_and_release_parent(cont.parent_group_id, record, ctx);
        } else if let Some(resolved) =
            release_handle(&mut ctx.competition_groups, cont.parent_group_id)
        {
            next.push(resolved);
        }
    } else if let Some(resolved) = release_handle(&mut ctx.competition_groups, cont.parent_group_id)
    {
        next.push(resolved);
    }

    PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::ConsumeCurrent,
        next,
        reason: ReasonDetail::default(),
    }
}

fn resolve_hybrid_compose(
    cont: &HybridComposeCont,
    group: &CompetitionGroup,
    ctx: &mut OrchestratorContext,
) -> PassResult {
    let mut next = Vec::new();
    if let Some(winner) = group.best.as_ref() {
        let composed = compose_extraction(cont.op, cont.var_k, winner.expr.clone_tree());

        let fw_ok = if let Some(eval) = cont.parent_eval.as_ref() {
            full_width_check_eval(
                eval,
                cont.parent_num_vars,
                &composed,
                ctx.bitwidth,
                DEFAULT_NUM_SAMPLES,
            )
            .passed
        } else {
            true
        };

        if fw_ok {
            let cost = compute_cost(&composed).cost;
            let verification = if cont.parent_eval.is_some() {
                VerificationState::Verified
            } else {
                VerificationState::Unverified
            };
            let lean_signature_certificate = signature_certificate_for_candidate(
                ctx.bitwidth,
                &cont.parent_signature,
                &cont.parent_real_vars,
                &composed,
            );
            let record = CandidateRecord {
                expr: composed,
                cost,
                verification,
                real_vars: cont.parent_real_vars.clone(),
                source_pass: PassId::SignatureHybridDecompose,
                needs_original_space_verification: cont.parent_needs_original_space_verification,
                sig_vector: cont.parent_signature.clone(),
                lean_certificate: None,
                lean_signature_certificate,
            };
            next = submit_and_release_parent(cont.parent_group_id, record, ctx);
        } else if let Some(resolved) =
            release_handle(&mut ctx.competition_groups, cont.parent_group_id)
        {
            next.push(resolved);
        }
    } else if let Some(resolved) = release_handle(&mut ctx.competition_groups, cont.parent_group_id)
    {
        next.push(resolved);
    }

    PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::ConsumeCurrent,
        next,
        reason: ReasonDetail::default(),
    }
}

// ---------------------------------------------------------------
// OperandRewrite / ProductCollapse — join machinery.
// ---------------------------------------------------------------

fn record_winner(group: &CompetitionGroup) -> Option<CandidateRecord> {
    group.best.as_ref().map(|w| CandidateRecord {
        expr: w.expr.clone_tree(),
        cost: w.cost,
        verification: w.verification,
        real_vars: w.real_vars.clone(),
        source_pass: w.source_pass,
        needs_original_space_verification: w.needs_original_space_verification,
        sig_vector: w.sig_vector.clone(),
        lean_certificate: w.lean_certificate.clone(),
        lean_signature_certificate: w.lean_signature_certificate.clone(),
    })
}

fn emit_join_rewrite_operand(
    join: &OperandJoinState,
    item: &WorkItem,
    replacement: Box<Expr>,
) -> WorkItem {
    let mut repl = Some(replacement);
    let (rebuilt, _) = replace_by_hash(join.full_ast.clone_tree(), join.target_hash, &mut repl);
    let new_cls = classify_structural(&rebuilt);
    let solve_ctx = if join.has_solve_ctx {
        Some(cobra_orchestrator::AstSolveContext {
            vars: join.solve_ctx_vars.clone(),
            evaluator: join.solve_ctx_evaluator.clone(),
            input_sig: join.solve_ctx_input_sig.clone(),
        })
    } else {
        None
    };
    let lean_certificate = cobra_orchestrator::LeanCertificate::try_single_rewrite_between_64(
        join.bitwidth,
        join.full_ast.clone_tree(),
        rebuilt.clone_tree(),
    )
    .or_else(|| {
        Some(cobra_orchestrator::LeanCertificate::new(
            join.bitwidth,
            join.full_ast.clone_tree(),
            rebuilt.clone_tree(),
        ))
    });
    let mut rewritten = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
        expr: rebuilt,
        classification: Some(new_cls.clone()),
        provenance: Provenance::Rewritten,
        solve_ctx,
    })));
    rewritten.features = item.features.clone();
    rewritten.features.classification = Some(new_cls);
    rewritten.features.provenance = Provenance::Rewritten;
    rewritten.metadata = item.metadata.clone();
    rewritten.metadata.lean_certificate = lean_certificate;
    rewritten.metadata.lean_signature_certificate = None;
    rewritten.depth = join.parent_depth;
    rewritten.rewrite_gen = join.rewrite_gen + 1;
    rewritten.attempted_mask = 0;
    rewritten.group_id = join.parent_group_id;
    rewritten.history.clone_from(&join.parent_history);
    rewritten
}

fn emit_join_candidate_product(
    join: &ProductJoinState,
    item: &WorkItem,
    replacement: Box<Expr>,
    source_pass: PassId,
) -> Option<WorkItem> {
    let mut repl = Some(replacement);
    let (rebuilt, _) = replace_by_hash(join.full_ast.clone_tree(), join.target_hash, &mut repl);
    let active_vars = if join.has_solve_ctx {
        join.solve_ctx_vars.clone()
    } else {
        join.vars.clone()
    };
    let source_sig = if join.has_solve_ctx && !join.solve_ctx_input_sig.is_empty() {
        join.solve_ctx_input_sig.clone()
    } else {
        evaluate_boolean_signature(&join.full_ast, active_vars.len() as u32, join.bitwidth)
    };
    let cost = compute_cost(&rebuilt).cost;
    let lean_signature_certificate =
        signature_certificate_for_candidate(join.bitwidth, &source_sig, &active_vars, &rebuilt)?;

    let mut cand_item = WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
        expr: rebuilt,
        real_vars: active_vars,
        cost,
        producing_pass: source_pass,
        needs_original_space_verification: false,
    })));
    cand_item.features = item.features.clone();
    cand_item.metadata = item.metadata.clone();
    cand_item.metadata.verification = VerificationState::Verified;
    cand_item.metadata.sig_vector = source_sig;
    cand_item.metadata.lean_certificate = None;
    cand_item.metadata.lean_signature_certificate = Some(lean_signature_certificate);
    cand_item.depth = join.parent_depth;
    cand_item.rewrite_gen = join.rewrite_gen + 1;
    cand_item.attempted_mask = 0;
    cand_item.group_id = join.parent_group_id;
    cand_item.history.clone_from(&join.parent_history);
    Some(cand_item)
}

fn resolve_operand_rewrite(
    cont: OperandRewriteCont,
    group: &CompetitionGroup,
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> PassResult {
    let mut pr = PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::ConsumeCurrent,
        next: Vec::new(),
        reason: ReasonDetail::default(),
    };

    let Some(JoinState::Operand(join_box)) = ctx.join_states.get(&cont.join_id).cloned() else {
        return pr;
    };
    let mut join = *join_box;

    use cobra_orchestrator::OperandRole;
    match cont.role {
        OperandRole::Lhs => {
            join.lhs_resolved = true;
            join.lhs_winner = record_winner(group);
        }
        OperandRole::Rhs => {
            join.rhs_resolved = true;
            join.rhs_winner = record_winner(group);
        }
    }

    if !join.lhs_resolved || !join.rhs_resolved {
        ctx.join_states
            .insert(cont.join_id, JoinState::Operand(Box::new(join)));
        return pr;
    }

    // Both sides closed. Build up to three candidate `Mul`s and keep
    // the cheapest verified one.
    let baseline = join.baseline_cost;
    let bw = join.bitwidth;
    let num_vars = join.vars.len() as u32;

    let mut best: Option<(Box<Expr>, ExprCost)> = None;
    let try_cand = |lhs: Box<Expr>, rhs: Box<Expr>, best: &mut Option<(Box<Expr>, ExprCost)>| {
        let mul = Expr::mul(lhs, rhs);
        let c = compute_cost(&mul).cost;
        if !is_better(&c, &baseline) {
            return;
        }
        if let Some((_, bc)) = best {
            if !is_better(&c, bc) {
                return;
            }
        }
        let chk_eval = cobra_core::evaluator::Evaluator::from_expr(&join.original_mul, bw);
        let chk = full_width_check_eval(&chk_eval, num_vars, &mul, bw, DEFAULT_NUM_SAMPLES);
        if !chk.passed {
            return;
        }
        *best = Some((mul, c));
    };

    if let Some(lhs_w) = &join.lhs_winner {
        try_cand(
            lhs_w.expr.clone_tree(),
            join.original_mul.children[1].clone_tree(),
            &mut best,
        );
    }
    if let Some(rhs_w) = &join.rhs_winner {
        try_cand(
            join.original_mul.children[0].clone_tree(),
            rhs_w.expr.clone_tree(),
            &mut best,
        );
    }
    if let (Some(lhs_w), Some(rhs_w)) = (&join.lhs_winner, &join.rhs_winner) {
        try_cand(lhs_w.expr.clone_tree(), rhs_w.expr.clone_tree(), &mut best);
    }

    let parent_group_id = join.parent_group_id;
    if let Some((expr, _)) = best {
        pr.next.push(emit_join_rewrite_operand(&join, item, expr));
    } else if let Some(parent_gid) = parent_group_id {
        if let Some(resolved) = release_handle(&mut ctx.competition_groups, parent_gid) {
            pr.next.push(resolved);
        }
    }

    ctx.join_states.remove(&cont.join_id);
    pr
}

fn resolve_product_collapse(
    cont: ProductCollapseCont,
    group: &CompetitionGroup,
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> PassResult {
    let mut pr = PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::ConsumeCurrent,
        next: Vec::new(),
        reason: ReasonDetail::default(),
    };

    let Some(JoinState::Product(join_box)) = ctx.join_states.get(&cont.join_id).cloned() else {
        return pr;
    };
    let mut join = *join_box;

    match cont.role {
        FactorRole::X => {
            join.x_resolved = true;
            join.x_winner = record_winner(group);
        }
        FactorRole::Y => {
            join.y_resolved = true;
            join.y_winner = record_winner(group);
        }
    }

    if !join.x_resolved || !join.y_resolved {
        ctx.join_states
            .insert(cont.join_id, JoinState::Product(Box::new(join)));
        return pr;
    }

    if let (Some(x_w), Some(y_w)) = (&join.x_winner, &join.y_winner) {
        let candidate = Expr::mul(x_w.expr.clone_tree(), y_w.expr.clone_tree());
        let bw = join.bitwidth;
        let num_vars = join.vars.len() as u32;
        let chk_eval = cobra_core::evaluator::Evaluator::from_expr(&join.original_expr, bw);
        let chk = full_width_check_eval(&chk_eval, num_vars, &candidate, bw, DEFAULT_NUM_SAMPLES);
        if chk.passed {
            let cost = compute_cost(&candidate).cost;
            if is_better(&cost, &join.baseline_cost) {
                if let Some(candidate) =
                    emit_join_candidate_product(&join, item, candidate, x_w.source_pass)
                {
                    pr.decision = PassDecision::SolvedCandidate;
                    pr.next.push(candidate);
                }
            }
        }
    }

    ctx.join_states.remove(&cont.join_id);
    pr
}

// ---------------------------------------------------------------
// RemainderRecombine — verify and stitch residual + prefix.
// ---------------------------------------------------------------

#[allow(clippy::too_many_lines)]
fn resolve_residual_recombine(
    cont: &RemainderRecombineCont,
    group: &CompetitionGroup,
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> PassResult {
    let mut pr = PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::ConsumeCurrent,
        next: Vec::new(),
        reason: ReasonDetail::default(),
    };

    let release_parent = |pr: &mut PassResult, ctx: &mut OrchestratorContext| {
        if let Some(pid) = cont.parent_group_id {
            if let Some(resolved) = release_handle(&mut ctx.competition_groups, pid) {
                pr.next.push(resolved);
            }
        }
    };

    let Some(winner) = group.best.as_ref() else {
        release_parent(&mut pr, ctx);
        return pr;
    };

    if ctx.evaluator.is_none() && cont.target_vars.is_empty() {
        release_parent(&mut pr, ctx);
        return pr;
    }

    let target_vars: Vec<String> = if cont.target_vars.is_empty() {
        ctx.original_vars.clone()
    } else {
        cont.target_vars.clone()
    };
    let target_eval = if cont.target_vars.is_empty() {
        ctx.evaluator.as_ref().expect("guarded above").clone()
    } else {
        cont.target_eval.clone()
    };

    let mut solved = winner.expr.clone_tree();
    if !cont.remainder_support.is_empty() && winner.real_vars.len() < target_vars.len() {
        remap_var_indices(&mut solved, &cont.remainder_support);
    }

    let num_vars = target_vars.len() as u32;
    let res_check =
        full_width_check_eval(&cont.remainder_eval, num_vars, &solved, ctx.bitwidth, 64);
    if !res_check.passed {
        release_parent(&mut pr, ctx);
        return pr;
    }

    let combined = if cont.prefix_expr.children.is_empty()
        && matches!(cont.prefix_expr.kind, cobra_core::expr::Kind::Constant(0))
    {
        solved
    } else {
        Expr::add(cont.prefix_expr.clone_tree(), solved)
    };

    let orig_check = full_width_check_eval(
        &target_eval,
        num_vars,
        &combined,
        ctx.bitwidth,
        DEFAULT_NUM_SAMPLES,
    );
    if !orig_check.passed {
        release_parent(&mut pr, ctx);
        return pr;
    }

    let cost = compute_cost(&combined).cost;
    let Some(recombined_signature_certificate) = signature_certificate_for_candidate(
        ctx.bitwidth,
        &cont.source_sig,
        &target_vars,
        &combined,
    ) else {
        release_parent(&mut pr, ctx);
        return pr;
    };

    if let Some(parent_gid) = cont.parent_group_id {
        let record = CandidateRecord {
            expr: combined,
            cost,
            verification: VerificationState::Verified,
            real_vars: target_vars.clone(),
            source_pass: PassId::ResidualSupported,
            needs_original_space_verification: false,
            sig_vector: cont.source_sig.clone(),
            lean_certificate: None,
            lean_signature_certificate: Some(recombined_signature_certificate),
        };
        submit_normalized_candidate(
            &mut ctx.competition_groups,
            parent_gid,
            record,
            ctx.bitwidth,
        );
        release_parent(&mut pr, ctx);
    } else {
        let mut cand_item = WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
            expr: combined,
            real_vars: target_vars,
            cost,
            producing_pass: PassId::ResidualSupported,
            needs_original_space_verification: false,
        })));
        cand_item.features = item.features.clone();
        cand_item.metadata = item.metadata.clone();
        cand_item.metadata.verification = VerificationState::Verified;
        cand_item.metadata.sig_vector.clone_from(&cont.source_sig);
        cand_item.metadata.lean_certificate = None;
        cand_item.metadata.lean_signature_certificate = Some(recombined_signature_certificate);
        cand_item.metadata.decomposition_meta = Some(DecompositionMeta {
            extractor_kind: project_extractor_kind(cont.origin) as u8,
            solver_kind: ResidualSolverKind::SupportedPipeline as u8,
            has_solver: true,
            core_degree: cont.prefix_degree,
        });
        cand_item.depth = item.depth;
        cand_item.rewrite_gen = item.rewrite_gen;
        cand_item.attempted_mask = item.attempted_mask;
        cand_item.history.clone_from(&item.history);

        pr.decision = PassDecision::SolvedCandidate;
        pr.next.push(cand_item);
    }

    pr
}

// ---------------------------------------------------------------
// LiftedSubstitute — substitute virtual-var bindings.
// ---------------------------------------------------------------

fn substitute_bindings(
    expr: &Expr,
    bindings: &[LiftedBinding],
    original_var_count: u32,
) -> Box<Expr> {
    if let cobra_core::expr::Kind::Variable(vi) = expr.kind {
        if vi >= original_var_count {
            for b in bindings {
                if b.outer_var_index == vi {
                    return b.subtree.clone_tree();
                }
            }
            return Expr::variable(vi);
        }
    }
    let mut result = expr.clone_tree();
    for child in &mut result.children {
        let new_child = substitute_bindings(child, bindings, original_var_count);
        **child = *new_child;
    }
    result
}

fn resolve_lifted_substitute(
    cont: &LiftedSubstituteCont,
    group: &CompetitionGroup,
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> PassResult {
    let Some(winner) = group.best.as_ref() else {
        return PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: aggregate_failure(group, "Lifted substitute: no winner in group"),
        };
    };

    // Step 1: remap reduced outer space → full outer space.
    let mut remapped = winner.expr.clone_tree();
    if winner.real_vars.len() < cont.outer_vars.len() {
        let remap =
            cobra_core::expr_rewrite::build_var_support(&cont.outer_vars, &winner.real_vars);
        remap_var_indices(&mut remapped, &remap);
    }

    // Step 2: substitute lifted bindings.
    let substituted = substitute_bindings(&remapped, &cont.bindings, cont.original_var_count);

    let Some(eval) = cont.original_eval.as_ref() else {
        return PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ast_reason(
                ReasonCategory::GuardFailed,
                "Lifted substitute requires original evaluator for full-width verification",
            ),
        };
    };

    let num_vars = cont.original_vars.len() as u32;
    let chk = full_width_check_eval(
        eval,
        num_vars,
        &substituted,
        ctx.bitwidth,
        DEFAULT_NUM_SAMPLES,
    );
    if !chk.passed {
        return PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ast_reason(
                ReasonCategory::VerifyFailed,
                "Lifted substitute failed full-width verification",
            ),
        };
    }

    let cost = compute_cost(&substituted).cost;
    let substituted_signature_certificate = signature_certificate_for_candidate(
        ctx.bitwidth,
        &cont.source_sig,
        &cont.original_vars,
        &substituted,
    );
    let Some(substituted_signature_certificate) = substituted_signature_certificate else {
        return PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ast_reason(
                ReasonCategory::VerifyFailed,
                "Lifted substitute has no matching Lean signature certificate",
            ),
        };
    };
    let mut cand_item = WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
        expr: substituted,
        real_vars: cont.original_vars.clone(),
        cost,
        producing_pass: winner.source_pass,
        needs_original_space_verification: false,
    })));
    cand_item.features = item.features.clone();
    cand_item.metadata = item.metadata.clone();
    cand_item.metadata.verification = VerificationState::Verified;
    cand_item.metadata.sig_vector.clone_from(&cont.source_sig);
    cand_item.metadata.lean_certificate = None;
    cand_item.metadata.lean_signature_certificate = Some(substituted_signature_certificate);
    cand_item.depth = item.depth;
    cand_item.rewrite_gen = item.rewrite_gen;
    cand_item.attempted_mask = item.attempted_mask;
    cand_item.history.clone_from(&item.history);

    PassResult {
        decision: PassDecision::SolvedCandidate,
        disposition: ItemDisposition::ConsumeCurrent,
        next: vec![cand_item],
        reason: ReasonDetail::default(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluator::Evaluator;
    use cobra_core::pass_contract::VerificationState;
    use cobra_core::simplify_outcome::Options;
    use cobra_orchestrator::{
        create_group, CandidateRecord, CompetitionResolvedPayload, ContinuationData,
    };

    fn mk_resolve_item(group_id: u32) -> WorkItem {
        WorkItem::new(StateData::CompetitionResolved(CompetitionResolvedPayload {
            group_id,
        }))
    }

    #[test]
    fn none_continuation_emits_winner_as_candidate() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        let gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        ctx.competition_groups.get_mut(&gid).unwrap().best = Some(CandidateRecord {
            expr: Expr::variable(0),
            cost: cobra_core::expr_cost::compute_cost(&Expr::variable(0)).cost,
            verification: VerificationState::Verified,
            real_vars: vec!["x".into()],
            source_pass: PassId::SignaturePatternMatch,
            needs_original_space_verification: false,
            sig_vector: vec![0, 1],
            lean_certificate: None,
            lean_signature_certificate: None,
        });

        let item = mk_resolve_item(gid);
        let pr = run_resolve_competition(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::SolvedCandidate);
        assert_eq!(pr.next.len(), 1);
        assert!(matches!(pr.next[0].payload, StateData::Candidate(_)));
        // Group erased.
        assert!(!ctx.competition_groups.contains_key(&gid));
    }

    #[test]
    fn none_continuation_keeps_only_matching_winner_certificates() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        let gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        ctx.competition_groups.get_mut(&gid).unwrap().best = Some(CandidateRecord {
            expr: Expr::variable(0),
            cost: cobra_core::expr_cost::compute_cost(&Expr::variable(0)).cost,
            verification: VerificationState::Verified,
            real_vars: vec!["x".into()],
            source_pass: PassId::SignaturePatternMatch,
            needs_original_space_verification: false,
            sig_vector: vec![0, 1],
            lean_certificate: Some(cobra_orchestrator::LeanCertificate::new(
                64,
                Expr::add(Expr::variable(0), Expr::constant(0)),
                Expr::variable(0),
            )),
            lean_signature_certificate: cobra_orchestrator::LeanSignatureCertificate::new(
                64,
                1,
                vec![0, 1],
                Expr::variable(0),
            ),
        });

        let pr = run_resolve_competition(&mk_resolve_item(gid), &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::SolvedCandidate);
        assert!(pr.next[0].metadata.lean_certificate.is_some());
        assert!(pr.next[0].metadata.lean_signature_certificate.is_some());
    }

    #[test]
    fn none_continuation_drops_stale_winner_certificates() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        let gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        ctx.competition_groups.get_mut(&gid).unwrap().best = Some(CandidateRecord {
            expr: Expr::variable(0),
            cost: cobra_core::expr_cost::compute_cost(&Expr::variable(0)).cost,
            verification: VerificationState::Verified,
            real_vars: vec!["x".into()],
            source_pass: PassId::SignaturePatternMatch,
            needs_original_space_verification: false,
            sig_vector: vec![0, 1],
            lean_certificate: Some(cobra_orchestrator::LeanCertificate::new(
                64,
                Expr::variable(0),
                Expr::constant(0),
            )),
            lean_signature_certificate: cobra_orchestrator::LeanSignatureCertificate::new(
                64,
                1,
                vec![1, 0],
                Expr::variable(0),
            ),
        });

        let pr = run_resolve_competition(&mk_resolve_item(gid), &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::SolvedCandidate);
        assert!(pr.next[0].metadata.lean_certificate.is_none());
        assert!(pr.next[0].metadata.lean_signature_certificate.is_none());
        assert_eq!(
            pr.next[0].metadata.verification,
            VerificationState::Unverified
        );
    }

    #[test]
    fn none_continuation_with_no_winner_blocks() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        let gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        let item = mk_resolve_item(gid);
        let pr = run_resolve_competition(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Blocked);
        assert!(pr.next.is_empty());
    }

    #[test]
    fn missing_group_is_noop_advance() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
        let item = mk_resolve_item(999);
        let pr = run_resolve_competition(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
    }

    #[test]
    fn bitwise_compose_replaces_child_endpoint_certificate_with_parent_signature_certificate() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let parent_gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        let child_gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);

        {
            let child = ctx.competition_groups.get_mut(&child_gid).unwrap();
            child.best = Some(CandidateRecord {
                expr: Expr::variable(0),
                cost: cobra_core::expr_cost::compute_cost(&Expr::variable(0)).cost,
                verification: VerificationState::Verified,
                real_vars: vec!["y".into()],
                source_pass: PassId::SignaturePatternMatch,
                needs_original_space_verification: false,
                sig_vector: vec![0, 1],
                lean_certificate: Some(cobra_orchestrator::LeanCertificate::new(
                    64,
                    Expr::variable(0),
                    Expr::variable(0),
                )),
                lean_signature_certificate: None,
            });
            child.continuation = Some(ContinuationData::BitwiseCompose(Box::new(
                BitwiseComposeCont {
                    var_k: 0,
                    gate: cobra_orchestrator::GateKind::Xor,
                    add_coeff: 0,
                    active_context_indices: vec![1],
                    parent_group_id: parent_gid,
                    parent_eval: Some(Evaluator::from_expr(
                        &Expr::xor(Expr::variable(0), Expr::variable(1)),
                        64,
                    )),
                    parent_signature: vec![0, 1, 1, 0],
                    parent_real_vars: vec!["x".into(), "y".into()],
                    parent_original_indices: vec![0, 1],
                    parent_num_vars: 2,
                    parent_needs_original_space_verification: false,
                },
            )));
        }

        let pr = run_resolve_competition(&mk_resolve_item(child_gid), &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        let best = ctx.competition_groups[&parent_gid]
            .best
            .as_ref()
            .expect("parent candidate submitted");
        assert!(best.lean_certificate.is_none());
        let cert = best
            .lean_signature_certificate
            .as_ref()
            .expect("parent signature certificate");
        assert!(cert.matches_signature(64, 2, &[0, 1, 1, 0], &best.expr));
    }

    #[test]
    fn hybrid_compose_replaces_child_endpoint_certificate_with_parent_signature_certificate() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let parent_gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        let child_gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);

        {
            let child = ctx.competition_groups.get_mut(&child_gid).unwrap();
            child.best = Some(CandidateRecord {
                expr: Expr::variable(1),
                cost: cobra_core::expr_cost::compute_cost(&Expr::variable(1)).cost,
                verification: VerificationState::Verified,
                real_vars: vec!["x".into(), "y".into()],
                source_pass: PassId::SignaturePatternMatch,
                needs_original_space_verification: false,
                sig_vector: vec![0, 0, 1, 1],
                lean_certificate: Some(cobra_orchestrator::LeanCertificate::new(
                    64,
                    Expr::variable(1),
                    Expr::variable(1),
                )),
                lean_signature_certificate: None,
            });
            child.continuation = Some(ContinuationData::HybridCompose(Box::new(
                HybridComposeCont {
                    var_k: 0,
                    op: cobra_orchestrator::ExtractOp::Xor,
                    parent_group_id: parent_gid,
                    parent_eval: Some(Evaluator::from_expr(
                        &Expr::xor(Expr::variable(0), Expr::variable(1)),
                        64,
                    )),
                    parent_signature: vec![0, 1, 1, 0],
                    parent_real_vars: vec!["x".into(), "y".into()],
                    parent_original_indices: vec![0, 1],
                    parent_num_vars: 2,
                    parent_needs_original_space_verification: false,
                },
            )));
        }

        let pr = run_resolve_competition(&mk_resolve_item(child_gid), &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        let best = ctx.competition_groups[&parent_gid]
            .best
            .as_ref()
            .expect("parent candidate submitted");
        assert!(best.lean_certificate.is_none());
        let cert = best
            .lean_signature_certificate
            .as_ref()
            .expect("parent signature certificate");
        assert!(cert.matches_signature(64, 2, &[0, 1, 1, 0], &best.expr));
    }

    #[test]
    fn operand_join_rewrite_replaces_stale_metadata_with_endpoint_certificate() {
        let full_ast = Expr::mul(Expr::variable(0), Expr::variable(1));
        let join = OperandJoinState {
            lhs_winner: None,
            rhs_winner: None,
            lhs_resolved: true,
            rhs_resolved: true,
            full_ast: full_ast.clone_tree(),
            original_mul: full_ast.clone_tree(),
            target_hash: cobra_orchestrator::expr_identity_hash(&full_ast),
            baseline_cost: cobra_core::expr_cost::compute_cost(&full_ast).cost,
            vars: vec!["x".into(), "y".into()],
            parent_group_id: None,
            has_solve_ctx: false,
            solve_ctx_vars: Vec::new(),
            solve_ctx_evaluator: None,
            solve_ctx_input_sig: Vec::new(),
            bitwidth: 64,
            parent_depth: 0,
            rewrite_gen: 0,
            parent_history: Vec::new(),
        };
        let mut item = mk_resolve_item(0);
        item.metadata.lean_certificate = Some(cobra_orchestrator::LeanCertificate::new(
            64,
            Expr::variable(0),
            Expr::variable(0),
        ));
        item.metadata.lean_signature_certificate =
            cobra_orchestrator::LeanSignatureCertificate::new(64, 1, vec![0, 1], Expr::variable(0));

        let rewritten = emit_join_rewrite_operand(
            &join,
            &item,
            Expr::mul(Expr::variable(0), Expr::variable(1)),
        );
        let cert = rewritten
            .metadata
            .lean_certificate
            .as_ref()
            .expect("endpoint certificate");
        if let StateData::FoldedAst(rewritten_ast) = &rewritten.payload {
            assert!(cert.matches_endpoints(64, &full_ast, &rewritten_ast.expr));
        } else {
            panic!("expected folded AST");
        }
        assert!(rewritten.metadata.lean_signature_certificate.is_none());
    }

    #[test]
    fn product_join_rewrite_replaces_stale_metadata_with_signature_certificate() {
        let full_ast = Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::mul(Expr::variable(0), Expr::variable(2)),
        );
        let join = ProductJoinState {
            x_winner: None,
            y_winner: None,
            x_resolved: true,
            y_resolved: true,
            original_expr: full_ast.clone_tree(),
            baseline_cost: cobra_core::expr_cost::compute_cost(&full_ast).cost,
            vars: vec!["x".into(), "y".into(), "z".into()],
            parent_group_id: None,
            has_solve_ctx: false,
            solve_ctx_vars: Vec::new(),
            solve_ctx_evaluator: None,
            solve_ctx_input_sig: Vec::new(),
            bitwidth: 64,
            parent_depth: 0,
            rewrite_gen: 0,
            parent_history: Vec::new(),
            full_ast: full_ast.clone_tree(),
            target_hash: cobra_orchestrator::expr_identity_hash(&full_ast),
        };
        let mut item = mk_resolve_item(0);
        item.metadata.lean_certificate = Some(cobra_orchestrator::LeanCertificate::new(
            64,
            Expr::variable(0),
            Expr::variable(0),
        ));
        item.metadata.lean_signature_certificate =
            cobra_orchestrator::LeanSignatureCertificate::new(64, 1, vec![0, 1], Expr::variable(0));

        let candidate = emit_join_candidate_product(
            &join,
            &item,
            Expr::mul(
                Expr::variable(0),
                Expr::add(Expr::variable(1), Expr::variable(2)),
            ),
            PassId::ProductIdentityCollapse,
        )
        .expect("product join emits signature-certified candidate");
        assert!(candidate.metadata.lean_certificate.is_none());
        let cert = candidate
            .metadata
            .lean_signature_certificate
            .as_ref()
            .expect("signature certificate");
        if let StateData::Candidate(candidate_payload) = &candidate.payload {
            assert!(cert.matches_signature(
                64,
                3,
                &[0, 0, 0, 1, 0, 1, 0, 2],
                &candidate_payload.expr
            ));
        } else {
            panic!("expected candidate");
        }
    }

    #[test]
    fn lifted_substitute_substitutes_and_emits_candidate() {
        // Outer winner: virtual var v0 (index 1; original_var_count = 1).
        // Binding v0 = `x ^ 0`. Substituted result is `x ^ 0` which is `x`.
        // Original eval is the identity in x.
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        let outer_winner = Expr::variable(1);
        let binding = LiftedBinding {
            kind: cobra_orchestrator::LiftedValueKind::ArithmeticAtom,
            outer_var_index: 1,
            subtree: Expr::xor(Expr::variable(0), Expr::constant(0)),
            structural_hash: 0,
            original_support: vec![0],
        };
        let original_eval = Evaluator::from_expr(&Expr::variable(0), 64);

        let cont = ContinuationData::LiftedSubstitute(Box::new(LiftedSubstituteCont {
            bindings: vec![binding],
            outer_vars: vec!["x".into(), "v0".into()],
            original_var_count: 1,
            original_eval: Some(original_eval),
            original_vars: vec!["x".into()],
            source_sig: vec![0, 1],
        }));

        let gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        {
            let g = ctx.competition_groups.get_mut(&gid).unwrap();
            g.best = Some(CandidateRecord {
                expr: outer_winner,
                cost: cobra_core::expr_cost::ExprCost::default(),
                verification: VerificationState::Verified,
                real_vars: vec!["x".into(), "v0".into()],
                source_pass: PassId::SignaturePatternMatch,
                needs_original_space_verification: false,
                sig_vector: vec![],
                lean_certificate: None,
                lean_signature_certificate: None,
            });
            g.continuation = Some(cont);
        }

        let item = mk_resolve_item(gid);
        let pr = run_resolve_competition(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::SolvedCandidate);
        assert_eq!(pr.next.len(), 1);
        let StateData::Candidate(cand) = &pr.next[0].payload else {
            panic!("expected Candidate");
        };
        assert!(pr.next[0].metadata.lean_certificate.is_none());
        let cert = pr.next[0]
            .metadata
            .lean_signature_certificate
            .as_ref()
            .expect("substituted candidate gets source signature certificate");
        assert!(cert.matches_signature(64, 1, &[0, 1], &cand.expr));
        // Should evaluate to x.
        let eval = Evaluator::from_expr(&cand.expr, 64);
        for &v in &[0u64, 1, 2, 7, 1024] {
            assert_eq!(eval.eval(&[v]), v);
        }
    }

    #[test]
    fn residual_recombine_emits_fresh_source_signature_certificate() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        ctx.evaluator = Some(Evaluator::from_expr(&Expr::variable(0), 64));

        let cont = ContinuationData::RemainderRecombine(Box::new(RemainderRecombineCont {
            prefix_expr: Expr::constant(0),
            origin: cobra_orchestrator::RemainderOrigin::ProductCore,
            remainder_eval: Evaluator::from_expr(&Expr::variable(0), 64),
            source_sig: vec![0, 1],
            remainder_support: Vec::new(),
            prefix_degree: 0,
            parent_group_id: None,
            target_eval: Evaluator::from_expr(&Expr::variable(0), 64),
            target_vars: vec!["x".into()],
        }));

        let gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        {
            let group = ctx.competition_groups.get_mut(&gid).unwrap();
            group.best = Some(CandidateRecord {
                expr: Expr::variable(0),
                cost: cobra_core::expr_cost::compute_cost(&Expr::variable(0)).cost,
                verification: VerificationState::Verified,
                real_vars: vec!["x".into()],
                source_pass: PassId::SignaturePatternMatch,
                needs_original_space_verification: false,
                sig_vector: vec![0, 1],
                lean_certificate: Some(cobra_orchestrator::LeanCertificate::new(
                    64,
                    Expr::variable(0),
                    Expr::variable(0),
                )),
                lean_signature_certificate: None,
            });
            group.continuation = Some(cont);
        }

        let item = mk_resolve_item(gid);
        let pr = run_resolve_competition(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::SolvedCandidate);
        let StateData::Candidate(cand) = &pr.next[0].payload else {
            panic!("expected Candidate");
        };
        assert!(pr.next[0].metadata.lean_certificate.is_none());
        let cert = pr.next[0]
            .metadata
            .lean_signature_certificate
            .as_ref()
            .expect("recombined candidate gets source signature certificate");
        assert!(cert.matches_signature(64, 1, &[0, 1], &cand.expr));
    }
}
