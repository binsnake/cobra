//! `ResolveCompetition` — fires when a `CompetitionResolved` work item
//! reaches the scheduler. Per-continuation dispatch routes the winning
//! candidate (or accumulates failure reasons) into:
//!
//! - `None`: emit the winner straight through as a `Candidate`.
//! - `BitwiseCompose` / `HybridCompose`: stitch the recovered child
//!   expression back into the gate template that spawned it, then
//!   submit it to the parent group and release that group's handle.
//! - `OperandRewrite` / `ProductCollapse`: record the side that just
//!   resolved on the shared `JoinState`. When both sides have closed,
//!   build candidate `Mul`s and emit a rewritten AST.
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

use cobra_core::expr::Expr;
use cobra_core::expr_cost::{compute_cost, is_better, ExprCost};
use cobra_core::expr_utils::remap_var_indices;
use cobra_core::pass_contract::{
    DecompositionMeta, ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame,
    VerificationState,
};
use cobra_core::result::Result;

use cobra_orchestrator::{
    project_extractor_kind, release_handle, replace_by_hash, submit_candidate, AstPayload,
    BitwiseComposeCont, CandidatePayload, CandidateRecord, CompetitionGroup, ContinuationData,
    FactorRole, HybridComposeCont, ItemDisposition, JoinState, LiftedBinding, LiftedSubstituteCont,
    OperandJoinState, OperandRewriteCont, OrchestratorContext, PassDecision, PassId, PassResult,
    ProductCollapseCont, ProductJoinState, Provenance, RemainderRecombineCont, ResidualSolverKind,
    StateData, WorkItem,
};

use crate::bitwise_decomposer::{compose, remap_vars};
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
        ContinuationData::None => resolve_none(&group, item),
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

fn resolve_none(group: &CompetitionGroup, item: &WorkItem) -> PassResult {
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
        cand_item.metadata.verification = winner.verification;
        cand_item.metadata.sig_vector.clone_from(&winner.sig_vector);
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
    submit_candidate(&mut ctx.competition_groups, parent_group_id, record);
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
            let record = CandidateRecord {
                expr: composed,
                cost,
                verification,
                real_vars: cont.parent_real_vars.clone(),
                source_pass: PassId::SignatureBitwiseDecompose,
                needs_original_space_verification: cont.parent_needs_original_space_verification,
                sig_vector: Vec::new(),
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
            let record = CandidateRecord {
                expr: composed,
                cost,
                verification,
                real_vars: cont.parent_real_vars.clone(),
                source_pass: PassId::SignatureHybridDecompose,
                needs_original_space_verification: cont.parent_needs_original_space_verification,
                sig_vector: Vec::new(),
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
    rewritten.depth = join.parent_depth;
    rewritten.rewrite_gen = join.rewrite_gen + 1;
    rewritten.attempted_mask = 0;
    rewritten.group_id = join.parent_group_id;
    rewritten.history.clone_from(&join.parent_history);
    rewritten
}

fn emit_join_rewrite_product(
    join: &ProductJoinState,
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
    rewritten.depth = join.parent_depth;
    rewritten.rewrite_gen = join.rewrite_gen + 1;
    rewritten.attempted_mask = 0;
    rewritten.group_id = join.parent_group_id;
    rewritten.history.clone_from(&join.parent_history);
    rewritten
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

    if let Some((expr, _)) = best {
        pr.next.push(emit_join_rewrite_operand(&join, item, expr));
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
                pr.next
                    .push(emit_join_rewrite_product(&join, item, candidate));
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

    if let Some(parent_gid) = cont.parent_group_id {
        let record = CandidateRecord {
            expr: combined,
            cost,
            verification: VerificationState::Verified,
            real_vars: target_vars.clone(),
            source_pass: PassId::ResidualSupported,
            needs_original_space_verification: false,
            sig_vector: Vec::new(),
        };
        submit_candidate(&mut ctx.competition_groups, parent_gid, record);
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
            source_sig: vec![],
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
        // Should evaluate to x.
        let eval = Evaluator::from_expr(&cand.expr, 64);
        for &v in &[0u64, 1, 2, 7, 1024] {
            assert_eq!(eval.eval(&[v]), v);
        }
    }
}
