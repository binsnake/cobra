//! Integration tests for the main dispatch loop. These exercise the
//! loop end-to-end without depending on any real pass — either by
//! pre-seeding verified candidates (which bypass `select_next_pass`
//! entirely) or by using tiny stub passes wired into a local registry.

use cobra_core::evaluator::Evaluator;
use cobra_core::expr::{Expr, Kind};
use cobra_core::expr_cost::ExprCost;
use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, VerificationState,
};
use cobra_core::result::Result;
use cobra_core::simplify_outcome::{Options, ProofLevel, SimplifyOutcomeKind};
use cobra_orchestrator::{
    create_group, simplify_from_worklist, AstPayload, CandidatePayload, ItemDisposition,
    OrchestratorContext, OrchestratorPolicy, PassDecision, PassDescriptor, PassId, PassResult,
    PassTag, Provenance, StateData, StateKind, Worklist,
};

fn mk_candidate(verified: bool) -> CandidatePayload {
    CandidatePayload {
        expr: Expr::add(Expr::variable(0), Expr::variable(1)),
        real_vars: vec!["x".into(), "y".into()],
        cost: ExprCost::default(),
        producing_pass: PassId::VerifyCandidate,
        needs_original_space_verification: !verified,
    }
}

fn mk_candidate_item(verified: bool) -> cobra_orchestrator::WorkItem {
    let mut item =
        cobra_orchestrator::WorkItem::new(StateData::Candidate(Box::new(mk_candidate(verified))));
    item.metadata.verification = if verified {
        VerificationState::Verified
    } else {
        VerificationState::Unverified
    };
    item
}

#[test]
fn verified_candidate_returned_immediately() {
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    let mut worklist = Worklist::new();
    worklist.push(mk_candidate_item(true));

    let outcome =
        simplify_from_worklist(&mut ctx, worklist, OrchestratorPolicy::default(), &[], None)
            .unwrap();

    assert_eq!(outcome.kind, SimplifyOutcomeKind::Simplified);
    assert!(outcome.verified);
    assert_eq!(outcome.real_vars, vec!["x".to_owned(), "y".to_owned()]);
    let expr = outcome.expr.expect("simplified expr");
    assert!(matches!(expr.kind, Kind::Add));
    // Loop ran exactly once (we popped and returned).
    assert_eq!(outcome.telemetry.total_expansions, 1);
}

#[test]
fn verified_original_space_candidate_gets_generated_endpoint_certificate() {
    let original = Expr::add(Expr::variable(0), Expr::variable(1));
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    ctx.original_expr = Some(original.clone_tree());
    let mut worklist = Worklist::new();
    worklist.push(mk_candidate_item(true));

    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        OrchestratorPolicy::default(),
        &[],
        Some(&original),
    )
    .unwrap();

    assert_eq!(outcome.kind, SimplifyOutcomeKind::Simplified);
    assert!(outcome.verified);
    assert_eq!(outcome.proof_level, ProofLevel::LeanCertified);
}

#[test]
fn verified_reduced_space_candidate_gets_remapped_endpoint_certificate() {
    let original = Expr::variable(1);
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    ctx.original_expr = Some(original.clone_tree());

    let mut item = mk_candidate_item(true);
    if let StateData::Candidate(cand) = &mut item.payload {
        cand.expr = Expr::variable(0);
        cand.real_vars = vec!["y".into()];
    }

    let mut worklist = Worklist::new();
    worklist.push(item);

    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        OrchestratorPolicy::default(),
        &[],
        Some(&original),
    )
    .unwrap();

    assert_eq!(outcome.kind, SimplifyOutcomeKind::Simplified);
    assert!(outcome.verified);
    assert_eq!(outcome.real_vars, vec!["y".to_owned()]);
    assert_eq!(outcome.proof_level, ProofLevel::LeanCertified);
}

#[test]
fn empty_worklist_returns_exhausted() {
    let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
    let outcome = simplify_from_worklist(
        &mut ctx,
        Worklist::new(),
        OrchestratorPolicy::default(),
        &[],
        None,
    )
    .unwrap();
    assert_eq!(outcome.kind, SimplifyOutcomeKind::UnchangedUnsupported);
    assert!(!outcome.verified);
    assert!(outcome.diag.reason.contains("Worklist exhausted"));
    assert_eq!(outcome.telemetry.total_expansions, 0);
}

#[test]
fn empty_worklist_echoes_original_expr() {
    let original = Expr::add(Expr::variable(0), Expr::constant(7));
    let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
    let outcome = simplify_from_worklist(
        &mut ctx,
        Worklist::new(),
        OrchestratorPolicy::default(),
        &[],
        Some(&original),
    )
    .unwrap();
    assert_eq!(outcome.kind, SimplifyOutcomeKind::UnchangedUnsupported);
    assert_eq!(outcome.expr, Some(original));
}

#[test]
fn unverified_candidate_without_pass_exhausts() {
    // Unverified candidates go through VerifyCandidate, but the
    // registry is empty. The scheduler picks `VerifyCandidate` (since
    // `needs_original_space_verification = true` blocks the early
    // return), but the registry has no descriptor for it — the loop
    // continues past the missing entry and eventually exhausts.
    let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
    let mut worklist = Worklist::new();
    worklist.push(mk_candidate_item(false));

    let outcome =
        simplify_from_worklist(&mut ctx, worklist, OrchestratorPolicy::default(), &[], None)
            .unwrap();
    assert_eq!(outcome.kind, SimplifyOutcomeKind::UnchangedUnsupported);
    // The loop should have popped the candidate once, then looped
    // again finding nothing (pass registry empty) and bailed after
    // select_next_pass exhausted eligible passes.
    assert!(outcome.telemetry.total_expansions >= 1);
}

#[test]
fn stubbed_verify_candidate_pass_returns_success() {
    // A tiny stub `VerifyCandidate` that flips `needs_original_space_verification`
    // to false and re-emits the candidate — the loop will then accept
    // it on the second pop.
    #[allow(clippy::unnecessary_wraps)]
    fn stub_verify(
        item: &cobra_orchestrator::WorkItem,
        _ctx: &mut OrchestratorContext,
    ) -> Result<PassResult> {
        let StateData::Candidate(cand) = &item.payload else {
            return Ok(PassResult::not_applicable(ReasonDetail::default()));
        };
        let mut next_payload = (**cand).clone();
        next_payload.needs_original_space_verification = false;
        let mut next =
            cobra_orchestrator::WorkItem::new(StateData::Candidate(Box::new(next_payload)));
        next.metadata.verification = VerificationState::Verified;
        Ok(PassResult {
            decision: PassDecision::SolvedCandidate,
            disposition: ItemDisposition::ConsumeCurrent,
            next: vec![next],
            reason: ReasonDetail::default(),
        })
    }

    fn always_applicable(_item: &cobra_orchestrator::WorkItem, _ctx: &OrchestratorContext) -> bool {
        true
    }

    let registry = [PassDescriptor {
        id: PassId::VerifyCandidate,
        consumes: StateKind::CandidateExpr,
        tag: PassTag::Verifier,
        applicable: always_applicable,
        run: stub_verify,
    }];

    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    let mut worklist = Worklist::new();
    worklist.push(mk_candidate_item(false));

    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        OrchestratorPolicy::default(),
        &registry,
        None,
    )
    .unwrap();

    assert_eq!(outcome.kind, SimplifyOutcomeKind::Simplified);
    assert!(outcome.verified);
    assert_eq!(outcome.telemetry.candidates_verified, 1);
    // Two pops: the original item (runs VerifyCandidate), then the
    // re-emitted verified candidate which returns immediately.
    assert_eq!(outcome.telemetry.total_expansions, 2);
}

#[test]
fn expansion_budget_cuts_off_the_loop() {
    // Registry with a pass that retains the current item forever.
    #[allow(clippy::unnecessary_wraps)]
    fn never_finish(
        _item: &cobra_orchestrator::WorkItem,
        _ctx: &mut OrchestratorContext,
    ) -> Result<PassResult> {
        Ok(PassResult {
            decision: PassDecision::Advance,
            disposition: ItemDisposition::RetainCurrent,
            next: vec![],
            reason: ReasonDetail::default(),
        })
    }

    fn always(_item: &cobra_orchestrator::WorkItem, _ctx: &OrchestratorContext) -> bool {
        true
    }

    let registry = [PassDescriptor {
        id: PassId::VerifyCandidate,
        consumes: StateKind::CandidateExpr,
        tag: PassTag::Verifier,
        applicable: always,
        run: never_finish,
    }];

    let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
    let mut worklist = Worklist::new();
    worklist.push(mk_candidate_item(false));

    let policy = OrchestratorPolicy {
        max_expansions: 5,
        ..OrchestratorPolicy::default()
    };

    let outcome = simplify_from_worklist(&mut ctx, worklist, policy, &registry, None).unwrap();

    // Each retained pop records one attempt; the attempted_mask bit
    // blocks reselection, so after one "retain" cycle the scheduler
    // picks nothing and the item drops. Total expansions capped at
    // `max_expansions` or exits cleanly below — just assert it
    // respected the cap.
    assert!(outcome.telemetry.total_expansions <= 5);
    assert_eq!(outcome.kind, SimplifyOutcomeKind::UnchangedUnsupported);
}

#[test]
fn grouped_candidate_submits_and_resolves() {
    // A verified candidate that owns a group handle should submit into
    // the group and trigger resolution (handle → 0). That resolution
    // emits a CompetitionResolved work item; without a registered
    // `ResolveCompetition` pass it will eventually exhaust, but the
    // group should be submitted-to along the way.
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
    let gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);

    let mut item = mk_candidate_item(true);
    item.group_id = Some(gid);
    let mut worklist = Worklist::new();
    worklist.push(item);

    let outcome =
        simplify_from_worklist(&mut ctx, worklist, OrchestratorPolicy::default(), &[], None)
            .unwrap();

    // The candidate went into the group, not straight out as Success.
    assert_eq!(outcome.kind, SimplifyOutcomeKind::UnchangedUnsupported);
    let group = ctx
        .competition_groups
        .get(&gid)
        .expect("group still present after resolution");
    let best = group.best.as_ref().expect("candidate submitted");
    assert_eq!(best.verification, VerificationState::Verified);
    // Handle count went from 1 → 0 via `release_handle`.
    assert_eq!(group.open_handles, 0);
}

#[test]
fn failing_pass_records_last_failure_into_best_unsupported() {
    #[allow(clippy::unnecessary_wraps)]
    fn fail(
        _item: &cobra_orchestrator::WorkItem,
        _ctx: &mut OrchestratorContext,
    ) -> Result<PassResult> {
        Ok(PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::ConsumeCurrent,
            next: vec![],
            reason: ReasonDetail {
                top: ReasonFrame {
                    code: ReasonCode {
                        category: ReasonCategory::NoSolution,
                        domain: ReasonDomain::Verifier,
                        subcode: 0,
                    },
                    message: "solver bailed".into(),
                    fields: vec![],
                },
                causes: vec![],
            },
        })
    }

    fn always(_item: &cobra_orchestrator::WorkItem, _ctx: &OrchestratorContext) -> bool {
        true
    }

    let registry = [PassDescriptor {
        id: PassId::VerifyCandidate,
        consumes: StateKind::CandidateExpr,
        tag: PassTag::Verifier,
        applicable: always,
        run: fail,
    }];

    let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
    let mut worklist = Worklist::new();
    worklist.push(mk_candidate_item(false));

    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        OrchestratorPolicy::default(),
        &registry,
        None,
    )
    .unwrap();

    assert_eq!(outcome.kind, SimplifyOutcomeKind::UnchangedUnsupported);
    assert_eq!(outcome.diag.reason, "solver bailed");
}

#[test]
fn exhaustion_promotes_pic_rewrite_to_verified_candidate() {
    // Seed a FoldedAst carrying a cheaper PIC-produced rewrite that the
    // pipeline abandons (empty registry → no pass fires). The main
    // loop's exhaustion-path fallback must: (1) verify the rewrite
    // against the original evaluator, (2) promote it to a Success
    // outcome, and (3) stamp `reason_code = BestRewritePromoted`.

    // Original input: (x & y) * (x | y) + (x & ~y) * (~x & y) — expands
    // to x*y under the PIC identity at full width. Cost is high.
    let original = Expr::add(
        Expr::mul(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::or(Expr::variable(0), Expr::variable(1)),
        ),
        Expr::mul(
            Expr::and(Expr::variable(0), Expr::not(Expr::variable(1))),
            Expr::and(Expr::not(Expr::variable(0)), Expr::variable(1)),
        ),
    );

    // The rewrite PIC would have produced: x * y. Strictly cheaper.
    let rewrite = Expr::mul(Expr::variable(0), Expr::variable(1));

    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    ctx.evaluator = Some(Evaluator::from_expr(&original, 64));

    // Build the FoldedAst work item with rewrite_gen=1 and a history
    // entry for ProductIdentityCollapse — the eligibility gate needs
    // both.
    let mut item = cobra_orchestrator::WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
        expr: rewrite.clone(),
        classification: None,
        provenance: Provenance::Rewritten,
        solve_ctx: None,
    })));
    item.rewrite_gen = 1;
    item.history.push(PassId::ProductIdentityCollapse);

    let mut worklist = Worklist::new();
    worklist.push(item);

    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        OrchestratorPolicy::default(),
        &[],
        Some(&original),
    )
    .unwrap();

    assert_eq!(outcome.kind, SimplifyOutcomeKind::Simplified);
    assert!(outcome.verified);
    let out_expr = outcome.expr.expect("promoted rewrite present");
    // Structurally `x * y`.
    assert!(matches!(out_expr.kind, Kind::Mul));
    let code = outcome.diag.reason_code.expect("reason_code stamped");
    assert_eq!(code.category, ReasonCategory::BestRewritePromoted);
    assert_eq!(code.domain, ReasonDomain::StructuralTransform);
    assert!(outcome.diag.transform_produced_candidate);
}

#[test]
fn exhaustion_preserves_lean_certificate_on_promoted_best_rewrite() {
    let original = Expr::add(Expr::variable(0), Expr::constant(0));
    let rewrite = Expr::variable(0);

    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
    ctx.evaluator = Some(Evaluator::from_expr(&original, 64));

    let mut item = cobra_orchestrator::WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
        expr: rewrite.clone(),
        classification: None,
        provenance: Provenance::Rewritten,
        solve_ctx: None,
    })));
    item.rewrite_gen = 1;
    item.history.push(PassId::AtomIdentityRewrite);
    item.metadata.lean_certificate = cobra_orchestrator::LeanCertificate::try_single_rewrite_64(
        64,
        original.clone_tree(),
        cobra_orchestrator::ExprPath::default(),
        rewrite,
    );

    let mut worklist = Worklist::new();
    worklist.push(item);

    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        OrchestratorPolicy::default(),
        &[],
        Some(&original),
    )
    .unwrap();

    assert_eq!(outcome.kind, SimplifyOutcomeKind::Simplified);
    assert!(outcome.verified);
    assert_eq!(outcome.proof_level, ProofLevel::LeanCertified);
}

#[test]
fn exhaustion_leaves_unchanged_for_non_pic_rewrite() {
    // Same cheap rewrite but with no PIC in the history — eligibility
    // gate must refuse promotion, so the outcome stays
    // UnchangedUnsupported. Guards against over-firing.
    let original = Expr::add(Expr::variable(0), Expr::variable(1));
    let rewrite = Expr::add(Expr::variable(0), Expr::variable(1));

    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    ctx.evaluator = Some(Evaluator::from_expr(&original, 64));

    let mut item = cobra_orchestrator::WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
        expr: rewrite,
        classification: None,
        provenance: Provenance::Rewritten,
        solve_ctx: None,
    })));
    item.rewrite_gen = 1;
    // History deliberately missing PIC — pretend OperandSimplify was
    // the only transform. The fallback must skip it.
    item.history.push(PassId::OperandSimplify);

    let mut worklist = Worklist::new();
    worklist.push(item);

    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        OrchestratorPolicy::default(),
        &[],
        Some(&original),
    )
    .unwrap();

    assert_eq!(outcome.kind, SimplifyOutcomeKind::UnchangedUnsupported);
}
