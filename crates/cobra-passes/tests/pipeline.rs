//! End-to-end tests exercising the seed helper + scheduler dispatch
//! through the current (partial) `PASS_REGISTRY`.

use cobra_core::classification::{SemanticClass, StructuralFlag};
use cobra_core::simplify_outcome::Options;
use cobra_orchestrator::{
    simplify_from_worklist, OrchestratorContext, OrchestratorPolicy, Worklist,
};
use cobra_parser::parse_to_ast;
use cobra_passes::seed_with_ast;

#[test]
fn seeding_classifies_input_and_survives_dispatch() {
    // Parse "(x & 0xFF) + y" — a semilinear expression.
    let parsed = parse_to_ast("(x & 0xFF) + y", 64).unwrap();

    let mut ctx = OrchestratorContext::new(Options::default(), parsed.vars, 64);
    let mut worklist = Worklist::new();
    seed_with_ast(&parsed.expr, &mut ctx, &mut worklist).unwrap();

    // Seeding alone is enough to stamp the classification.
    assert_eq!(
        ctx.run_metadata.input_classification.semantic,
        SemanticClass::Semilinear,
    );
    assert!(ctx
        .run_metadata
        .input_classification
        .flags
        .contains(StructuralFlag::HAS_BITWISE));

    // Now run the dispatch loop. No downstream passes are wired yet,
    // so it'll exhaust — but it must not panic and must not clobber
    // the classification.
    let policy = OrchestratorPolicy {
        max_expansions: 32,
        ..OrchestratorPolicy::default()
    };
    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        policy,
        cobra_passes::PASS_REGISTRY,
        Some(&parsed.expr),
    )
    .unwrap();

    // Semilinear input + no passes → returns unsupported with the
    // classification preserved in the diagnostic.
    assert_eq!(
        outcome.diag.classification.semantic,
        SemanticClass::Semilinear,
    );
}

#[test]
fn seeding_pure_arith_with_not_triggers_lowering_flag() {
    // "~(x + 1)" at bitwidth 8 — LowerNotOverArith fires during seeding.
    let parsed = parse_to_ast("~(x + 1)", 8).unwrap();
    let mut ctx = OrchestratorContext::new(
        Options {
            bitwidth: 8,
            ..Options::default()
        },
        parsed.vars,
        8,
    );
    let mut worklist = Worklist::new();
    seed_with_ast(&parsed.expr, &mut ctx, &mut worklist).unwrap();
    assert!(ctx.lowering_fired);
    // Two items queued: the lowered one and the original.
    assert_eq!(worklist.len(), 2);
}

#[test]
fn lower_not_over_arith_fires_for_applicable_input() {
    // Parse "~(x + 1)" at bitwidth 8 — LowerNotOverArith should rewrite
    // this to Add(Neg(x+1), 0xFF). We can't easily observe the lowered
    // AST via simplify_from_worklist (no pass returns it as a
    // Candidate), but we can verify the helpers directly.
    use cobra_passes::{has_not_over_arith, lower_not_over_arith};

    let parsed = parse_to_ast("~(x + 1)", 8).unwrap();
    assert!(has_not_over_arith(&parsed.expr));
    let lowered = lower_not_over_arith(parsed.expr, 8);
    // After lowering there must be no remaining Not-over-arith.
    assert!(!has_not_over_arith(&lowered));
}

#[test]
fn registry_contains_expected_passes() {
    use cobra_orchestrator::PassId;
    let ids: Vec<PassId> = cobra_passes::PASS_REGISTRY.iter().map(|d| d.id).collect();
    assert_eq!(
        ids,
        vec![
            PassId::LowerNotOverArith,
            PassId::ClassifyAst,
            PassId::BuildSignatureState,
            PassId::VerifyCandidate,
            PassId::SignaturePatternMatch,
            PassId::SignatureAnf,
            PassId::PrepareCoeffModel,
            PassId::SignatureCobCandidate,
            PassId::SignatureMultivarPolyRecovery,
            PassId::SignatureSingletonPolyRecovery,
            PassId::SemilinearNormalize,
            PassId::SemilinearCheck,
            PassId::SemilinearRewrite,
            PassId::SemilinearReconstruct,
            PassId::PrepareDirectRemainder,
            PassId::PrepareRemainderFromCore,
            PassId::ExtractProductCore,
            PassId::ExtractPolyCoreD2,
            PassId::ExtractPolyCoreD3,
            PassId::ExtractPolyCoreD4,
            PassId::ExtractTemplateCore,
            PassId::ResidualSupported,
            PassId::ResidualPolyRecovery,
            PassId::ResidualGhost,
            PassId::ResidualFactoredGhost,
            PassId::ResidualFactoredGhostEscalated,
            PassId::ResidualTemplate,
            PassId::SignatureBitwiseDecompose,
            PassId::SignatureHybridDecompose,
            PassId::ResolveCompetition,
            PassId::OperandSimplify,
            PassId::ProductIdentityCollapse,
            PassId::AtomIdentityRewrite,
            PassId::XorLowering,
            PassId::LiftArithmeticAtoms,
            PassId::LiftRepeatedSubexpressions,
            PassId::PrepareLiftedOuterSolve,
        ]
    );
}

/// First end-to-end simplification: `parse "x ^ y"`, drive through
/// the full pipeline, expect a Simplified outcome whose expression is
/// `Xor(Variable(0), Variable(1))`.
#[test]
fn pipeline_simplifies_xor_via_pattern_match() {
    use cobra_core::expr::Kind;
    use cobra_core::simplify_outcome::{Options, SimplifyOutcomeKind};

    let parsed = parse_to_ast("x ^ y", 64).unwrap();
    let mut ctx = OrchestratorContext::new(Options::default(), parsed.vars.clone(), 64);
    ctx.evaluator = Some(cobra_core::evaluator::Evaluator::from_expr(
        &parsed.expr,
        64,
    ));

    let mut worklist = Worklist::new();
    cobra_passes::seed_with_ast(&parsed.expr, &mut ctx, &mut worklist).unwrap();

    let policy = OrchestratorPolicy {
        max_expansions: 64,
        ..OrchestratorPolicy::default()
    };
    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        policy,
        cobra_passes::PASS_REGISTRY,
        Some(&parsed.expr),
    )
    .unwrap();

    assert_eq!(outcome.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(
        outcome.verified,
        outcome.proof_level == cobra_core::simplify_outcome::ProofLevel::LeanCertified
    );
    assert_eq!(outcome.real_vars, vec!["x".to_owned(), "y".to_owned()]);
    let expr = outcome.expr.expect("simplified expression");
    assert!(matches!(expr.kind, Kind::Xor));
    assert!(outcome.telemetry.candidates_verified >= 1);
}

/// Scaled-boolean lift: `parse "5 + 2 * (x ^ y)"` simplifies back to
/// the same affine form. Public verification is reported only when the
/// result carries Lean-certified evidence.
#[test]
fn pipeline_simplifies_scaled_boolean_xor() {
    use cobra_core::expr::Kind;
    use cobra_core::simplify_outcome::{Options, SimplifyOutcomeKind};

    let parsed = parse_to_ast("5 + 2 * (x ^ y)", 64).unwrap();
    let mut ctx = OrchestratorContext::new(Options::default(), parsed.vars.clone(), 64);
    ctx.evaluator = Some(cobra_core::evaluator::Evaluator::from_expr(
        &parsed.expr,
        64,
    ));

    let mut worklist = Worklist::new();
    cobra_passes::seed_with_ast(&parsed.expr, &mut ctx, &mut worklist).unwrap();

    let policy = OrchestratorPolicy {
        // With upstream-style competition groups, the scaled form keeps
        // exploring decomposition branches before the parent group
        // resolves. The default policy handles it; keep this bounded
        // but above the observed grouped path length.
        max_expansions: 192,
        ..OrchestratorPolicy::default()
    };
    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        policy,
        cobra_passes::PASS_REGISTRY,
        Some(&parsed.expr),
    )
    .unwrap();

    assert_eq!(outcome.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(
        outcome.verified,
        outcome.proof_level == cobra_core::simplify_outcome::ProofLevel::LeanCertified
    );
    let expr = outcome.expr.expect("simplified expression");
    // Either Add(5, Mul(2, Xor)) directly, or potentially a tree the
    // cleanup pass canonicalised — assert via signature equivalence to
    // shield against later cleanup-rule changes.
    let actual_sig = cobra_core::evaluate_boolean_signature(&expr, 2, 64);
    let expected_sig = vec![5u64, 7, 7, 5];
    assert_eq!(actual_sig, expected_sig);
    assert!(matches!(expr.kind, Kind::Add | Kind::Mul));
}

/// Pattern matcher recovers a constant from a constant signature.
#[test]
fn pipeline_simplifies_constant() {
    use cobra_core::expr::{Expr, Kind};
    use cobra_core::simplify_outcome::{Options, SimplifyOutcomeKind};

    // 7 & 14 = 6 — no variables; sig = [6].
    let expr = Expr::and(Expr::constant(7), Expr::constant(14));
    let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
    ctx.evaluator = Some(cobra_core::evaluator::Evaluator::from_expr(&expr, 64));

    let mut worklist = Worklist::new();
    cobra_passes::seed_with_ast(&expr, &mut ctx, &mut worklist).unwrap();

    let policy = OrchestratorPolicy {
        max_expansions: 32,
        ..OrchestratorPolicy::default()
    };
    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        policy,
        cobra_passes::PASS_REGISTRY,
        Some(&expr),
    )
    .unwrap();

    assert_eq!(outcome.kind, SimplifyOutcomeKind::Simplified);
    let simplified = outcome.expr.expect("simplified expression");
    assert!(matches!(simplified.kind, Kind::Constant(6)));
}

/// Canonical README MBA: `(x & y) + (x | y)` must collapse to `x + y`
/// at seeding time via `simplify_pattern_subtrees`, with the
/// [`try_simplify_two_var_pattern_sum`][cobra_passes::try_simplify_two_var_pattern_sum]
/// combinator filling the 3-valued-sig gap that the scaled-boolean
/// lift can't reach. The input expression's signature is equal to
/// `x + y`'s, so the full-width verifier accepts the rewrite.
#[test]
fn pipeline_collapses_and_plus_or_to_add_via_pattern_sum() {
    use cobra_core::expr::Expr;
    use cobra_core::simplify_outcome::{Options, SimplifyOutcomeKind};

    let input = Expr::add(
        Expr::and(Expr::variable(0), Expr::variable(1)),
        Expr::or(Expr::variable(0), Expr::variable(1)),
    );
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    ctx.evaluator = Some(cobra_core::evaluator::Evaluator::from_expr(&input, 64));

    let mut worklist = Worklist::new();
    cobra_passes::seed_with_ast(&input, &mut ctx, &mut worklist).unwrap();

    // After seeding the input expression stored in the worklist's
    // AST item must already be signature-equivalent to `x + y`. The
    // scaled-boolean matcher will still miss the resulting sig
    // [0,1,1,2], so the remainder of the pipeline doesn't need to
    // fire — this test locks in the pre-simplification alone.
    let policy = OrchestratorPolicy {
        max_expansions: 64,
        ..OrchestratorPolicy::default()
    };
    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        policy,
        cobra_passes::PASS_REGISTRY,
        Some(&input),
    )
    .unwrap();

    // The pipeline may not yet produce a Simplified outcome for linear
    // `x + y` (no linear solver is wired), but seed-time rewriting must
    // fire. Verify by running `simplify_pattern_subtrees` directly and
    // confirming it is signature-equivalent to the original at bw=64.
    let rewritten = cobra_passes::simplify_pattern_subtrees(input.clone_tree(), 64);
    let before = cobra_core::evaluate_boolean_signature(&input, 2, 64);
    let after = cobra_core::evaluate_boolean_signature(&rewritten, 2, 64);
    assert_eq!(before, after);
    // Cost strictly improved.
    assert!(cobra_core::is_better(
        &cobra_core::expr_cost::compute_cost(&rewritten).cost,
        &cobra_core::expr_cost::compute_cost(&input).cost,
    ));
    // The outcome itself is either Simplified or Unsupported, but must
    // not be a hard failure.
    assert!(matches!(
        outcome.kind,
        SimplifyOutcomeKind::Simplified | SimplifyOutcomeKind::UnchangedUnsupported,
    ));
}

/// `SignatureAnf` rescues a 3-variable Boolean MBA that the 2-var
/// pattern-matcher and scaled-boolean lift both miss.
#[test]
fn pipeline_simplifies_three_var_xor_via_anf() {
    use cobra_core::expr::Kind;
    use cobra_core::simplify_outcome::{Options, SimplifyOutcomeKind};

    let parsed = parse_to_ast("x ^ y ^ z", 64).unwrap();
    let mut ctx = OrchestratorContext::new(Options::default(), parsed.vars.clone(), 64);
    ctx.evaluator = Some(cobra_core::evaluator::Evaluator::from_expr(
        &parsed.expr,
        64,
    ));

    let mut worklist = Worklist::new();
    cobra_passes::seed_with_ast(&parsed.expr, &mut ctx, &mut worklist).unwrap();

    let policy = OrchestratorPolicy {
        max_expansions: 128,
        ..OrchestratorPolicy::default()
    };
    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        policy,
        cobra_passes::PASS_REGISTRY,
        Some(&parsed.expr),
    )
    .unwrap();

    assert_eq!(outcome.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(
        outcome.verified,
        outcome.proof_level == cobra_core::simplify_outcome::ProofLevel::LeanCertified
    );
    let expr = outcome.expr.expect("simplified expression");
    // `x ^ y ^ z` — some XOR tree at the top. ANF build yields a
    // left-associative XOR chain.
    assert!(matches!(expr.kind, Kind::Xor));
    // Signature of the simplified expression must equal the input's.
    let sig_in = cobra_core::evaluate_boolean_signature(&parsed.expr, 3, 64);
    let sig_out = cobra_core::evaluate_boolean_signature(&expr, 3, 64);
    assert_eq!(sig_in, sig_out);
}

/// Feed "x + y" through seeding + scheduler. No signature-technique
/// passes are wired yet, so dispatch exhausts, but it does so after
/// `BuildSignatureState` has constructed a signature-state item —
/// telemetry should reflect the expansions.
#[test]
fn pipeline_produces_signature_state_for_linear_add() {
    use cobra_core::expr::Expr;
    use cobra_core::simplify_outcome::Options;

    let expr = Expr::add(Expr::variable(0), Expr::variable(1));
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    ctx.evaluator = Some(cobra_core::evaluator::Evaluator::from_expr(&expr, 64));

    let mut worklist = Worklist::new();
    cobra_passes::seed_with_ast(&expr, &mut ctx, &mut worklist).unwrap();

    let policy = OrchestratorPolicy {
        max_expansions: 32,
        ..OrchestratorPolicy::default()
    };
    let outcome = simplify_from_worklist(
        &mut ctx,
        worklist,
        policy,
        cobra_passes::PASS_REGISTRY,
        Some(&expr),
    )
    .unwrap();

    assert!(outcome.telemetry.total_expansions > 0);
    assert_eq!(outcome.diag.classification.semantic, SemanticClass::Linear);
}
