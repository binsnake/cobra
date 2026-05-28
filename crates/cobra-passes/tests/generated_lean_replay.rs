//! Replays generated Lean certificates from real pass outputs.
//!
//! These tests are cheap Rust assertions by default.  When
//! `COBRA_LEAN_REPLAY=1` is set, they also write the generated Lean source to
//! a temporary file and run `lake env lean` against the formal model.

use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use cobra_core::classification::{Classification, SemanticClass, StructuralFlag};
use cobra_core::evaluate_boolean_signature;
use cobra_core::evaluator::Evaluator;
use cobra_core::expr::{Expr, Kind};
use cobra_core::expr_rewrite::cleanup_final_expr;
use cobra_core::pass_contract::VerificationState;
use cobra_core::simplify_outcome::Options;
use cobra_ir::{interpolate_coefficients, normalize_to_semilinear};
use cobra_orchestrator::{
    create_group, create_join, expr_identity_hash, AstPayload, BitwiseComposeCont,
    CandidatePayload, CandidateRecord, CompetitionResolvedPayload, ContinuationData,
    CoreCandidatePayload, EliminationResult, ExtractOp, ExtractorKind, FactorRole, GateKind,
    HybridComposeCont, ItemDisposition, JoinState, LiftedBinding, LiftedSubstituteCont,
    LiftedValueKind, OperandJoinState, OperandRewriteCont, OperandRole, OrchestratorContext,
    PassDecision, PassId, ProductCollapseCont, ProductJoinState, Provenance, RemainderOrigin,
    RemainderStatePayload, RemainderTargetContext, ResidualSolverKind, RewrittenSemilinearPayload,
    SemilinearContext, SignatureCoeffStatePayload, SignatureStatePayload,
    SignatureSubproblemContext, StateData, WorkItem, Worklist,
};
use cobra_verify::{
    emit_bv_decide_certificate, emit_constant_signature_certificate,
    emit_signature_certificate_model, emit_step_chain_certificate, ExprPath, LeanCertificate,
    LeanSignatureCertificate, LeanTheorem,
};

fn mk_ast_item(expr: Box<Expr>, provenance: Provenance) -> WorkItem {
    WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
        expr,
        classification: None,
        provenance,
        solve_ctx: None,
    })))
}

fn mk_classified_ast_item(
    expr: Box<Expr>,
    provenance: Provenance,
    classification: Classification,
) -> WorkItem {
    WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
        expr,
        classification: Some(classification),
        provenance,
        solve_ctx: None,
    })))
}

fn mk_signature_item(sig: Vec<u64>, real_vars: Vec<String>) -> WorkItem {
    let elimination = EliminationResult {
        reduced_sig: sig.clone(),
        real_vars: real_vars.clone(),
        spurious_vars: Vec::new(),
    };
    WorkItem::new(StateData::Signature(Box::new(SignatureStatePayload {
        ctx: SignatureSubproblemContext {
            sig,
            original_indices: (0..real_vars.len() as u32).collect(),
            real_vars,
            elimination,
            needs_original_space_verification: false,
        },
    })))
}

fn mk_signature_coeff_item(
    sig: Vec<u64>,
    real_vars: Vec<String>,
    ctx: &mut OrchestratorContext,
) -> WorkItem {
    let coeffs = interpolate_coefficients(sig.clone(), real_vars.len() as u32, ctx.bitwidth);
    let elimination = EliminationResult {
        reduced_sig: sig.clone(),
        real_vars: real_vars.clone(),
        spurious_vars: Vec::new(),
    };
    let payload = SignatureCoeffStatePayload {
        ctx: SignatureSubproblemContext {
            sig,
            real_vars,
            elimination,
            original_indices: Vec::new(),
            needs_original_space_verification: false,
        },
        coeffs,
    };
    let mut item = WorkItem::new(StateData::SignatureCoeff(Box::new(payload)));
    let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    item.group_id = Some(group_id);
    item
}

fn mk_resolve_item(group_id: u32) -> WorkItem {
    WorkItem::new(StateData::CompetitionResolved(CompetitionResolvedPayload {
        group_id,
    }))
}

fn mk_remainder_payload(
    remainder_expr: &Expr,
    prefix_expr: Box<Expr>,
    target_expr: &Expr,
    vars: Vec<String>,
    origin: RemainderOrigin,
    is_boolean_null: bool,
    degree_floor: u8,
) -> RemainderStatePayload {
    let remainder_sig = evaluate_boolean_signature(remainder_expr, vars.len() as u32, 64);
    let source_sig = evaluate_boolean_signature(target_expr, vars.len() as u32, 64);
    RemainderStatePayload {
        origin,
        prefix_expr,
        prefix_degree: 0,
        remainder_eval: Evaluator::from_expr(remainder_expr, 64),
        source_sig,
        remainder_sig: remainder_sig.clone(),
        remainder_elim: EliminationResult {
            reduced_sig: remainder_sig,
            real_vars: vars.clone(),
            spurious_vars: Vec::new(),
        },
        remainder_support: (0..vars.len() as u32).collect(),
        is_boolean_null,
        degree_floor,
        target: RemainderTargetContext {
            eval: Evaluator::from_expr(target_expr, 64),
            vars,
            remap_support: Vec::new(),
        },
    }
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("workspace root")
        .to_path_buf()
}

fn replay_enabled() -> bool {
    std::env::var("COBRA_LEAN_REPLAY").is_ok_and(|value| value == "1")
}

fn ensure_lean_built(formal_dir: &Path) {
    static LEAN_BUILD: OnceLock<()> = OnceLock::new();
    LEAN_BUILD.get_or_init(|| {
        let output = Command::new("lake")
            .arg("-R")
            .arg("build")
            .current_dir(formal_dir)
            .output()
            .expect("run lake -R build");
        assert!(
            output.status.success(),
            "Lean build failed before replay\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    });
}

fn replay_lean(name: &str, source: &str) {
    if !replay_enabled() {
        return;
    }

    let formal_dir = workspace_root().join("formal").join("lean");
    ensure_lean_built(&formal_dir);
    let out_dir = std::env::temp_dir().join("cobra_lean_replay");
    fs::create_dir_all(&out_dir).expect("create Lean replay temp directory");
    let lean_file = out_dir.join(format!("{name}.lean"));
    fs::write(&lean_file, source).expect("write generated Lean certificate");

    let output = Command::new("lake")
        .arg("env")
        .arg("lean")
        .arg(&lean_file)
        .current_dir(&formal_dir)
        .output()
        .expect("run lake env lean");

    assert!(
        output.status.success(),
        "Lean replay failed for {name}\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn replay_endpoint_certificate(name: &str, cert: &LeanCertificate) {
    assert!(
        cert.matches_endpoints(cert.bitwidth, &cert.original, &cert.simplified),
        "{name}: endpoint certificate metadata must match its theorem endpoints"
    );
    for (idx, step) in cert.steps.iter().enumerate() {
        assert_eq!(
            *step.context.plug(step.before.clone_tree()),
            if idx == 0 {
                *cert.original.clone_tree()
            } else {
                *cert.steps[idx - 1]
                    .context
                    .plug(cert.steps[idx - 1].after.clone_tree())
            },
            "{name}: step {idx} input must continue the endpoint chain"
        );
        assert!(
            step.path.0.len() <= u8::MAX as usize,
            "{name}: step {idx} path is outside generated path bounds"
        );
    }
    if let Some(last) = cert.steps.last() {
        assert_eq!(
            *last.context.plug(last.after.clone_tree()),
            *cert.simplified.clone_tree(),
            "{name}: endpoint chain must end at certificate simplified expression"
        );
    }
    let source = emit_step_chain_certificate(name, cert)
        .unwrap_or_else(|| emit_bv_decide_certificate(name, cert));
    if !cert.steps.is_empty() {
        assert!(
            !source.contains("try bv_decide"),
            "{name}: theorem-backed step-chain proof must not fall back to bv_decide"
        );
        for (idx, step) in cert.steps.iter().enumerate() {
            assert!(
                source.contains(&format!("using {}", step.theorem.lean_name())),
                "{name}: step {idx} must apply its recorded theorem {}",
                step.theorem.lean_name()
            );
        }
    }
    replay_lean(name, &source);
}

fn replay_signature_certificate(name: &str, cert: &LeanSignatureCertificate) {
    assert!(
        cert.matches_signature(cert.bitwidth, cert.num_vars, &cert.signature, &cert.expr),
        "{name}: signature certificate metadata must match its theorem target"
    );
    let source = emit_signature_certificate_model(name, cert).expect("emit signature certificate");
    replay_lean(name, &source);
}

#[test]
fn lean_emitter_fallbacks_replays_in_lean() {
    let endpoint = LeanCertificate::new(
        64,
        Expr::add(Expr::variable(0), Expr::constant(0)),
        Expr::variable(0),
    );
    let endpoint_source = emit_bv_decide_certificate("lean_emitter_bv_decide_fallback", &endpoint);
    replay_lean("lean_emitter_bv_decide_fallback", &endpoint_source);

    let constant_source = emit_constant_signature_certificate(
        "lean_emitter_constant_signature",
        64,
        2,
        &[7, 7, 7, 7],
        7,
    )
    .expect("constant signature certificate");
    replay_lean("lean_emitter_constant_signature", &constant_source);
}

fn replay_public_cleanup_case(name: &str, original: Box<Expr>) {
    let cleaned = cleanup_final_expr(original.clone_tree(), 64);
    assert_ne!(
        *original, *cleaned,
        "{name}: cleanup case must exercise a real public-output rewrite"
    );
    let cert = LeanCertificate::new(64, original, cleaned);
    replay_endpoint_certificate(name, &cert);
}

#[test]
fn public_cleanup_generated_certificate_replays_in_lean() {
    replay_public_cleanup_case(
        "public_cleanup_constant_fold_replay",
        Expr::add(
            Expr::add(Expr::constant(1), Expr::constant(2)),
            Expr::variable(0),
        ),
    );
    replay_public_cleanup_case(
        "public_cleanup_refold_not_replay",
        Expr::add(Expr::neg(Expr::variable(0)), Expr::constant(u64::MAX)),
    );
    replay_public_cleanup_case(
        "public_cleanup_common_factor_replay",
        Expr::add(
            Expr::mul(
                Expr::variable(0),
                Expr::add(Expr::variable(1), Expr::variable(2)),
            ),
            Expr::mul(
                Expr::variable(3),
                Expr::add(Expr::variable(1), Expr::variable(2)),
            ),
        ),
    );
}

#[test]
fn public_cleanup_after_certified_endpoint_replays_in_lean() {
    let original = Expr::add(
        Expr::add(Expr::variable(0), Expr::constant(0)),
        Expr::constant(0),
    );
    let pass_endpoint = Expr::add(Expr::variable(0), Expr::constant(0));
    let public_endpoint = cleanup_final_expr(pass_endpoint.clone_tree(), 64);
    assert_eq!(*public_endpoint, *Expr::variable(0));

    let pass_cert =
        LeanCertificate::try_single_rewrite_between_64(64, original, pass_endpoint.clone_tree())
            .expect("pass endpoint certificate");
    let cleanup_cert =
        LeanCertificate::try_single_rewrite_between_64(64, pass_endpoint, public_endpoint)
            .expect("public cleanup certificate");
    let cert = pass_cert
        .merge_step_chain(cleanup_cert)
        .expect("composed public certificate");

    replay_endpoint_certificate("public_cleanup_after_certified_endpoint_replay", &cert);
}

#[test]
fn lean_theorem_exports_replays_in_lean() {
    let mut source = String::from("import Cobra\n\n");
    for theorem in LeanTheorem::ALL {
        source.push_str("#check ");
        source.push_str(theorem.lean_name());
        source.push('\n');
    }
    replay_lean("lean_theorem_exports", &source);
}

fn replay_local_rewrite(name: &str, before: Box<Expr>, after: Box<Expr>, theorem: LeanTheorem) {
    let cert = LeanCertificate::try_single_rewrite_64(64, before, ExprPath::default(), after)
        .expect("recognized local rewrite certificate");
    assert_eq!(cert.steps.len(), 1);
    assert_eq!(cert.steps[0].theorem, theorem);
    replay_endpoint_certificate(name, &cert);
    replay_direct_rewrite_theorem(name, &cert, theorem);
}

fn replay_direct_rewrite_theorem(name: &str, cert: &LeanCertificate, theorem: LeanTheorem) {
    let args = match theorem_arity(theorem) {
        0 => "",
        1 => " (env 0)",
        2 => " (env 0) (env 1)",
        3 => " (env 0) (env 1) (env 2)",
        arity => panic!("{name}: unsupported direct theorem arity {arity} for {theorem:?}"),
    };
    let source = format!(
        "import Cobra\n\n\
         namespace Cobra.Generated\n\n\
         theorem {name}_direct_theorem : Cobra.Expr.SemEq {} ({}) ({}) := by\n\
         \x20 intro env\n\
         \x20 simpa [Cobra.Expr.eval, Cobra.allOnes, BitVec.sub_eq_add_neg] using {}{}\n\n\
         end Cobra.Generated\n",
        cert.bitwidth,
        cobra_verify::emit_expr(&cert.original),
        cobra_verify::emit_expr(&cert.simplified),
        theorem.lean_name(),
        args,
    );
    replay_lean(&format!("{name}_direct_theorem"), &source);
}

fn theorem_arity(theorem: LeanTheorem) -> usize {
    match theorem {
        LeanTheorem::BnotEqNegAddMask64
        | LeanTheorem::BnotEqNegAddAllOnes64
        | LeanTheorem::AddZero64
        | LeanTheorem::MulZero64
        | LeanTheorem::MulOne64
        | LeanTheorem::ZeroAdd64
        | LeanTheorem::ZeroMul64
        | LeanTheorem::OneMul64
        | LeanTheorem::NegNeg64
        | LeanTheorem::NotNot64
        | LeanTheorem::AndSelf64
        | LeanTheorem::OrSelf64
        | LeanTheorem::XorSelf64
        | LeanTheorem::XorZero64
        | LeanTheorem::ZeroXor64
        | LeanTheorem::AndZero64
        | LeanTheorem::ZeroAnd64
        | LeanTheorem::OrZero64
        | LeanTheorem::ZeroOr64
        | LeanTheorem::AndAllOnes64
        | LeanTheorem::AllOnesAnd64
        | LeanTheorem::OrAllOnes64
        | LeanTheorem::AllOnesOr64
        | LeanTheorem::ShrZero64 => 1,
        LeanTheorem::Const3And1_64 => 0,
        LeanTheorem::XorEqAddSubTwoMulAnd64
        | LeanTheorem::OrSubAndEqXor64
        | LeanTheorem::AndOrSumEqAdd64
        | LeanTheorem::TwoMulAndOrSumEqTwoMulAdd64
        | LeanTheorem::NotOrSubNotEqAnd64
        | LeanTheorem::NotOrAddSelfAddOneEqAnd64
        | LeanTheorem::XorViaOrNot64
        | LeanTheorem::AddComm64
        | LeanTheorem::MulComm64
        | LeanTheorem::AndComm64
        | LeanTheorem::OrComm64
        | LeanTheorem::XorComm64
        | LeanTheorem::DemorganNotAnd64
        | LeanTheorem::DemorganOrNotNot64
        | LeanTheorem::DemorganNotAndNotNot64
        | LeanTheorem::DemorganNotOr64
        | LeanTheorem::DemorganNotOrNotNot64 => 2,
        LeanTheorem::AddAssoc64
        | LeanTheorem::MulAssoc64
        | LeanTheorem::MulAdd64
        | LeanTheorem::AddMul64 => 3,
        LeanTheorem::CompileSound
        | LeanTheorem::ContextPreservesSemanticEquivalence
        | LeanTheorem::RewriteStepSound
        | LeanTheorem::ChainSound => {
            panic!("non-scalar theorem {theorem:?} cannot discharge a direct local rewrite")
        }
    }
}

fn replay_context_frame_rewrite(name: &str, root: Box<Expr>, path: ExprPath) {
    let original = root.clone_tree();
    let cert = LeanCertificate::try_single_rewrite_64(64, root, path, Expr::variable(0))
        .expect("context rewrite certificate");
    assert_eq!(cert.steps.len(), 1);
    assert_eq!(cert.steps[0].theorem, LeanTheorem::AddZero64);
    assert_eq!(cert.steps[0].context.frames.len(), 1);
    assert!(cert.matches_endpoints(64, &original, &cert.simplified));
    replay_endpoint_certificate(name, &cert);
}

#[test]
fn lean_context_frame_matrix_replays_in_lean() {
    let before = || Expr::add(Expr::variable(0), Expr::constant(0));

    replay_context_frame_rewrite(
        "lean_context_add_l_replay",
        Expr::add(before(), Expr::variable(1)),
        ExprPath(vec![0]),
    );
    replay_context_frame_rewrite(
        "lean_context_add_r_replay",
        Expr::add(Expr::variable(1), before()),
        ExprPath(vec![1]),
    );
    replay_context_frame_rewrite(
        "lean_context_mul_l_replay",
        Expr::mul(before(), Expr::variable(1)),
        ExprPath(vec![0]),
    );
    replay_context_frame_rewrite(
        "lean_context_mul_r_replay",
        Expr::mul(Expr::variable(1), before()),
        ExprPath(vec![1]),
    );
    replay_context_frame_rewrite(
        "lean_context_and_l_replay",
        Expr::and(before(), Expr::variable(1)),
        ExprPath(vec![0]),
    );
    replay_context_frame_rewrite(
        "lean_context_and_r_replay",
        Expr::and(Expr::variable(1), before()),
        ExprPath(vec![1]),
    );
    replay_context_frame_rewrite(
        "lean_context_or_l_replay",
        Expr::or(before(), Expr::variable(1)),
        ExprPath(vec![0]),
    );
    replay_context_frame_rewrite(
        "lean_context_or_r_replay",
        Expr::or(Expr::variable(1), before()),
        ExprPath(vec![1]),
    );
    replay_context_frame_rewrite(
        "lean_context_xor_l_replay",
        Expr::xor(before(), Expr::variable(1)),
        ExprPath(vec![0]),
    );
    replay_context_frame_rewrite(
        "lean_context_xor_r_replay",
        Expr::xor(Expr::variable(1), before()),
        ExprPath(vec![1]),
    );
    replay_context_frame_rewrite(
        "lean_context_not_replay",
        Expr::not(before()),
        ExprPath(vec![0]),
    );
    replay_context_frame_rewrite(
        "lean_context_neg_replay",
        Expr::neg(before()),
        ExprPath(vec![0]),
    );
    replay_context_frame_rewrite(
        "lean_context_shr_replay",
        Expr::shr(before(), 3),
        ExprPath(vec![0]),
    );
}

fn replay_local_rewrite_seen(
    seen: &mut HashSet<LeanTheorem>,
    name: &str,
    before: Box<Expr>,
    after: Box<Expr>,
    theorem: LeanTheorem,
) {
    replay_local_rewrite(name, before, after, theorem);
    assert!(seen.insert(theorem), "duplicate replay for {theorem:?}");
}

#[test]
fn local_rewrite_theorem_matrix_replays_in_lean() {
    let x = Expr::variable(0);
    let y = Expr::variable(1);
    let mut seen = HashSet::new();

    replay_local_rewrite_seen(
        &mut seen,
        "local_add_zero_replay",
        Expr::add(x.clone_tree(), Expr::constant(0)),
        x.clone_tree(),
        LeanTheorem::AddZero64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_zero_add_replay",
        Expr::add(Expr::constant(0), x.clone_tree()),
        x.clone_tree(),
        LeanTheorem::ZeroAdd64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_xor_lowering_replay",
        Expr::xor(x.clone_tree(), y.clone_tree()),
        Expr::add(
            Expr::add(x.clone_tree(), y.clone_tree()),
            Expr::neg(Expr::mul(
                Expr::constant(2),
                Expr::and(x.clone_tree(), y.clone_tree()),
            )),
        ),
        LeanTheorem::XorEqAddSubTwoMulAnd64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_or_sub_and_replay",
        Expr::add(
            Expr::or(x.clone_tree(), y.clone_tree()),
            Expr::neg(Expr::and(x.clone_tree(), y.clone_tree())),
        ),
        Expr::xor(x.clone_tree(), y.clone_tree()),
        LeanTheorem::OrSubAndEqXor64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_and_or_sum_replay",
        Expr::add(
            Expr::and(x.clone_tree(), y.clone_tree()),
            Expr::or(x.clone_tree(), y.clone_tree()),
        ),
        Expr::add(x.clone_tree(), y.clone_tree()),
        LeanTheorem::AndOrSumEqAdd64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_two_mul_and_or_sum_replay",
        Expr::add(
            Expr::mul(Expr::constant(2), Expr::and(x.clone_tree(), y.clone_tree())),
            Expr::mul(Expr::constant(2), Expr::or(x.clone_tree(), y.clone_tree())),
        ),
        Expr::add(
            Expr::mul(Expr::constant(2), x.clone_tree()),
            Expr::mul(Expr::constant(2), y.clone_tree()),
        ),
        LeanTheorem::TwoMulAndOrSumEqTwoMulAdd64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_not_or_sub_not_replay",
        Expr::add(
            Expr::or(Expr::not(x.clone_tree()), y.clone_tree()),
            Expr::neg(Expr::not(x.clone_tree())),
        ),
        Expr::and(x.clone_tree(), y.clone_tree()),
        LeanTheorem::NotOrSubNotEqAnd64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_not_or_add_self_add_one_replay",
        Expr::add(
            Expr::add(
                Expr::or(Expr::not(x.clone_tree()), y.clone_tree()),
                x.clone_tree(),
            ),
            Expr::constant(1),
        ),
        Expr::and(x.clone_tree(), y.clone_tree()),
        LeanTheorem::NotOrAddSelfAddOneEqAnd64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_xor_via_or_not_replay",
        Expr::add(
            Expr::add(
                Expr::add(x.clone_tree(), Expr::neg(y.clone_tree())),
                Expr::neg(Expr::mul(
                    Expr::constant(2),
                    Expr::or(x.clone_tree(), Expr::not(y.clone_tree())),
                )),
            ),
            Expr::neg(Expr::constant(2)),
        ),
        Expr::xor(x.clone_tree(), y.clone_tree()),
        LeanTheorem::XorViaOrNot64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_mul_zero_replay",
        Expr::mul(x.clone_tree(), Expr::constant(0)),
        Expr::constant(0),
        LeanTheorem::MulZero64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_zero_mul_replay",
        Expr::mul(Expr::constant(0), x.clone_tree()),
        Expr::constant(0),
        LeanTheorem::ZeroMul64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_mul_one_replay",
        Expr::mul(x.clone_tree(), Expr::constant(1)),
        x.clone_tree(),
        LeanTheorem::MulOne64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_one_mul_replay",
        Expr::mul(Expr::constant(1), x.clone_tree()),
        x.clone_tree(),
        LeanTheorem::OneMul64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_and_self_replay",
        Expr::and(x.clone_tree(), x.clone_tree()),
        x.clone_tree(),
        LeanTheorem::AndSelf64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_and_zero_replay",
        Expr::and(x.clone_tree(), Expr::constant(0)),
        Expr::constant(0),
        LeanTheorem::AndZero64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_const_3_and_1_replay",
        Expr::and(Expr::constant(3), Expr::constant(1)),
        Expr::constant(1),
        LeanTheorem::Const3And1_64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_zero_and_replay",
        Expr::and(Expr::constant(0), x.clone_tree()),
        Expr::constant(0),
        LeanTheorem::ZeroAnd64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_and_all_ones_replay",
        Expr::and(x.clone_tree(), Expr::constant(u64::MAX)),
        x.clone_tree(),
        LeanTheorem::AndAllOnes64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_all_ones_and_replay",
        Expr::and(Expr::constant(u64::MAX), x.clone_tree()),
        x.clone_tree(),
        LeanTheorem::AllOnesAnd64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_or_self_replay",
        Expr::or(x.clone_tree(), x.clone_tree()),
        x.clone_tree(),
        LeanTheorem::OrSelf64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_or_zero_replay",
        Expr::or(x.clone_tree(), Expr::constant(0)),
        x.clone_tree(),
        LeanTheorem::OrZero64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_zero_or_replay",
        Expr::or(Expr::constant(0), x.clone_tree()),
        x.clone_tree(),
        LeanTheorem::ZeroOr64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_or_all_ones_replay",
        Expr::or(x.clone_tree(), Expr::constant(u64::MAX)),
        Expr::constant(u64::MAX),
        LeanTheorem::OrAllOnes64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_all_ones_or_replay",
        Expr::or(Expr::constant(u64::MAX), x.clone_tree()),
        Expr::constant(u64::MAX),
        LeanTheorem::AllOnesOr64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_xor_self_replay",
        Expr::xor(x.clone_tree(), x.clone_tree()),
        Expr::constant(0),
        LeanTheorem::XorSelf64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_xor_zero_replay",
        Expr::xor(x.clone_tree(), Expr::constant(0)),
        x.clone_tree(),
        LeanTheorem::XorZero64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_zero_xor_replay",
        Expr::xor(Expr::constant(0), x.clone_tree()),
        x.clone_tree(),
        LeanTheorem::ZeroXor64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_not_not_replay",
        Expr::not(Expr::not(x.clone_tree())),
        x.clone_tree(),
        LeanTheorem::NotNot64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_demorgan_not_and_replay",
        Expr::not(Expr::and(x.clone_tree(), y.clone_tree())),
        Expr::or(Expr::not(x.clone_tree()), Expr::not(y.clone_tree())),
        LeanTheorem::DemorganNotAnd64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_demorgan_or_not_not_replay",
        Expr::or(Expr::not(x.clone_tree()), Expr::not(y.clone_tree())),
        Expr::not(Expr::and(x.clone_tree(), y.clone_tree())),
        LeanTheorem::DemorganOrNotNot64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_demorgan_not_and_not_not_replay",
        Expr::not(Expr::and(
            Expr::not(x.clone_tree()),
            Expr::not(y.clone_tree()),
        )),
        Expr::or(x.clone_tree(), y.clone_tree()),
        LeanTheorem::DemorganNotAndNotNot64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_demorgan_not_or_replay",
        Expr::not(Expr::or(x.clone_tree(), y.clone_tree())),
        Expr::and(Expr::not(x.clone_tree()), Expr::not(y.clone_tree())),
        LeanTheorem::DemorganNotOr64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_demorgan_not_or_not_not_replay",
        Expr::not(Expr::or(
            Expr::not(x.clone_tree()),
            Expr::not(y.clone_tree()),
        )),
        Expr::and(x.clone_tree(), y.clone_tree()),
        LeanTheorem::DemorganNotOrNotNot64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_bnot_lower_replay",
        Expr::not(x.clone_tree()),
        Expr::add(Expr::neg(x.clone_tree()), Expr::constant(u64::MAX)),
        LeanTheorem::BnotEqNegAddAllOnes64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_neg_neg_replay",
        Expr::neg(Expr::neg(x.clone_tree())),
        x.clone_tree(),
        LeanTheorem::NegNeg64,
    );
    replay_local_rewrite_seen(
        &mut seen,
        "local_shr_zero_replay",
        Expr::shr(x.clone_tree(), 0),
        x,
        LeanTheorem::ShrZero64,
    );

    let expected: HashSet<_> = LeanTheorem::RECOGNIZED_REWRITE_64.iter().copied().collect();
    assert_eq!(
        seen, expected,
        "every theorem recognized by identify_rewrite_theorem_64 must replay in Lean"
    );
}

#[test]
fn lower_not_over_arith_generated_certificate_replays_in_lean() {
    replay_lower_not_over_arith_case(
        "lower_not_over_arith_replay",
        Expr::not(Expr::add(Expr::variable(0), Expr::constant(1))),
        vec!["x".into()],
    );
}

fn replay_lower_not_over_arith_case(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);
    let item = mk_ast_item(expr, Provenance::Original);

    let pr = cobra_passes::lower_not_over_arith::run_lower_not_over_arith(&item, &mut ctx)
        .expect("lowering pass");
    assert_eq!(pr.decision, PassDecision::Advance, "{name}");
    assert_eq!(pr.disposition, ItemDisposition::RetainCurrent, "{name}");

    let cert = pr.next[0]
        .metadata
        .lean_certificate
        .as_ref()
        .expect("endpoint certificate");
    replay_endpoint_certificate(name, cert);
}

#[test]
fn lower_not_over_arith_family_generated_certificate_replays_in_lean() {
    replay_lower_not_over_arith_case(
        "lower_not_over_arith_mul_replay",
        Expr::not(Expr::mul(Expr::variable(0), Expr::constant(3))),
        vec!["x".into()],
    );
    replay_lower_not_over_arith_case(
        "lower_not_over_arith_nested_bitwise_replay",
        Expr::and(
            Expr::variable(0),
            Expr::not(Expr::add(Expr::variable(1), Expr::constant(1))),
        ),
        vec!["x".into(), "y".into()],
    );
    replay_lower_not_over_arith_case(
        "lower_not_over_arith_two_step_chain_replay",
        Expr::and(
            Expr::not(Expr::add(Expr::variable(0), Expr::constant(1))),
            Expr::not(Expr::mul(Expr::variable(1), Expr::constant(3))),
        ),
        vec!["x".into(), "y".into()],
    );
}

#[test]
fn signature_pattern_match_generated_certificate_replays_in_lean() {
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    let item = mk_signature_item(vec![0, 1, 1, 0], vec!["x".into(), "y".into()]);

    let pr = cobra_passes::signature_pattern_match::run_signature_pattern_match(&item, &mut ctx)
        .expect("signature pattern pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate("signature_pattern_match_replay", cert);
}

fn replay_signature_pattern_case(name: &str, sig: Vec<u64>, vars: Vec<String>) {
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    let item = mk_signature_item(sig, vars);

    let pr = cobra_passes::signature_pattern_match::run_signature_pattern_match(&item, &mut ctx)
        .expect("signature pattern pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn signature_pattern_match_grouped_candidate_generated_certificate_replays_in_lean() {
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    let mut item = mk_signature_item(vec![0, 1, 1, 0], vec!["x".into(), "y".into()]);
    let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    item.group_id = Some(group_id);

    let pr = cobra_passes::signature_pattern_match::run_signature_pattern_match(&item, &mut ctx)
        .expect("signature pattern pass");
    assert_eq!(pr.decision, PassDecision::Advance);
    assert!(pr.next.is_empty());

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate("signature_pattern_match_grouped_candidate_replay", cert);
}

fn replay_build_signature_state_flow(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let mut item = mk_ast_item(expr, Provenance::Original);
    item.metadata.lean_certificate = Some(LeanCertificate::new(
        64,
        Expr::variable(0),
        Expr::variable(0),
    ));
    item.metadata.lean_signature_certificate =
        LeanSignatureCertificate::new(64, 1, vec![0, 1], Expr::variable(0));

    let built = cobra_passes::build_signature_state::run_build_signature_state(&item, &mut ctx)
        .expect("build signature state pass");
    assert_eq!(built.decision, PassDecision::Advance, "{name}");
    assert_eq!(built.next.len(), 1, "{name}");
    assert!(
        matches!(built.next[0].payload, StateData::Signature(_)),
        "{name}"
    );
    assert!(built.next[0].metadata.lean_certificate.is_none(), "{name}");
    assert!(
        built.next[0].metadata.lean_signature_certificate.is_none(),
        "{name}"
    );

    let group_id = built.next[0].group_id.expect("signature group");
    let matched = cobra_passes::signature_pattern_match::run_signature_pattern_match(
        &built.next[0],
        &mut ctx,
    )
    .expect("signature pattern pass after build signature state");
    assert_eq!(matched.decision, PassDecision::Advance, "{name}");

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

fn replay_normalized_candidate_signature_case(
    name: &str,
    expr: Box<Expr>,
    vars: Vec<String>,
    source_pass: PassId,
) {
    let sig = evaluate_boolean_signature(&expr, vars.len() as u32, 64);
    let original_cost = cobra_core::expr_cost::compute_cost(&expr).cost;
    let record = CandidateRecord {
        expr,
        cost: original_cost,
        verification: VerificationState::Verified,
        real_vars: vars,
        source_pass,
        needs_original_space_verification: false,
        sig_vector: sig.clone(),
        lean_certificate: None,
        lean_signature_certificate: None,
    };

    let normalized = cobra_passes::candidate_normalize::normalize_candidate_record(record, 64);
    assert!(
        cobra_core::expr_cost::is_better(&normalized.cost, &original_cost),
        "{name}: normalization should produce fresh candidate evidence"
    );
    assert_eq!(normalized.sig_vector, sig, "{name}");
    let cert = normalized
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    assert!(cert.matches_signature(
        64,
        normalized.real_vars.len() as u32,
        &sig,
        &normalized.expr
    ));
    replay_signature_certificate(name, cert);
}

#[test]
fn build_signature_state_flow_generated_certificate_replays_in_lean() {
    replay_build_signature_state_flow(
        "build_signature_state_xor_pattern_flow_replay",
        Expr::xor(Expr::variable(0), Expr::variable(1)),
        vec!["x".into(), "y".into()],
    );
    replay_build_signature_state_flow(
        "build_signature_state_spurious_var_flow_replay",
        Expr::variable(0),
        vec!["x".into(), "y".into()],
    );
}

#[test]
fn seed_pattern_rewrite_generated_certificate_replays_in_lean() {
    let expr = Expr::add(
        Expr::and(Expr::variable(0), Expr::variable(1)),
        Expr::or(Expr::variable(0), Expr::variable(1)),
    );
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    let mut worklist = Worklist::new();
    cobra_passes::seed_with_ast(&expr, &mut ctx, &mut worklist).expect("seed with AST");

    let mut cert = None;
    while let Some(item) = worklist.pop() {
        if item.history.contains(&PassId::PatternSubtreeRewrite) {
            cert = item.metadata.lean_certificate;
            break;
        }
    }
    let cert = cert.expect("seed pattern rewrite certificate");
    assert!(cert
        .steps
        .iter()
        .any(|step| step.theorem == LeanTheorem::AndOrSumEqAdd64));
    replay_endpoint_certificate("seed_pattern_rewrite_replay", &cert);
}

#[test]
fn pattern_matcher_scaled_pattern_sum_theorem_replays_in_lean() {
    let original = Expr::add(
        Expr::mul(
            Expr::constant(2),
            Expr::and(Expr::variable(0), Expr::variable(1)),
        ),
        Expr::mul(
            Expr::constant(2),
            Expr::or(Expr::variable(0), Expr::variable(1)),
        ),
    );
    let (rewritten, cert) = cobra_passes::pattern_matcher::simplify_pattern_subtrees_certified(
        original.clone_tree(),
        64,
    );
    assert!(
        cobra_core::expr_cost::is_better(
            &cobra_core::expr_cost::compute_cost(&rewritten).cost,
            &cobra_core::expr_cost::compute_cost(&original).cost,
        ),
        "scaled pattern-sum fallback must exercise a real simplification"
    );
    let cert = cert.expect("endpoint certificate");
    assert!(cert.matches_endpoints(64, &original, &rewritten));
    assert!(
        cert.steps
            .iter()
            .any(|step| { step.theorem == LeanTheorem::TwoMulAndOrSumEqTwoMulAdd64 }),
        "scaled pattern-sum should use its named theorem"
    );
    replay_endpoint_certificate("pattern_matcher_scaled_pattern_sum_theorem_replay", &cert);
}

#[test]
fn pattern_matcher_demorgan_table_theorem_replays_in_lean() {
    let original = Expr::not(Expr::or(
        Expr::not(Expr::variable(0)),
        Expr::not(Expr::variable(1)),
    ));
    let (rewritten, cert) = cobra_passes::pattern_matcher::simplify_pattern_subtrees_certified(
        original.clone_tree(),
        64,
    );
    assert_eq!(*rewritten, *Expr::and(Expr::variable(0), Expr::variable(1)));
    let cert = cert.expect("theorem-backed endpoint certificate");
    assert!(cert.matches_endpoints(64, &original, &rewritten));
    assert!(
        cert.steps
            .iter()
            .any(|step| step.theorem == LeanTheorem::DemorganNotOrNotNot64),
        "table-driven De Morgan simplification should use its named theorem"
    );
    replay_endpoint_certificate("pattern_matcher_demorgan_table_theorem_replay", &cert);
}

#[test]
fn pattern_matcher_demorgan_dual_table_theorem_replays_in_lean() {
    let original = Expr::not(Expr::and(
        Expr::not(Expr::variable(0)),
        Expr::not(Expr::variable(1)),
    ));
    let (rewritten, cert) = cobra_passes::pattern_matcher::simplify_pattern_subtrees_certified(
        original.clone_tree(),
        64,
    );
    assert_eq!(*rewritten, *Expr::or(Expr::variable(0), Expr::variable(1)));
    let cert = cert.expect("theorem-backed endpoint certificate");
    assert!(cert.matches_endpoints(64, &original, &rewritten));
    assert!(
        cert.steps
            .iter()
            .any(|step| step.theorem == LeanTheorem::DemorganNotAndNotNot64),
        "dual De Morgan table simplification should use its named theorem"
    );
    replay_endpoint_certificate("pattern_matcher_demorgan_dual_table_theorem_replay", &cert);
}

#[test]
fn signature_pattern_match_family_generated_certificate_replays_in_lean() {
    replay_signature_pattern_case(
        "signature_pattern_match_constant_replay",
        vec![7, 7, 7, 7],
        vec!["x".into(), "y".into()],
    );
    replay_signature_pattern_case(
        "signature_pattern_match_affine_1var_replay",
        vec![5, 7],
        vec!["x".into()],
    );
    replay_signature_pattern_case(
        "signature_pattern_match_and_replay",
        vec![0, 0, 0, 1],
        vec!["x".into(), "y".into()],
    );
    replay_signature_pattern_case(
        "signature_pattern_match_or_replay",
        vec![0, 1, 1, 1],
        vec!["x".into(), "y".into()],
    );
    replay_signature_pattern_case(
        "signature_pattern_match_xnor_replay",
        vec![u64::MAX, 0, 0, u64::MAX],
        vec!["x".into(), "y".into()],
    );
    replay_signature_pattern_case(
        "signature_pattern_match_scaled_xor_replay",
        vec![5, 7, 7, 5],
        vec!["x".into(), "y".into()],
    );

    let vars3 = vec!["x".to_owned(), "y".to_owned(), "z".to_owned()];
    let expr3 = Expr::xor(
        Expr::xor(Expr::variable(0), Expr::variable(1)),
        Expr::variable(2),
    );
    replay_signature_pattern_case(
        "signature_pattern_match_3var_boolean_replay",
        evaluate_boolean_signature(&expr3, 3, 64),
        vars3,
    );

    let vars4 = vec![
        "a".to_owned(),
        "b".to_owned(),
        "c".to_owned(),
        "d".to_owned(),
    ];
    let expr4 = Expr::and(
        Expr::and(Expr::variable(0), Expr::variable(1)),
        Expr::and(Expr::variable(2), Expr::variable(3)),
    );
    replay_signature_pattern_case(
        "signature_pattern_match_4var_boolean_replay",
        evaluate_boolean_signature(&expr4, 4, 64),
        vars4,
    );

    let vars5 = vec![
        "a".to_owned(),
        "b".to_owned(),
        "c".to_owned(),
        "d".to_owned(),
        "e".to_owned(),
    ];
    replay_signature_pattern_case(
        "signature_pattern_match_5var_boolean_replay",
        evaluate_boolean_signature(&Expr::variable(4), 5, 64),
        vars5,
    );

    let vars6 = vec![
        "a".to_owned(),
        "b".to_owned(),
        "c".to_owned(),
        "d".to_owned(),
        "e".to_owned(),
        "f".to_owned(),
    ];
    replay_signature_pattern_case(
        "signature_pattern_match_6var_boolean_replay",
        evaluate_boolean_signature(&Expr::variable(5), 6, 64),
        vars6,
    );
    replay_normalized_candidate_signature_case(
        "signature_pattern_match_late_normalized_and_plus_or_replay",
        Expr::add(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::or(Expr::variable(0), Expr::variable(1)),
        ),
        vec!["x".into(), "y".into()],
        PassId::SignaturePatternMatch,
    );
    replay_normalized_candidate_signature_case(
        "signature_pattern_match_late_normalized_add_zero_replay",
        Expr::add(Expr::variable(0), Expr::constant(0)),
        vec!["x".into()],
        PassId::SignaturePatternMatch,
    );
}

#[test]
fn signature_anf_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned(), "y".to_owned(), "z".to_owned()];
    let sig = vec![0, 1, 1, 0, 1, 0, 0, 1];
    let expr = Expr::xor(
        Expr::xor(Expr::variable(0), Expr::variable(1)),
        Expr::variable(2),
    );
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let item = mk_signature_item(sig, vars);

    let pr = cobra_passes::signature_anf::run_signature_anf(&item, &mut ctx).expect("ANF pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate("signature_anf_replay", cert);
}

fn replay_signature_anf_case(
    name: &str,
    sig: Vec<u64>,
    vars: Vec<String>,
    evaluator_expr: Option<Box<Expr>>,
) {
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    if let Some(expr) = evaluator_expr {
        ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    }
    let item = mk_signature_item(sig, vars);

    let pr = cobra_passes::signature_anf::run_signature_anf(&item, &mut ctx).expect("ANF pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn signature_anf_grouped_candidate_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned(), "y".to_owned(), "z".to_owned()];
    let sig = vec![0, 1, 1, 0, 1, 0, 0, 1];
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    let mut item = mk_signature_item(sig, vars);
    let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    item.group_id = Some(group_id);

    let pr = cobra_passes::signature_anf::run_signature_anf(&item, &mut ctx).expect("ANF pass");
    assert_eq!(pr.decision, PassDecision::Advance);
    assert!(pr.next.is_empty());

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate("signature_anf_grouped_candidate_replay", cert);
}

#[test]
fn signature_anf_product_shadow_repair_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned(), "y".to_owned()];
    let sig = vec![0, 0, 0, 1];
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(
        &Expr::mul(Expr::variable(0), Expr::variable(1)),
        64,
    ));
    let item = mk_signature_item(sig, vars);

    let pr = cobra_passes::signature_anf::run_signature_anf(&item, &mut ctx).expect("ANF pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);
    let StateData::Candidate(candidate) = &pr.next[0].payload else {
        panic!("ANF product-shadow repair must emit a candidate");
    };
    assert!(
        matches!(candidate.expr.kind, Kind::Mul),
        "product-shadow repair must be accepted only as the guarded MUL candidate"
    );

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    assert!(
        matches!(cert.expr.kind, Kind::Mul),
        "Lean evidence must target the repaired candidate, not the shadow AND"
    );
    replay_signature_certificate("signature_anf_product_shadow_repair_replay", cert);
}

#[test]
fn signature_anf_family_generated_certificate_replays_in_lean() {
    replay_signature_anf_case(
        "signature_anf_constant_zero_replay",
        vec![0, 0, 0, 0],
        vec!["x".into(), "y".into()],
        None,
    );
    replay_signature_anf_case(
        "signature_anf_constant_one_replay",
        vec![1, 1, 1, 1],
        vec!["x".into(), "y".into()],
        None,
    );
    replay_signature_anf_case(
        "signature_anf_two_var_and_repair_replay",
        vec![0, 0, 0, 1],
        vec!["x".into(), "y".into()],
        Some(Expr::mul(Expr::variable(0), Expr::variable(1))),
    );

    let vars4 = vec![
        "a".to_owned(),
        "b".to_owned(),
        "c".to_owned(),
        "d".to_owned(),
    ];
    let xor4 = Expr::xor(
        Expr::xor(Expr::variable(0), Expr::variable(1)),
        Expr::xor(Expr::variable(2), Expr::variable(3)),
    );
    replay_signature_anf_case(
        "signature_anf_four_var_xor_replay",
        evaluate_boolean_signature(&xor4, 4, 64),
        vars4,
        Some(xor4),
    );
    replay_normalized_candidate_signature_case(
        "signature_anf_late_normalized_scaled_boolean_sum_replay",
        Expr::add(
            Expr::constant(5),
            Expr::mul(Expr::constant(5), Expr::variable(0)),
        ),
        vec!["x".into()],
        PassId::SignatureAnf,
    );
}

#[test]
fn signature_cob_candidate_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned(), "y".to_owned()];
    let sig = vec![0, 1, 1, 0];
    let expr = Expr::xor(Expr::variable(0), Expr::variable(1));
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let item = mk_signature_coeff_item(sig, vars, &mut ctx);
    let group_id = item.group_id.expect("group id");

    let pr = cobra_passes::signature_cob_candidate::run_signature_cob_candidate(&item, &mut ctx)
        .expect("COB pass");
    assert_eq!(pr.decision, PassDecision::Advance);

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate("signature_cob_candidate_replay", cert);
}

fn replay_signature_cob_case(name: &str, sig: Vec<u64>, vars: Vec<String>) {
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    let item = mk_signature_coeff_item(sig, vars, &mut ctx);
    let group_id = item.group_id.expect("group id");

    let pr = cobra_passes::signature_cob_candidate::run_signature_cob_candidate(&item, &mut ctx)
        .expect("COB pass");
    assert_eq!(pr.decision, PassDecision::Advance);

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

fn replay_signature_cob_override_case(
    name: &str,
    sig: Vec<u64>,
    expr: Box<Expr>,
    vars: Vec<String>,
) {
    let arity = vars.len() as u32;
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(
        &Expr::add(Expr::variable(0), Expr::variable(1)),
        64,
    ));
    let mut item = mk_signature_coeff_item(sig, vars, &mut ctx);
    if let StateData::SignatureCoeff(payload) = &mut item.payload {
        payload.ctx.original_indices = (0..arity).collect();
    }
    item.evaluator_override = Some(Evaluator::from_expr(&expr, 64));
    item.evaluator_override_arity = arity;
    let group_id = item.group_id.expect("group id");

    let pr = cobra_passes::signature_cob_candidate::run_signature_cob_candidate(&item, &mut ctx)
        .expect("COB override pass");
    assert_eq!(pr.decision, PassDecision::Advance);

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn signature_cob_candidate_override_generated_certificate_replays_in_lean() {
    replay_signature_cob_override_case(
        "signature_cob_candidate_override_replay",
        vec![0, 1, 1, 0],
        Expr::xor(Expr::variable(0), Expr::variable(1)),
        vec!["x".into(), "y".into()],
    );
}

fn replay_prepare_coeff_model_flow(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let sig = evaluate_boolean_signature(&expr, vars.len() as u32, 64);
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let mut item = mk_signature_item(sig, vars);
    let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    item.group_id = Some(group_id);

    let prepared = cobra_passes::prepare_coeff_model::run_prepare_coeff_model(&item, &mut ctx)
        .expect("prepare coeff model pass");
    assert_eq!(prepared.decision, PassDecision::Advance, "{name}");
    assert_eq!(prepared.next.len(), 1, "{name}");
    assert!(
        matches!(prepared.next[0].payload, StateData::SignatureCoeff(_)),
        "{name}"
    );
    assert!(
        prepared.next[0].metadata.lean_certificate.is_none(),
        "{name}"
    );
    assert!(
        prepared.next[0]
            .metadata
            .lean_signature_certificate
            .is_none(),
        "{name}"
    );

    let solved = cobra_passes::signature_cob_candidate::run_signature_cob_candidate(
        &prepared.next[0],
        &mut ctx,
    )
    .expect("COB pass after prepare coeff model");
    assert_eq!(solved.decision, PassDecision::Advance, "{name}");

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn signature_cob_candidate_family_generated_certificate_replays_in_lean() {
    replay_signature_cob_case(
        "signature_cob_constant_replay",
        vec![13, 13, 13, 13],
        vec!["x".into(), "y".into()],
    );
    replay_signature_cob_case(
        "signature_cob_affine_1var_replay",
        vec![5, 9],
        vec!["x".into()],
    );
    replay_signature_cob_case(
        "signature_cob_three_var_xor_replay",
        vec![0, 1, 1, 0, 1, 0, 0, 1],
        vec!["x".into(), "y".into(), "z".into()],
    );
    replay_signature_cob_case(
        "signature_cob_non_boolean_2var_replay",
        vec![3, 5, 7, 11],
        vec!["x".into(), "y".into()],
    );
    replay_normalized_candidate_signature_case(
        "signature_cob_late_normalized_scaled_xor_const_replay",
        Expr::add(
            Expr::constant(3),
            Expr::mul(
                Expr::constant(3),
                Expr::xor(Expr::constant(1), Expr::variable(0)),
            ),
        ),
        vec!["x".into()],
        PassId::SignatureCobCandidate,
    );
}

#[test]
fn prepare_coeff_model_flow_generated_certificate_replays_in_lean() {
    replay_prepare_coeff_model_flow(
        "prepare_coeff_model_cob_flow_replay",
        Expr::xor(Expr::variable(0), Expr::variable(1)),
        vec!["x".into(), "y".into()],
    );
    replay_prepare_coeff_model_flow(
        "prepare_coeff_model_non_boolean_cob_flow_replay",
        Expr::add(
            Expr::constant(3),
            Expr::mul(Expr::constant(5), Expr::variable(0)),
        ),
        vec!["x".into()],
    );
}

#[test]
fn xor_lowering_generated_certificate_replays_in_lean() {
    replay_xor_lowering_case(
        "xor_lowering_replay",
        Expr::and(
            Expr::xor(
                Expr::add(Expr::variable(0), Expr::variable(1)),
                Expr::variable(2),
            ),
            Expr::constant(1),
        ),
        vec!["x".into(), "y".into(), "z".into()],
    );
}

fn replay_xor_lowering_case(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);
    let item = mk_ast_item(expr, Provenance::Original);

    let pr =
        cobra_passes::xor_lowering::run_xor_lowering(&item, &mut ctx).expect("xor lowering pass");
    assert_eq!(pr.decision, PassDecision::Advance, "{name}");
    assert_eq!(pr.disposition, ItemDisposition::ReplaceCurrent, "{name}");

    let cert = pr.next[0]
        .metadata
        .lean_certificate
        .as_ref()
        .expect("endpoint certificate");
    assert!(
        cert.steps
            .iter()
            .any(|step| step.theorem == LeanTheorem::XorEqAddSubTwoMulAnd64),
        "{name} should carry a theorem-backed xor lowering step"
    );
    replay_endpoint_certificate(name, cert);
}

#[test]
fn xor_lowering_family_generated_certificate_replays_in_lean() {
    replay_xor_lowering_case(
        "xor_lowering_wide_mask_replay",
        Expr::and(
            Expr::xor(
                Expr::add(Expr::variable(0), Expr::constant(5)),
                Expr::variable(1),
            ),
            Expr::constant(0xff),
        ),
        vec!["x".into(), "y".into()],
    );
    replay_xor_lowering_case(
        "xor_lowering_nested_add_mask_replay",
        Expr::and(
            Expr::xor(
                Expr::add(
                    Expr::add(Expr::variable(0), Expr::variable(1)),
                    Expr::constant(3),
                ),
                Expr::variable(2),
            ),
            Expr::constant(0xffff),
        ),
        vec!["x".into(), "y".into(), "z".into()],
    );
}

#[test]
fn semilinear_reconstruct_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned(), "y".to_owned()];
    let expr = Expr::and(Expr::variable(0), Expr::variable(1));
    let ir = normalize_to_semilinear(&expr, &vars, 64).expect("semilinear IR");
    let eval = Evaluator::from_expr(&expr, 64);
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(eval.clone());
    let item = WorkItem::new(StateData::SemilinearRewritten(Box::new(
        RewrittenSemilinearPayload {
            ctx: SemilinearContext {
                ir,
                vars,
                evaluator: Some(eval),
            },
        },
    )));

    let pr = cobra_passes::semilinear_reconstruct::run_semilinear_reconstruct(&item, &mut ctx)
        .expect("semilinear reconstruct pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate("semilinear_reconstruct_replay", cert);
}

fn replay_semilinear_flow_case(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let classification = Classification {
        semantic: SemanticClass::Semilinear,
        flags: StructuralFlag::HAS_BITWISE | StructuralFlag::HAS_ARITHMETIC,
    };
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let item = mk_classified_ast_item(expr, Provenance::Original, classification);

    let normalized = cobra_passes::semilinear_normalize::run_semilinear_normalize(&item, &mut ctx)
        .expect("semilinear normalize pass");
    assert_eq!(normalized.decision, PassDecision::Advance);

    let checked =
        cobra_passes::semilinear_check::run_semilinear_check(&normalized.next[0], &mut ctx)
            .expect("semilinear check pass");
    assert_eq!(checked.decision, PassDecision::Advance);

    let rewritten =
        cobra_passes::semilinear_rewrite::run_semilinear_rewrite(&checked.next[0], &mut ctx)
            .expect("semilinear rewrite pass");
    assert_eq!(rewritten.decision, PassDecision::Advance);

    let reconstructed = cobra_passes::semilinear_reconstruct::run_semilinear_reconstruct(
        &rewritten.next[0],
        &mut ctx,
    )
    .expect("semilinear reconstruct pass");
    assert_eq!(reconstructed.decision, PassDecision::SolvedCandidate);

    let cert = reconstructed.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn semilinear_flow_generated_certificate_replays_in_lean() {
    replay_semilinear_flow_case(
        "semilinear_flow_and_plus_var_replay",
        Expr::add(
            Expr::and(Expr::variable(0), Expr::constant(0xff)),
            Expr::variable(1),
        ),
        vec!["x".into(), "y".into()],
    );
}

#[test]
fn semilinear_family_generated_certificate_replays_in_lean() {
    replay_semilinear_flow_case(
        "semilinear_family_mask_plus_two_vars_replay",
        Expr::add(
            Expr::add(
                Expr::and(Expr::variable(0), Expr::constant(0xff)),
                Expr::variable(1),
            ),
            Expr::variable(2),
        ),
        vec!["x".into(), "y".into(), "z".into()],
    );
    replay_semilinear_flow_case(
        "semilinear_family_swapped_mask_replay",
        Expr::add(
            Expr::and(Expr::variable(1), Expr::constant(0xff)),
            Expr::variable(0),
        ),
        vec!["x".into(), "y".into()],
    );
}

#[test]
fn atom_simplifier_constant_fold_generated_certificate_replays_in_lean() {
    let original = Expr::and(Expr::constant(3), Expr::constant(1));
    let (simplified, cert) =
        cobra_passes::atom_simplifier::simplify_atom_certified(original.clone_tree(), 64);
    assert_eq!(*simplified, *Expr::constant(1));
    let cert = cert.expect("constant fold endpoint certificate");
    assert_eq!(cert.steps.len(), 1);
    assert_eq!(cert.steps[0].theorem, LeanTheorem::Const3And1_64);
    assert!(cert.matches_endpoints(64, &original, &simplified));
    replay_endpoint_certificate("atom_simplifier_constant_fold_replay", &cert);
}

#[test]
fn residual_recombine_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned()];
    let expr = Expr::variable(0);
    let eval = Evaluator::from_expr(&expr, 64);
    let residual = RemainderStatePayload {
        origin: RemainderOrigin::PolynomialCore,
        prefix_expr: Expr::constant(0),
        prefix_degree: 0,
        remainder_eval: eval.clone(),
        source_sig: vec![0, 1],
        remainder_sig: vec![0, 1],
        remainder_elim: EliminationResult::default(),
        remainder_support: vec![0],
        is_boolean_null: false,
        degree_floor: 0,
        target: RemainderTargetContext {
            eval,
            vars: vars.clone(),
            remap_support: Vec::new(),
        },
    };
    let parent = WorkItem::new(StateData::Remainder(Box::new(residual.clone())));
    let ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);

    let pr = cobra_passes::residual_common::try_recombine_and_emit(
        &residual,
        Expr::variable(0),
        &vars,
        &parent,
        &ctx,
        PassId::ResidualPolyRecovery,
        ResidualSolverKind::PolynomialRecovery,
    )
    .expect("residual recombine pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate("residual_recombine_replay", cert);
}

#[test]
fn residual_recombine_context_target_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned(), "y".to_owned()];
    let target = Expr::add(Expr::variable(0), Expr::variable(1));
    let prefix = Expr::variable(0);
    let residual_expr = Expr::variable(1);
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&target, 64));
    let residual_eval = Evaluator::from_expr(&residual_expr, 64);
    let residual = RemainderStatePayload {
        origin: RemainderOrigin::PolynomialCore,
        prefix_expr: prefix,
        prefix_degree: 1,
        remainder_eval: residual_eval,
        source_sig: evaluate_boolean_signature(&target, 2, 64),
        remainder_sig: evaluate_boolean_signature(&residual_expr, 2, 64),
        remainder_elim: EliminationResult {
            reduced_sig: vec![0, 1],
            real_vars: vec!["y".to_owned()],
            spurious_vars: vec!["x".to_owned()],
        },
        remainder_support: vec![1],
        is_boolean_null: false,
        degree_floor: 0,
        target: RemainderTargetContext {
            eval: Evaluator::default(),
            vars: Vec::new(),
            remap_support: vec![1],
        },
    };
    let parent = WorkItem::new(StateData::Remainder(Box::new(residual.clone())));

    let pr = cobra_passes::residual_common::try_recombine_and_emit(
        &residual,
        Expr::variable(0),
        &["y".to_owned()],
        &parent,
        &ctx,
        PassId::ResidualPolyRecovery,
        ResidualSolverKind::PolynomialRecovery,
    )
    .expect("residual recombine with context target");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate("residual_recombine_context_target_replay", cert);
}

#[test]
fn residual_recombine_remapped_vars_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned(), "y".to_owned(), "z".to_owned()];
    let target = Expr::add(Expr::variable(0), Expr::variable(2));
    let prefix = Expr::variable(0);
    let residual_expr = Expr::variable(2);
    let target_eval = Evaluator::from_expr(&target, 64);
    let residual_eval = Evaluator::from_expr(&residual_expr, 64);
    let source_sig = evaluate_boolean_signature(&target, 3, 64);
    let residual_sig = evaluate_boolean_signature(&residual_expr, 3, 64);
    let residual = RemainderStatePayload {
        origin: RemainderOrigin::PolynomialCore,
        prefix_expr: prefix,
        prefix_degree: 1,
        remainder_eval: residual_eval,
        source_sig,
        remainder_sig: residual_sig,
        remainder_elim: EliminationResult {
            reduced_sig: vec![0, 1],
            real_vars: vec!["z".to_owned()],
            spurious_vars: vec!["x".to_owned(), "y".to_owned()],
        },
        remainder_support: vec![2],
        is_boolean_null: false,
        degree_floor: 0,
        target: RemainderTargetContext {
            eval: target_eval,
            vars: vars.clone(),
            remap_support: vec![2],
        },
    };
    let parent = WorkItem::new(StateData::Remainder(Box::new(residual.clone())));
    let ctx = OrchestratorContext::new(Options::default(), vars, 64);

    let pr = cobra_passes::residual_common::try_recombine_and_emit(
        &residual,
        Expr::variable(0),
        &["z".to_owned()],
        &parent,
        &ctx,
        PassId::ResidualPolyRecovery,
        ResidualSolverKind::PolynomialRecovery,
    )
    .expect("residual recombine with remapped vars");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate("residual_recombine_remapped_vars_replay", cert);
}

#[test]
fn residual_poly_recovery_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned()];
    let target = Expr::mul(Expr::variable(0), Expr::variable(0));
    let residual = mk_remainder_payload(
        &target,
        Expr::constant(0),
        &target,
        vars.clone(),
        RemainderOrigin::PolynomialCore,
        false,
        2,
    );
    let item = WorkItem::new(StateData::Remainder(Box::new(residual)));
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);

    let pr = cobra_passes::residual_poly_recovery::run_residual_poly_recovery(&item, &mut ctx)
        .expect("residual poly recovery pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate("residual_poly_recovery_replay", cert);
}

fn replay_residual_poly_case(name: &str, target: Box<Expr>, vars: Vec<String>, degree_floor: u8) {
    let residual = mk_remainder_payload(
        &target,
        Expr::constant(0),
        &target,
        vars.clone(),
        RemainderOrigin::PolynomialCore,
        false,
        degree_floor,
    );
    let item = WorkItem::new(StateData::Remainder(Box::new(residual)));
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);

    let pr = cobra_passes::residual_poly_recovery::run_residual_poly_recovery(&item, &mut ctx)
        .expect("residual poly recovery pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate, "{name}");

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn residual_poly_recovery_family_generated_certificate_replays_in_lean() {
    replay_residual_poly_case(
        "residual_poly_recovery_cubic_replay",
        Expr::mul(
            Expr::mul(Expr::variable(0), Expr::variable(0)),
            Expr::variable(0),
        ),
        vec!["x".into()],
        3,
    );
    replay_residual_poly_case(
        "residual_poly_recovery_two_var_quadratic_replay",
        Expr::add(
            Expr::add(
                Expr::mul(
                    Expr::constant(2),
                    Expr::mul(Expr::variable(0), Expr::variable(1)),
                ),
                Expr::variable(0),
            ),
            Expr::constant(3),
        ),
        vec!["x".into(), "y".into()],
        2,
    );
}

#[test]
fn residual_ghost_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned(), "y".to_owned()];
    let target = Expr::mul(Expr::variable(0), Expr::variable(1));
    let prefix = Expr::and(Expr::variable(0), Expr::variable(1));
    let residual_expr = Expr::add(target.clone_tree(), Expr::neg(prefix.clone_tree()));
    let residual = mk_remainder_payload(
        &residual_expr,
        prefix,
        &target,
        vars.clone(),
        RemainderOrigin::ProductCore,
        true,
        0,
    );
    let item = WorkItem::new(StateData::Remainder(Box::new(residual)));
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);

    let pr = cobra_passes::residual_ghost::run_residual_ghost(&item, &mut ctx)
        .expect("residual ghost pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate("residual_ghost_replay", cert);
}

#[test]
fn prepare_direct_remainder_recombine_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned(), "y".to_owned()];
    let mul_xy = Expr::mul(Expr::variable(0), Expr::variable(1));
    let and_xy = Expr::and(Expr::variable(0), Expr::variable(1));
    let expr = Expr::add(mul_xy, Expr::neg(and_xy));
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let item = mk_ast_item(expr.clone_tree(), Provenance::Original);

    let prepared =
        cobra_passes::prepare_direct_remainder::run_prepare_direct_remainder(&item, &mut ctx)
            .expect("prepare direct remainder pass");
    assert_eq!(prepared.decision, PassDecision::Advance);

    let StateData::Remainder(residual) = &prepared.next[0].payload else {
        panic!("expected direct remainder payload");
    };
    let solved = cobra_passes::residual_common::try_recombine_and_emit(
        residual,
        expr,
        &ctx.original_vars,
        &prepared.next[0],
        &ctx,
        PassId::PrepareDirectRemainder,
        ResidualSolverKind::GhostResidual,
    )
    .expect("direct remainder recombine");
    assert_eq!(solved.decision, PassDecision::SolvedCandidate);

    let cert = solved.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate("prepare_direct_remainder_recombine_replay", cert);
}

fn replay_prepare_direct_remainder_ghost_flow(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let mut item = mk_ast_item(expr, Provenance::Original);
    item.metadata.lean_certificate = Some(LeanCertificate::new(
        64,
        Expr::variable(0),
        Expr::variable(0),
    ));
    item.metadata.lean_signature_certificate =
        LeanSignatureCertificate::new(64, 1, vec![0, 1], Expr::variable(0));

    let prepared =
        cobra_passes::prepare_direct_remainder::run_prepare_direct_remainder(&item, &mut ctx)
            .expect("prepare direct remainder pass");
    assert_eq!(prepared.decision, PassDecision::Advance, "{name}");
    assert_eq!(prepared.next.len(), 1, "{name}");
    assert!(
        matches!(prepared.next[0].payload, StateData::Remainder(_)),
        "{name}"
    );
    assert!(
        prepared.next[0].metadata.lean_certificate.is_none(),
        "{name}"
    );
    assert!(
        prepared.next[0]
            .metadata
            .lean_signature_certificate
            .is_none(),
        "{name}"
    );

    let solved = cobra_passes::residual_ghost::run_residual_ghost(&prepared.next[0], &mut ctx)
        .expect("residual ghost pass after direct remainder");
    assert_eq!(solved.decision, PassDecision::SolvedCandidate, "{name}");

    let cert = solved.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn prepare_direct_remainder_ghost_flow_generated_certificate_replays_in_lean() {
    replay_prepare_direct_remainder_ghost_flow(
        "prepare_direct_remainder_ghost_mul_and_replay",
        Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::neg(Expr::and(Expr::variable(0), Expr::variable(1))),
        ),
        vec!["x".into(), "y".into()],
    );
    replay_prepare_direct_remainder_ghost_flow(
        "prepare_direct_remainder_ghost_scaled_mul_and_replay",
        Expr::add(
            Expr::mul(
                Expr::constant(3),
                Expr::mul(Expr::variable(0), Expr::variable(1)),
            ),
            Expr::neg(Expr::mul(
                Expr::constant(3),
                Expr::and(Expr::variable(0), Expr::variable(1)),
            )),
        ),
        vec!["x".into(), "y".into()],
    );
    replay_prepare_direct_remainder_ghost_flow(
        "prepare_direct_remainder_ghost_shifted_vars_replay",
        Expr::add(
            Expr::mul(Expr::variable(1), Expr::variable(2)),
            Expr::neg(Expr::and(Expr::variable(1), Expr::variable(2))),
        ),
        vec!["x".into(), "y".into(), "z".into()],
    );
}

fn replay_residual_ghost_case(
    name: &str,
    residual_expr: Box<Expr>,
    prefix: Box<Expr>,
    target: Box<Expr>,
) {
    let vars = vec!["x".to_owned(), "y".to_owned()];
    let residual = mk_remainder_payload(
        &residual_expr,
        prefix,
        &target,
        vars.clone(),
        RemainderOrigin::ProductCore,
        true,
        0,
    );
    let item = WorkItem::new(StateData::Remainder(Box::new(residual)));
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);

    let pr = cobra_passes::residual_ghost::run_residual_ghost(&item, &mut ctx)
        .expect("residual ghost pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate, "{name}");

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn residual_ghost_family_generated_certificate_replays_in_lean() {
    let mul_xy = Expr::mul(Expr::variable(0), Expr::variable(1));
    let and_xy = Expr::and(Expr::variable(0), Expr::variable(1));
    let ghost_xy = Expr::add(mul_xy.clone_tree(), Expr::neg(and_xy.clone_tree()));
    replay_residual_ghost_case(
        "residual_ghost_basic_mul_sub_and_replay",
        ghost_xy.clone_tree(),
        and_xy.clone_tree(),
        mul_xy.clone_tree(),
    );

    let scaled_ghost = Expr::mul(Expr::constant(3), ghost_xy.clone_tree());
    replay_residual_ghost_case(
        "residual_ghost_scaled_mul_sub_and_replay",
        scaled_ghost.clone_tree(),
        and_xy.clone_tree(),
        Expr::add(and_xy, scaled_ghost),
    );
}

#[test]
fn residual_factored_ghost_generated_certificate_replays_in_lean() {
    let ghost = Expr::add(
        Expr::mul(Expr::variable(0), Expr::variable(1)),
        Expr::neg(Expr::and(Expr::variable(0), Expr::variable(1))),
    );
    let residual_expr = Expr::mul(Expr::constant(3), ghost);
    let prefix = Expr::and(Expr::variable(0), Expr::variable(1));
    let target = Expr::add(prefix.clone_tree(), residual_expr.clone_tree());
    replay_residual_factored_ghost_case(
        "residual_factored_ghost_replay",
        residual_expr,
        prefix,
        target,
        vec!["x".into(), "y".into()],
        false,
    );
}

fn replay_residual_factored_ghost_case(
    name: &str,
    residual_expr: Box<Expr>,
    prefix: Box<Expr>,
    target: Box<Expr>,
    vars: Vec<String>,
    escalated: bool,
) {
    let residual = mk_remainder_payload(
        &residual_expr,
        prefix,
        &target,
        vars.clone(),
        RemainderOrigin::ProductCore,
        true,
        0,
    );
    let item = WorkItem::new(StateData::Remainder(Box::new(residual)));
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);

    let pr = if escalated {
        cobra_passes::residual_factored_ghost::run_residual_factored_ghost_escalated(
            &item, &mut ctx,
        )
    } else {
        cobra_passes::residual_factored_ghost::run_residual_factored_ghost(&item, &mut ctx)
    }
    .expect("residual factored ghost pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate, "{name}");

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn residual_factored_ghost_family_generated_certificate_replays_in_lean() {
    let mul_xy = Expr::mul(Expr::variable(0), Expr::variable(1));
    let and_xy = Expr::and(Expr::variable(0), Expr::variable(1));
    let ghost = Expr::add(mul_xy, Expr::neg(and_xy.clone_tree()));

    let linear_factor = Expr::add(Expr::variable(0), Expr::variable(1));
    let linear_residual = Expr::mul(linear_factor, ghost.clone_tree());
    replay_residual_factored_ghost_case(
        "residual_factored_ghost_escalated_linear_factor_replay",
        linear_residual.clone_tree(),
        and_xy.clone_tree(),
        Expr::add(and_xy.clone_tree(), linear_residual),
        vec!["x".into(), "y".into()],
        true,
    );

    let quadratic_factor = Expr::mul(Expr::variable(0), Expr::variable(0));
    let quadratic_residual = Expr::mul(quadratic_factor, ghost);
    replay_residual_factored_ghost_case(
        "residual_factored_ghost_escalated_quadratic_factor_replay",
        quadratic_residual.clone_tree(),
        and_xy.clone_tree(),
        Expr::add(and_xy, quadratic_residual),
        vec!["x".into(), "y".into()],
        true,
    );
}

#[test]
fn residual_template_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned(), "y".to_owned(), "z".to_owned()];
    let target = Expr::xor(
        Expr::and(Expr::variable(0), Expr::variable(1)),
        Expr::or(Expr::variable(0), Expr::variable(2)),
    );
    let residual = mk_remainder_payload(
        &target,
        Expr::constant(0),
        &target,
        vars.clone(),
        RemainderOrigin::TemplateCore,
        false,
        0,
    );
    let item = WorkItem::new(StateData::Remainder(Box::new(residual)));
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);

    let pr = cobra_passes::residual_template::run_residual_template(&item, &mut ctx)
        .expect("residual template pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate("residual_template_replay", cert);
}

fn replay_residual_template_case(
    name: &str,
    target: Box<Expr>,
    vars: Vec<String>,
    origin: RemainderOrigin,
) {
    let residual = mk_remainder_payload(
        &target,
        Expr::constant(0),
        &target,
        vars.clone(),
        origin,
        false,
        0,
    );
    let item = WorkItem::new(StateData::Remainder(Box::new(residual)));
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);

    let pr = cobra_passes::residual_template::run_residual_template(&item, &mut ctx)
        .expect("residual template pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate, "{name}");

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn residual_template_family_generated_certificate_replays_in_lean() {
    replay_residual_template_case(
        "residual_template_direct_atom_replay",
        Expr::variable(0),
        vec!["x".into()],
        RemainderOrigin::TemplateCore,
    );
    replay_residual_template_case(
        "residual_template_layer1_xor_replay",
        Expr::xor(Expr::variable(0), Expr::variable(1)),
        vec!["x".into(), "y".into()],
        RemainderOrigin::TemplateCore,
    );
    replay_residual_template_case(
        "residual_template_layer1_and_replay",
        Expr::and(Expr::variable(0), Expr::variable(1)),
        vec!["x".into(), "y".into()],
        RemainderOrigin::TemplateCore,
    );
    replay_residual_template_case(
        "residual_template_layer2_xor_and_or_replay",
        Expr::xor(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::or(Expr::variable(0), Expr::variable(2)),
        ),
        vec!["x".into(), "y".into(), "z".into()],
        RemainderOrigin::TemplateCore,
    );
    replay_residual_template_case(
        "residual_template_unary_not_wrap_replay",
        Expr::not(Expr::xor(Expr::variable(0), Expr::variable(1))),
        vec!["x".into(), "y".into()],
        RemainderOrigin::TemplateCore,
    );
}

#[test]
fn bitwise_compose_generated_certificate_replays_in_lean() {
    replay_bitwise_compose_case(
        "bitwise_compose_replay",
        GateKind::Xor,
        0,
        Expr::xor(Expr::variable(0), Expr::variable(1)),
        vec![0, 1, 1, 0],
    );
}

fn replay_bitwise_compose_case(
    name: &str,
    gate: GateKind,
    add_coeff: u64,
    parent_expr: Box<Expr>,
    parent_signature: Vec<u64>,
) {
    replay_bitwise_compose_custom_case(
        name,
        gate,
        add_coeff,
        vec!["x".into(), "y".into()],
        Expr::variable(0),
        vec!["y".into()],
        vec![0, 1],
        vec![1],
        parent_expr,
        parent_signature,
    );
}

#[allow(clippy::too_many_arguments)]
fn replay_bitwise_compose_custom_case(
    name: &str,
    gate: GateKind,
    add_coeff: u64,
    parent_vars: Vec<String>,
    child_expr: Box<Expr>,
    child_vars: Vec<String>,
    child_signature: Vec<u64>,
    active_context_indices: Vec<u32>,
    parent_expr: Box<Expr>,
    parent_signature: Vec<u64>,
) {
    let mut ctx = OrchestratorContext::new(Options::default(), parent_vars.clone(), 64);
    let parent_gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    let child_gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);

    {
        let child = ctx.competition_groups.get_mut(&child_gid).unwrap();
        child.best = Some(CandidateRecord {
            expr: child_expr.clone_tree(),
            cost: cobra_core::expr_cost::compute_cost(&child_expr).cost,
            verification: VerificationState::Verified,
            real_vars: child_vars,
            source_pass: PassId::SignaturePatternMatch,
            needs_original_space_verification: false,
            sig_vector: child_signature,
            lean_certificate: None,
            lean_signature_certificate: None,
        });
        child.continuation = Some(ContinuationData::BitwiseCompose(Box::new(
            BitwiseComposeCont {
                var_k: 0,
                gate,
                add_coeff,
                active_context_indices,
                parent_group_id: parent_gid,
                parent_eval: Some(Evaluator::from_expr(&parent_expr, 64)),
                parent_signature,
                parent_real_vars: parent_vars.clone(),
                parent_original_indices: (0..parent_vars.len() as u32).collect(),
                parent_num_vars: parent_vars.len() as u32,
                parent_needs_original_space_verification: false,
            },
        )));
    }

    let pr = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(child_gid),
        &mut ctx,
    )
    .expect("resolve bitwise composition");
    assert_eq!(pr.decision, PassDecision::Advance);

    let best = ctx.competition_groups[&parent_gid]
        .best
        .as_ref()
        .expect("parent candidate");
    let cert = best
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn bitwise_compose_without_parent_eval_generated_certificate_replays_in_lean() {
    let parent_vars = vec!["x".to_owned(), "y".to_owned()];
    let parent_expr = Expr::xor(Expr::variable(0), Expr::variable(1));
    let parent_signature = evaluate_boolean_signature(&parent_expr, 2, 64);
    let mut ctx = OrchestratorContext::new(Options::default(), parent_vars.clone(), 64);
    let parent_gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    let child_gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);

    {
        let child = ctx.competition_groups.get_mut(&child_gid).unwrap();
        child.best = Some(CandidateRecord {
            expr: Expr::variable(0),
            cost: cobra_core::expr_cost::ExprCost::default(),
            verification: VerificationState::Verified,
            real_vars: vec!["y".into()],
            source_pass: PassId::SignaturePatternMatch,
            needs_original_space_verification: false,
            sig_vector: vec![0, 1],
            lean_certificate: None,
            lean_signature_certificate: None,
        });
        child.continuation = Some(ContinuationData::BitwiseCompose(Box::new(
            BitwiseComposeCont {
                var_k: 0,
                gate: GateKind::Xor,
                add_coeff: 0,
                active_context_indices: vec![1],
                parent_group_id: parent_gid,
                parent_eval: None,
                parent_signature: parent_signature.clone(),
                parent_real_vars: parent_vars.clone(),
                parent_original_indices: vec![0, 1],
                parent_num_vars: 2,
                parent_needs_original_space_verification: false,
            },
        )));
    }

    let pr = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(child_gid),
        &mut ctx,
    )
    .expect("resolve bitwise composition without parent evaluator");
    assert_eq!(pr.decision, PassDecision::Advance);

    let best = ctx.competition_groups[&parent_gid]
        .best
        .as_ref()
        .expect("parent candidate");
    assert_eq!(best.verification, VerificationState::Unverified);
    let cert = best
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    assert!(cert.matches_signature(64, 2, &parent_signature, &parent_expr));
    replay_signature_certificate("bitwise_compose_without_parent_eval_replay", cert);
}

#[test]
fn bitwise_compose_family_generated_certificate_replays_in_lean() {
    replay_bitwise_compose_case(
        "bitwise_compose_and_replay",
        GateKind::And,
        0,
        Expr::and(Expr::variable(0), Expr::variable(1)),
        vec![0, 0, 0, 1],
    );
    replay_bitwise_compose_case(
        "bitwise_compose_or_replay",
        GateKind::Or,
        0,
        Expr::or(Expr::variable(0), Expr::variable(1)),
        vec![0, 1, 1, 1],
    );
    replay_bitwise_compose_case(
        "bitwise_compose_add_replay",
        GateKind::Add,
        1,
        Expr::add(Expr::variable(0), Expr::variable(1)),
        vec![0, 1, 1, 2],
    );
    let parent_expr = Expr::xor(
        Expr::variable(0),
        Expr::and(Expr::variable(1), Expr::variable(2)),
    );
    let parent_signature = evaluate_boolean_signature(&parent_expr, 3, 64);
    replay_bitwise_compose_custom_case(
        "bitwise_compose_remapped_child_replay",
        GateKind::Xor,
        0,
        vec!["x".into(), "y".into(), "z".into()],
        Expr::and(Expr::variable(0), Expr::variable(1)),
        vec!["y".into(), "z".into()],
        vec![0, 0, 0, 1],
        vec![1, 2],
        parent_expr,
        parent_signature,
    );
}

#[test]
fn signature_bitwise_decompose_direct_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned()];
    let sig = vec![0, 1];
    let expr = Expr::variable(0);
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let mut item = mk_signature_item(sig, vars);
    let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    item.group_id = Some(group_id);

    let pr =
        cobra_passes::signature_bitwise_decompose::run_signature_bitwise_decompose(&item, &mut ctx)
            .expect("signature bitwise decompose pass");
    assert_eq!(pr.decision, PassDecision::Advance);

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate("signature_bitwise_decompose_direct_replay", cert);
}

fn replay_signature_bitwise_decompose_child_flow(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let sig = evaluate_boolean_signature(&expr, vars.len() as u32, 64);
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let mut item = mk_signature_item(sig, vars);
    let parent_group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    item.group_id = Some(parent_group_id);

    let decomposed =
        cobra_passes::signature_bitwise_decompose::run_signature_bitwise_decompose(&item, &mut ctx)
            .expect("signature bitwise decompose pass");
    assert_eq!(decomposed.decision, PassDecision::Advance, "{name}");

    let mut resolved_child = false;
    for child in &decomposed.next {
        assert!(matches!(child.payload, StateData::Signature(_)), "{name}");
        assert!(child.metadata.lean_certificate.is_none(), "{name}");
        assert!(
            child.metadata.lean_signature_certificate.is_none(),
            "{name}"
        );
        let child_group_id = child.group_id.expect("child group id");

        let matched =
            cobra_passes::signature_pattern_match::run_signature_pattern_match(child, &mut ctx)
                .expect("signature pattern pass for bitwise child");
        if matched.decision != PassDecision::Advance {
            continue;
        }

        let resolved = cobra_passes::resolve_competition::run_resolve_competition(
            &mk_resolve_item(child_group_id),
            &mut ctx,
        )
        .expect("resolve bitwise child");
        assert_eq!(resolved.decision, PassDecision::Advance, "{name}");
        resolved_child = true;
        if ctx.competition_groups[&parent_group_id].best.is_some() {
            break;
        }
    }

    assert!(
        resolved_child,
        "{name}: expected at least one child signature to solve"
    );
    let cert = ctx.competition_groups[&parent_group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn signature_bitwise_decompose_child_flow_generated_certificate_replays_in_lean() {
    replay_signature_bitwise_decompose_child_flow(
        "signature_bitwise_decompose_child_xor_and_replay",
        Expr::xor(
            Expr::variable(0),
            Expr::and(Expr::variable(1), Expr::variable(2)),
        ),
        vec!["x".into(), "y".into(), "z".into()],
    );
    replay_signature_bitwise_decompose_child_flow(
        "signature_bitwise_decompose_child_or_xor_replay",
        Expr::or(
            Expr::variable(0),
            Expr::xor(Expr::variable(1), Expr::variable(2)),
        ),
        vec!["x".into(), "y".into(), "z".into()],
    );
}

#[test]
fn resolve_none_carry_generated_certificate_replays_in_lean() {
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    let expr = Expr::add(Expr::variable(0), Expr::variable(1));
    let sig = evaluate_boolean_signature(&expr, 2, 64);
    let cert = LeanSignatureCertificate::new(64, 2, sig.clone(), expr.clone_tree())
        .expect("signature certificate");
    ctx.competition_groups.get_mut(&group_id).unwrap().best = Some(CandidateRecord {
        expr: expr.clone_tree(),
        cost: cobra_core::expr_cost::compute_cost(&expr).cost,
        verification: VerificationState::Verified,
        real_vars: vec!["x".into(), "y".into()],
        source_pass: PassId::SignaturePatternMatch,
        needs_original_space_verification: false,
        sig_vector: sig.clone(),
        lean_certificate: None,
        lean_signature_certificate: Some(cert),
    });

    let pr = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(group_id),
        &mut ctx,
    )
    .expect("resolve none continuation");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("carried signature certificate");
    assert!(cert.matches_signature(64, 2, &sig, &expr));
    replay_signature_certificate("resolve_none_carry_replay", cert);
}

#[test]
fn resolve_none_endpoint_carry_generated_certificate_replays_in_lean() {
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    let original = Expr::add(
        Expr::or(Expr::variable(0), Expr::variable(1)),
        Expr::neg(Expr::and(Expr::variable(0), Expr::variable(1))),
    );
    let simplified = Expr::xor(Expr::variable(0), Expr::variable(1));
    let sig = evaluate_boolean_signature(&simplified, 2, 64);
    let cert =
        LeanCertificate::try_single_rewrite_between_64(64, original, simplified.clone_tree())
            .expect("endpoint certificate");
    ctx.competition_groups.get_mut(&group_id).unwrap().best = Some(CandidateRecord {
        expr: simplified.clone_tree(),
        cost: cobra_core::expr_cost::compute_cost(&simplified).cost,
        verification: VerificationState::Verified,
        real_vars: vec!["x".into(), "y".into()],
        source_pass: PassId::AtomIdentityRewrite,
        needs_original_space_verification: false,
        sig_vector: sig,
        lean_certificate: Some(cert),
        lean_signature_certificate: None,
    });

    let pr = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(group_id),
        &mut ctx,
    )
    .expect("resolve none endpoint continuation");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_certificate
        .as_ref()
        .expect("carried endpoint certificate");
    replay_endpoint_certificate("resolve_none_endpoint_carry_replay", cert);
}

#[test]
fn hybrid_compose_generated_certificate_replays_in_lean() {
    replay_hybrid_compose_case(
        "hybrid_compose_replay",
        ExtractOp::Xor,
        Expr::xor(Expr::variable(0), Expr::variable(1)),
        vec![0, 1, 1, 0],
    );
}

fn replay_hybrid_compose_case(
    name: &str,
    op: ExtractOp,
    parent_expr: Box<Expr>,
    parent_signature: Vec<u64>,
) {
    replay_hybrid_compose_custom_case(
        name,
        op,
        0,
        vec!["x".into(), "y".into()],
        Expr::variable(1),
        vec![0, 0, 1, 1],
        parent_expr,
        parent_signature,
    );
}

#[allow(clippy::too_many_arguments)]
fn replay_hybrid_compose_custom_case(
    name: &str,
    op: ExtractOp,
    var_k: u32,
    parent_vars: Vec<String>,
    child_expr: Box<Expr>,
    child_signature: Vec<u64>,
    parent_expr: Box<Expr>,
    parent_signature: Vec<u64>,
) {
    let mut ctx = OrchestratorContext::new(Options::default(), parent_vars.clone(), 64);
    let parent_gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    let child_gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);

    {
        let child = ctx.competition_groups.get_mut(&child_gid).unwrap();
        child.best = Some(CandidateRecord {
            expr: child_expr.clone_tree(),
            cost: cobra_core::expr_cost::compute_cost(&child_expr).cost,
            verification: VerificationState::Verified,
            real_vars: parent_vars.clone(),
            source_pass: PassId::SignaturePatternMatch,
            needs_original_space_verification: false,
            sig_vector: child_signature,
            lean_certificate: Some(cobra_orchestrator::LeanCertificate::new(
                64,
                child_expr.clone_tree(),
                child_expr,
            )),
            lean_signature_certificate: None,
        });
        child.continuation = Some(ContinuationData::HybridCompose(Box::new(
            HybridComposeCont {
                var_k,
                op,
                parent_group_id: parent_gid,
                parent_eval: Some(Evaluator::from_expr(&parent_expr, 64)),
                parent_signature,
                parent_real_vars: parent_vars.clone(),
                parent_original_indices: (0..parent_vars.len() as u32).collect(),
                parent_num_vars: parent_vars.len() as u32,
                parent_needs_original_space_verification: false,
            },
        )));
    }

    let pr = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(child_gid),
        &mut ctx,
    )
    .expect("resolve hybrid composition");
    assert_eq!(pr.decision, PassDecision::Advance);

    let best = ctx.competition_groups[&parent_gid]
        .best
        .as_ref()
        .expect("parent candidate");
    let cert = best
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn hybrid_compose_without_parent_eval_generated_certificate_replays_in_lean() {
    let parent_vars = vec!["x".to_owned(), "y".to_owned()];
    let parent_expr = Expr::xor(Expr::variable(0), Expr::variable(1));
    let parent_signature = evaluate_boolean_signature(&parent_expr, 2, 64);
    let mut ctx = OrchestratorContext::new(Options::default(), parent_vars.clone(), 64);
    let parent_gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    let child_gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);

    {
        let child = ctx.competition_groups.get_mut(&child_gid).unwrap();
        child.best = Some(CandidateRecord {
            expr: Expr::variable(1),
            cost: cobra_core::expr_cost::ExprCost::default(),
            verification: VerificationState::Verified,
            real_vars: parent_vars.clone(),
            source_pass: PassId::SignaturePatternMatch,
            needs_original_space_verification: false,
            sig_vector: vec![0, 0, 1, 1],
            lean_certificate: None,
            lean_signature_certificate: None,
        });
        child.continuation = Some(ContinuationData::HybridCompose(Box::new(
            HybridComposeCont {
                var_k: 0,
                op: ExtractOp::Xor,
                parent_group_id: parent_gid,
                parent_eval: None,
                parent_signature: parent_signature.clone(),
                parent_real_vars: parent_vars.clone(),
                parent_original_indices: vec![0, 1],
                parent_num_vars: 2,
                parent_needs_original_space_verification: false,
            },
        )));
    }

    let pr = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(child_gid),
        &mut ctx,
    )
    .expect("resolve hybrid composition without parent evaluator");
    assert_eq!(pr.decision, PassDecision::Advance);

    let best = ctx.competition_groups[&parent_gid]
        .best
        .as_ref()
        .expect("parent candidate");
    assert_eq!(best.verification, VerificationState::Unverified);
    let cert = best
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    assert!(cert.matches_signature(64, 2, &parent_signature, &parent_expr));
    replay_signature_certificate("hybrid_compose_without_parent_eval_replay", cert);
}

#[test]
fn hybrid_compose_family_generated_certificate_replays_in_lean() {
    replay_hybrid_compose_case(
        "hybrid_compose_add_replay",
        ExtractOp::Add,
        Expr::add(Expr::variable(0), Expr::variable(1)),
        vec![0, 1, 1, 2],
    );
    let residual = Expr::xor(Expr::variable(0), Expr::variable(2));
    let parent_expr = Expr::xor(Expr::variable(1), residual.clone_tree());
    let parent_signature = evaluate_boolean_signature(&parent_expr, 3, 64);
    let child_signature = evaluate_boolean_signature(&residual, 3, 64);
    replay_hybrid_compose_custom_case(
        "hybrid_compose_three_var_nonzero_k_replay",
        ExtractOp::Xor,
        1,
        vec!["x".into(), "y".into(), "z".into()],
        residual,
        child_signature,
        parent_expr,
        parent_signature,
    );
}

#[test]
fn signature_hybrid_decompose_flow_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned(), "y".to_owned()];
    let sig = vec![0, 1, 1, 0];
    let expr = Expr::xor(Expr::variable(0), Expr::variable(1));
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let mut item = mk_signature_item(sig, vars);
    let parent_group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    item.group_id = Some(parent_group_id);

    let pr =
        cobra_passes::signature_hybrid_decompose::run_signature_hybrid_decompose(&item, &mut ctx)
            .expect("signature hybrid decompose pass");
    assert_eq!(pr.decision, PassDecision::Advance);
    assert!(!pr.next.is_empty());

    for child in &pr.next {
        let StateData::Signature(child_sig) = &child.payload else {
            panic!("expected hybrid child signature");
        };
        let child_group_id = child.group_id.expect("child group id");
        assert!(child.metadata.lean_certificate.is_none());
        assert!(child.metadata.lean_signature_certificate.is_none());

        if child_sig.ctx.elimination.reduced_sig != vec![0, 0, 1, 1]
            && child_sig.ctx.elimination.reduced_sig != vec![0, 1, 0, 1]
        {
            continue;
        }

        let matched =
            cobra_passes::signature_pattern_match::run_signature_pattern_match(child, &mut ctx)
                .expect("signature pattern pass for hybrid child");
        if matched.decision != PassDecision::Advance {
            continue;
        }

        cobra_passes::resolve_competition::run_resolve_competition(
            &mk_resolve_item(child_group_id),
            &mut ctx,
        )
        .expect("resolve hybrid child");

        if ctx.competition_groups[&parent_group_id].best.is_some() {
            break;
        }
    }

    let cert = ctx.competition_groups[&parent_group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate("signature_hybrid_decompose_flow_replay", cert);
}

#[test]
fn lifted_substitute_generated_certificate_replays_in_lean() {
    replay_lifted_substitute_direct_case(
        "lifted_substitute_replay",
        vec!["x".into()],
        vec![LiftedBinding {
            kind: LiftedValueKind::ArithmeticAtom,
            outer_var_index: 1,
            subtree: Expr::xor(Expr::variable(0), Expr::constant(0)),
            structural_hash: 0,
            original_support: vec![0],
        }],
        vec!["x".into(), "v0".into()],
        Expr::variable(1),
        vec!["x".into(), "v0".into()],
        Expr::variable(0),
    );

    let x_plus_y = Expr::add(Expr::variable(0), Expr::variable(1));
    let z_xor_one = Expr::xor(Expr::variable(2), Expr::constant(1));
    replay_lifted_substitute_direct_case(
        "lifted_substitute_reduced_outer_multi_binding_replay",
        vec!["x".into(), "y".into(), "z".into()],
        vec![
            LiftedBinding {
                kind: LiftedValueKind::ArithmeticAtom,
                outer_var_index: 3,
                subtree: x_plus_y.clone_tree(),
                structural_hash: 0,
                original_support: vec![0, 1],
            },
            LiftedBinding {
                kind: LiftedValueKind::ArithmeticAtom,
                outer_var_index: 4,
                subtree: z_xor_one.clone_tree(),
                structural_hash: 0,
                original_support: vec![2],
            },
        ],
        vec!["x".into(), "y".into(), "z".into(), "v0".into(), "v1".into()],
        Expr::xor(Expr::variable(0), Expr::variable(1)),
        vec!["v0".into(), "v1".into()],
        Expr::xor(x_plus_y, z_xor_one),
    );
}

fn replay_lifted_substitute_direct_case(
    name: &str,
    original_vars: Vec<String>,
    bindings: Vec<LiftedBinding>,
    outer_vars: Vec<String>,
    winner_expr: Box<Expr>,
    winner_real_vars: Vec<String>,
    original_expr: Box<Expr>,
) {
    let mut ctx = OrchestratorContext::new(Options::default(), original_vars.clone(), 64);
    let source_sig = evaluate_boolean_signature(&original_expr, original_vars.len() as u32, 64);
    let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);

    {
        let group = ctx.competition_groups.get_mut(&group_id).unwrap();
        group.best = Some(CandidateRecord {
            expr: winner_expr.clone_tree(),
            cost: cobra_core::expr_cost::ExprCost::default(),
            verification: VerificationState::Verified,
            real_vars: winner_real_vars,
            source_pass: PassId::SignaturePatternMatch,
            needs_original_space_verification: false,
            sig_vector: Vec::new(),
            lean_certificate: None,
            lean_signature_certificate: None,
        });
        group.continuation = Some(ContinuationData::LiftedSubstitute(Box::new(
            LiftedSubstituteCont {
                bindings,
                outer_vars,
                original_var_count: original_vars.len() as u32,
                original_eval: Some(Evaluator::from_expr(&original_expr, 64)),
                original_vars,
                source_sig,
            },
        )));
    }

    let pr = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(group_id),
        &mut ctx,
    )
    .expect("resolve lifted substitute");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

fn replay_lifted_flow(name: &str, expr: Box<Expr>, vars: Vec<String>, repeated: bool) {
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let item = mk_ast_item(expr, Provenance::Original);

    let lift = if repeated {
        cobra_passes::lift_repeated_subexpressions::run_lift_repeated_subexpressions(
            &item, &mut ctx,
        )
        .expect("lift repeated subexpressions pass")
    } else {
        cobra_passes::lift_arithmetic_atoms::run_lift_arithmetic_atoms(&item, &mut ctx)
            .expect("lift arithmetic atoms pass")
    };
    assert_eq!(lift.decision, PassDecision::Advance);

    let prepared = cobra_passes::prepare_lifted_outer_solve::run_prepare_lifted_outer_solve(
        &lift.next[0],
        &mut ctx,
    )
    .expect("prepare lifted outer solve pass");
    assert_eq!(prepared.decision, PassDecision::Advance);

    let group_id = prepared.next[0].group_id.expect("lifted outer group id");
    let StateData::FoldedAst(outer_ast) = &prepared.next[0].payload else {
        panic!("expected lifted outer AST");
    };
    assert!(outer_ast.solve_ctx.is_some(), "{name}");
    if let Some(cert) = prepared.next[0].metadata.lean_certificate.as_ref() {
        replay_endpoint_certificate(&format!("{name}_prepared_outer"), cert);
    }
    assert!(
        prepared.next[0]
            .metadata
            .lean_signature_certificate
            .is_none(),
        "{name}"
    );

    let signature =
        cobra_passes::build_signature_state::run_build_signature_state(&prepared.next[0], &mut ctx)
            .expect("build signature state for lifted outer");
    assert_eq!(signature.decision, PassDecision::Advance, "{name}");
    assert_eq!(signature.next.len(), 1, "{name}");

    let matched = cobra_passes::signature_pattern_match::run_signature_pattern_match(
        &signature.next[0],
        &mut ctx,
    )
    .expect("signature pattern match lifted outer");
    if matched.decision != PassDecision::Advance {
        let prepared_coeff = cobra_passes::prepare_coeff_model::run_prepare_coeff_model(
            &signature.next[0],
            &mut ctx,
        )
        .expect("prepare coeff model for lifted outer");
        assert_eq!(prepared_coeff.decision, PassDecision::Advance, "{name}");
        let recovered =
            cobra_passes::signature_singleton_poly_recovery::run_signature_singleton_poly_recovery(
                &prepared_coeff.next[0],
                &mut ctx,
            )
            .expect("singleton poly recovery for lifted outer");
        assert_eq!(recovered.decision, PassDecision::Advance, "{name}");
    }

    let resolved = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(group_id),
        &mut ctx,
    )
    .expect("resolve lifted substitution");
    assert_eq!(resolved.decision, PassDecision::SolvedCandidate);

    let cert = resolved.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn lift_arithmetic_atoms_flow_generated_certificate_replays_in_lean() {
    let expr = Expr::and(
        Expr::add(Expr::variable(0), Expr::variable(1)),
        Expr::variable(2),
    );
    replay_lifted_flow(
        "lift_arithmetic_atoms_flow_replay",
        expr,
        vec!["x".into(), "y".into(), "z".into()],
        false,
    );
}

#[test]
fn lift_arithmetic_atoms_family_generated_certificate_replays_in_lean() {
    replay_lifted_flow(
        "lift_arithmetic_atoms_or_mul_shell_replay",
        Expr::or(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        ),
        vec!["x".into(), "y".into(), "z".into()],
        false,
    );
    replay_lifted_flow(
        "lift_arithmetic_atoms_xor_add_neg_shell_replay",
        Expr::xor(
            Expr::add(Expr::variable(0), Expr::neg(Expr::variable(1))),
            Expr::variable(2),
        ),
        vec!["x".into(), "y".into(), "z".into()],
        false,
    );
}

#[test]
fn prepare_lifted_outer_pattern_certificate_replays_in_lean() {
    let payload = cobra_orchestrator::LiftedSkeletonPayload {
        outer_expr: Expr::add(Expr::variable(2), Expr::constant(0)),
        outer_ctx: cobra_orchestrator::AstSolveContext {
            vars: vec!["x".into(), "y".into(), "v0".into()],
            evaluator: None,
            input_sig: vec![0, 0, 0, 1, 0, 0, 0, 1],
        },
        bindings: vec![LiftedBinding {
            kind: LiftedValueKind::ArithmeticAtom,
            outer_var_index: 2,
            subtree: Expr::add(Expr::variable(0), Expr::variable(1)),
            structural_hash: 0,
            original_support: vec![0, 1],
        }],
        original_var_count: 2,
        baseline_cost: cobra_core::expr_cost::ExprCost::default(),
        source_sig: Vec::new(),
        original_ctx: cobra_orchestrator::AstSolveContext::default(),
    };
    let item = WorkItem::new(StateData::LiftedSkeleton(Box::new(payload)));
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);

    let pr =
        cobra_passes::prepare_lifted_outer_solve::run_prepare_lifted_outer_solve(&item, &mut ctx)
            .expect("prepare lifted outer solve pass");
    assert_eq!(pr.decision, PassDecision::Advance);
    let cert = pr.next[0]
        .metadata
        .lean_certificate
        .as_ref()
        .expect("outer pattern simplification endpoint certificate");
    assert_eq!(cert.steps.len(), 1);
    assert_eq!(cert.steps[0].theorem, LeanTheorem::AddZero64);
    replay_endpoint_certificate("prepare_lifted_outer_pattern_replay", cert);
}

#[test]
fn lift_repeated_subexpressions_flow_generated_certificate_replays_in_lean() {
    let inner1 = Expr::or(
        Expr::xor(Expr::variable(0), Expr::variable(1)),
        Expr::variable(2),
    );
    let inner2 = Expr::or(
        Expr::xor(Expr::variable(0), Expr::variable(1)),
        Expr::variable(2),
    );
    replay_lifted_flow(
        "lift_repeated_subexpressions_flow_replay",
        Expr::add(inner1, inner2),
        vec!["x".into(), "y".into(), "z".into()],
        true,
    );
}

#[test]
fn lift_repeated_subexpressions_family_generated_certificate_replays_in_lean() {
    let add_l = Expr::add(
        Expr::and(Expr::variable(0), Expr::variable(1)),
        Expr::variable(2),
    );
    let add_r = Expr::add(
        Expr::and(Expr::variable(0), Expr::variable(1)),
        Expr::variable(2),
    );
    replay_lifted_flow(
        "lift_repeated_subexpressions_mul_repeated_add_replay",
        Expr::mul(add_l, add_r),
        vec!["x".into(), "y".into(), "z".into()],
        true,
    );

    let inner_l = Expr::xor(
        Expr::or(Expr::variable(0), Expr::variable(1)),
        Expr::variable(2),
    );
    let inner_r = Expr::xor(
        Expr::or(Expr::variable(0), Expr::variable(1)),
        Expr::variable(2),
    );
    replay_lifted_flow(
        "lift_repeated_subexpressions_and_repeated_xor_replay",
        Expr::and(inner_l, inner_r),
        vec!["x".into(), "y".into(), "z".into()],
        true,
    );
}

#[test]
fn operand_join_rewrite_generated_certificate_replays_in_lean() {
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    let original_mul = Expr::mul(
        Expr::and(Expr::variable(0), Expr::constant(u64::MAX)),
        Expr::variable(1),
    );
    let join = OperandJoinState {
        lhs_winner: None,
        rhs_winner: None,
        lhs_resolved: false,
        rhs_resolved: false,
        full_ast: original_mul.clone_tree(),
        original_mul: original_mul.clone_tree(),
        target_hash: expr_identity_hash(&original_mul),
        baseline_cost: cobra_core::expr_cost::compute_cost(&original_mul).cost,
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
    let join_id = create_join(
        &mut ctx.join_states,
        &mut ctx.next_join_id,
        JoinState::Operand(Box::new(join)),
    );
    let lhs_group = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    let rhs_group = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);

    {
        let lhs = ctx.competition_groups.get_mut(&lhs_group).unwrap();
        lhs.best = Some(CandidateRecord {
            expr: Expr::variable(0),
            cost: cobra_core::expr_cost::compute_cost(&Expr::variable(0)).cost,
            verification: VerificationState::Verified,
            real_vars: vec!["x".into(), "y".into()],
            source_pass: PassId::SignaturePatternMatch,
            needs_original_space_verification: false,
            sig_vector: vec![0, 1, 0, 1],
            lean_certificate: None,
            lean_signature_certificate: None,
        });
        lhs.continuation = Some(ContinuationData::OperandRewrite(OperandRewriteCont {
            join_id,
            role: OperandRole::Lhs,
        }));
    }
    ctx.competition_groups
        .get_mut(&rhs_group)
        .unwrap()
        .continuation = Some(ContinuationData::OperandRewrite(OperandRewriteCont {
        join_id,
        role: OperandRole::Rhs,
    }));

    let first = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(lhs_group),
        &mut ctx,
    )
    .expect("resolve lhs operand join");
    assert_eq!(first.decision, PassDecision::Advance);
    assert!(first.next.is_empty());

    let second = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(rhs_group),
        &mut ctx,
    )
    .expect("resolve rhs operand join");
    assert_eq!(second.decision, PassDecision::Advance);
    assert_eq!(second.next.len(), 1);

    let cert = second.next[0]
        .metadata
        .lean_certificate
        .as_ref()
        .expect("endpoint certificate");
    assert!(
        cert.steps
            .iter()
            .any(|step| step.theorem == LeanTheorem::AndAllOnes64),
        "operand join rewrite should carry the nested and-all-ones theorem"
    );
    replay_endpoint_certificate("operand_join_rewrite_replay", cert);
}

fn replay_operand_simplify_flow(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);
    let item = mk_ast_item(expr, Provenance::Original);

    let fanned = cobra_passes::operand_simplify::run_operand_simplify(&item, &mut ctx)
        .expect("operand simplify pass");
    assert_eq!(fanned.decision, PassDecision::Advance, "{name}");
    assert!(!fanned.next.is_empty(), "{name}");

    let mut final_cert = None;
    for child in &fanned.next {
        let group_id = child.group_id.expect("operand child group");
        let matched =
            cobra_passes::signature_pattern_match::run_signature_pattern_match(child, &mut ctx)
                .expect("signature pattern match operand child");
        assert_eq!(matched.decision, PassDecision::Advance, "{name}");

        let resolved = cobra_passes::resolve_competition::run_resolve_competition(
            &mk_resolve_item(group_id),
            &mut ctx,
        )
        .expect("resolve operand join");
        if let Some(cert) = resolved
            .next
            .first()
            .and_then(|item| item.metadata.lean_certificate.clone())
        {
            final_cert = Some(cert);
        }
    }

    let cert = final_cert.as_ref().expect("endpoint certificate");
    if name == "operand_simplify_lhs_flow_replay" {
        assert!(
            cert.steps
                .iter()
                .any(|step| step.theorem == LeanTheorem::AndAllOnes64),
            "{name} should carry the nested and-all-ones theorem"
        );
    }
    replay_endpoint_certificate(name, cert);
}

#[test]
fn operand_simplify_flow_generated_certificate_replays_in_lean() {
    replay_operand_simplify_flow(
        "operand_simplify_lhs_flow_replay",
        Expr::mul(
            Expr::and(Expr::variable(0), Expr::constant(u64::MAX)),
            Expr::variable(1),
        ),
        vec!["x".into(), "y".into()],
    );
}

#[test]
fn operand_simplify_family_generated_certificate_replays_in_lean() {
    replay_operand_simplify_flow(
        "operand_simplify_rhs_flow_replay",
        Expr::mul(
            Expr::variable(0),
            Expr::or(Expr::variable(1), Expr::constant(0)),
        ),
        vec!["x".into(), "y".into()],
    );
    replay_operand_simplify_flow(
        "operand_simplify_two_sided_flow_replay",
        Expr::mul(
            Expr::and(Expr::variable(0), Expr::constant(u64::MAX)),
            Expr::or(Expr::variable(1), Expr::constant(0)),
        ),
        vec!["x".into(), "y".into()],
    );
}

fn replay_product_join_rewrite_case(
    name: &str,
    vars: Vec<String>,
    original_expr: Box<Expr>,
    full_ast: Box<Expr>,
    replacement_x: Box<Expr>,
    replacement_y: Box<Expr>,
    resolve_y_first: bool,
    has_solve_ctx: bool,
) {
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    let source_sig = evaluate_boolean_signature(&full_ast, vars.len() as u32, 64);
    let join = ProductJoinState {
        x_winner: None,
        y_winner: None,
        x_resolved: false,
        y_resolved: false,
        original_expr: original_expr.clone_tree(),
        baseline_cost: cobra_core::expr_cost::compute_cost(&original_expr).cost,
        vars: vars.clone(),
        parent_group_id: None,
        has_solve_ctx,
        solve_ctx_vars: if has_solve_ctx {
            vars.clone()
        } else {
            Vec::new()
        },
        solve_ctx_evaluator: None,
        solve_ctx_input_sig: if has_solve_ctx {
            source_sig.clone()
        } else {
            Vec::new()
        },
        bitwidth: 64,
        parent_depth: 0,
        rewrite_gen: 0,
        parent_history: Vec::new(),
        full_ast,
        target_hash: expr_identity_hash(&original_expr),
    };
    let join_id = create_join(
        &mut ctx.join_states,
        &mut ctx.next_join_id,
        JoinState::Product(Box::new(join)),
    );
    let x_group = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    let y_group = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);

    for (group_id, expr, role) in [
        (x_group, replacement_x, FactorRole::X),
        (y_group, replacement_y, FactorRole::Y),
    ] {
        let group = ctx.competition_groups.get_mut(&group_id).unwrap();
        group.best = Some(CandidateRecord {
            expr: expr.clone_tree(),
            cost: cobra_core::expr_cost::compute_cost(&expr).cost,
            verification: VerificationState::Verified,
            real_vars: vars.clone(),
            source_pass: PassId::SignaturePatternMatch,
            needs_original_space_verification: false,
            sig_vector: Vec::new(),
            lean_certificate: None,
            lean_signature_certificate: None,
        });
        group.continuation = Some(ContinuationData::ProductCollapse(ProductCollapseCont {
            join_id,
            role,
        }));
    }

    let (first_group, first_label, second_group, second_label) = if resolve_y_first {
        (y_group, "y", x_group, "x")
    } else {
        (x_group, "x", y_group, "y")
    };

    let first = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(first_group),
        &mut ctx,
    )
    .unwrap_or_else(|err| panic!("resolve {first_label} product join for {name}: {err}"));
    assert_eq!(first.decision, PassDecision::Advance);
    assert!(first.next.is_empty());

    let second = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(second_group),
        &mut ctx,
    )
    .unwrap_or_else(|err| panic!("resolve {second_label} product join for {name}: {err}"));
    assert_eq!(second.decision, PassDecision::SolvedCandidate);
    assert_eq!(second.next.len(), 1);

    let cert = second.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn product_join_rewrite_generated_certificate_replays_in_lean() {
    replay_product_join_rewrite_case(
        "product_join_rewrite_replay",
        vec!["x".into(), "y".into()],
        Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::constant(0),
        ),
        Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::constant(0),
        ),
        Expr::variable(0),
        Expr::variable(1),
        false,
        false,
    );

    let xy_plus_zero = Expr::add(
        Expr::mul(Expr::variable(0), Expr::variable(1)),
        Expr::constant(0),
    );
    replay_product_join_rewrite_case(
        "product_join_nested_rebuild_replay",
        vec!["x".into(), "y".into(), "z".into()],
        xy_plus_zero.clone_tree(),
        Expr::xor(xy_plus_zero, Expr::variable(2)),
        Expr::variable(0),
        Expr::variable(1),
        true,
        false,
    );

    let x_times_sum_plus_zero = Expr::add(
        Expr::mul(
            Expr::variable(0),
            Expr::add(Expr::variable(1), Expr::variable(2)),
        ),
        Expr::constant(0),
    );
    replay_product_join_rewrite_case(
        "product_join_nontrivial_factor_replay",
        vec!["x".into(), "y".into(), "z".into()],
        x_times_sum_plus_zero.clone_tree(),
        x_times_sum_plus_zero,
        Expr::variable(0),
        Expr::add(Expr::variable(1), Expr::variable(2)),
        false,
        false,
    );

    let solve_ctx_product = Expr::add(
        Expr::mul(Expr::variable(0), Expr::variable(1)),
        Expr::constant(0),
    );
    replay_product_join_rewrite_case(
        "product_join_solve_ctx_source_sig_replay",
        vec!["x".into(), "y".into()],
        solve_ctx_product.clone_tree(),
        solve_ctx_product,
        Expr::variable(0),
        Expr::variable(1),
        true,
        true,
    );
}

#[test]
fn product_identity_collapse_flow_generated_certificate_replays_in_lean() {
    let x = Expr::variable(0);
    let y = Expr::variable(1);
    let inner = Expr::and(x.clone_tree(), y.clone_tree());
    let x_only = Expr::and(x.clone_tree(), Expr::not(y.clone_tree()));
    let y_only = Expr::and(Expr::not(x.clone_tree()), y.clone_tree());
    let union = Expr::or(x.clone_tree(), y.clone_tree());
    let expr = Expr::add(Expr::mul(inner, union), Expr::mul(x_only, y_only));
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    let item = mk_ast_item(expr, Provenance::Original);

    let pr =
        cobra_passes::product_identity_collapse::run_product_identity_collapse(&item, &mut ctx)
            .expect("product identity collapse pass");
    assert_eq!(pr.decision, PassDecision::Advance);
    assert_eq!(pr.disposition, ItemDisposition::ConsumeCurrent);
    assert!(pr.next.len() >= 2);

    let mut final_cert = None;
    for child in pr.next.iter().take(2) {
        let StateData::Signature(sig_payload) = &child.payload else {
            panic!("expected product-collapse signature child");
        };
        match sig_payload.ctx.sig.as_slice() {
            [0, 1, 0, 1] | [0, 0, 1, 1] => {}
            other => panic!("unexpected product child signature: {other:?}"),
        }
        let group_id = child.group_id.expect("child group id");
        assert!(child.metadata.lean_certificate.is_none());
        assert!(child.metadata.lean_signature_certificate.is_none());

        let matched =
            cobra_passes::signature_pattern_match::run_signature_pattern_match(child, &mut ctx)
                .expect("signature pattern match product-collapse child");
        assert_eq!(matched.decision, PassDecision::Advance);

        let resolved = cobra_passes::resolve_competition::run_resolve_competition(
            &mk_resolve_item(group_id),
            &mut ctx,
        )
        .expect("resolve product-collapse child");
        if let Some(cert) = resolved
            .next
            .first()
            .and_then(|item| item.metadata.lean_signature_certificate.clone())
        {
            final_cert = Some(cert);
            break;
        }
    }

    let cert = final_cert.as_ref().expect("signature certificate");
    replay_signature_certificate("product_identity_collapse_flow_replay", cert);
}

fn replay_product_identity_collapse_pattern_flow(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);
    let item = mk_ast_item(expr, Provenance::Original);

    let pr =
        cobra_passes::product_identity_collapse::run_product_identity_collapse(&item, &mut ctx)
            .expect("product identity collapse pass");
    assert_eq!(pr.decision, PassDecision::Advance, "{name}");
    assert_eq!(pr.disposition, ItemDisposition::ConsumeCurrent, "{name}");
    assert!(!pr.next.is_empty(), "{name}");

    let mut final_cert = None;
    for child in &pr.next {
        let group_id = child.group_id.expect("product child group");
        let matched =
            cobra_passes::signature_pattern_match::run_signature_pattern_match(child, &mut ctx)
                .expect("signature pattern match product child");
        assert_eq!(matched.decision, PassDecision::Advance, "{name}");

        let resolved = cobra_passes::resolve_competition::run_resolve_competition(
            &mk_resolve_item(group_id),
            &mut ctx,
        )
        .expect("resolve product-collapse child");
        if let Some(cert) = resolved
            .next
            .first()
            .and_then(|item| item.metadata.lean_signature_certificate.clone())
        {
            final_cert = Some(cert);
            break;
        }
    }

    let cert = final_cert.as_ref().expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn product_identity_collapse_pattern_flow_generated_certificate_replays_in_lean() {
    let x = Expr::variable(0);
    let y = Expr::variable(1);
    let inner = Expr::and(x.clone_tree(), y.clone_tree());
    let x_only = Expr::and(x.clone_tree(), Expr::not(y.clone_tree()));
    let y_only = Expr::and(Expr::not(x.clone_tree()), y.clone_tree());
    let union = Expr::or(x.clone_tree(), y.clone_tree());
    replay_product_identity_collapse_pattern_flow(
        "product_identity_collapse_pattern_flow_replay",
        Expr::add(Expr::mul(inner, union), Expr::mul(x_only, y_only)),
        vec!["x".into(), "y".into()],
    );
}

#[test]
fn product_identity_collapse_family_generated_certificate_replays_in_lean() {
    let x = Expr::variable(0);
    let y = Expr::variable(1);
    let inner = Expr::and(x.clone_tree(), y.clone_tree());
    let x_only = Expr::and(x.clone_tree(), Expr::not(y.clone_tree()));
    let y_only = Expr::and(Expr::not(x.clone_tree()), y.clone_tree());
    let union = Expr::or(x.clone_tree(), y.clone_tree());
    replay_product_identity_collapse_pattern_flow(
        "product_identity_collapse_swapped_products_replay",
        Expr::add(Expr::mul(x_only, y_only), Expr::mul(union, inner)),
        vec!["x".into(), "y".into()],
    );

    let a = Expr::variable(0);
    let b = Expr::variable(1);
    let c = Expr::variable(2);
    let ab = Expr::and(a.clone_tree(), b.clone_tree());
    let a_only = Expr::and(a.clone_tree(), Expr::not(b.clone_tree()));
    let b_only = Expr::and(Expr::not(a.clone_tree()), b.clone_tree());
    let ab_union = Expr::or(a.clone_tree(), b.clone_tree());
    let product_site = Expr::add(Expr::mul(ab, ab_union), Expr::mul(a_only, b_only));
    replay_product_identity_collapse_pattern_flow(
        "product_identity_collapse_nested_product_replay",
        Expr::add(product_site, c),
        vec!["a".into(), "b".into(), "c".into()],
    );
}

#[test]
fn atom_identity_rewrite_generated_certificate_replays_in_lean() {
    replay_atom_identity_case(
        "atom_identity_rewrite_replay",
        Expr::add(
            Expr::or(Expr::variable(0), Expr::variable(1)),
            Expr::neg(Expr::and(Expr::variable(0), Expr::variable(1))),
        ),
        vec!["x".into(), "y".into()],
    );
}

fn replay_atom_identity_case(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let item = mk_ast_item(expr, Provenance::Original);
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);

    let pr = cobra_passes::atom_identity_rewrite::run_atom_identity_rewrite(&item, &mut ctx)
        .expect("atom identity rewrite pass");
    assert_eq!(pr.decision, PassDecision::Advance, "{name}");

    let cert = pr.next[0]
        .metadata
        .lean_certificate
        .as_ref()
        .expect("endpoint certificate");
    replay_endpoint_certificate(name, cert);
}

#[test]
fn atom_identity_rewrite_family_generated_certificate_replays_in_lean() {
    let x = Expr::variable(0);
    let y = Expr::variable(1);
    replay_atom_identity_case(
        "atom_identity_not_or_sub_not_replay",
        Expr::add(
            Expr::or(Expr::not(x.clone_tree()), y.clone_tree()),
            Expr::neg(Expr::not(x.clone_tree())),
        ),
        vec!["x".into(), "y".into()],
    );
    replay_atom_identity_case(
        "atom_identity_nested_or_sub_and_replay",
        Expr::add(
            Expr::add(
                Expr::or(Expr::variable(0), Expr::variable(1)),
                Expr::neg(Expr::and(Expr::variable(0), Expr::variable(1))),
            ),
            Expr::variable(2),
        ),
        vec!["x".into(), "y".into(), "z".into()],
    );
    replay_atom_identity_case(
        "atom_identity_not_or_add_self_add_one_replay",
        Expr::add(
            Expr::add(
                Expr::or(Expr::not(x.clone_tree()), y.clone_tree()),
                x.clone_tree(),
            ),
            Expr::constant(1),
        ),
        vec!["x".into(), "y".into()],
    );
    replay_atom_identity_case(
        "atom_identity_xor_via_or_not_replay",
        Expr::add(
            Expr::add(
                Expr::add(x.clone_tree(), Expr::neg(y.clone_tree())),
                Expr::neg(Expr::mul(
                    Expr::constant(2),
                    Expr::or(x.clone_tree(), Expr::not(y.clone_tree())),
                )),
            ),
            Expr::neg(Expr::constant(2)),
        ),
        vec!["x".into(), "y".into()],
    );
}

#[test]
fn prepare_remainder_constant_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned()];
    let target = Expr::add(Expr::variable(0), Expr::constant(5));
    let item = WorkItem::new(StateData::CoreCandidate(Box::new(CoreCandidatePayload {
        core_expr: Expr::variable(0),
        extractor_kind: ExtractorKind::Polynomial,
        degree_used: 1,
        source_sig: vec![5, 6],
        target: RemainderTargetContext {
            eval: Evaluator::from_expr(&target, 64),
            vars: vars.clone(),
            remap_support: Vec::new(),
        },
    })));
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);

    let pr =
        cobra_passes::prepare_remainder_from_core::run_prepare_remainder_from_core(&item, &mut ctx)
            .expect("prepare remainder pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate("prepare_remainder_constant_replay", cert);
}

#[test]
fn prepare_remainder_supported_flow_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned(), "y".to_owned()];
    let core = Expr::mul(Expr::variable(0), Expr::variable(1));
    let target = Expr::add(core.clone_tree(), Expr::variable(0));
    let source_sig = evaluate_boolean_signature(&target, vars.len() as u32, 64);
    let item = WorkItem::new(StateData::CoreCandidate(Box::new(CoreCandidatePayload {
        core_expr: core,
        extractor_kind: ExtractorKind::ProductAst,
        degree_used: 0,
        source_sig,
        target: RemainderTargetContext {
            eval: Evaluator::from_expr(&target, 64),
            vars: vars.clone(),
            remap_support: Vec::new(),
        },
    })));
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);

    let prepared =
        cobra_passes::prepare_remainder_from_core::run_prepare_remainder_from_core(&item, &mut ctx)
            .expect("prepare remainder pass");
    assert_eq!(prepared.decision, PassDecision::Advance);

    let supported =
        cobra_passes::residual_supported::run_residual_supported(&prepared.next[0], &mut ctx)
            .expect("residual supported pass");
    assert_eq!(supported.decision, PassDecision::Advance);
    assert_eq!(supported.next.len(), 1);

    let child_group = supported.next[0].group_id.expect("residual child group");
    let matched = cobra_passes::signature_pattern_match::run_signature_pattern_match(
        &supported.next[0],
        &mut ctx,
    )
    .expect("signature pattern match residual");
    assert_eq!(matched.decision, PassDecision::Advance);

    let resolved = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(child_group),
        &mut ctx,
    )
    .expect("resolve residual recombine");
    assert_eq!(resolved.decision, PassDecision::SolvedCandidate);

    let cert = resolved.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate("prepare_remainder_supported_flow_replay", cert);
}

#[test]
fn extract_product_core_generated_certificate_replays_in_lean() {
    replay_extract_product_core_case(
        "extract_product_core_replay",
        Expr::mul(Expr::variable(0), Expr::variable(1)),
        2,
    );
}

fn replay_extract_product_core_case(name: &str, expr: Box<Expr>, num_vars: u32) {
    let vars = (0..num_vars)
        .map(|idx| format!("x{idx}"))
        .collect::<Vec<_>>();
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let item = mk_ast_item(expr, Provenance::Original);

    let pr = cobra_passes::extract_product_core::run_extract_product_core(&item, &mut ctx)
        .expect("extract product core pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn extract_product_core_family_generated_certificate_replays_in_lean() {
    replay_extract_product_core_case(
        "extract_product_core_two_products_replay",
        Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::mul(Expr::variable(1), Expr::variable(2)),
        ),
        3,
    );
    replay_extract_product_core_case(
        "extract_product_core_nested_three_products_replay",
        Expr::add(
            Expr::add(
                Expr::mul(Expr::variable(0), Expr::variable(1)),
                Expr::mul(Expr::variable(2), Expr::variable(3)),
            ),
            Expr::mul(Expr::variable(0), Expr::variable(3)),
        ),
        4,
    );
    replay_extract_product_core_case(
        "extract_product_core_square_plus_product_replay",
        Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(0)),
            Expr::mul(Expr::variable(0), Expr::variable(1)),
        ),
        2,
    );
}

fn replay_poly_core(name: &str, expr: Box<Expr>, degree: u8, num_vars: u32) {
    let vars = (0..num_vars)
        .map(|idx| format!("x{idx}"))
        .collect::<Vec<_>>();
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let item = mk_ast_item(expr, Provenance::Original);

    let pr = match degree {
        2 => cobra_passes::extract_poly_core::run_extract_poly_core_d2(&item, &mut ctx),
        3 => cobra_passes::extract_poly_core::run_extract_poly_core_d3(&item, &mut ctx),
        4 => cobra_passes::extract_poly_core::run_extract_poly_core_d4(&item, &mut ctx),
        _ => panic!("unsupported replay degree"),
    }
    .expect("extract polynomial core pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn extract_poly_core_d2_generated_certificate_replays_in_lean() {
    replay_poly_core(
        "extract_poly_core_d2_replay",
        Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::mul(Expr::variable(0), Expr::variable(0)),
        ),
        2,
        2,
    );
}

#[test]
fn extract_poly_core_d2_family_generated_certificate_replays_in_lean() {
    replay_poly_core(
        "extract_poly_core_d2_affine_plus_product_replay",
        Expr::add(
            Expr::add(
                Expr::mul(Expr::variable(0), Expr::variable(1)),
                Expr::variable(2),
            ),
            Expr::constant(7),
        ),
        2,
        3,
    );
    replay_poly_core(
        "extract_poly_core_d2_two_squares_replay",
        Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(0)),
            Expr::mul(Expr::variable(1), Expr::variable(1)),
        ),
        2,
        2,
    );
}

#[test]
fn extract_poly_core_d3_generated_certificate_replays_in_lean() {
    let x3 = Expr::mul(
        Expr::mul(Expr::variable(0), Expr::variable(0)),
        Expr::variable(0),
    );
    replay_poly_core("extract_poly_core_d3_replay", x3, 3, 2);
}

#[test]
fn extract_poly_core_d3_family_generated_certificate_replays_in_lean() {
    replay_poly_core(
        "extract_poly_core_d3_mixed_cubic_replay",
        Expr::add(
            Expr::mul(
                Expr::mul(Expr::variable(0), Expr::variable(0)),
                Expr::variable(1),
            ),
            Expr::mul(Expr::variable(1), Expr::variable(1)),
        ),
        3,
        2,
    );
    replay_poly_core(
        "extract_poly_core_d3_trivar_product_replay",
        Expr::mul(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        ),
        3,
        3,
    );
}

#[test]
fn extract_poly_core_d4_generated_certificate_replays_in_lean() {
    let x2 = Expr::mul(Expr::variable(0), Expr::variable(0));
    replay_poly_core(
        "extract_poly_core_d4_replay",
        Expr::mul(x2.clone_tree(), x2),
        4,
        2,
    );
}

#[test]
fn extract_poly_core_d4_family_generated_certificate_replays_in_lean() {
    let x2 = Expr::mul(Expr::variable(0), Expr::variable(0));
    let y2 = Expr::mul(Expr::variable(1), Expr::variable(1));
    replay_poly_core(
        "extract_poly_core_d4_biquadratic_replay",
        Expr::mul(x2.clone_tree(), y2.clone_tree()),
        4,
        2,
    );
    replay_poly_core(
        "extract_poly_core_d4_quartic_plus_cubic_replay",
        Expr::add(
            Expr::mul(x2.clone_tree(), x2),
            Expr::mul(y2, Expr::variable(1)),
        ),
        4,
        2,
    );
}

#[test]
fn extract_template_core_generated_certificate_replays_in_lean() {
    let expr = Expr::xor(Expr::variable(0), Expr::variable(1));
    replay_extract_template_core_case("extract_template_core_replay", expr, 2);
}

fn replay_extract_template_core_case(name: &str, expr: Box<Expr>, num_vars: u32) {
    let classification = Classification {
        semantic: SemanticClass::NonPolynomial,
        flags: StructuralFlag::HAS_BITWISE_OVER_ARITH,
    };
    let vars = (0..num_vars)
        .map(|idx| format!("x{idx}"))
        .collect::<Vec<_>>();
    let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let item = mk_classified_ast_item(expr, Provenance::Original, classification);

    let pr = cobra_passes::extract_template_core::run_extract_template_core(&item, &mut ctx)
        .expect("extract template core pass");
    assert_eq!(pr.decision, PassDecision::SolvedCandidate);

    let cert = pr.next[0]
        .metadata
        .lean_signature_certificate
        .as_ref()
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn extract_template_core_family_generated_certificate_replays_in_lean() {
    replay_extract_template_core_case(
        "extract_template_core_layer1_and_replay",
        Expr::and(Expr::variable(0), Expr::variable(1)),
        2,
    );
    replay_extract_template_core_case(
        "extract_template_core_layer2_xor_and_or_replay",
        Expr::xor(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::or(Expr::variable(0), Expr::variable(2)),
        ),
        3,
    );
    replay_extract_template_core_case(
        "extract_template_core_unary_not_wrap_replay",
        Expr::not(Expr::and(Expr::variable(0), Expr::variable(1))),
        2,
    );
}

#[test]
fn verify_candidate_generated_certificate_replays_in_lean() {
    let original = Expr::add(
        Expr::and(Expr::variable(0), Expr::variable(1)),
        Expr::or(Expr::variable(0), Expr::variable(1)),
    );
    let simplified = Expr::add(Expr::variable(0), Expr::variable(1));
    let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
    ctx.original_expr = Some(original.clone_tree());
    ctx.evaluator = Some(Evaluator::from_expr(&original, 64));
    let item = WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
        expr: simplified,
        real_vars: vec!["x".into(), "y".into()],
        cost: cobra_core::expr_cost::ExprCost::default(),
        producing_pass: PassId::VerifyCandidate,
        needs_original_space_verification: true,
    })));

    let pr = cobra_passes::verify_candidate::run_verify_candidate(&item, &mut ctx)
        .expect("verify candidate pass");
    assert_eq!(pr.decision, PassDecision::Advance);

    let cert = pr.next[0]
        .metadata
        .lean_certificate
        .as_ref()
        .expect("endpoint certificate");
    assert!(
        cert.steps
            .iter()
            .any(|step| step.theorem == LeanTheorem::AndOrSumEqAdd64),
        "verify_candidate_replay should carry the and/or sum theorem"
    );
    replay_endpoint_certificate("verify_candidate_replay", cert);
}

fn replay_verify_candidate_case(
    name: &str,
    original: Box<Expr>,
    simplified: Box<Expr>,
    original_vars: Vec<String>,
    real_vars: Vec<String>,
) {
    let mut ctx = OrchestratorContext::new(Options::default(), original_vars, 64);
    ctx.original_expr = Some(original.clone_tree());
    ctx.evaluator = Some(Evaluator::from_expr(&original, 64));
    let item = WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
        expr: simplified,
        real_vars,
        cost: cobra_core::expr_cost::ExprCost::default(),
        producing_pass: PassId::VerifyCandidate,
        needs_original_space_verification: true,
    })));

    let pr = cobra_passes::verify_candidate::run_verify_candidate(&item, &mut ctx)
        .expect("verify candidate pass");
    assert_eq!(pr.decision, PassDecision::Advance, "{name}");

    let cert = pr.next[0]
        .metadata
        .lean_certificate
        .as_ref()
        .expect("endpoint certificate");
    if name == "verify_candidate_three_var_or_sub_and_replay" {
        assert!(
            cert.steps
                .iter()
                .any(|step| step.theorem == LeanTheorem::OrSubAndEqXor64),
            "{name} should carry the nested or-sub-and theorem"
        );
    }
    replay_endpoint_certificate(name, cert);
}

#[test]
fn verify_candidate_family_generated_certificate_replays_in_lean() {
    replay_verify_candidate_case(
        "verify_candidate_remapped_var_replay",
        Expr::variable(1),
        Expr::variable(0),
        vec!["x".into(), "y".into()],
        vec!["y".into()],
    );
    replay_verify_candidate_case(
        "verify_candidate_three_var_or_sub_and_replay",
        Expr::add(
            Expr::add(
                Expr::or(Expr::variable(0), Expr::variable(1)),
                Expr::neg(Expr::and(Expr::variable(0), Expr::variable(1))),
            ),
            Expr::variable(2),
        ),
        Expr::add(
            Expr::xor(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        ),
        vec!["x".into(), "y".into(), "z".into()],
        vec!["x".into(), "y".into(), "z".into()],
    );
}

#[test]
fn signature_multivar_poly_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned(), "y".to_owned()];
    let orig = Expr::add(
        Expr::mul(Expr::variable(0), Expr::variable(1)),
        Expr::mul(Expr::variable(0), Expr::variable(0)),
    );
    let sig = vec![0, 1, 0, 2];
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&orig, 64));
    let mut item = mk_signature_item(sig, vars);
    let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    item.group_id = Some(group_id);
    item.features.classification = Some(Classification {
        semantic: SemanticClass::Polynomial,
        flags: StructuralFlag::HAS_MUL | StructuralFlag::HAS_MULTIVAR_HIGH_POWER,
    });

    let pr = cobra_passes::signature_multivar_poly_recovery::run_signature_multivar_poly_recovery(
        &item, &mut ctx,
    )
    .expect("multivar poly recovery pass");
    assert_eq!(pr.decision, PassDecision::Advance);

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate("signature_multivar_poly_replay", cert);
}

fn replay_signature_multivar_poly_case(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let sig = evaluate_boolean_signature(&expr, vars.len() as u32, 64);
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let mut item = mk_signature_item(sig, vars);
    let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    item.group_id = Some(group_id);
    item.features.classification = Some(Classification {
        semantic: SemanticClass::Polynomial,
        flags: StructuralFlag::HAS_MUL | StructuralFlag::HAS_MULTIVAR_HIGH_POWER,
    });

    let pr = cobra_passes::signature_multivar_poly_recovery::run_signature_multivar_poly_recovery(
        &item, &mut ctx,
    )
    .expect("multivar poly recovery pass");
    assert_eq!(pr.decision, PassDecision::Advance);

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

fn replay_signature_multivar_poly_override_case(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let arity = vars.len() as u32;
    let sig = evaluate_boolean_signature(&expr, arity, 64);
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(
        &Expr::add(Expr::variable(0), Expr::variable(1)),
        64,
    ));
    let mut item = mk_signature_item(sig, vars);
    let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    item.group_id = Some(group_id);
    item.evaluator_override = Some(Evaluator::from_expr(&expr, 64));
    item.evaluator_override_arity = arity;
    item.features.classification = Some(Classification {
        semantic: SemanticClass::Polynomial,
        flags: StructuralFlag::HAS_MUL | StructuralFlag::HAS_MULTIVAR_HIGH_POWER,
    });

    let pr = cobra_passes::signature_multivar_poly_recovery::run_signature_multivar_poly_recovery(
        &item, &mut ctx,
    )
    .expect("multivar poly recovery override pass");
    assert_eq!(pr.decision, PassDecision::Advance);

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn signature_multivar_poly_override_generated_certificate_replays_in_lean() {
    replay_signature_multivar_poly_override_case(
        "signature_multivar_poly_override_replay",
        Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::mul(Expr::variable(0), Expr::variable(0)),
        ),
        vec!["x".into(), "y".into()],
    );
}

#[test]
fn signature_multivar_poly_family_generated_certificate_replays_in_lean() {
    replay_signature_multivar_poly_case(
        "signature_multivar_poly_univariate_cubic_replay",
        Expr::mul(
            Expr::mul(Expr::variable(0), Expr::variable(0)),
            Expr::variable(0),
        ),
        vec!["x".into()],
    );
    replay_signature_multivar_poly_case(
        "signature_multivar_poly_mixed_cubic_replay",
        Expr::add(
            Expr::mul(
                Expr::mul(Expr::variable(0), Expr::variable(0)),
                Expr::variable(1),
            ),
            Expr::mul(Expr::variable(1), Expr::variable(1)),
        ),
        vec!["x".into(), "y".into()],
    );
}

#[test]
fn signature_singleton_poly_generated_certificate_replays_in_lean() {
    let vars = vec!["x".to_owned()];
    let sig = vec![0, 1];
    let orig = Expr::mul(Expr::variable(0), Expr::variable(0));
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&orig, 64));
    let item = mk_signature_coeff_item(sig, vars, &mut ctx);
    let group_id = item.group_id.expect("group id");

    let pr =
        cobra_passes::signature_singleton_poly_recovery::run_signature_singleton_poly_recovery(
            &item, &mut ctx,
        )
        .expect("singleton poly recovery pass");
    assert_eq!(pr.decision, PassDecision::Advance);

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate("signature_singleton_poly_replay", cert);
}

fn replay_signature_singleton_poly_case(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let sig = evaluate_boolean_signature(&expr, vars.len() as u32, 64);
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let item = mk_signature_coeff_item(sig, vars, &mut ctx);
    let group_id = item.group_id.expect("group id");

    let pr =
        cobra_passes::signature_singleton_poly_recovery::run_signature_singleton_poly_recovery(
            &item, &mut ctx,
        )
        .expect("singleton poly recovery pass");
    assert_eq!(pr.decision, PassDecision::Advance);

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

fn replay_signature_singleton_poly_remainder_flow(name: &str, expr: Box<Expr>, vars: Vec<String>) {
    let sig = evaluate_boolean_signature(&expr, vars.len() as u32, 64);
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
    let item = mk_signature_coeff_item(sig, vars, &mut ctx);
    let parent_group_id = item.group_id.expect("parent group id");

    let lowered =
        cobra_passes::signature_singleton_poly_recovery::run_signature_singleton_poly_recovery(
            &item, &mut ctx,
        )
        .expect("singleton poly recovery pass");
    assert_eq!(lowered.decision, PassDecision::Advance, "{name}");
    assert_eq!(lowered.next.len(), 1, "{name}");
    assert!(
        matches!(lowered.next[0].payload, StateData::Remainder(_)),
        "{name}"
    );

    let supported =
        cobra_passes::residual_supported::run_residual_supported(&lowered.next[0], &mut ctx)
            .expect("residual supported pass");
    assert_eq!(supported.decision, PassDecision::Advance, "{name}");
    assert_eq!(supported.next.len(), 1, "{name}");
    let child_group_id = supported.next[0].group_id.expect("residual child group");

    let matched = cobra_passes::signature_pattern_match::run_signature_pattern_match(
        &supported.next[0],
        &mut ctx,
    )
    .expect("signature pattern match residual child");
    assert_eq!(matched.decision, PassDecision::Advance, "{name}");

    let solved = cobra_passes::resolve_competition::run_resolve_competition(
        &mk_resolve_item(child_group_id),
        &mut ctx,
    )
    .expect("resolve residual child");
    assert_eq!(solved.decision, PassDecision::Advance, "{name}");

    let cert = ctx.competition_groups[&parent_group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

fn replay_signature_singleton_poly_inline_override_case(
    name: &str,
    expr: Box<Expr>,
    vars: Vec<String>,
) {
    let arity = vars.len() as u32;
    let sig = evaluate_boolean_signature(&expr, vars.len() as u32, 64);
    let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
    let mut item = mk_signature_coeff_item(sig, vars, &mut ctx);
    let group_id = item.group_id.expect("group id");
    if let StateData::SignatureCoeff(payload) = &mut item.payload {
        payload.ctx.original_indices = (0..arity).collect();
    }
    item.evaluator_override = Some(Evaluator::from_expr(&expr, 64));
    item.evaluator_override_arity = arity;

    let pr =
        cobra_passes::signature_singleton_poly_recovery::run_signature_singleton_poly_recovery(
            &item, &mut ctx,
        )
        .expect("singleton poly recovery inline override pass");
    assert_eq!(pr.decision, PassDecision::Advance, "{name}");
    assert!(pr.next.is_empty(), "{name}");

    let cert = ctx.competition_groups[&group_id]
        .best
        .as_ref()
        .and_then(|best| best.lean_signature_certificate.as_ref())
        .expect("signature certificate");
    replay_signature_certificate(name, cert);
}

#[test]
fn signature_singleton_poly_inline_override_generated_certificate_replays_in_lean() {
    replay_signature_singleton_poly_inline_override_case(
        "signature_singleton_poly_inline_override_replay",
        Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(0)),
            Expr::and(Expr::variable(0), Expr::variable(1)),
        ),
        vec!["x".into(), "y".into()],
    );
}

#[test]
fn signature_singleton_poly_family_generated_certificate_replays_in_lean() {
    replay_signature_singleton_poly_case(
        "signature_singleton_poly_cubic_replay",
        Expr::mul(
            Expr::mul(Expr::variable(0), Expr::variable(0)),
            Expr::variable(0),
        ),
        vec!["x".into()],
    );
    replay_signature_singleton_poly_case(
        "signature_singleton_poly_two_var_squares_replay",
        Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(0)),
            Expr::mul(Expr::variable(1), Expr::variable(1)),
        ),
        vec!["x".into(), "y".into()],
    );
    replay_signature_singleton_poly_remainder_flow(
        "signature_singleton_poly_remainder_supported_replay",
        Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(0)),
            Expr::and(Expr::variable(0), Expr::variable(1)),
        ),
        vec!["x".into(), "y".into()],
    );
}
