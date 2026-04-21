//! `cobra` — CLI driver around the simplifier pipeline.
//!
//! Parses an MBA expression, runs the orchestrator, and prints either
//! the simplified form (with `Verified` / `Unverified` status) or a
//! diagnostic explaining why nothing fired. Exits non-zero on parse
//! errors or `--verify` failures.

use std::process::ExitCode;

use clap::Parser;

use cobra_core::evaluate_boolean_signature;
use cobra_core::evaluator::Evaluator;
use cobra_core::expr::render;
use cobra_core::expr_rewrite::build_var_support;
use cobra_core::expr_utils::remap_var_indices;
use cobra_core::pass_contract::VerificationState;
use cobra_core::simplify_outcome::{Options, SimplifyOutcomeKind};

use cobra_orchestrator::{OrchestratorContext, OrchestratorPolicy, Worklist};
use cobra_parser::parse_to_ast;
use cobra_passes::{full_width_check_eval, seed_with_ast, PASS_REGISTRY};

#[derive(Parser, Debug)]
#[command(
    name = "cobra",
    version,
    about = "CoBRA-rs: parse, simplify, and (optionally) verify an MBA expression"
)]
struct Args {
    /// MBA expression in infix syntax (e.g. "x + y" or "(x ^ y) + 2 * (x & y)").
    ///
    /// `allow_hyphen_values = true` is required so that leading-unary-minus
    /// expressions like `--mba "-x - 1"` are accepted instead of being
    /// swallowed by clap's flag parser.
    #[arg(long, allow_hyphen_values = true)]
    mba: String,

    /// Bitwidth for arithmetic (8, 16, 32, 64).
    #[arg(long, default_value_t = 64)]
    bitwidth: u32,

    /// Maximum variable count in any subproblem (acts as a guard on
    /// signature-table passes).
    #[arg(long, default_value_t = 16)]
    max_vars: u32,

    /// Run an additional 1024-sample full-width check on the simplified
    /// expression against the original. Mismatch → exit 1.
    #[arg(long, default_value_t = false)]
    verify: bool,

    /// Print extra diagnostics (classification, telemetry, reason).
    #[arg(long, default_value_t = false)]
    verbose: bool,
}

fn run(args: &Args) -> Result<i32, String> {
    if !matches!(args.bitwidth, 8 | 16 | 32 | 64) {
        return Err(format!(
            "unsupported --bitwidth {} (must be 8, 16, 32, or 64)",
            args.bitwidth
        ));
    }

    let parsed = parse_to_ast(&args.mba, args.bitwidth)
        .map_err(|e| format!("parse error: {}", e.message))?;
    let original = parsed.expr.clone_tree();

    let opts = Options {
        bitwidth: args.bitwidth,
        max_vars: args.max_vars,
        ..Options::default()
    };
    let mut ctx = OrchestratorContext::new(opts, parsed.vars.clone(), args.bitwidth);
    ctx.evaluator = Some(Evaluator::from_expr(&original, args.bitwidth));
    ctx.input_sig =
        evaluate_boolean_signature(&original, parsed.vars.len() as u32, args.bitwidth);

    let mut worklist = Worklist::new();
    seed_with_ast(&original, &mut ctx, &mut worklist).map_err(|e| format!("seed error: {e:?}"))?;

    let policy = OrchestratorPolicy::default();
    let outcome = cobra_orchestrator::simplify_from_worklist(
        &mut ctx,
        worklist,
        policy,
        PASS_REGISTRY,
        Some(&original),
    )
    .map_err(|e| format!("pipeline error: {e:?}"))?;

    if args.verbose {
        eprintln!("classification: {:?}", outcome.diag.classification.semantic);
        eprintln!(
            "telemetry: expansions={}, depth={}, verified={}, queue_high_water={}",
            outcome.telemetry.total_expansions,
            outcome.telemetry.max_depth_reached,
            outcome.telemetry.candidates_verified,
            outcome.telemetry.queue_high_water,
        );
    }

    match outcome.kind {
        SimplifyOutcomeKind::Simplified => {
            let raw = outcome.expr.as_ref().expect("Simplified must carry expr");
            let mut expr_owned = raw.clone();
            if !outcome.real_vars.is_empty() && outcome.real_vars.len() < parsed.vars.len() {
                let idx_map = build_var_support(&parsed.vars, &outcome.real_vars);
                remap_var_indices(&mut expr_owned, &idx_map);
            }
            let expr = &expr_owned;
            let rendered = render(expr, &parsed.vars, args.bitwidth);
            let status = if outcome.verified {
                "verified"
            } else {
                "unverified"
            };
            println!("{rendered}");
            if args.verbose {
                eprintln!("status: {status}");
            }

            if args.verify {
                let verifier_eval = Evaluator::from_expr(&original, args.bitwidth);
                let chk = full_width_check_eval(
                    &verifier_eval,
                    parsed.vars.len() as u32,
                    expr,
                    args.bitwidth,
                    1024,
                );
                if !chk.passed {
                    eprintln!("--verify FAILED: simplified expression diverges from input");
                    return Ok(1);
                }
                if args.verbose {
                    eprintln!("--verify: passed (1024 samples)");
                }
            }
            Ok(0)
        }
        SimplifyOutcomeKind::UnchangedUnsupported | SimplifyOutcomeKind::Error => {
            let _ = VerificationState::Unverified;
            let rendered = render(&original, &parsed.vars, args.bitwidth);
            println!("{rendered}");
            if !outcome.diag.reason.is_empty() {
                eprintln!("reason: {}", outcome.diag.reason);
            }
            Ok(0)
        }
    }
}

fn main() -> ExitCode {
    let args = Args::parse();
    match run(&args) {
        Ok(0) => ExitCode::SUCCESS,
        Ok(n) => ExitCode::from(n as u8),
        Err(msg) => {
            eprintln!("error: {msg}");
            ExitCode::FAILURE
        }
    }
}
