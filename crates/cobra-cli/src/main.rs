//! `cobra` — CLI driver around the simplifier pipeline.
//!
//! Parses an MBA expression, runs the orchestrator, and prints either
//! the simplified form (with `Verified` / `Unverified` status) or a
//! diagnostic explaining why nothing fired. Exits non-zero on parse
//! errors or `--verify` failures.

use std::process::ExitCode;
use std::thread;

use clap::Parser;

use cobra_core::expr::{render, Expr};
use cobra_core::expr_rewrite::build_var_support;
use cobra_core::expr_utils::remap_var_indices;
use cobra_core::is_valid_bitwidth;
use cobra_core::simplify_outcome::{Options, SimplifyOutcomeKind};

use cobra_parser::parse_to_ast;
use cobra_passes::simplify_expr;
#[cfg(feature = "z3")]
use cobra_verify::{Verifier, VerifyOpts, VerifyOutcome, Z3Verifier};

const CLI_STACK_SIZE: usize = 64 * 1024 * 1024;

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

    /// Bitwidth for arithmetic (1 through 64).
    #[arg(long, default_value_t = 64)]
    bitwidth: u32,

    /// Maximum variable count in any subproblem (acts as a guard on
    /// signature-table passes).
    #[arg(long, default_value_t = 16)]
    max_vars: u32,

    /// Run a Z3 equivalence proof on the simplified expression against the
    /// original. If this binary was built without the `z3` feature, the flag
    /// is accepted and ignored with a warning, matching upstream.
    #[arg(long, default_value_t = false)]
    verify: bool,

    /// Print extra diagnostics (classification, telemetry, reason).
    #[arg(long, default_value_t = false)]
    verbose: bool,
}

fn run(args: &Args) -> Result<i32, String> {
    if !is_valid_bitwidth(args.bitwidth) {
        return Err(format!(
            "unsupported --bitwidth {} (must be in 1..=64)",
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
    let outcome = simplify_expr(&original, &parsed.vars, opts)
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
                return Ok(run_z3_verify(&original, expr, &parsed.vars, args.bitwidth));
            }
            Ok(0)
        }
        SimplifyOutcomeKind::UnchangedUnsupported | SimplifyOutcomeKind::Error => {
            let rendered = render(&original, &parsed.vars, args.bitwidth);
            println!("{rendered}");
            if !outcome.diag.reason.is_empty() {
                eprintln!("reason: {}", outcome.diag.reason);
            }
            Ok(0)
        }
    }
}

#[cfg(feature = "z3")]
fn run_z3_verify(original: &Expr, simplified: &Expr, vars: &[String], bitwidth: u32) -> i32 {
    let verifier = Z3Verifier;
    match verifier.prove_equiv(
        original,
        simplified,
        vars,
        VerifyOpts {
            bitwidth,
            ..VerifyOpts::default()
        },
    ) {
        VerifyOutcome::Equivalent => {
            eprintln!("[Z3] Verified: equivalent");
            0
        }
        VerifyOutcome::Disproved { counterexample } => {
            eprintln!("[Z3] Verification failed: {counterexample}");
            1
        }
        VerifyOutcome::TimedOut => {
            eprintln!("[Z3] Verification failed: Z3 returned unknown (possible timeout)");
            1
        }
        VerifyOutcome::Unverified => {
            eprintln!("[Z3] Verification failed: no verifier backend available");
            1
        }
    }
}

#[cfg(not(feature = "z3"))]
fn run_z3_verify(_original: &Expr, _simplified: &Expr, _vars: &[String], _bitwidth: u32) -> i32 {
    eprintln!("Warning: Z3 not available, --verify ignored");
    0
}

fn real_main() -> ExitCode {
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

fn main() -> ExitCode {
    thread::Builder::new()
        .name("cobra-cli".into())
        .stack_size(CLI_STACK_SIZE)
        .spawn(real_main)
        .expect("spawn cobra CLI worker")
        .join()
        .expect("cobra CLI worker panicked")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(bitwidth: u32) -> Args {
        Args {
            mba: "x".to_string(),
            bitwidth,
            max_vars: 16,
            verify: false,
            verbose: false,
        }
    }

    #[test]
    fn run_accepts_minimum_public_bitwidth() {
        assert_eq!(run(&args(1)), Ok(0));
    }

    #[test]
    fn run_rejects_bitwidths_outside_public_range() {
        assert!(run(&args(0)).unwrap_err().contains("1..=64"));
        assert!(run(&args(65)).unwrap_err().contains("1..=64"));
    }

    #[cfg(not(feature = "z3"))]
    #[test]
    fn run_verify_without_z3_matches_upstream_warning_path() {
        let mut args = args(64);
        args.verify = true;
        assert_eq!(run(&args), Ok(0));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn run_verify_with_z3_accepts_equivalent_simplification() {
        let mut args = args(64);
        args.verify = true;
        assert_eq!(run(&args), Ok(0));
    }
}
