//! `cobra-cli` — CLI driver around the simplifier pipeline.
//!
//! Parses an MBA expression, runs the orchestrator, and prints either
//! the simplified form (with `Verified` / `Unverified` status) or a
//! diagnostic explaining why nothing fired. Exits non-zero on parse
//! errors or `--verify` failures.

use std::process::ExitCode;
use std::thread;

use clap::Parser;

#[cfg(feature = "z3")]
use cobra::verify::{Verifier, VerifyOpts, VerifyOutcome, Z3Verifier};
use cobra::{
    is_valid_bitwidth, outcome_expr_in_original_space, parse_to_ast, render, simplify_expr, Expr,
    Options, SimplifyOutcomeKind,
};

const CLI_STACK_SIZE: usize = 64 * 1024 * 1024;

#[derive(Parser, Debug)]
#[command(
    name = "cobra-cli",
    version,
    about = "CoBRA-rs: parse, simplify, and (optionally) verify an MBA expression"
)]
struct Args {
    /// MBA expression in infix syntax (e.g. "x + y" or "(x ^ y) + 2 * (x & y)").
    //
    // Leading-unary-minus expressions must remain values rather than being
    // interpreted as clap flags.
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
    #[cfg(not(feature = "z3"))]
    if args.verify {
        eprintln!("error: --verify requested, but this binary was built without Z3");
        return Ok(1);
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
            let expr_owned = outcome_expr_in_original_space(&outcome, &parsed.vars)
                .expect("Simplified must carry expr");
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
        SimplifyOutcomeKind::UnchangedUnsupported => {
            let rendered = render(&original, &parsed.vars, args.bitwidth);
            println!("{rendered}");
            if !outcome.diag.reason.is_empty() {
                eprintln!("reason: {}", outcome.diag.reason);
            }
            Ok(0)
        }
        SimplifyOutcomeKind::Error => {
            let reason = if outcome.diag.reason.is_empty() {
                "simplifier returned an unspecified error"
            } else {
                &outcome.diag.reason
            };
            eprintln!("error: {reason}");
            Ok(1)
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
    eprintln!("error: --verify requested, but this binary was built without Z3");
    1
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
    fn run_verify_without_z3_fails_closed() {
        let mut args = args(64);
        args.verify = true;
        assert_eq!(run(&args), Ok(1));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn run_verify_with_z3_accepts_equivalent_simplification() {
        let mut args = args(64);
        args.verify = true;
        assert_eq!(run(&args), Ok(0));
    }
}
