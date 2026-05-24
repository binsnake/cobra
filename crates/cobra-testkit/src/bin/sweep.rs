//! `cobra-sweep` — stream one or more dataset `.txt` files through the
//! simplifier and report per-file + aggregate tallies. Each case is
//! probed against both the input (safety / equivalence) and the

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::thread;
use std::time::Instant;

use clap::Parser;

use cobra_core::is_valid_bitwidth;
use cobra_testkit::{parse_dataset, run_case, CaseKind, CaseReport, Report};

const SWEEP_STACK_SIZE: usize = 64 * 1024 * 1024;

#[derive(Parser, Debug)]
#[command(
    name = "cobra-sweep",
    about = "Run CoBRA simplification over one or more dataset files and report tallies",
    version
)]
struct Args {
    /// Dataset `.txt` files. Pass one or many.
    #[arg(required = true)]
    files: Vec<PathBuf>,

    /// Bitwidth for arithmetic.
    #[arg(long, default_value_t = 64)]
    bitwidth: u32,

    /// Limit the number of cases read from each file (0 = unlimited).
    #[arg(long, default_value_t = 0)]
    limit: u32,

    /// Print one line per case (otherwise only per-file / aggregate).
    #[arg(long)]
    per_case: bool,

    /// Fail (exit 1) if any case produced a simplification that was
    #[arg(long, default_value_t = true)]
    fail_on_unsafe: bool,

    /// Fail (exit 1) if any case produced a pipeline error.
    #[arg(long, default_value_t = false)]
    fail_on_error: bool,
}

fn sweep_file(path: &Path, args: &Args) -> Report {
    let body = match fs::read_to_string(path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("error: could not read {}: {e}", path.display());
            return Report::default();
        }
    };
    let mut cases = parse_dataset(&body);
    if args.limit > 0 && cases.len() > args.limit as usize {
        cases.truncate(args.limit as usize);
    }

    let mut report = Report::default();
    let started = Instant::now();
    for case in &cases {
        let r = run_case(case, args.bitwidth);
        if args.per_case {
            print_case_line(path, case.line_number, &r);
        } else if matches!(r.kind, CaseKind::Errored)
            || (matches!(r.kind, CaseKind::Simplified) && !r.equivalent_to_input)
        {
            // Always surface regressions even without --per-case.
            print_case_line(path, case.line_number, &r);
        }
        report.record(&r);
    }
    let elapsed = started.elapsed();

    println!(
        "{}: total={} simplified={} verified={} parity={} unsafe={} unchanged={} skipped={} errored={} ({:.2}s)",
        path.display(),
        report.total,
        report.simplified,
        report.verified,
        report.parity,
        report.unsafe_changes,
        report.unchanged,
        report.skipped,
        report.errored,
        elapsed.as_secs_f64(),
    );
    report
}

fn print_case_line(path: &Path, line: u32, r: &CaseReport) {
    let tag = match r.kind {
        CaseKind::Simplified => {
            if r.equivalent_to_input {
                if r.matches_expected {
                    "verified+parity"
                } else {
                    "verified"
                }
            } else {
                "UNSAFE"
            }
        }
        CaseKind::Unchanged => "unchanged",
        CaseKind::Skipped => "skipped",
        CaseKind::Errored => "ERROR",
    };
    let detail = r.error.as_deref().unwrap_or("");
    println!("  {}:{line} {tag} {detail}", path.display());
}

fn merge(into: &mut Report, other: &Report) {
    into.total += other.total;
    into.simplified += other.simplified;
    into.verified += other.verified;
    into.parity += other.parity;
    into.unchanged += other.unchanged;
    into.skipped += other.skipped;
    into.errored += other.errored;
    into.unsafe_changes += other.unsafe_changes;
}

fn run() -> ExitCode {
    let args = Args::parse();
    if !is_valid_bitwidth(args.bitwidth) {
        eprintln!(
            "error: unsupported --bitwidth {} (must be in 1..=64)",
            args.bitwidth
        );
        return ExitCode::FAILURE;
    }

    let mut aggregate = Report::default();
    for path in &args.files {
        let r = sweep_file(path, &args);
        merge(&mut aggregate, &r);
    }

    println!(
        "total: cases={} simplified={} verified={} parity={} unsafe={} unchanged={} skipped={} errored={}",
        aggregate.total,
        aggregate.simplified,
        aggregate.verified,
        aggregate.parity,
        aggregate.unsafe_changes,
        aggregate.unchanged,
        aggregate.skipped,
        aggregate.errored,
    );

    if args.fail_on_unsafe && aggregate.unsafe_changes > 0 {
        return ExitCode::FAILURE;
    }
    if args.fail_on_error && aggregate.errored > 0 {
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}

fn main() -> ExitCode {
    thread::Builder::new()
        .name("cobra-sweep".into())
        .stack_size(SWEEP_STACK_SIZE)
        .spawn(run)
        .expect("spawn cobra-sweep worker")
        .join()
        .expect("cobra-sweep worker panicked")
}
