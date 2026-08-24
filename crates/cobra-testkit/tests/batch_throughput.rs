//! Batch-throughput measurement: many expressions simplified in quick
//! succession through the public `simplify_expr` entry point, the way a
//! deobfuscator embedding the library calls it.
//!
//! Ignored by default; run explicitly with
//! `cargo test --release --test batch_throughput -- --ignored --nocapture`.

use std::time::Instant;

use cobra::{parse_to_ast, simplify_expr, Options};

/// (label, expression, parses-at-all sanity)
const CORPUS: &[(&str, &str)] = &[
    ("trivial", "x + y"),
    ("single_lemma", "(x ^ y) + 2 * (x & y)"),
    ("absorption", "x & (x | y)"),
    ("chain", "(x & y) + (x | y) + 0"),
    ("mba_dense", "2*(x|y) - (x^y)"),
    ("three_var", "(x & y) * (x | y) + (x & ~y) * (~x & y) + z"),
    ("no_progress", "x ^ y ^ x"),
];

fn run_batch_with(label: &str, source: &str, iterations: u32, opts: &Options) {
    let parsed = parse_to_ast(source, 64).expect("corpus parses");
    let started = Instant::now();
    for _ in 0..iterations {
        let outcome =
            simplify_expr(&parsed.expr, &parsed.vars, opts.clone()).expect("simplify succeeds");
        std::hint::black_box(&outcome);
    }
    let elapsed = started.elapsed();
    println!(
        "{label:>14}: {iterations} calls in {:>8.1?}  ({:>9.1?}/call)",
        elapsed,
        elapsed / iterations
    );
}

fn run_batch(label: &str, source: &str, iterations: u32) {
    run_batch_with(label, source, iterations, &Options::default());
}

#[test]
#[ignore = "throughput measurement, run explicitly with --ignored --nocapture"]
fn batch_throughput() {
    // Warm the per-process caches (pattern tables, etc.) so the measurement
    // reflects steady-state batch behaviour, not first-call setup.
    for (_, source) in CORPUS {
        let parsed = parse_to_ast(source, 64).expect("corpus parses");
        let _ = simplify_expr(&parsed.expr, &parsed.vars, Options::default());
    }

    for (label, source) in CORPUS {
        run_batch(label, source, 200);
    }

    println!("--- spot_check = false ---");
    let no_spot = Options {
        spot_check: false,
        ..Options::default()
    };
    for (label, source) in CORPUS {
        run_batch_with(label, source, 200, &no_spot);
    }

    println!("--- bitwise decomposition disabled ---");
    let no_decomp = Options {
        enable_bitwise_decomposition: false,
        ..Options::default()
    };
    for (label, source) in CORPUS {
        run_batch_with(label, source, 200, &no_decomp);
    }
}
