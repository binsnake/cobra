//! Minimal sample sweep — a handful of representative MBA cases. The
//! full dataset sweep is intentionally *not* run here; this test only
//! proves that the harness wires up correctly and the pipeline solves
//! a small known-good batch. For the full sweep, use the
//! `cobra-sweep` binary.

use cobra_testkit::{parse_dataset, run_case, Case, CaseKind, Report};

const SAMPLE: &str = r"# Minimal dataset sample — one case per shape.
# Simple XOR identity.
(x ^ y) + 2 * (x & y), x + y
# Boolean 3-variable identity.
(a & ~b) | (~a & b) | (a & b), a | b
# Affine identity.
x + x, 2 * x
# Polynomial shape (passes through unchanged — already simple).
x*x + x*y, x*x + x*y
";

#[test]
fn harness_parses_sample_lines() {
    let cases = parse_dataset(SAMPLE);
    assert_eq!(cases.len(), 4);
    assert_eq!(cases[0].input, "(x ^ y) + 2 * (x & y)");
    assert_eq!(cases[0].expected, "x + y");
}

#[test]
fn pipeline_verifies_minimal_sample() {
    let cases = parse_dataset(SAMPLE);
    let mut report = Report::default();
    let mut regressions: Vec<String> = Vec::new();
    for case in &cases {
        let r = run_case(case, 64);
        report.record(&r);
        if matches!(r.kind, CaseKind::Simplified) && !r.equivalent_to_input {
            regressions.push(format!(
                "line {}: simplified diverges from input",
                case.line_number
            ));
        }
        if let Some(e) = &r.error {
            regressions.push(format!("line {}: {e}", case.line_number));
        }
    }

    assert!(
        regressions.is_empty(),
        "safety regressions on sample:\n{}",
        regressions.join("\n")
    );
    assert_eq!(report.total, 4);
    assert_eq!(report.unsafe_changes, 0);
    assert_eq!(report.errored, 0);
}

/// Regression for the nested-lift ghost-variable leak: an inner lift binds
/// `r0` (group A) and an outer lift binds `v0` (nested group B); when group B
/// resolved it used to emit a free candidate that bypassed group A, leaving
/// `r0` (a lifted var with index >= the 2 input vars b,e) in the final expr.
/// That previously PANICKED in `expr::render` and tripped the harness'
/// "simplified vars are not a subset of input vars" check.
///
/// This case has only two input variables (`b`, `e`), so any var index >= 2 in
/// the output is a leak. `run_case` rejects such an output as `Errored`
/// (its `remap_to_input_space` returns `None`), so asserting `errored == 0`
/// and `unsafe_changes == 0` proves the output's vars are a subset of input
/// (max var index < 2) and that it is never an unsafe rewrite.
#[test]
fn nested_lift_does_not_leak_ghost_variable() {
    let case = Case {
        line_number: 1,
        input: "~ (~ ((((~ b | e) + b) + 1) - 1) - (~ ((((~ b | e) + b) + 1) \
                - 1) & ((b ^ b) + ((b & b) + (b & b))))) + 1"
            .into(),
        // Ground truth is irrelevant here — we only assert the safety/subset
        // invariants, so echo the input as the "expected" column.
        expected: "~ (~ ((((~ b | e) + b) + 1) - 1) - (~ ((((~ b | e) + b) + 1) \
                   - 1) & ((b ^ b) + ((b & b) + (b & b))))) + 1"
            .into(),
    };

    let report = run_case(&case, 64);

    // No leaked lifted/aux variable: a var index >= 2 (only b,e are inputs)
    // would make `run_case` return `Errored`.
    assert_ne!(
        report.kind,
        CaseKind::Errored,
        "nested-lift leak: output references a variable not in the input \
         (error: {:?})",
        report.error
    );
    // Whether the pipeline simplifies it or leaves it unchanged, the result
    // must never be an unsafe (non-input-equivalent) rewrite.
    if report.kind == CaseKind::Simplified {
        assert!(
            report.equivalent_to_input,
            "nested-lift case produced an output that diverges from the input"
        );
    }
}
