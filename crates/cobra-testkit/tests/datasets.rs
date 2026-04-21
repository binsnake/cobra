//! Minimal sample sweep — a handful of representative MBA cases. The
//! full dataset sweep is intentionally *not* run here; this test only
//! proves that the harness wires up correctly and the pipeline solves
//! a small known-good batch. For the full sweep, use the
//! `cobra-sweep` binary.

use cobra_testkit::{parse_dataset, run_case, CaseKind, Report};

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
