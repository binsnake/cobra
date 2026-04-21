//! Dataset harness for the `CoBRA` pipeline.
//!
//! - [`parse_dataset`] splits a `.txt` file into `(input, expected)`
//!   pairs. Comments (`#`) and blank lines are skipped. The separator
//!   `find_separator` behaviour (respecting parens and brackets).
//! - [`run_case`] drives one expression through the Rust pipeline and
//!   (simplified ≡ expected) and a safety check (simplified ≡ input).
//! - [`Report`] aggregates a batch of [`CaseReport`]s for a sweep.
//!
//! The harness is deliberately small — dataset streaming and the
//! sweep binary live on top of this library.

use cobra_core::evaluate_boolean_signature;
use cobra_core::evaluator::Evaluator;
use cobra_core::expr::Expr;
use cobra_core::expr_rewrite::build_var_support;
use cobra_core::expr_utils::remap_var_indices;
use cobra_core::simplify_outcome::{Options, SimplifyOutcomeKind};

use cobra_orchestrator::{OrchestratorContext, OrchestratorPolicy, Worklist};
use cobra_parser::parse_to_ast;
use cobra_passes::{full_width_check_eval, seed_with_ast, PASS_REGISTRY};

#[derive(Clone, Debug)]
pub struct Case {
    pub line_number: u32,
    pub input: String,
    pub expected: String,
}

/// Parse a dataset file body into `(input, expected)` pairs.
///
/// - lines starting with `#` are comments,
/// - blank lines are ignored,
/// - if a top-level tab (`\t`) is present, it separates input from
///   expected (`input <TAB> expected`),
/// - otherwise the line is a comma-separated list of one-or-more
///   equivalent forms. The *first* form is the obfuscated input; the
///   *last* is the canonical simplified form; middle forms are
///   alternative representations and are skipped.
///
/// The comma mode handles both the common `input,expected` layout
/// and the `input, alt1, ..., altN, expected` layout used by
/// datasets like `gamba/mba_flatten.txt`.
#[must_use]
pub fn parse_dataset(body: &str) -> Vec<Case> {
    let mut out = Vec::new();
    for (idx, raw) in body.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (input, expected) = if let Some(tab) = top_level_tab(line) {
            (line[..tab].trim().to_string(), line[tab + 1..].trim().to_string())
        } else {
            let commas = top_level_commas(line);
            let Some(&first) = commas.first() else {
                continue;
            };
            let last = *commas.last().expect("non-empty checked above");
            (
                line[..first].trim().to_string(),
                line[last + 1..].trim().to_string(),
            )
        };
        if input.is_empty() || expected.is_empty() {
            continue;
        }
        // Placeholder for "no ground truth": several datasets use a
        // lone `-` in the expected column. Skip those rather than
        // counting them as parse errors.
        if expected == "-" {
            continue;
        }
        out.push(Case {
            line_number: (idx + 1) as u32,
            input,
            expected,
        });
    }
    out
}

fn top_level_tab(line: &str) -> Option<usize> {
    let mut depth: i32 = 0;
    for (i, b) in line.bytes().enumerate() {
        match b {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b'\t' if depth == 0 => return Some(i),
            _ => {}
        }
    }
    None
}

fn top_level_commas(line: &str) -> Vec<usize> {
    let mut out = Vec::new();
    let mut depth: i32 = 0;
    for (i, b) in line.bytes().enumerate() {
        match b {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b',' if depth == 0 => out.push(i),
            _ => {}
        }
    }
    out
}

/// Top-level disposition for one case.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CaseKind {
    /// Pipeline produced a simplified expression.
    Simplified,
    Unchanged,
    /// Failure before the pipeline reached a decision (parse / seed / pipeline error).
    Errored,
}

/// Result of running one dataset case. Carries both a safety check
#[derive(Clone, Debug)]
pub struct CaseReport {
    pub kind: CaseKind,
    /// True when the pipeline simplified and `simplified ≡ input` on
    /// the full-width probe set. Always `false` for `Unchanged` /
    /// `Errored`.
    pub equivalent_to_input: bool,
    /// True when the pipeline simplified and `simplified ≡ expected`
    /// on the full-width probe set. Always `false` for `Unchanged` /
    /// `Errored`.
    pub matches_expected: bool,
    /// On `Errored`, a short message.
    pub error: Option<String>,
}

/// Drive one `Case` through the pipeline and compare against both the
/// using a 256-sample full-width probe.
#[must_use]
pub fn run_case(case: &Case, bitwidth: u32) -> CaseReport {
    let Ok(parsed_input) = parse_to_ast(&case.input, bitwidth) else {
        return errored("input parse failed");
    };
    let Ok(parsed_expected) = parse_to_ast(&case.expected, bitwidth) else {
        return errored("expected parse failed");
    };

    let input_expr = parsed_input.expr.clone_tree();
    let opts = Options {
        bitwidth,
        ..Options::default()
    };
    let mut ctx = OrchestratorContext::new(opts, parsed_input.vars.clone(), bitwidth);
    ctx.evaluator = Some(Evaluator::from_expr(&input_expr, bitwidth));
    ctx.input_sig =
        evaluate_boolean_signature(&input_expr, parsed_input.vars.len() as u32, bitwidth);

    let mut worklist = Worklist::new();
    if seed_with_ast(&input_expr, &mut ctx, &mut worklist).is_err() {
        return errored("seed failed");
    }

    let outcome = match cobra_orchestrator::simplify_from_worklist(
        &mut ctx,
        worklist,
        OrchestratorPolicy::default(),
        PASS_REGISTRY,
        Some(&input_expr),
    ) {
        Ok(o) => o,
        Err(e) => return errored(&format!("pipeline error: {e:?}")),
    };

    match outcome.kind {
        SimplifyOutcomeKind::UnchangedUnsupported | SimplifyOutcomeKind::Error => CaseReport {
            kind: CaseKind::Unchanged,
            equivalent_to_input: false,
            matches_expected: false,
            error: None,
        },
        SimplifyOutcomeKind::Simplified => {
            // Remap the simplified expression from the orchestrator's
            // reduced `real_vars` space back into the original
            // dataset-test post-processing.
            let simplified_raw = outcome.expr.as_ref().expect("Simplified carries expr");
            let mut simplified = simplified_raw.clone();
            if !outcome.real_vars.is_empty()
                && outcome.real_vars.len() < parsed_input.vars.len()
            {
                let idx_map = build_var_support(&parsed_input.vars, &outcome.real_vars);
                remap_var_indices(&mut simplified, &idx_map);
            }
            let n_vars = parsed_input.vars.len().max(parsed_expected.vars.len()) as u32;
            let equivalent_to_input =
                probes_match(&input_expr, &simplified, n_vars, bitwidth);
            let matches_expected =
                probes_match(&parsed_expected.expr, &simplified, n_vars, bitwidth);
            CaseReport {
                kind: CaseKind::Simplified,
                equivalent_to_input,
                matches_expected,
                error: None,
            }
        }
    }
}

fn probes_match(reference: &Expr, candidate: &Expr, n_vars: u32, bitwidth: u32) -> bool {
    let eval = Evaluator::from_expr(reference, bitwidth);
    full_width_check_eval(&eval, n_vars, candidate, bitwidth, 256).passed
}

fn errored(msg: &str) -> CaseReport {
    CaseReport {
        kind: CaseKind::Errored,
        equivalent_to_input: false,
        matches_expected: false,
        error: Some(msg.to_string()),
    }
}

/// Aggregated tally for a batch of cases.
#[derive(Clone, Debug, Default)]
pub struct Report {
    pub total: u32,
    /// Pipeline produced a simplified expression.
    pub simplified: u32,
    /// `simplified ≡ input` on the probe set. Subset of `simplified`.
    pub verified: u32,
    /// `simplified ≡ expected` on the probe set. Subset of `simplified`.
    pub parity: u32,
    /// Pipeline ran but left the input unchanged.
    pub unchanged: u32,
    /// Setup / pipeline error.
    pub errored: u32,
    /// Pipeline simplified but diverged from the input — a correctness
    /// regression. Subset of `simplified`, disjoint from `verified`.
    pub unsafe_changes: u32,
}

impl Report {
    pub fn record(&mut self, r: &CaseReport) {
        self.total += 1;
        match r.kind {
            CaseKind::Simplified => {
                self.simplified += 1;
                if r.equivalent_to_input {
                    self.verified += 1;
                } else {
                    self.unsafe_changes += 1;
                }
                if r.matches_expected {
                    self.parity += 1;
                }
            }
            CaseKind::Unchanged => self.unchanged += 1,
            CaseKind::Errored => self.errored += 1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_dataset_skips_comments_and_blanks() {
        let body = "# header\n\nx + y, x + y\n# another\n(x ^ y) + 2*(x & y),x + y\n";
        let cases = parse_dataset(body);
        assert_eq!(cases.len(), 2);
        assert_eq!(cases[0].input, "x + y");
        assert_eq!(cases[0].expected, "x + y");
        assert_eq!(cases[1].input, "(x ^ y) + 2*(x & y)");
        assert_eq!(cases[1].expected, "x + y");
    }

    #[test]
    fn parse_dataset_splits_on_top_level_commas() {
        // Commas inside parens are ignored; first top-level comma
        // starts the input/expected split, last top-level comma
        // starts the expected form.
        let body = "f(a, b) + 1, f(a, b) + 1\n";
        let cases = parse_dataset(body);
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].input, "f(a, b) + 1");
        assert_eq!(cases[0].expected, "f(a, b) + 1");
    }

    #[test]
    fn parse_dataset_handles_multi_form_lines() {
        // `input, alt1, alt2, expected` — middle forms are skipped.
        let body = "x + y, (x ^ y) + 2*(x & y), x | y, x + y\n";
        let cases = parse_dataset(body);
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].input, "x + y");
        assert_eq!(cases[0].expected, "x + y");
    }

    #[test]
    fn parse_dataset_handles_tab_separator() {
        // A top-level tab beats the comma split (oses/* datasets).
        let body = "f(a, b) + 1\tg(a, b) + 2\n";
        let cases = parse_dataset(body);
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].input, "f(a, b) + 1");
        assert_eq!(cases[0].expected, "g(a, b) + 2");
    }

    #[test]
    fn report_tallies_outcomes() {
        let mut r = Report::default();
        r.record(&CaseReport {
            kind: CaseKind::Simplified,
            equivalent_to_input: true,
            matches_expected: true,
            error: None,
        });
        r.record(&CaseReport {
            kind: CaseKind::Simplified,
            equivalent_to_input: true,
            matches_expected: false,
            error: None,
        });
        r.record(&CaseReport {
            kind: CaseKind::Simplified,
            equivalent_to_input: false,
            matches_expected: false,
            error: None,
        });
        r.record(&CaseReport {
            kind: CaseKind::Unchanged,
            equivalent_to_input: false,
            matches_expected: false,
            error: None,
        });
        r.record(&CaseReport {
            kind: CaseKind::Errored,
            equivalent_to_input: false,
            matches_expected: false,
            error: Some("x".into()),
        });
        assert_eq!(r.total, 5);
        assert_eq!(r.simplified, 3);
        assert_eq!(r.verified, 2);
        assert_eq!(r.parity, 1);
        assert_eq!(r.unsafe_changes, 1);
        assert_eq!(r.unchanged, 1);
        assert_eq!(r.errored, 1);
    }
}
