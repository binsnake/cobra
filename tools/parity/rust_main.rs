//! In-process Rust runner for the cross-language `CoBRA` parity harness.
//!
//! The manifest and JSONL schemas are documented in `tools/parity/README.md`.
//! This binary intentionally avoids CLI/serialization dependencies so the
//! measured stages contain only the library work named in the output.

use std::env;
use std::fs::File;
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, Instant};

use cobra::core::expr_cost::{compute_cost, ExprCost};
use cobra::core::{compile, eval as eval_compiled, evaluate_boolean_signature};
use cobra::{
    build_var_support, parse_to_ast, remap_var_indices, render, simplify, Expr, Options,
    SimplifyOutcome, SimplifyOutcomeKind,
};

const SCHEMA: &str = "cobra-parity-v2";
const RUNNER_STACK_SIZE: usize = 64 * 1024 * 1024;
const FULL_WIDTH_PROBE_ALGORITHM: &str = "splitmix64-v1";
const FULL_WIDTH_PROBE_COUNT: usize = 256;
const FULL_WIDTH_PROBE_SEED: u64 = 0x243f_6a88_85a3_08d3;
const FNV1A_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
const FNV1A_PRIME: u64 = 0x0000_0100_0000_01b3;

#[derive(Debug)]
struct Args {
    manifest: PathBuf,
    output: Option<PathBuf>,
    warmup: usize,
    repetitions: usize,
}

#[derive(Clone, Debug)]
struct Case {
    id: String,
    bitwidth: u32,
    max_vars: u32,
    expression: String,
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
struct Cost {
    weighted_size: u32,
    nonlinear_mul_count: u32,
    max_depth: u32,
}

impl From<ExprCost> for Cost {
    fn from(value: ExprCost) -> Self {
        Self {
            weighted_size: value.weighted_size,
            nonlinear_mul_count: value.nonlinear_mul_count,
            max_depth: value.max_depth,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Snapshot {
    outcome: String,
    verified: bool,
    proof_level: String,
    semantic_class: String,
    structural_flags: u32,
    reason_category: String,
    reason_domain: String,
    reason_subcode: u16,
    vars_count: usize,
    real_vars_count: usize,
    signature_len: usize,
    signature_hash: String,
    output_signature_len: usize,
    output_signature_hash: String,
    full_width_probe_algorithm: String,
    full_width_probe_count: usize,
    input_full_width_hash: String,
    output_full_width_hash: String,
    full_width_probe_equivalent: bool,
    full_width_probe_mismatch_count: usize,
    input_cost: Option<Cost>,
    output_cost: Option<Cost>,
    output: String,
    error: String,
}

#[derive(Copy, Clone, Debug, Default)]
struct StageTimes {
    parse: u64,
    signature: u64,
    simplify: u64,
    render: u64,
}

#[derive(Debug)]
struct TimedRun {
    snapshot: Snapshot,
    times: StageTimes,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FullWidthFingerprint {
    input_hash: String,
    output_hash: String,
    equivalent: bool,
    mismatch_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SemanticFingerprint {
    output_signature_len: usize,
    output_signature_hash: String,
    full_width: FullWidthFingerprint,
}

#[derive(Debug)]
struct CaseRecord {
    snapshot: Snapshot,
    deterministic: bool,
    parse_samples: Vec<u64>,
    signature_samples: Vec<u64>,
    simplify_samples: Vec<u64>,
    render_samples: Vec<u64>,
}

fn usage() -> &'static str {
    "Usage: cobra-parity-rust --manifest <path> [--output <path|->] \
     [--warmup <n>] [--repetitions <n>]"
}

fn parse_usize_flag(flag: &str, value: Option<String>) -> Result<usize, String> {
    value
        .ok_or_else(|| format!("{flag} requires a value"))?
        .parse::<usize>()
        .map_err(|_| format!("{flag} must be a non-negative integer"))
}

fn parse_args() -> Result<Args, String> {
    let mut manifest = None;
    let mut output = None;
    let mut warmup = 1usize;
    let mut repetitions = 5usize;
    let mut argv = env::args().skip(1);

    while let Some(arg) = argv.next() {
        match arg.as_str() {
            "--manifest" => {
                manifest = Some(PathBuf::from(
                    argv.next()
                        .ok_or_else(|| "--manifest requires a path".to_owned())?,
                ));
            }
            "--output" => {
                let value = argv
                    .next()
                    .ok_or_else(|| "--output requires a path or '-'".to_owned())?;
                if value == "-" {
                    output = None;
                } else {
                    output = Some(PathBuf::from(value));
                }
            }
            "--warmup" => warmup = parse_usize_flag("--warmup", argv.next())?,
            "--repetitions" => {
                repetitions = parse_usize_flag("--repetitions", argv.next())?;
            }
            "--help" | "-h" => return Err(usage().to_owned()),
            other => return Err(format!("unknown option '{other}'\n{}", usage())),
        }
    }

    if repetitions == 0 {
        return Err("--repetitions must be at least 1".to_owned());
    }
    Ok(Args {
        manifest: manifest.ok_or_else(|| format!("--manifest is required\n{}", usage()))?,
        output,
        warmup,
        repetitions,
    })
}

fn read_manifest(path: &PathBuf) -> Result<Vec<Case>, String> {
    let file = File::open(path)
        .map_err(|error| format!("failed to open manifest '{}': {error}", path.display()))?;
    let mut cases = Vec::new();

    for (zero_based_line, line_result) in BufReader::new(file).lines().enumerate() {
        let line_number = zero_based_line + 1;
        let line = line_result
            .map_err(|error| format!("failed to read manifest line {line_number}: {error}"))?;
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }

        let fields: Vec<&str> = line.splitn(4, '\t').collect();
        if fields.len() != 4 {
            return Err(format!(
                "manifest line {line_number} must contain four tab-separated fields"
            ));
        }
        if fields[0].is_empty() {
            return Err(format!("manifest line {line_number} has an empty case id"));
        }
        if cases.iter().any(|case: &Case| case.id == fields[0]) {
            return Err(format!(
                "manifest line {line_number} repeats case id '{}'",
                fields[0]
            ));
        }

        let bitwidth = fields[1].parse::<u32>().map_err(|_| {
            format!(
                "manifest line {line_number} has invalid bitwidth '{}'",
                fields[1]
            )
        })?;
        if !(1..=64).contains(&bitwidth) {
            return Err(format!(
                "manifest line {line_number} bitwidth must be in 1..=64"
            ));
        }
        let max_vars = fields[2].parse::<u32>().map_err(|_| {
            format!(
                "manifest line {line_number} has invalid max_vars '{}'",
                fields[2]
            )
        })?;
        if fields[3].is_empty() {
            return Err(format!(
                "manifest line {line_number} has an empty expression"
            ));
        }

        cases.push(Case {
            id: fields[0].to_owned(),
            bitwidth,
            max_vars,
            expression: fields[3].to_owned(),
        });
    }

    if cases.is_empty() {
        return Err("manifest contains no cases".to_owned());
    }
    Ok(cases)
}

fn duration_ns(duration: Duration) -> u64 {
    u64::try_from(duration.as_nanos()).unwrap_or(u64::MAX)
}

fn fnv1a_u64s(values: &[u64]) -> String {
    let mut hash = FNV1A_OFFSET_BASIS;
    for value in values {
        for byte in value.to_le_bytes() {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(FNV1A_PRIME);
        }
    }
    format!("{hash:016x}")
}

fn update_fnv1a_u64(hash: &mut u64, value: u64) {
    for byte in value.to_le_bytes() {
        *hash ^= u64::from(byte);
        *hash = hash.wrapping_mul(FNV1A_PRIME);
    }
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut value = *state;
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn full_width_fingerprint(
    input: &Expr,
    output: &Expr,
    num_vars: u32,
    bitwidth: u32,
) -> FullWidthFingerprint {
    let mask = if bitwidth == 64 {
        u64::MAX
    } else {
        (1u64 << bitwidth) - 1
    };
    let input_program = compile(input, bitwidth);
    let output_program = compile(output, bitwidth);
    let mut input_stack = Vec::with_capacity(input_program.stack_size);
    let mut output_stack = Vec::with_capacity(output_program.stack_size);
    let mut inputs = vec![0u64; num_vars as usize];
    let mut rng_state = FULL_WIDTH_PROBE_SEED ^ (u64::from(bitwidth) << 32) ^ u64::from(num_vars);
    let mut input_hash = FNV1A_OFFSET_BASIS;
    let mut output_hash = FNV1A_OFFSET_BASIS;
    let mut mismatch_count = 0usize;

    for probe_index in 0..FULL_WIDTH_PROBE_COUNT {
        match probe_index {
            0 => inputs.fill(0),
            1 => inputs.fill(mask),
            _ => {
                for value in &mut inputs {
                    *value = splitmix64(&mut rng_state) & mask;
                }
            }
        }

        let input_value = eval_compiled(&input_program, &inputs, &mut input_stack);
        let output_value = eval_compiled(&output_program, &inputs, &mut output_stack);
        update_fnv1a_u64(&mut input_hash, input_value);
        update_fnv1a_u64(&mut output_hash, output_value);
        mismatch_count += usize::from(input_value != output_value);
    }

    FullWidthFingerprint {
        input_hash: format!("{input_hash:016x}"),
        output_hash: format!("{output_hash:016x}"),
        equivalent: mismatch_count == 0,
        mismatch_count,
    }
}

fn semantic_fingerprint(
    input: &Expr,
    output: &Expr,
    num_vars: u32,
    bitwidth: u32,
) -> SemanticFingerprint {
    let output_signature = evaluate_boolean_signature(output, num_vars, bitwidth);
    SemanticFingerprint {
        output_signature_len: output_signature.len(),
        output_signature_hash: fnv1a_u64s(&output_signature),
        full_width: full_width_fingerprint(input, output, num_vars, bitwidth),
    }
}

fn outcome_name(kind: SimplifyOutcomeKind) -> &'static str {
    match kind {
        SimplifyOutcomeKind::Simplified => "simplified",
        SimplifyOutcomeKind::UnchangedUnsupported => "unchanged_unsupported",
        SimplifyOutcomeKind::Error => "error",
    }
}

fn reason_fields(outcome: &SimplifyOutcome) -> (String, String, u16) {
    outcome.diag.reason_code.as_ref().map_or_else(
        || ("None".to_owned(), "Orchestrator".to_owned(), 0),
        |reason| {
            (
                format!("{:?}", reason.category),
                format!("{:?}", reason.domain),
                reason.subcode,
            )
        },
    )
}

fn failed_snapshot(stage: &str, message: String) -> Snapshot {
    Snapshot {
        outcome: format!("{stage}_error"),
        error: message,
        reason_category: "None".to_owned(),
        reason_domain: "Orchestrator".to_owned(),
        ..Snapshot::default()
    }
}

fn run_once(case: &Case) -> TimedRun {
    let mut times = StageTimes::default();

    let started = Instant::now();
    let parsed_result = parse_to_ast(&case.expression, case.bitwidth);
    times.parse = duration_ns(started.elapsed());
    let parsed = match parsed_result {
        Ok(parsed) => parsed,
        Err(error) => {
            return TimedRun {
                snapshot: failed_snapshot("parse", error.message),
                times,
            };
        }
    };

    let input_cost = Cost::from(compute_cost(&parsed.expr).cost);

    let started = Instant::now();
    let signature =
        evaluate_boolean_signature(&parsed.expr, parsed.vars.len() as u32, case.bitwidth);
    times.signature = duration_ns(started.elapsed());
    let signature_hash = fnv1a_u64s(&signature);

    let started = Instant::now();
    let options = Options {
        bitwidth: case.bitwidth,
        max_vars: case.max_vars,
        ..Options::default()
    };
    let simplify_result = simplify(&signature, &parsed.vars, Some(&parsed.expr), options);
    times.simplify = duration_ns(started.elapsed());
    let outcome = match simplify_result {
        Ok(outcome) => outcome,
        Err(error) => {
            let mut snapshot = failed_snapshot("simplify", error.message);
            snapshot.vars_count = parsed.vars.len();
            snapshot.signature_len = signature.len();
            snapshot.signature_hash = signature_hash;
            snapshot.input_cost = Some(input_cost);
            return TimedRun { snapshot, times };
        }
    };

    let mut display_expr = if outcome.kind == SimplifyOutcomeKind::Simplified {
        outcome
            .expr
            .clone()
            .unwrap_or_else(|| parsed.expr.clone_tree())
    } else {
        parsed.expr.clone_tree()
    };
    if outcome.kind == SimplifyOutcomeKind::Simplified
        && !outcome.real_vars.is_empty()
        && outcome.real_vars.len() < parsed.vars.len()
    {
        let index_map = build_var_support(&parsed.vars, &outcome.real_vars);
        remap_var_indices(Arc::make_mut(&mut display_expr), &index_map);
    }

    let started = Instant::now();
    let output = render(&display_expr, &parsed.vars, case.bitwidth);
    times.render = duration_ns(started.elapsed());
    let output_cost = Cost::from(compute_cost(&display_expr).cost);
    let semantics = semantic_fingerprint(
        &parsed.expr,
        &display_expr,
        parsed.vars.len() as u32,
        case.bitwidth,
    );

    let (reason_category, reason_domain, reason_subcode) = reason_fields(&outcome);

    TimedRun {
        snapshot: Snapshot {
            outcome: outcome_name(outcome.kind).to_owned(),
            verified: outcome.verified,
            proof_level: format!("{:?}", outcome.proof_level),
            semantic_class: format!("{:?}", outcome.diag.classification.semantic),
            structural_flags: outcome.diag.classification.flags.bits(),
            reason_category,
            reason_domain,
            reason_subcode,
            vars_count: parsed.vars.len(),
            real_vars_count: outcome.real_vars.len(),
            signature_len: signature.len(),
            signature_hash,
            output_signature_len: semantics.output_signature_len,
            output_signature_hash: semantics.output_signature_hash,
            full_width_probe_algorithm: FULL_WIDTH_PROBE_ALGORITHM.to_owned(),
            full_width_probe_count: FULL_WIDTH_PROBE_COUNT,
            input_full_width_hash: semantics.full_width.input_hash,
            output_full_width_hash: semantics.full_width.output_hash,
            full_width_probe_equivalent: semantics.full_width.equivalent,
            full_width_probe_mismatch_count: semantics.full_width.mismatch_count,
            input_cost: Some(input_cost),
            output_cost: Some(output_cost),
            output,
            error: outcome.diag.reason.clone(),
        },
        times,
    }
}

fn run_case(case: &Case, warmup: usize, repetitions: usize) -> CaseRecord {
    for _ in 0..warmup {
        let _ = run_once(case);
    }

    let mut snapshot = None;
    let mut deterministic = true;
    let mut parse_samples = Vec::with_capacity(repetitions);
    let mut signature_samples = Vec::with_capacity(repetitions);
    let mut simplify_samples = Vec::with_capacity(repetitions);
    let mut render_samples = Vec::with_capacity(repetitions);

    for _ in 0..repetitions {
        let run = run_once(case);
        if let Some(first) = snapshot.as_ref() {
            deterministic &= first == &run.snapshot;
        } else {
            snapshot = Some(run.snapshot.clone());
        }
        parse_samples.push(run.times.parse);
        signature_samples.push(run.times.signature);
        simplify_samples.push(run.times.simplify);
        render_samples.push(run.times.render);
    }

    CaseRecord {
        snapshot: snapshot.expect("repetitions is validated as non-zero"),
        deterministic,
        parse_samples,
        signature_samples,
        simplify_samples,
        render_samples,
    }
}

fn json_escape(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len() + 8);
    for character in value.chars() {
        match character {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\u{08}' => escaped.push_str("\\b"),
            '\u{0c}' => escaped.push_str("\\f"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            c if c <= '\u{1f}' => {
                use std::fmt::Write as _;
                let _ = write!(escaped, "\\u{:04x}", u32::from(c));
            }
            c => escaped.push(c),
        }
    }
    escaped
}

fn push_string_field(json: &mut String, key: &str, value: &str) {
    use std::fmt::Write as _;
    let _ = write!(json, "\"{}\":\"{}\"", json_escape(key), json_escape(value));
}

fn push_cost(json: &mut String, cost: Option<Cost>) {
    use std::fmt::Write as _;
    if let Some(cost) = cost {
        let _ = write!(
            json,
            "{{\"weighted_size\":{},\"nonlinear_mul_count\":{},\"max_depth\":{}}}",
            cost.weighted_size, cost.nonlinear_mul_count, cost.max_depth
        );
    } else {
        json.push_str("null");
    }
}

fn push_u64_array(json: &mut String, values: &[u64]) {
    use std::fmt::Write as _;
    json.push('[');
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            json.push(',');
        }
        let _ = write!(json, "{value}");
    }
    json.push(']');
}

fn push_semantic_fields(json: &mut String, snapshot: &Snapshot) {
    use std::fmt::Write as _;

    let _ = write!(
        json,
        ",\"output_signature_len\":{}",
        snapshot.output_signature_len
    );
    json.push(',');
    push_string_field(
        json,
        "output_signature_hash",
        &snapshot.output_signature_hash,
    );
    json.push(',');
    push_string_field(
        json,
        "full_width_probe_algorithm",
        &snapshot.full_width_probe_algorithm,
    );
    let _ = write!(
        json,
        ",\"full_width_probe_count\":{}",
        snapshot.full_width_probe_count
    );
    json.push(',');
    push_string_field(
        json,
        "input_full_width_hash",
        &snapshot.input_full_width_hash,
    );
    json.push(',');
    push_string_field(
        json,
        "output_full_width_hash",
        &snapshot.output_full_width_hash,
    );
    let _ = write!(
        json,
        ",\"full_width_probe_equivalent\":{},\"full_width_probe_mismatch_count\":{}",
        snapshot.full_width_probe_equivalent, snapshot.full_width_probe_mismatch_count
    );
}

fn record_json(case: &Case, warmup: usize, repetitions: usize, record: &CaseRecord) -> String {
    use std::fmt::Write as _;

    let snapshot = &record.snapshot;
    let mut json = String::with_capacity(1024);
    json.push('{');
    push_string_field(&mut json, "schema", SCHEMA);
    json.push(',');
    push_string_field(&mut json, "engine", "rust");
    json.push(',');
    push_string_field(&mut json, "case_id", &case.id);
    json.push(',');
    push_string_field(&mut json, "expression", &case.expression);
    let _ = write!(
        json,
        ",\"bitwidth\":{},\"max_vars\":{},\"warmup\":{},\"repetitions\":{}",
        case.bitwidth, case.max_vars, warmup, repetitions
    );
    json.push(',');
    push_string_field(&mut json, "outcome", &snapshot.outcome);
    let _ = write!(
        json,
        ",\"verified\":{},\"deterministic\":{}",
        snapshot.verified, record.deterministic
    );
    json.push(',');
    push_string_field(&mut json, "proof_level", &snapshot.proof_level);
    json.push(',');
    push_string_field(&mut json, "semantic_class", &snapshot.semantic_class);
    let _ = write!(
        json,
        ",\"structural_flags\":{},\"vars_count\":{},\"real_vars_count\":{},\
         \"signature_len\":{}",
        snapshot.structural_flags,
        snapshot.vars_count,
        snapshot.real_vars_count,
        snapshot.signature_len
    );
    json.push(',');
    push_string_field(&mut json, "signature_hash", &snapshot.signature_hash);
    push_semantic_fields(&mut json, snapshot);
    json.push_str(",\"reason\":{");
    push_string_field(&mut json, "category", &snapshot.reason_category);
    json.push(',');
    push_string_field(&mut json, "domain", &snapshot.reason_domain);
    let _ = write!(json, ",\"subcode\":{}", snapshot.reason_subcode);
    json.push('}');
    json.push_str(",\"input_cost\":");
    push_cost(&mut json, snapshot.input_cost);
    json.push_str(",\"output_cost\":");
    push_cost(&mut json, snapshot.output_cost);
    json.push(',');
    push_string_field(&mut json, "output", &snapshot.output);
    json.push(',');
    push_string_field(&mut json, "error", &snapshot.error);
    json.push_str(",\"timings_ns\":{\"parse\":");
    push_u64_array(&mut json, &record.parse_samples);
    json.push_str(",\"signature\":");
    push_u64_array(&mut json, &record.signature_samples);
    json.push_str(",\"simplify\":");
    push_u64_array(&mut json, &record.simplify_samples);
    json.push_str(",\"render\":");
    push_u64_array(&mut json, &record.render_samples);
    json.push_str("}}");
    json
}

fn run(args: &Args) -> Result<(), String> {
    let cases = read_manifest(&args.manifest)?;
    let output: Box<dyn Write> = match &args.output {
        Some(path) => Box::new(
            File::create(path)
                .map_err(|error| format!("failed to create '{}': {error}", path.display()))?,
        ),
        None => Box::new(io::stdout()),
    };
    let mut writer = BufWriter::new(output);

    for case in &cases {
        let record = run_case(case, args.warmup, args.repetitions);
        writeln!(
            writer,
            "{}",
            record_json(case, args.warmup, args.repetitions, &record)
        )
        .map_err(|error| format!("failed to write results: {error}"))?;
    }
    writer
        .flush()
        .map_err(|error| format!("failed to flush results: {error}"))
}

fn real_main() -> Result<(), String> {
    let args = parse_args()?;
    let thread = std::thread::Builder::new()
        .name("cobra-parity-rust".to_owned())
        .stack_size(RUNNER_STACK_SIZE)
        .spawn(move || run(&args))
        .map_err(|error| format!("failed to start runner thread: {error}"))?;
    thread
        .join()
        .map_err(|_| "runner thread panicked".to_owned())?
}

fn main() {
    if let Err(error) = real_main() {
        eprintln!("{error}");
        std::process::exit(2);
    }
}
