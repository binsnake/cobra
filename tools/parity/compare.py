#!/usr/bin/env python3
"""Compare Rust/C++ CoBRA JSONL parity results and summarize timings."""

from __future__ import annotations

import argparse
import json
import math
import statistics
import sys
from pathlib import Path
from typing import Any


SCHEMA = "cobra-parity-v2"
STAGES = ("parse", "signature", "simplify", "render")
FULL_WIDTH_PROBE_ALGORITHM = "splitmix64-v1"
FULL_WIDTH_PROBE_COUNT = 256
CASE_FIELDS = (
    "expression",
    "bitwidth",
    "max_vars",
)
SEMANTIC_FIELDS = CASE_FIELDS + (
    "outcome",
    "signature_len",
    "signature_hash",
    "output_signature_len",
    "output_signature_hash",
    "full_width_probe_algorithm",
    "full_width_probe_count",
    "input_full_width_hash",
    "output_full_width_hash",
    "full_width_probe_equivalent",
    "full_width_probe_mismatch_count",
)
EXACT_FIELDS = SEMANTIC_FIELDS + (
    "input_cost",
    "output_cost",
    "output",
)
METADATA_FIELDS = (
    "semantic_class",
    "structural_flags",
    "vars_count",
    "real_vars_count",
    "verified",
    "proof_level",
    "reason",
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("rust", type=Path, help="Rust runner JSONL")
    parser.add_argument("cpp", type=Path, help="C++ runner JSONL")
    parser.add_argument(
        "--allow-output-difference",
        action="store_true",
        help="report, but do not fail on canonical output string differences",
    )
    parser.add_argument(
        "--semantic-parity",
        action="store_true",
        help=(
            "require matching outcomes and semantic fingerprints while treating "
            "rendered spelling, costs, and metadata as informational"
        ),
    )
    parser.add_argument(
        "--strict-metadata",
        action="store_true",
        help="also fail on diagnostics/proof metadata differences",
    )
    parser.add_argument(
        "--show-cases",
        action="store_true",
        help="print per-case timing medians in addition to aggregate ratios",
    )
    parser.add_argument(
        "--json-summary",
        type=Path,
        help="optionally write a machine-readable comparison summary",
    )
    return parser.parse_args()


def load_jsonl(path: Path, expected_engine: str) -> dict[str, dict[str, Any]]:
    records: dict[str, dict[str, Any]] = {}
    with path.open("r", encoding="utf-8") as source:
        for line_number, line in enumerate(source, 1):
            if not line.strip():
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as error:
                raise ValueError(f"{path}:{line_number}: invalid JSON: {error}") from error
            if record.get("schema") != SCHEMA:
                raise ValueError(
                    f"{path}:{line_number}: expected schema {SCHEMA!r}, "
                    f"got {record.get('schema')!r}"
                )
            if record.get("engine") != expected_engine:
                raise ValueError(
                    f"{path}:{line_number}: expected engine {expected_engine!r}, "
                    f"got {record.get('engine')!r}"
                )
            case_id = record.get("case_id")
            if not isinstance(case_id, str) or not case_id:
                raise ValueError(f"{path}:{line_number}: missing case_id")
            if case_id in records:
                raise ValueError(f"{path}:{line_number}: duplicate case_id {case_id!r}")
            timings = record.get("timings_ns")
            if not isinstance(timings, dict):
                raise ValueError(f"{path}:{line_number}: missing timings_ns")
            for stage in STAGES:
                values = timings.get(stage)
                if (
                    not isinstance(values, list)
                    or not values
                    or any(not isinstance(value, int) or value < 0 for value in values)
                ):
                    raise ValueError(
                        f"{path}:{line_number}: timings_ns.{stage} must be "
                        "a non-empty array of non-negative integers"
                    )
            records[case_id] = record
    if not records:
        raise ValueError(f"{path}: no records")
    return records


def median_ns(record: dict[str, Any], stage: str) -> float:
    return float(statistics.median(record["timings_ns"][stage]))


def geometric_mean(values: list[float]) -> float | None:
    positive = [value for value in values if value > 0 and math.isfinite(value)]
    if not positive:
        return None
    return math.exp(sum(math.log(value) for value in positive) / len(positive))


def format_value(value: Any) -> str:
    rendered = json.dumps(value, sort_keys=True, ensure_ascii=False)
    return rendered if len(rendered) <= 140 else rendered[:137] + "..."


def semantic_self_failures(
    case_id: str, engine: str, record: dict[str, Any]
) -> list[dict[str, Any]]:
    failures: list[dict[str, Any]] = []
    if (
        record.get("signature_len") != record.get("output_signature_len")
        or record.get("signature_hash") != record.get("output_signature_hash")
    ):
        failures.append(
            {
                "case_id": case_id,
                "field": f"{engine}.boolean_signature_equivalent",
                engine: {
                    "input_len": record.get("signature_len"),
                    "input_hash": record.get("signature_hash"),
                    "output_len": record.get("output_signature_len"),
                    "output_hash": record.get("output_signature_hash"),
                },
            }
        )
    if (
        record.get("full_width_probe_algorithm") != FULL_WIDTH_PROBE_ALGORITHM
        or record.get("full_width_probe_count") != FULL_WIDTH_PROBE_COUNT
        or record.get("full_width_probe_equivalent") is not True
        or record.get("full_width_probe_mismatch_count") != 0
        or record.get("input_full_width_hash") != record.get("output_full_width_hash")
    ):
        failures.append(
            {
                "case_id": case_id,
                "field": f"{engine}.full_width_probe_equivalent",
                engine: {
                    "algorithm": record.get("full_width_probe_algorithm"),
                    "count": record.get("full_width_probe_count"),
                    "input_hash": record.get("input_full_width_hash"),
                    "output_hash": record.get("output_full_width_hash"),
                    "equivalent": record.get("full_width_probe_equivalent"),
                    "mismatch_count": record.get("full_width_probe_mismatch_count"),
                },
            }
        )
    return failures


def main() -> int:
    args = parse_args()
    try:
        rust = load_jsonl(args.rust, "rust")
        cpp = load_jsonl(args.cpp, "cpp")
    except (OSError, ValueError) as error:
        print(f"comparison error: {error}", file=sys.stderr)
        return 2

    rust_ids = set(rust)
    cpp_ids = set(cpp)
    missing_in_cpp = sorted(rust_ids - cpp_ids)
    missing_in_rust = sorted(cpp_ids - rust_ids)
    common = sorted(rust_ids & cpp_ids)

    failures: list[dict[str, Any]] = []
    metadata_differences: list[dict[str, Any]] = []
    if missing_in_cpp:
        failures.append({"case_id": None, "field": "missing_in_cpp", "rust": missing_in_cpp})
    if missing_in_rust:
        failures.append({"case_id": None, "field": "missing_in_rust", "cpp": missing_in_rust})

    hard_fields = list(SEMANTIC_FIELDS if args.semantic_parity else EXACT_FIELDS)
    if args.allow_output_difference and not args.semantic_parity:
        hard_fields.remove("output")

    for case_id in common:
        rust_record = rust[case_id]
        cpp_record = cpp[case_id]
        if not rust_record.get("deterministic", False):
            failures.append(
                {
                    "case_id": case_id,
                    "field": "rust.deterministic",
                    "rust": rust_record.get("deterministic"),
                }
            )
        if not cpp_record.get("deterministic", False):
            failures.append(
                {
                    "case_id": case_id,
                    "field": "cpp.deterministic",
                    "cpp": cpp_record.get("deterministic"),
                }
            )
        failures.extend(semantic_self_failures(case_id, "rust", rust_record))
        failures.extend(semantic_self_failures(case_id, "cpp", cpp_record))
        for field in hard_fields:
            if rust_record.get(field) != cpp_record.get(field):
                failures.append(
                    {
                        "case_id": case_id,
                        "field": field,
                        "rust": rust_record.get(field),
                        "cpp": cpp_record.get(field),
                    }
                )
        informational_fields = list(METADATA_FIELDS)
        if args.semantic_parity:
            informational_fields.extend(("input_cost", "output_cost", "output"))
        elif args.allow_output_difference:
            informational_fields.append("output")
        for field in informational_fields:
            if rust_record.get(field) != cpp_record.get(field):
                difference = {
                    "case_id": case_id,
                    "field": field,
                    "rust": rust_record.get(field),
                    "cpp": cpp_record.get(field),
                }
                metadata_differences.append(difference)
                if args.strict_metadata and field in METADATA_FIELDS:
                    failures.append(difference)

    ratios_by_stage: dict[str, list[float]] = {stage: [] for stage in STAGES}
    timing_cases: list[dict[str, Any]] = []
    for case_id in common:
        stage_values: dict[str, dict[str, float | None]] = {}
        for stage in STAGES:
            rust_median = median_ns(rust[case_id], stage)
            cpp_median = median_ns(cpp[case_id], stage)
            ratio = rust_median / cpp_median if cpp_median > 0 else None
            if ratio is not None and ratio > 0:
                ratios_by_stage[stage].append(ratio)
            stage_values[stage] = {
                "rust_median_ns": rust_median,
                "cpp_median_ns": cpp_median,
                "rust_over_cpp": ratio,
            }
        timing_cases.append({"case_id": case_id, "stages": stage_values})

    aggregates = {
        stage: {
            "geomean_rust_over_cpp": geometric_mean(ratios_by_stage[stage]),
            "case_count": len(ratios_by_stage[stage]),
        }
        for stage in STAGES
    }

    mismatch_units = {
        difference.get("case_id") or "<manifest>" for difference in failures
    }
    print(
        f"Compared {len(common)} common case(s) in "
        f"{'semantic' if args.semantic_parity else 'exact'} mode: "
        f"{len(failures)} strict field mismatch(es) across "
        f"{len(mismatch_units)} case(s), "
        f"{len(metadata_differences)} informational difference(s)."
    )
    if failures:
        print("\nStrict mismatches:")
        for difference in failures:
            label = difference.get("case_id") or "<manifest>"
            print(f"  {label} :: {difference['field']}")
            if "rust" in difference:
                print(f"    rust: {format_value(difference['rust'])}")
            if "cpp" in difference:
                print(f"    cpp:  {format_value(difference['cpp'])}")

    if metadata_differences:
        mode = "strict" if args.strict_metadata else "informational"
        print(f"\nInformational differences ({mode}):")
        for difference in metadata_differences:
            print(
                f"  {difference['case_id']} :: {difference['field']}: "
                f"rust={format_value(difference['rust'])}, "
                f"cpp={format_value(difference['cpp'])}"
            )

    if args.show_cases and timing_cases:
        print("\nPer-case medians (ns; Rust/C++ > 1 means Rust is slower):")
        print(f"  {'case':28} {'stage':10} {'rust':>12} {'cpp':>12} {'ratio':>9}")
        for timing_case in timing_cases:
            for stage in STAGES:
                values = timing_case["stages"][stage]
                ratio = values["rust_over_cpp"]
                ratio_text = "n/a" if ratio is None else f"{ratio:.3f}x"
                print(
                    f"  {timing_case['case_id'][:28]:28} {stage:10} "
                    f"{values['rust_median_ns']:12.0f} "
                    f"{values['cpp_median_ns']:12.0f} {ratio_text:>9}"
                )

    print("\nAggregate geometric-mean ratios (Rust/C++):")
    for stage in STAGES:
        ratio = aggregates[stage]["geomean_rust_over_cpp"]
        ratio_text = "n/a" if ratio is None else f"{ratio:.3f}x"
        print(f"  {stage:10} {ratio_text}")

    summary = {
        "schema": SCHEMA,
        "comparison_mode": "semantic" if args.semantic_parity else "exact",
        "common_case_count": len(common),
        "strict_mismatch_count": len(failures),
        "strict_mismatch_case_count": len(mismatch_units),
        "metadata_difference_count": len(metadata_differences),
        "strict_mismatches": failures,
        "metadata_differences": metadata_differences,
        "timing_cases": timing_cases,
        "timing_aggregates": aggregates,
    }
    if args.json_summary is not None:
        args.json_summary.parent.mkdir(parents=True, exist_ok=True)
        args.json_summary.write_text(
            json.dumps(summary, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
            encoding="utf-8",
            newline="\n",
        )

    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
