#!/usr/bin/env python3
"""Generate deterministic TSV manifests for the CoBRA parity runners."""

from __future__ import annotations

import argparse
from collections.abc import Sequence
from pathlib import Path
from typing import TypeVar


Case = tuple[str, int, int, str]
T = TypeVar("T")

SMOKE_CASES: tuple[Case, ...] = (
    ("identity_xor_add", 64, 16, "(x ^ y) + 2 * (x & y)"),
    ("inclusion_exclusion", 64, 16, "7 * x + 7 * y - 7 * (x & y)"),
    ("xor_even_multiplicity", 64, 16, "x ^ y ^ x"),
    ("left_shift", 32, 16, "x << 3"),
    ("masked_partition", 16, 16, "(x & 255) + (x & 65280)"),
    ("polynomial_square", 16, 16, "x * x + 2 * x + 1"),
)

PERFORMANCE_CASES: tuple[Case, ...] = SMOKE_CASES + (
    (
        "linear_four_vars",
        64,
        16,
        "13 * (a ^ b) + 7 * (b & c) - 5 * (c | d) + 19 * (a & d)",
    ),
    (
        "semilinear_three_vars",
        64,
        16,
        "(x ^ y) * z + 3 * (x & y) + 5 * (y | z)",
    ),
    (
        "singleton_power_four",
        32,
        16,
        "x * x * x * x + 9 * x * x - 7 * x + 11",
    ),
    (
        "mixed_product",
        32,
        16,
        "(x + y) * (x ^ y) + 3 * (x & y) * z + 17",
    ),
    (
        "masked_multi_atom",
        32,
        16,
        "3 * (x & 255) + 5 * (x & 65280) + 7 * (y & 16711680)",
    ),
    (
        "nested_boolean_arithmetic",
        64,
        16,
        "((a ^ b) + 2 * (a & b)) * ((c ^ d) + 2 * (c & d))",
    ),
)

REGRESSION_CASES: tuple[Case, ...] = PERFORMANCE_CASES + (
    (
        "inclusion_arithmetic_operand",
        64,
        16,
        "(x ^ 4) + (10 * y + 5) - ((x ^ 4) & (10 * y + 5))",
    ),
    (
        "masked_high_bit_seed",
        64,
        16,
        "((x & 128) + (y & 127)) & 128",
    ),
    (
        "single_product_sign_square",
        64,
        16,
        "(x1 + x2) * (1 - 2 * (x3 & 1)) * (1 - 2 * (x3 & 1))",
    ),
    (
        "xor_complex_duplicate",
        64,
        16,
        "((((x + y) & z) | 3) ^ (((x * z) | (y & 85)) + w)) "
        "^ (((x * z) | (y & 85)) + w)",
    ),
    (
        "cost_blowup_guard",
        64,
        16,
        "x0+x1+x2+x3+x4+x5+x6+x7"
        "-(x0^x1^x2^x3^x4^x5^x6^x7)+(z^z)",
    ),
    (
        "aux_var_high_bit_live",
        64,
        16,
        "x & y & 2305843009213693952",
    ),
)

SUITES: dict[str, tuple[Case, ...]] = {
    "smoke": SMOKE_CASES,
    "performance": PERFORMANCE_CASES,
    "regression": REGRESSION_CASES,
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--suite",
        choices=sorted(SUITES),
        default="smoke",
        help="built-in deterministic case suite (default: smoke)",
    )
    parser.add_argument(
        "--no-builtins",
        action="store_true",
        help="omit the built-in suite and emit only dataset cases",
    )
    parser.add_argument(
        "--output",
        type=Path,
        required=True,
        help="destination TSV manifest",
    )
    parser.add_argument(
        "--dataset",
        type=Path,
        action="append",
        default=[],
        help=(
            "append deterministic samples from a CoBRA dataset; may be "
            "specified more than once"
        ),
    )
    parser.add_argument(
        "--dataset-limit",
        type=int,
        default=5,
        help="maximum evenly spaced cases per dataset (0 = all; default: 5)",
    )
    parser.add_argument(
        "--dataset-bitwidth",
        type=int,
        default=64,
        help="bit width assigned to dataset cases (default: 64)",
    )
    parser.add_argument(
        "--dataset-max-vars",
        type=int,
        default=16,
        help="max_vars assigned to dataset cases (default: 16)",
    )
    return parser.parse_args()


def top_level_separators(line: str, separator: str) -> list[int]:
    indices: list[int] = []
    depth = 0
    for index, char in enumerate(line):
        if char in "([":
            depth += 1
        elif char in ")]":
            depth -= 1
        elif char == separator and depth == 0:
            indices.append(index)
    return indices


def dataset_inputs(path: Path) -> list[tuple[int, str]]:
    rows: list[tuple[int, str]] = []
    body = path.read_text(encoding="utf-8")
    for line_number, raw in enumerate(body.splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        tabs = top_level_separators(line, "\t")
        commas = top_level_separators(line, ",")
        separators = tabs if tabs else commas
        if not separators:
            continue
        expression = line[: separators[0]].strip()
        if expression:
            rows.append((line_number, expression))
    return rows


def evenly_spaced(values: Sequence[T], limit: int) -> list[T]:
    if limit <= 0 or limit >= len(values):
        return list(values)
    if limit == 1:
        return [values[0]]
    last = len(values) - 1
    return [values[index * last // (limit - 1)] for index in range(limit)]


def dataset_prefix(path: Path) -> str:
    parts = [part for part in path.with_suffix("").parts[-2:] if part not in (".", "..")]
    raw = "_".join(parts)
    return "".join(char if char.isalnum() else "_" for char in raw).strip("_").lower()


def load_dataset_cases(
    paths: Sequence[Path],
    limit: int,
    bitwidth: int,
    max_vars: int,
) -> list[Case]:
    cases: list[Case] = []
    for path in paths:
        rows = dataset_inputs(path)
        prefix = dataset_prefix(path)
        for line_number, expression in evenly_spaced(rows, limit):
            cases.append(
                (
                    f"dataset_{prefix}_l{line_number}",
                    bitwidth,
                    max_vars,
                    expression,
                )
            )
    return cases


def validate(cases: Sequence[Case]) -> None:
    seen: set[str] = set()
    for case_id, bitwidth, max_vars, expression in cases:
        if not case_id or case_id in seen:
            raise ValueError(f"empty or duplicate case id: {case_id!r}")
        if "\t" in case_id or "\n" in case_id:
            raise ValueError(f"invalid case id: {case_id!r}")
        if "\t" in expression or "\n" in expression:
            raise ValueError(f"expression contains a tab or newline: {case_id}")
        if not 1 <= bitwidth <= 64:
            raise ValueError(f"invalid bitwidth for {case_id}: {bitwidth}")
        if max_vars < 0:
            raise ValueError(f"invalid max_vars for {case_id}: {max_vars}")
        seen.add(case_id)


def main() -> int:
    args = parse_args()
    if args.dataset_limit < 0:
        raise ValueError("--dataset-limit must be non-negative")
    builtin_cases = [] if args.no_builtins else list(SUITES[args.suite])
    sampled_cases = load_dataset_cases(
        args.dataset,
        args.dataset_limit,
        args.dataset_bitwidth,
        args.dataset_max_vars,
    )
    cases = builtin_cases + sampled_cases
    validate(cases)

    lines = [
        "# cobra-parity-manifest-v1",
        "# case_id<TAB>bitwidth<TAB>max_vars<TAB>expression",
    ]
    lines.extend(
        f"{case_id}\t{bitwidth}\t{max_vars}\t{expression}"
        for case_id, bitwidth, max_vars, expression in cases
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    print(
        f"wrote {len(cases)} cases to {args.output} "
        f"({len(builtin_cases)} {args.suite}, {len(sampled_cases)} dataset)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
