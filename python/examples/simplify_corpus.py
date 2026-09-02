#!/usr/bin/env python3
"""Simplify a whole corpus at once and check the results.

Shows the two things `simplify_many` is for: handing the extension a batch
instead of one expression at a time, and spreading the work over every core
with the interpreter lock released.

    python simplify_corpus.py ../../datasets/univariate64.txt --limit 200

Every result is checked against its input over a set of sampled points. That
is the same idea as the probe the simplifier uses internally: exhaustive
checking is impossible at 64 bits, so agreement is sampled.
"""

from __future__ import annotations

import argparse
import random
import sys
import time
from pathlib import Path

import cobra_mba
from cobra_mba import Expr, OutcomeKind


def read_corpus(path: Path, limit: int | None) -> list[str]:
    """Read the first field of each line, skipping comments and blanks."""
    cases: list[str] = []
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        # Dataset lines are either "input<TAB>expected" or a comma-separated
        # list of equivalent forms whose first entry is the obfuscated one.
        field = line.split("\t")[0] if "\t" in line else split_top_level(line)[0]
        cases.append(field.strip())
        if limit is not None and len(cases) >= limit:
            break
    return cases


def split_top_level(line: str) -> list[str]:
    """Split on commas that are not inside parentheses."""
    parts: list[str] = []
    depth = start = 0
    for index, char in enumerate(line):
        if char == "(":
            depth += 1
        elif char == ")":
            depth = max(0, depth - 1)
        elif char == "," and depth == 0:
            parts.append(line[start:index])
            start = index + 1
    parts.append(line[start:])
    return parts


def agrees(left: Expr, right: Expr, samples: int, rng: random.Random) -> bool:
    """Compare two expressions over sampled points, in bulk."""
    widths = left.variable_widths
    columns = {
        name: [rng.getrandbits(width) for _ in range(samples)]
        for name, width in zip(left.variables, widths)
    }
    return left.evaluate_many(columns) == right.evaluate_many(columns)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus", type=Path, help="dataset file to read")
    parser.add_argument("--limit", type=int, default=None, help="stop after N cases")
    parser.add_argument("--bitwidth", type=int, default=64)
    parser.add_argument("--workers", type=int, default=None)
    parser.add_argument(
        "--certified-only",
        action="store_true",
        help=(
            "keep the Lean certificate gate on. It is the soundness gate, and it "
            "leaves almost every corpus expression untouched"
        ),
    )
    parser.add_argument("--samples", type=int, default=64, help="probe points per result")
    args = parser.parse_args()

    if not args.corpus.exists():
        print(f"no such file: {args.corpus}", file=sys.stderr)
        return 1

    cases = read_corpus(args.corpus, args.limit)
    if not cases:
        print("corpus is empty", file=sys.stderr)
        return 1

    started = time.perf_counter()
    results = cobra_mba.simplify_many(
        cases,
        bitwidth=args.bitwidth,
        workers=args.workers,
        require_lean_certificate=args.certified_only,
        # One malformed line should not cost the whole run.
        on_error="none",
    )
    elapsed = time.perf_counter() - started

    rng = random.Random(0xC0B7A)
    simplified = unchanged = failed = disagreed = 0
    levels: dict[str, int] = {}

    for source, result in zip(cases, results):
        if result is None:
            failed += 1
            continue
        if result.kind != OutcomeKind.SIMPLIFIED or result.expr is None:
            unchanged += 1
            continue
        simplified += 1
        name = str(result.proof_level).rsplit(".", maxsplit=1)[-1]
        levels[name] = levels.get(name, 0) + 1
        if not agrees(result.expr, result.original, args.samples, rng):
            disagreed += 1
            print(f"DISAGREES: {source}  ->  {result}", file=sys.stderr)

    rate = len(cases) / elapsed if elapsed else float("inf")
    print(f"corpus       {args.corpus}")
    print(f"cases        {len(cases)}")
    print(f"elapsed      {elapsed:.3f} s  ({rate:,.0f} expressions/second)")
    print(f"simplified   {simplified}")
    print(f"unchanged    {unchanged}")
    print(f"unparsable   {failed}")
    print(f"evidence     {levels or 'none'}")
    print(f"disagreed    {disagreed}")

    return 1 if disagreed else 0


if __name__ == "__main__":
    raise SystemExit(main())
