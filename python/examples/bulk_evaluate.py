#!/usr/bin/env python3
"""Evaluate one expression at many points, quickly.

`evaluate_many` takes every point across the boundary in one call, keeps one
compiled evaluator, and runs with the interpreter lock released. Columns can be
ordinary Python sequences, or raw bytes holding little-endian 64-bit values,
which is the fastest shape and the one a NumPy array converts to directly.

    python bulk_evaluate.py --points 200000

The script also uses bulk evaluation for what it is most useful for in
practice: checking that a simplified expression really does agree with the one
it came from.
"""

from __future__ import annotations

import argparse
import random
import struct
import time

import cobra_mba
from cobra_mba import Expr, OutcomeKind

EXPRESSION = "(x ^ y) + 2 * (x & y) + (x | y)"


def timed(label: str, work) -> tuple[str, float, object]:
    started = time.perf_counter()
    value = work()
    return label, time.perf_counter() - started, value


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--points", type=int, default=200_000)
    parser.add_argument("--expression", default=EXPRESSION)
    args = parser.parse_args()

    expr = Expr.parse(args.expression)
    names = expr.variables
    rng = random.Random(4)
    columns = {name: [rng.getrandbits(64) for _ in range(args.points)] for name in names}
    raw_columns = {
        name: struct.pack(f"<{args.points}Q", *values) for name, values in columns.items()
    }

    print(f"expression   {expr}")
    print(f"variables    {names}")
    print(f"points       {args.points:,}\n")

    runs = [
        timed(
            "one point at a time",
            lambda: [
                expr.evaluate(dict(zip(names, point)))
                for point in zip(*(columns[name] for name in names))
            ],
        ),
        timed("evaluate_many, lists", lambda: expr.evaluate_many(columns)),
        timed("evaluate_many, bytes in", lambda: expr.evaluate_many(raw_columns)),
        timed(
            "evaluate_many, bytes in and out",
            lambda: expr.evaluate_many(raw_columns, raw=True),
        ),
    ]

    baseline = runs[0][1]
    reference = runs[0][2]
    for label, elapsed, value in runs:
        # Every path has to produce the same numbers.
        got = list(struct.unpack(f"<{args.points}Q", value)) if isinstance(value, bytes) else value
        assert got == reference, f"{label} disagreed"
        print(f"  {label:<34} {elapsed * 1000:8.1f} ms   {baseline / elapsed:5.1f}x")

    # NumPy, if it is installed. `tobytes()` produces exactly the raw column
    # form, and `frombuffer` reads the raw result back with no copy.
    try:
        import numpy as np
    except ImportError:
        print("\nnumpy is not installed, skipping the array example")
    else:
        arrays = {name: np.array(values, dtype=np.uint64) for name, values in columns.items()}
        started = time.perf_counter()
        raw = expr.evaluate_many({n: a.tobytes() for n, a in arrays.items()}, raw=True)
        out = np.frombuffer(raw, dtype="<u8")
        elapsed = time.perf_counter() - started
        assert out.tolist() == reference
        print(f"\n  {'numpy round trip':<34} {elapsed * 1000:8.1f} ms   {baseline / elapsed:5.1f}x")
        print(f"  result: {out[:4]} ... dtype={out.dtype}")

    # What bulk evaluation is actually for: checking a simplification.
    print("\nchecking a simplification over the same points")
    result = cobra_mba.simplify(args.expression, require_lean_certificate=False)
    if result.kind == OutcomeKind.SIMPLIFIED and result.expr is not None:
        before = expr.evaluate_many(raw_columns, raw=True)
        after = result.expr.evaluate_many(raw_columns, raw=True)
        print(f"  {expr}")
        print(f"  {result}")
        print(f"  agree on all {args.points:,} points: {before == after}")
        print(f"  evidence: {result.proof_level}")
    else:
        print(f"  nothing simplified: {result.kind}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
