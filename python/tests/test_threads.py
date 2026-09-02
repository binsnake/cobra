"""Concurrency: the pipeline is safe to drive from several Python threads."""

from __future__ import annotations

import threading
from concurrent.futures import ThreadPoolExecutor

import cobra_mba
from cobra_mba import Expr

CORPUS = [
    "(x ^ y) + 2 * (x & y)",
    "(x | y) - (x & y)",
    "x + y",
    "x ^ x",
    "~(~x)",
    "(a & b) + (a | b)",
    "a + b + c",
    "x * y + x",
    "(x ^ y) ^ y",
    "x & x",
]


def test_thread_pool_matches_serial_results() -> None:
    cases = CORPUS * 6
    serial = [str(cobra_mba.simplify(case)) for case in cases]

    with ThreadPoolExecutor(max_workers=8) as pool:
        parallel = [str(result) for result in pool.map(cobra_mba.simplify, cases)]

    assert parallel == serial


def test_parallel_parsing_and_evaluation_agree() -> None:
    def work(case: str) -> tuple[str, int, list[int]]:
        expr = Expr.parse(case)
        point = list(range(1, len(expr.variables) + 1))
        return expr.render(), expr.evaluate(point), expr.signature()

    cases = CORPUS * 4
    serial = [work(case) for case in cases]

    with ThreadPoolExecutor(max_workers=8) as pool:
        parallel = list(pool.map(work, cases))

    assert parallel == serial


def test_the_gil_is_released_during_a_run() -> None:
    # A background thread must keep making progress while a simplification
    # runs, which is only true if the native call detaches from the GIL.
    ticks = 0
    stop = threading.Event()

    def spin() -> None:
        nonlocal ticks
        while not stop.is_set():
            ticks += 1

    spinner = threading.Thread(target=spin, daemon=True)
    spinner.start()
    try:
        before = ticks
        for _ in range(20):
            cobra_mba.simplify("(x ^ y) + 2 * (x & y)")
        progressed = ticks - before
    finally:
        stop.set()
        spinner.join(timeout=5)

    assert progressed > 0


def test_expressions_can_be_shared_between_threads() -> None:
    shared = Expr.parse("(x ^ y) + 2 * (x & y)")

    def evaluate(seed: int) -> int:
        return shared.evaluate(x=seed, y=seed + 1)

    with ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(evaluate, range(64)))

    assert results == [shared.evaluate(x=i, y=i + 1) for i in range(64)]
