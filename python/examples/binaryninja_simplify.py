"""Binary Ninja: simplify the MBA expressions in a function's HLIL.

Run it headlessly:

    python binaryninja_simplify.py /path/to/binary --function main

or from Binary Ninja's Python console:

    import binaryninja_simplify
    binaryninja_simplify.report(bv, bv.get_functions_by_name("main")[0])

`cobra_mba` has to be importable from the interpreter Binary Ninja runs. In the
UI that is Settings, then Python interpreter; headless installs use the
environment `pip install binaryninja` was run in.

What it does: walks each HLIL instruction, translates arithmetic and bitwise
subtrees into the simplifier's syntax, and reports the ones that come back
shorter. Nothing is written to the database.

Note on soundness: this turns the Lean certificate gate off, because with it on
almost nothing in real obfuscated code simplifies. That accepts probe-only
assurance, so read a result as a strong lead rather than as proof.

This script has not been run against a live Binary Ninja installation. Treat
the API details as a starting point.
"""

from __future__ import annotations

import argparse
import sys

import cobra_mba
from cobra_mba import OutcomeKind

try:
    import binaryninja
    from binaryninja import HighLevelILOperation as Op
except ImportError:  # pragma: no cover - only meaningful inside Binary Ninja
    binaryninja = None
    Op = None

MIN_NODES = 7

if Op is not None:
    BINARY = {
        Op.HLIL_ADD: "+",
        Op.HLIL_SUB: "-",
        Op.HLIL_MUL: "*",
        Op.HLIL_AND: "&",
        Op.HLIL_OR: "|",
        Op.HLIL_XOR: "^",
    }
    UNARY = {
        Op.HLIL_NEG: "-",
        Op.HLIL_NOT: "~",
    }
    SHIFTS = {
        Op.HLIL_LSL: "<<",
        Op.HLIL_LSR: ">>",
    }
else:  # pragma: no cover
    BINARY = UNARY = SHIFTS = {}


class Untranslatable(Exception):
    """The subtree contains something the simplifier has no syntax for."""


def variable_name(variable, names: dict[int, str]) -> str:
    """A stable identifier the parser will accept for one HLIL variable."""
    key = variable.identifier
    if key not in names:
        raw = variable.name or f"var_{key:x}"
        cleaned = "".join(c if c.isalnum() or c == "_" else "_" for c in raw)
        if not cleaned or cleaned[0].isdigit():
            cleaned = f"v_{cleaned}"
        if cleaned in names.values():
            cleaned = f"{cleaned}_{len(names)}"
        names[key] = cleaned
    return names[key]


def translate(expr, names: dict[int, str], depth: int = 0) -> str:
    """Render one HLIL expression in the simplifier's infix syntax."""
    if depth > 64:
        raise Untranslatable("too deep")

    operation = expr.operation

    if operation == Op.HLIL_VAR:
        return variable_name(expr.var, names)
    if operation == Op.HLIL_CONST:
        return str(expr.constant & ((1 << 64) - 1))
    if operation in UNARY:
        return f"{UNARY[operation]}({translate(expr.src, names, depth + 1)})"
    if operation in BINARY:
        left = translate(expr.left, names, depth + 1)
        right = translate(expr.right, names, depth + 1)
        return f"({left} {BINARY[operation]} {right})"
    if operation in SHIFTS:
        if expr.right.operation != Op.HLIL_CONST:
            raise Untranslatable("shift by a non-literal")
        amount = expr.right.constant
        if not 0 <= amount < 64:
            raise Untranslatable("shift out of range")
        return f"({translate(expr.left, names, depth + 1)} {SHIFTS[operation]} {amount})"

    raise Untranslatable(f"unsupported operation {operation}")


def node_count(expr, depth: int = 0) -> int:
    if depth > 64:
        return 0
    total = 1
    for operand in getattr(expr, "operands", []):
        if hasattr(operand, "operation"):
            total += node_count(operand, depth + 1)
    return total


def candidates(function) -> list[tuple[object, str]]:
    """The outermost translatable arithmetic subtree of each instruction."""
    found: list[tuple[object, str]] = []
    seen: set[str] = set()

    def walk(expr, depth: int = 0) -> None:
        if depth > 64 or not hasattr(expr, "operation"):
            return
        if expr.operation in BINARY or expr.operation in SHIFTS:
            if node_count(expr) >= MIN_NODES:
                names: dict[int, str] = {}
                try:
                    text = translate(expr, names)
                except Untranslatable:
                    pass
                else:
                    if names and text not in seen:
                        seen.add(text)
                        found.append((expr, text))
                    # The outermost subtree is the one worth simplifying.
                    return
        for operand in getattr(expr, "operands", []):
            walk(operand, depth + 1)

    for block in function.hlil:
        for instruction in block:
            walk(instruction)
    return found


def report(bv, function, bitwidth: int = 64) -> int:
    """Print every expression the simplifier makes shorter."""
    del bv
    found = candidates(function)
    if not found:
        print(f"[cobra] {function.name}: no translatable arithmetic found")
        return 0

    results = cobra_mba.simplify_many(
        [text for _, text in found],
        bitwidth=bitwidth,
        require_lean_certificate=False,
        on_error="none",
    )

    shorter = 0
    for (expr, source), result in zip(found, results):
        if result is None or result.kind != OutcomeKind.SIMPLIFIED:
            continue
        simplified = str(result)
        if len(simplified) >= len(source):
            continue
        shorter += 1
        print(f"[cobra] {expr.address:#x}")
        print(f"          from: {source}")
        print(f"          to:   {simplified}   ({result.proof_level})")

    print(f"[cobra] {function.name}: {shorter} of {len(found)} expressions got shorter")
    return shorter


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", help="file to analyse")
    parser.add_argument("--function", action="append", help="limit to these functions")
    parser.add_argument("--bitwidth", type=int, default=64)
    args = parser.parse_args()

    if binaryninja is None:
        print("binaryninja is not importable from this interpreter", file=sys.stderr)
        return 1

    with binaryninja.load(args.binary) as bv:
        functions = list(bv.functions)
        if args.function:
            wanted = set(args.function)
            functions = [f for f in functions if f.name in wanted]
            if not functions:
                print(f"no function matched {sorted(wanted)}", file=sys.stderr)
                return 1
        total = sum(report(bv, function, args.bitwidth) for function in functions)
    print(f"[cobra] {total} expressions simplified across {len(functions)} functions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
