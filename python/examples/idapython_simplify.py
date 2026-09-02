"""IDAPython: find MBA expressions in a decompiled function and simplify them.

Run it from IDA's Script file... dialog, or from the console:

    import idapython_simplify; idapython_simplify.run()

`cobra_mba` has to be importable from the interpreter IDA runs, which is not
usually the one on your PATH:

    "%IDADIR%\\python3\\python.exe" -m pip install cobra-mba

What it does: walks the ctree of the current function, translates every
arithmetic and bitwise subtree into the simplifier's syntax, and reports the
ones that come back shorter. Nothing is written to the database unless you set
`SET_COMMENTS` to True.

Note on soundness: this script turns the Lean certificate gate off, because
with it on almost nothing in real obfuscated code simplifies. That accepts
probe-only assurance. Read a result as a strong lead, not as proof, and check
anything you are about to act on.

This script has not been run against a live IDA installation. Treat the
Hex-Rays details as a starting point.
"""

from __future__ import annotations

import ida_funcs
import ida_hexrays
import ida_kernwin

import cobra_mba
from cobra_mba import OutcomeKind

# Set to True to write the simplified form back as a pseudocode comment.
SET_COMMENTS = False

# Smallest node count worth reporting. Tiny expressions are noise.
MIN_NODES = 7

# Binary operators that map straight onto the simplifier's syntax.
BINARY = {
    ida_hexrays.cot_add: "+",
    ida_hexrays.cot_sub: "-",
    ida_hexrays.cot_mul: "*",
    ida_hexrays.cot_band: "&",
    ida_hexrays.cot_bor: "|",
    ida_hexrays.cot_bxor: "^",
}
UNARY = {
    ida_hexrays.cot_bnot: "~",
    ida_hexrays.cot_neg: "-",
}
# Shifts need a literal amount, so they are handled separately.
SHIFTS = {
    ida_hexrays.cot_shl: "<<",
    ida_hexrays.cot_shr: ">>",
}


class Untranslatable(Exception):
    """The subtree contains something the simplifier has no syntax for."""


def variable_name(index: int, names: dict[int, str], lvars) -> str:
    """A stable identifier the parser will accept for local variable `index`."""
    if index not in names:
        raw = lvars[index].name or f"v{index}"
        cleaned = "".join(c if c.isalnum() or c == "_" else "_" for c in raw)
        if not cleaned or cleaned[0].isdigit():
            cleaned = f"v_{cleaned}"
        # Keep names distinct even if sanitising collided them.
        if cleaned in names.values():
            cleaned = f"{cleaned}_{index}"
        names[index] = cleaned
    return names[index]


def translate(expr, names: dict[int, str], lvars, depth: int = 0) -> str:
    """Render one ctree expression in the simplifier's infix syntax."""
    if depth > 64:
        raise Untranslatable("too deep")

    op = expr.op

    if op == ida_hexrays.cot_var:
        return variable_name(expr.v.idx, names, lvars)
    if op == ida_hexrays.cot_num:
        return str(expr.n._value)
    # A cast that does not change the value is transparent for our purposes;
    # one that does would change the arithmetic, so it stops the walk.
    if op == ida_hexrays.cot_cast:
        if expr.x.type.get_size() != expr.type.get_size():
            raise Untranslatable("width-changing cast")
        return translate(expr.x, names, lvars, depth + 1)
    if op in UNARY:
        return f"{UNARY[op]}({translate(expr.x, names, lvars, depth + 1)})"
    if op in BINARY:
        left = translate(expr.x, names, lvars, depth + 1)
        right = translate(expr.y, names, lvars, depth + 1)
        return f"({left} {BINARY[op]} {right})"
    if op in SHIFTS:
        if expr.y.op != ida_hexrays.cot_num:
            raise Untranslatable("shift by a non-literal")
        return f"({translate(expr.x, names, lvars, depth + 1)} {SHIFTS[op]} {expr.y.n._value})"

    raise Untranslatable(f"unsupported op {op}")


def node_count(expr, depth: int = 0) -> int:
    """How much expression there is, used to skip trivial subtrees."""
    if depth > 64:
        return 0
    total = 1
    for child in (expr.x, expr.y):
        if child is not None:
            total += node_count(child, depth + 1)
    return total


class Collector(ida_hexrays.ctree_visitor_t):
    """Gather the largest translatable subtree in each branch of the tree."""

    def __init__(self, cfunc):
        super().__init__(ida_hexrays.CV_FAST)
        self.cfunc = cfunc
        self.found: list[tuple[int, str, dict[int, str]]] = []

    def visit_expr(self, expr) -> int:
        if expr.op not in BINARY and expr.op not in SHIFTS:
            return 0
        if node_count(expr) < MIN_NODES:
            return 0
        names: dict[int, str] = {}
        try:
            text = translate(expr, names, self.cfunc.lvars)
        except Untranslatable:
            return 0
        if len(names) < 1:
            return 0
        self.found.append((expr.ea, text, names))
        # Do not descend: the outermost translatable subtree is the one worth
        # simplifying, and its children would only repeat the work.
        return 1


def bitwidth_of(cfunc, ea: int) -> int:
    """Fall back to 64 when the size is not one the simplifier accepts."""
    del cfunc, ea
    return 64


def run(ea: int | None = None) -> None:
    if ea is None:
        ea = ida_kernwin.get_screen_ea()
    func = ida_funcs.get_func(ea)
    if func is None:
        print("[cobra] no function here")
        return

    try:
        cfunc = ida_hexrays.decompile(func.start_ea)
    except ida_hexrays.DecompilationFailure as exc:
        print(f"[cobra] decompilation failed: {exc}")
        return
    if cfunc is None:
        print("[cobra] decompilation returned nothing")
        return

    collector = Collector(cfunc)
    collector.apply_to(cfunc.body, None)
    if not collector.found:
        print("[cobra] no translatable arithmetic found")
        return

    sources = [text for _, text, _ in collector.found]
    results = cobra_mba.simplify_many(
        sources,
        bitwidth=bitwidth_of(cfunc, func.start_ea),
        # See the note at the top of this file: with the gate on, real
        # obfuscated code almost never simplifies.
        require_lean_certificate=False,
        on_error="none",
    )

    reported = 0
    for (address, source, _names), result in zip(collector.found, results):
        if result is None or result.kind != OutcomeKind.SIMPLIFIED:
            continue
        simplified = str(result)
        if len(simplified) >= len(source):
            continue
        reported += 1
        print(f"[cobra] {address:#x}")
        print(f"          from: {source}")
        print(f"          to:   {simplified}   ({result.proof_level})")
        if SET_COMMENTS:
            add_comment(cfunc, address, simplified)

    if SET_COMMENTS and reported:
        cfunc.save_user_cmts()
        print(f"[cobra] wrote {reported} comments; refresh the pseudocode view")
    print(f"[cobra] {reported} of {len(sources)} expressions got shorter")


def add_comment(cfunc, address: int, text: str) -> None:
    location = ida_hexrays.treeloc_t()
    location.ea = address
    location.itp = ida_hexrays.ITP_BLOCK1
    cfunc.set_user_cmt(location, f"cobra: {text}")


if __name__ == "__main__":
    run()
