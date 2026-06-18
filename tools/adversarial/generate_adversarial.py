#!/usr/bin/env python3
"""Adversarial MBA-expression generator for the cobra simplifier.

Emits expression strings (CLI grammar: + - * & | ^ ~ << >> **, integer
literals, named variables) across the attack families documented in
ATTACKS.md, then *self-verifies* each case with an exact u64 modular
evaluator before printing it:

  * completeness families carry a known true simplification; the emitted
    obfuscation is checked to be equal to it at random full-width points, so
    a faithful engine MUST reach the target -- failure to do so is a bug.
  * the soundness family ("soundness_trap") reproduces the engine's exact
    deterministic probe schedule (spot_check.rs) and proves the trap vanishes
    on every probe yet differs at a witness -- a verifier-evasion case.

No third-party deps. Python 3.8+.

Usage:
    python generate_adversarial.py --family all
    python generate_adversarial.py --family soundness_trap --nvars 3 --samples 8
    python generate_adversarial.py --list
"""
from __future__ import annotations

import argparse
import json
import random
import sys
from typing import Callable, Dict, List, Tuple

# --------------------------------------------------------------------------
# Exact modular semantics (mirrors crates/cobra-core/src/arith.rs).
# --------------------------------------------------------------------------

def mask_for(bits: int) -> int:
    return (1 << bits) - 1


def eval_expr(s: str, env: Dict[str, int], bits: int) -> int:
    """Evaluate a generated expression string under the same modular
    semantics cobra uses. Supports the operators the generator emits."""
    m = mask_for(bits)

    # A tiny recursive-descent evaluator over the CLI grammar.
    toks = _tokenize(s)
    pos = 0

    def peek():
        return toks[pos] if pos < len(toks) else None

    def eat(t=None):
        nonlocal pos
        tok = toks[pos]
        if t is not None and tok != t:
            raise ValueError(f"expected {t!r} got {tok!r} in {s!r}")
        pos += 1
        return tok

    # precedence: | , ^ , & , +- , */ , unary , ** , atom
    def p_or():
        v = p_xor()
        while peek() == "|":
            eat(); v = (v | p_xor()) & m
        return v

    def p_xor():
        v = p_and()
        while peek() == "^":
            eat(); v = (v ^ p_and()) & m
        return v

    def p_and():
        v = p_add()
        while peek() == "&":
            eat(); v = (v & p_add()) & m
        return v

    def p_add():
        v = p_mul()
        while peek() in ("+", "-"):
            op = eat()
            r = p_mul()
            v = (v + r if op == "+" else v - r) & m
        return v

    def p_mul():
        v = p_shift()
        while peek() in ("*",):
            eat(); v = (v * p_shift()) & m
        return v

    def p_shift():
        v = p_unary()
        while peek() in ("<<", ">>"):
            op = eat()
            k = p_unary()
            v = ((v << k) & m) if op == "<<" else (v >> k)
        return v

    def p_unary():
        t = peek()
        if t == "-":
            eat(); return (-p_unary()) & m
        if t == "~":
            eat(); return (~p_unary()) & m
        return p_pow()

    def p_pow():
        v = p_atom()
        if peek() == "**":
            eat(); e = p_atom(); v = pow(v, e, m + 1)
        return v

    def p_atom():
        t = peek()
        if t == "(":
            eat("("); v = p_or(); eat(")"); return v
        eat()
        if t.startswith("0x"):
            return int(t, 16) & m
        if t.isdigit():
            return int(t) & m
        return env[t] & m

    v = p_or()
    if pos != len(toks):
        raise ValueError(f"trailing tokens in {s!r}: {toks[pos:]}")
    return v


def _tokenize(s: str) -> List[str]:
    out: List[str] = []
    i = 0
    two = {"**", "<<", ">>"}
    while i < len(s):
        c = s[i]
        if c.isspace():
            i += 1; continue
        if s[i:i + 2] in two:
            out.append(s[i:i + 2]); i += 2; continue
        if c in "()+-*&|^~":
            out.append(c); i += 1; continue
        j = i
        while j < len(s) and (s[j].isalnum() or s[j] in "_x"):
            j += 1
        out.append(s[i:j]); i = j
    return out


def _check_equiv(a: str, b: str, varnames: List[str], bits: int, trials: int = 400) -> bool:
    rng = random.Random(0xC0B7A)
    m = mask_for(bits)
    edge = [0, 1, m, m - 1, 2, 3, 5, 7, 1 << (bits - 1)]
    for t in range(trials):
        env = {v: (edge[t] if t < len(edge) else rng.getrandbits(bits)) & m for v in varnames}
        if eval_expr(a, env, bits) != eval_expr(b, env, bits):
            return False
    return True


# --------------------------------------------------------------------------
# Reproduction of cobra's deterministic probe schedule (spot_check.rs).
# --------------------------------------------------------------------------

def _splitmix64(state: int) -> Tuple[int, int]:
    M = mask_for(64)
    state = (state + 0x9E3779B97F4A7C15) & M
    z = state
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & M
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & M
    return (z ^ (z >> 31)) & M, state


def _seed_for(num_vars: int, bitwidth: int, num_samples: int) -> int:
    s = num_vars & mask_for(64)
    a, s = _splitmix64(s)
    s ^= (bitwidth << 8)
    b, s = _splitmix64(s)
    s ^= (num_samples << 16)
    c, s = _splitmix64(s)
    return (a ^ ((b << 21 | b >> 43) & mask_for(64)) ^ ((c << 42 | c >> 22) & mask_for(64))) & mask_for(64)


def _random_probe_points(num_vars: int, bitwidth: int, num_samples: int) -> List[List[int]]:
    """The `num_samples` random full-width probe points, exactly as
    for_each_full_width_probe draws them."""
    m = mask_for(bitwidth)
    state = _seed_for(num_vars, bitwidth, num_samples)
    points = []
    for _ in range(num_samples):
        pt = []
        for _ in range(num_vars):
            v, state = _splitmix64(state)
            pt.append(v & m)
        points.append(pt)
    return points


def _adversarial_values(bits: int) -> List[int]:
    m = mask_for(bits)
    vals = {0, 1, m, (m - 1) & m, (m - 2) & m, (m - 3) & m, 3, 5, 7,
            0x5555555555555555 & m, 0xAAAAAAAAAAAAAAAA & m}
    for k in range(1, bits):
        p = 1 << k
        vals.add((p - 1) & m)
        vals.add(p & m)
        if k + 1 < bits:
            vals.add((p + 1) & m)
    return sorted(vals)


# --------------------------------------------------------------------------
# Completeness families. Each returns (description, target, obfuscated, vars).
# --------------------------------------------------------------------------

def fam_wide_bitwise_atom(nvars: int, bits: int):
    """A1: bitwise core spanning >5 vars -> opaque atom, no decomposition.
    Identity used: (x & y) + (x | y) == x + y, lifted over a wide AND."""
    nvars = max(6, nvars)
    vs = [f"v{i}" for i in range(nvars)]
    wide_and = " & ".join(vs)
    wide_or = " | ".join(vs)
    obf = f"({wide_and}) + ({wide_or})"
    target = " + ".join(vs)  # holds only pairwise; for >2 it is NOT x+y.
    # For >2 vars (x&y)+(x|y)!=x+y, so emit the honest 2-var identity widened
    # by an opaque carrier term that the engine should peel off:
    obf = f"({wide_and}) + ({wide_or}) - ({wide_and})"  # == wide_or, trivially
    target = wide_or
    return ("A1 wide-bitwise-atom (>5-var AND forces opaque atom)", target, obf, vs)


def fam_variable_wall(nvars: int, bits: int):
    """A2: linear MBA over many vars. target = sum; obfuscate each term via
    x = (x ^ 0) and (x|x), plus a global +k-k carrier."""
    nvars = min(max(nvars, 12), 20)
    vs = [f"v{i}" for i in range(nvars)]
    target = " + ".join(vs)
    parts = []
    for v in vs:
        # x == (x | x) == ((x ^ 0) & v) ... keep it a true identity:
        parts.append(f"({v} ^ 0)")
    obf = " + ".join(parts) + " + 123 - 123"
    return (f"A2 variable-wall ({nvars}-var linear identity)", target, obf, vs)


def fam_high_degree_poly(nvars: int, bits: int, degree: int = 12):
    """A3: high-degree polynomial that collapses. ((a+b)**k) expanded stays
    high-degree; target is the same value but the engine's degree cap blocks
    recovery. We give a genuine collapse: (a**k - a**k) + (a+b) == a+b but
    written with a large literal power as the carrier."""
    vs = ["a", "b"]
    target = "a + b"
    obf = f"a ** {degree} - a ** {degree} + a + b"
    return (f"A3 high-degree-poly (degree-{degree} carrier)", target, obf, vs)


def fam_unknown_shape(nvars: int, bits: int):
    """A5: bitwise-over-arith without a multiply -> no structural recovery.
    Honest identity: ~(x) == -x - 1 (two's complement). Obfuscate -x-1."""
    vs = ["a", "b", "c", "d"]
    target = "~(a + (b & (c + d)))"
    # -(a + (b&(c+d))) - 1  equals ~(...)  -- a true identity the engine
    # ought to recognise but the classifier routes nowhere.
    obf = "-(a + (b & (c + d))) - 1"
    return ("A5 unknown-shape (bitwise-over-arith, no mul)", target, obf, vs)


def fam_nonpoly_shift(nvars: int, bits: int):
    """A6: shift/low-bit term, non-polynomial. Identity: a == (a>>1)*2 + (a&1)
    holds for unsigned a. Engine's poly path bails on the divisibility gate."""
    vs = ["a"]
    target = "a"
    obf = "(a >> 1) * 2 + (a & 1)"
    return ("A6 non-polynomial-shift (a == (a>>1)*2 + (a&1))", target, obf, vs)


def fam_xor_mask_wall(nvars: int, bits: int):
    """A1b (EMPIRICALLY CONFIRMED MISS): the identity

        a ^ (a & M) == a & ~M

    with M a wide OR of `nvars-1` other variables. The true form is a single
    AND, but once the bitwise atom's support reaches 5+ variables the engine
    fails to recover it: it returns the input essentially unchanged (support
    5-6) or emits a much LARGER equivalent blow-up (support 7+). Solved only
    for <=4 total variables. This is the most reliable "cannot solve" family
    reachable from the public grammar."""
    nvars = max(5, nvars)
    others = [chr(ord("b") + i) for i in range(nvars - 1)]
    m = " | ".join(others)
    obf = f"a ^ (a & ({m}))"
    target = f"a & ~({m})"
    return (
        f"A1b xor-mask-wall ({nvars}-var; a^(a&M) == a&~M, missed for >=5 vars)",
        target,
        obf,
        ["a", *others],
    )


def fam_budget_exhaustion(nvars: int, bits: int, depth: int = 60):
    """A7: deeply nested product carrier around a trivial identity to burn
    the 1024-expansion budget. target = a; carrier multiplies by (b-b+1)."""
    vs = ["a", "b"]
    target = "a"
    carrier = "a"
    for _ in range(depth):
        carrier = f"({carrier}) * (b - b + 1)"  # *1, value-preserving
    return (f"A7 budget-exhaustion (depth-{depth} *1 nest)", target, carrier, vs)


# --------------------------------------------------------------------------
# Soundness family.
# --------------------------------------------------------------------------

def fam_soundness_trap(nvars: int, bits: int, samples: int = 8):
    """B1: build D that vanishes on cobra's entire probe schedule but is
    nonzero generically, so g = f + D passes full_width_check_eval despite
    g != f. Reproduces the deterministic random points so the evasion is
    guaranteed, not probabilistic.

    Returns (description, claimed_simplification f, obfuscated g, vars, witness).
    """
    nvars = max(3, nvars)
    vs = [f"v{i}" for i in range(nvars)]
    a, b, c = vs[0], vs[1], vs[2]

    # Random a-coordinates the verifier will sample (deterministic).
    rand_pts = _random_probe_points(nvars, bits, samples)
    a_coords = sorted({pt[0] for pt in rand_pts})

    # D = v0*v1*v2*(v0 - v1) * prod_i (v0 - a_i)
    factors = [a, b, c, f"({a} - {b})"]
    for ai in a_coords:
        factors.append(f"({a} - {ai})")
    D = " * ".join(factors)

    f = " + ".join(vs)                  # arbitrary simple "true" answer
    g = f"({f}) + ({D})"                # inequivalent to f, but probe-equal

    # --- self-verification ---------------------------------------------
    m = mask_for(bits)
    # 1) vanishes on all structured probes
    adv = _adversarial_values(bits)
    def D_at(env):
        return eval_expr(D, env, bits)
    for val in adv:                                  # all-equal
        assert D_at({v: val for v in vs}) == 0
    for i in range(nvars):                           # single-var nonzero
        for val in adv:
            env = {v: 0 for v in vs}; env[vs[i]] = val
            assert D_at(env) == 0
    for pt in rand_pts:                              # deterministic randoms
        assert D_at({v: pt[k] for k, v in enumerate(vs)}) == 0
    # 2) nonzero at a witness with 3+ distinct nonzero vars. Search v0 for a
    # value avoiding every linear root (v0!=0, v0!=v1, v0 not an a_i).
    a_set = set(a_coords)
    witness = None
    for v0 in range(3, 3 + 8192, 2):
        if v0 in a_set:
            continue
        cand = {v: ((v0 + 3 * k) & m) for k, v in enumerate(vs)}
        if cand[a] == cand[b] or cand[a] in a_set:
            continue
        if D_at(cand) != 0:
            witness = cand
            break
    if witness is None:
        # 2-adic obstruction: with many distinct roots, ~half the linear
        # factors (v0 - a_i) are even, so the product accumulates >`bits`
        # factors of 2 and is identically 0 mod 2^bits -- D collapses to the
        # zero FUNCTION, not just zero on the probe set. The deterministic-seed
        # evasion is therefore only cheaply constructible for small sample
        # counts. This is itself a finding: the 64-sample residual gate and
        # 256-sample orchestrator filter are incidentally hardened by Z/2^bits.
        raise SystemExit(
            f"[soundness_trap] no valid trap at samples={samples}, bits={bits}: "
            f"the {len(a_coords)} linear root factors collapse D to zero mod 2^{bits} "
            f"(2-adic obstruction). Use a smaller --samples (e.g. 8 for the default "
            f"CLI full-width check) or a smaller --bitwidth.")
    assert eval_expr(f, witness, bits) != eval_expr(g, witness, bits)

    desc = (f"B1 soundness-trap ({nvars} vars, evades {samples}-sample check; "
            f"f != g but equal on entire probe schedule)")
    return (desc, f, g, vs, witness)


COMPLETENESS: Dict[str, Callable] = {
    "wide_bitwise_atom": fam_wide_bitwise_atom,
    "xor_mask_wall": fam_xor_mask_wall,
    "variable_wall": fam_variable_wall,
    "high_degree_poly": fam_high_degree_poly,
    "unknown_shape": fam_unknown_shape,
    "nonpoly_shift": fam_nonpoly_shift,
    "budget_exhaustion": fam_budget_exhaustion,
}


def emit_completeness(name: str, fn, nvars: int, bits: int, as_json: bool):
    desc, target, obf, vs = fn(nvars, bits)
    ok = _check_equiv(target, obf, vs, bits)
    rec = {
        "family": name, "kind": "completeness", "description": desc,
        "bitwidth": bits, "vars": vs,
        "true_simplification": target, "obfuscated_input": obf,
        "equivalent_self_checked": ok,
        "cli": f'cobra --mba "{obf}" --bitwidth {bits} --verbose',
    }
    if not ok:
        rec["WARNING"] = "obfuscation NOT equivalent to target; family needs fixing"
    _print(rec, as_json)


def emit_soundness(nvars: int, bits: int, samples: int, as_json: bool):
    desc, f, g, vs, witness = fam_soundness_trap(nvars, bits, samples)
    rec = {
        "family": "soundness_trap", "kind": "soundness", "description": desc,
        "bitwidth": bits, "vars": vs, "samples_evaded": samples,
        "claimed_simplification": f, "obfuscated_input": g,
        "witness_point": witness,
        "witness_disagree": {
            "f": eval_expr(f, witness, bits), "g": eval_expr(g, witness, bits)},
        "note": ("g passes full_width_check_eval against f at this sample count "
                 "yet is inequivalent -- false accept."),
        "cli": f'cobra --mba "{g}" --bitwidth {bits} --verbose',
    }
    _print(rec, as_json)


def _print(rec, as_json: bool):
    if as_json:
        print(json.dumps(rec))
    else:
        print(f"# {rec['description']}")
        if rec["kind"] == "completeness":
            print(f"#   target   : {rec['true_simplification']}")
            print(f"#   self-eq  : {rec['equivalent_self_checked']}")
            if "WARNING" in rec:
                print(f"#   WARNING  : {rec['WARNING']}")
            print(rec["obfuscated_input"])
        else:
            print(f"#   claims   : {rec['claimed_simplification']}")
            print(f"#   witness  : {rec['witness_point']} -> "
                  f"f={rec['witness_disagree']['f']} g={rec['witness_disagree']['g']}")
            print(rec["obfuscated_input"])
        print()


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    fams = ["all", "completeness", "soundness_trap"] + list(COMPLETENESS)
    ap.add_argument("--family", default="all", choices=fams)
    ap.add_argument("--nvars", type=int, default=6)
    ap.add_argument("--bitwidth", type=int, default=64)
    ap.add_argument("--samples", type=int, default=8,
                    help="probe sample count to evade (8=CLI, 64=residual gate, 256=orchestrator)")
    ap.add_argument("--json", action="store_true", help="JSONL output")
    ap.add_argument("--list", action="store_true", help="list families and exit")
    args = ap.parse_args()

    if args.list:
        print("completeness families:")
        for k in COMPLETENESS:
            print(f"  {k}")
        print("soundness families:\n  soundness_trap")
        return

    want = args.family
    if want in ("all", "completeness"):
        for name, fn in COMPLETENESS.items():
            emit_completeness(name, fn, args.nvars, args.bitwidth, args.json)
    elif want in COMPLETENESS:
        emit_completeness(want, COMPLETENESS[want], args.nvars, args.bitwidth, args.json)

    if want in ("all", "soundness_trap"):
        emit_soundness(max(3, args.nvars), args.bitwidth, args.samples, args.json)


if __name__ == "__main__":
    sys.exit(main())
