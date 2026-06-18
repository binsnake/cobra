# Adversarial expression classes for cobra

Two threat models against the simplifier:

- **Completeness attacks** — inputs the engine *should* collapse but won't (it
  returns the input unchanged or burns its budget). These cost analyst time and
  hide logic behind "unsupported".
- **Soundness attacks** — inputs where a *wrong* simplification agrees with the
  original on every point the verifier actually checks, so an incorrect result
  is emitted (and, on some paths, labelled `verified`).

All families below are reachable through the public CLI grammar
(`+ - * & | ^ ~ neg << >> **`, integer literals, ≤ 20 variables; shift/exponent
operands must be literals — see [ast.rs:24](../../crates/cobra-parser/src/ast.rs)).

## A. Completeness / missed-simplification attacks

**Empirically confirmed misses** (run through the real pipeline; see
`crates/cobra-passes/tests/adversarial_corpus.rs` and its report):

- **`a ^ (a & M) == a & ~M`** (family A1b / `xor_mask_wall`). *Originally* solved
  only while the bitwise atom's support was ≤ 3–4 variables; at support ≥ 5 the
  engine returned the input unchanged, and at support ≥ 7 it emitted a *much
  larger* equivalent expression (anti-simplification — the signature
  reconstruction canonicalised the function to the `x ^ (x & y)` shape). ✅
  **Fixed** by two complementary changes:
  1. the certified `XorAndEqAndNot64` rewrite `x ^ (x & y) → x & ~y` (Lean
     theorem `Cobra.xor_and_eq_and_not_64`, `bv_decide`), applied at seed time
     *and* during late candidate normalization; and
  2. an **anti-bloat gate** in the orchestrator main loop: a bit-partition
     reconstruction (`SignatureCobCandidate` / `SignatureBitwiseDecompose` /
     `SignatureHybridDecompose`) whose weighted size exceeds ~4× the input is
     dropped, so the cheaper rewrite wins instead of the sum-of-products
     canonicalisation. Arithmetic-lowering / polynomial-recovery passes are
     exempt (they emit modestly-larger canonical forms such as `~(a+b) → -a-b-1`).

  All cases from 3 to 8 variables now simplify to `a & ~M` and stay verified.
  **Cross-check vs upstream CoBRA (C++ `cobra-cli`):** the C++ reference peels
  the 5/6-variable cases via De Morgan (`~f & ~e & ~(~a | b|c|d)`) but at **≥ 7
  variables emits the identical bloated sum-of-products** — so this was a genuine
  upstream gap, and our engine now produces the strictly smaller `a & ~M` where
  upstream does not.
- **≥ 17 distinct variables** is rejected outright: the orchestrator's default
  `max_vars = 16` raises `TooManyVariables` (below the parser's hard cap of 20),
  so any genuinely 17–20-variable expression is unsolvable without raising the
  limit.

| # | Family | Why it defeats the engine | Citation |
|-|-|-|-|
| A1 | **Wide bitwise atom** (`a&b&c&d&e&f ^ …`, ≥ 6 vars in one bitwise term) | Per-atom truth tables are abandoned once an atom's support exceeds 5 vars — the atom is treated as opaque, so semilinear decomposition never fires. | `semilinear.rs:111` |
| A1b | **xor-mask wall** (`a ^ (a & M)`, M a wide OR) — CONFIRMED | At ≥ 5-var atom support the AND-form `a & ~M` is never recovered; input echoed back or blown up. | empirical, see corpus test |
| A2 | **Variable wall** (linear MBA over 12–20 vars) | Signature track needs a `2^n` truth table; with the atom cap and a 20-var ceiling, large-arity identities starve the budget before reduction. | `mono.rs:11` (`MAX_POLY_VARS=20`), `signature_eval.rs:16` |
| A3 | **High-degree polynomial** (`(a+b)**k` expansions, k beyond the degree cap) | Tensor falling-factorial interpolation escalates degree only to a cap; past it the recovery returns `Blocked`. | `multivar_poly_recovery.rs` (degree escalation + divisibility gate) |
| A4 | **Grid-probe wall** (mixed/multilinear product over > 8 vars) | `probe_grid_check` refuses recovery once num_vars > 8. | `multivar_poly_recovery.rs:273` |
| A5 | **Unknown shape** (bitwise-over-arith *without* a multiply, e.g. `~(a + (b & (c + d)))`) | `HAS_BITWISE_OVER_ARITH` without `HAS_MUL` does not trigger structural recovery, so neither track runs. | `classification.rs:94` |
| A6 | **Non-polynomial periodic** (`>>`-laced terms, `(a>>1)+(a&1)…`) | `Shr`/low-bit masks aren't polynomials; the 2-adic divisibility gate fires and arithmetic recovery bails. | `multivar_poly_recovery.rs` |
| A7 | **Budget exhaustion** (deeply nested products) | Loop stops at `max_expansions = 1024`; deep nesting exhausts it before a candidate is produced. There is no wall-clock timeout — only the expansion count. | `context.rs:26`, `main_loop.rs` |

## B. Soundness attacks (verifier evasion)

The default acceptance check is **finite sampling**, not a proof. Z3 is behind
the optional `z3` feature ([main.rs:21](../../crates/cobra-cli/src/main.rs)); the
README admits Boolean-signature certs prove agreement *only on Boolean inputs*,
not full-width equivalence.

The full-width probe schedule in
[spot_check.rs:229](../../crates/cobra-core/src/spot_check.rs) is:

1. all variables set to the same "adversarial" value;
2. one variable set, **all others zero**;
3. expression-derived constants, same two patterns;
4. ≤ 64 *pairwise* probes (only two vars nonzero at a time);
5. `num_samples` random points from `splitmix64` seeded by
   `seed_for(num_vars, bitwidth, num_samples)` — **fully deterministic**.

Two structural weaknesses:

- **The schedule never sets 3+ variables simultaneously nonzero** except in step 5.
- **The random seed is a pure function of `(num_vars, bitwidth, num_samples)`**, so
  every "random" probe point is computable offline.

**Exploit (family B1, `soundness_trap`).** For `n ≥ 3` vars, pick any difference
term that

- vanishes whenever any variable is 0 (kills steps 2–4: a product `a*b*c*…`),
- vanishes when all variables are equal (factor `(a-b)`),
- vanishes at each deterministic random point (one linear factor `(a - aᵢ)` per
  sample `i`).

Then `D = a*b*c*(a-b) * Π_i (a - aᵢ)` is **zero on the entire probe schedule but
nonzero for generic distinct nonzero inputs**. So for any target `f`, the
obfuscated `g = f + D` is inequivalent to `f` yet `full_width_check_eval` reports
`passed = true` — a false accept. Default CLI uses 8 samples; the residual gate
uses 64 ([spot_check.rs:23](../../crates/cobra-core/src/spot_check.rs)) and the
orchestrator promotion filter uses 256
([main_loop.rs:386](../../crates/cobra-orchestrator/src/main_loop.rs)); the
generator parameterises the sample count so the trap can target a given path.
(`try_promote_best_rewrite` additionally requires a Lean certificate before
stamping `Verified`, so B1 most directly attacks every path that accepts on the
spot-check alone and prints the result as `unverified` — still wrong output.)

**Why higher sample counts are incidentally hard to evade.** The linear-factor
construction `Π_i (v0 - aᵢ)` collapses over `Z/2⁶⁴`: with enough distinct roots,
roughly half the factors are even, so the product accumulates more than 64
factors of two and becomes the **zero function**, not merely zero on the probe
set — destroying the witness. The generator detects this and refuses rather than
emit a degenerate case. In practice the default 8-sample CLI check is cheaply and
guaranteed-evadable; the 64-sample residual gate and 256-sample orchestrator
filter resist the cheap construction. This is itself a finding: **raising the
default spot-check sample count materially hardens the verifier against
precomputed-seed traps**, and is the lowest-cost mitigation.

## Recommended hardening

- Treat the bounded full-width check as a *filter*, never as proof; gate any
  result presented to the user behind Z3 or a Lean certificate.
- ✅ **Implemented:** bind the probe seed to a structural fingerprint of the
  original and candidate expressions. `seed_for` now takes an `expr_salt`
  derived from `Evaluator::structural_fingerprint` (which folds in every
  embedded constant) and `expr_fingerprint`. This keeps the schedule fully
  deterministic for reproducibility while making the precomputed-seed trap (B1)
  infeasible: a difference term engineered to vanish on the probe points must
  embed constants that themselves change the seed — a fixpoint that does not
  exist in practice. Regression-guarded by
  `precomputed_seed_trap_is_now_caught_by_salted_probe`.
- Still worth doing: add probes that set ≥ 3 variables nonzero with independent
  random values (defense in depth against structured-only traps), and raise the
  default sample count (the 2-adic structure of `Z/2⁶⁴` already defeats cheap
  polynomial traps past ~24 factors).

## Generator

[`generate_adversarial.py`](generate_adversarial.py) emits each family with an
exact u64 modular evaluator and **self-verifies** every case (obfuscation truly
equals its target; trap truly vanishes on the reproduced probe schedule and
differs at a witness point). See its `--help`.
