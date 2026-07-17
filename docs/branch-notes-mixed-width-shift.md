# Branch notes — `feat/ir-mixed-width-shift`

Working notes / PR draft for the mixed-width + shift + review-fix work. **Unmerged, unpushed.** Status: 782 unit tests green, `cargo fmt --all -- --check` clean, full dataset sweep clean (`unsafe=0`, no regression).

## What this branch does

Three logical groups of work, in commit order off `main` (`f8daba1`):

### 1. Mixed-width IR + shift (`20de19f` … `08c43a2`)
The expression IR was single-width (one global `bitwidth: u32`, no per-node width). This adds full mixed-width support with a sound, conservative model.
- `Kind` gains `ZExt(u32)`, `SExt(u32)`, `Trunc(u32)`, `Concat`. New `cobra-core/src/width.rs` (`width_of` / `is_uniform_width` / `validate_widths`) and `arith::{zext,sext,trunc}`.
- Per-variable widths threaded via `var_widths: Vec<u32>` on `AstResult` and `VerifyOpts` (default-filled to the run bitwidth; `VerifyOpts` dropped `Copy`→`Clone`).
- Z3 backend emits `bvzero_ext`/`bvsign_ext`/`extract`/`concat`; Lean stays 64-gated + an `is_uniform_width` guard (never certifies a mixed-width tree).
- **Soundness wall:** signature/truth-table machinery never bit-walks a cast. Mixed-width subtrees are lifted as opaque atoms (`semilinear::compute_atom_truth_table`), with `unreachable!` tripwires in `bit_partitioner`, a `HAS_UNKNOWN_SHAPE` flag in `classifier`, and a uniform-width gate on `semilinear_signature::is_linear_shortcut`.
- **Shift:** matches upstream trailofbits/CoBRA PR #46 — `a << k` lowers to `a * 2^k` at parse; `>>` stays `Kind::Shr(k)`. No `Kind::Shl` node (no non-parser shl path exists). Integration tests added.
- Design spec: `docs/mixed-width-ir-design.md`.

### 2. Review bug fixes + cleanups (`435e44f` … `2062936`)
From the review recorded in `docs/code-review-2026-06-08.md`:
- **Bug:** scheduler attempt-cache fingerprint was hard-coded to width 64 while the main loop recorded at `ctx.bitwidth` → cross-item dedup silently no-op'd off-64. Now threads `ctx.bitwidth` (regression test at width 32).
- **Bug (High):** `lean_emit` and `lean_cert` carried two copies of 12 theorem matchers that had begun to drift (risking wrong-argument proofs). Hoisted into one `lean_match` module (−373 lines).
- **Cleanups:** dead `SignatureVector`; math/helper dedup (`precision_bits`, `flatten_assoc`, `mod_inverse_odd_half`); dead-code stubs; `merge_certificate`/`active_ast_vars` hoists; etc.

### 3. qsynth ghost-variable leak fix (`ef366cd`, `6065242`, `0ea1810`)
A **pre-existing** upstream bug (reproduces identically on `main`), found by running the datasets. Nested lifts didn't chain: `lift_arithmetic_atoms` / `lift_repeated_subexpressions` dropped `item.group_id` (→ `None`) when emitting the lifted skeleton, so an inner lifted variable (index ≥ input-var-count) escaped back-substitution into the final output. 15/500 `qsynth_ea` cases leaked; the CLI panicked because `render` didn't bounds-check.
- `ef366cd` — `render` bounds-guard (`expr.rs`): no panic on an out-of-range var.
- `6065242` — orchestrator finalization guard (`entry.rs`): reject any output whose vars ⊄ input → fail-safe echo of the input.
- `0ea1810` — root cause: `parent_group_id` on `LiftedSubstituteCont`, propagated through `prepare_lifted_outer_solve` and resolved to the parent group in `resolve_competition` (mirrors `resolve_residual_recombine`), so the inner lift's substitution runs.

## Verification

Dataset harness: `cargo build --release --bin cobra-sweep`, then `cobra-sweep datasets/**/*.txt --bitwidth 64`. Gate = `unsafe=0` (no simplification that isn't equivalent to its input).

Full sweep, 74,885 cases (all datasets except the pathologically-slow 5-var `simba/e1_5vars`, spot-checked separately and identical to `main`):

|metric|before leak fix|after leak fix|
|-|-|-|
|simplified|74,859|74,874 (+15)|
|parity (matches ground truth)|73,830|73,845 (+15)|
|errored|19|4 (benign oses dataset quirk only)|
|unsafe|0|0|

- Branch is behavior-identical to `main` at 64-bit except for the leak fix (which is a strict improvement). Mixed-width arms are inert without cast nodes; the scheduler fix only changes behavior off-64.
- Unit tests: 782 green (`cargo test --workspace -- --test-threads=2`). New leak test: `nested_lift_does_not_leak_ghost_variable`.

## Known / deferred (not blocking)
- **Performance (pre-existing):** easy MBA is sub-ms/case, but hard synthesis (qsynth, permutation) and 5-var sets are slow due to the orchestrator's exhaustive search. Separate optimization opportunity.
- **Mixed-width reach:** representable/evaluable/Z3-verifiable and exercised by tests, but not yet reachable from the text parser (no cast syntax) — a follow-on if user-facing mixed-width is wanted.
- **Z3 feature** can't link in this environment (no `z3.h`); cast arms are API-checked, not execution-tested here.
- **CI** gates fmt + tests only; clippy is not run. ~19 pre-existing `clippy::pedantic` lints in the lean files predate this branch.
- Cross-crate duplications (SplitMix64 ×4, `hash_combine`, Stirling) deferred as they need coordinated multi-crate edits — see the review doc.
