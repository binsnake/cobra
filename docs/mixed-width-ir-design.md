# Mixed-width IR + shift hardening — design spec

Status: in progress on branch `feat/ir-mixed-width-shift`. This is the single source of truth for all implementation agents working this change. Goal: mixed-width expressions are **representable, evaluable, and sound** end-to-end (parse → IR → evaluate → Z3-verify), all 755 existing tests stay green, plus new mixed-width/shift tests. Passes that assume uniform width must treat mixed-width subtrees **conservatively (opaque)** — never miscompile — rather than simplify across width boundaries.

## Decisions
- **Shift (match upstream PR #46):** keep lowering `a << k` → `a * 2^k` (mul) at parse (`apter/ast.rs:apply_shl`). Keep `Kind::Shr(u32)` as the only shift node. Constant amounts only. **No `Kind::Shl` node.** No IR-level shl normalization (verified: no non-parser path constructs a left shift — all other `<<` are `1u64 << n` mask math). Optional: recognize `x * 2^k` for **render/cost only** (not an IR rewrite). Add tests.
- **Node-width:** full mixed-width *semantics* with a sound conservative fallback (above). Representation below.
- **Lean** stays 64-bit gated (`lean_cert.rs:934,957`); additionally gate on `is_uniform_width`. No width-parametric Lean now.

## Representation (cobra-core/src/expr.rs)
Add width-changing variants; all existing variants stay **same-width**; constants stay width-agnostic (masked to context width at use).
```rust
pub enum Kind {
    Constant(u64), Variable(u32),
    Add, Mul, And, Or, Xor,   // same-width binary
    Not, Neg, Shr(u32),       // same-width unary (unchanged)
    ZExt(u32), SExt(u32), Trunc(u32),  // NEW unary; result width = payload
    Concat,                            // NEW binary; result width = w(c0)+w(c1)
}
```
- `arity()`: `ZExt|SExt|Trunc => 1`, `Concat => 2`. `precedence()`: casts = unary prec (1); `Concat` a new loose level.
- Factories: `Expr::zext/sext/trunc(child, w)`, `Expr::concat(l, r)`. Render: `zext(x, w)` style; `x ++ y` for concat.

## Per-variable widths
Variables carry width via a **parallel `var_widths: Vec<u32>`** alongside every `var_names: Vec<String>`. Default-fill to the run's global `bitwidth` so all existing callers are unchanged. Thread into: `AstResult` (parser), `OrchestratorContext` (context.rs), `VerifyOpts` (verify/lib.rs), `Options` (simplify_outcome.rs). Audit every `make_var_asts` / var-table constructor — a missed site = wrong Z3 width = false "not equivalent".

## New module cobra-core/src/width.rs
```rust
pub fn width_of(expr: &Expr, var_widths: &[u32], default_w: u32) -> u32;
//  Constant -> default_w (context); Variable(i) -> var_widths[i];
//  ZExt/SExt/Trunc(w) -> w; Concat -> w(c0)+w(c1); same-width ops -> width_of(c0).
pub fn is_uniform_width(expr: &Expr, var_widths: &[u32], w: u32) -> bool;
//  true iff NO cast/Concat node anywhere AND every Variable width == w.
pub fn validate_widths(expr: &Expr, var_widths: &[u32], default_w: u32) -> Result<()>;
//  same-width operands must agree; Concat children any width; casts well-formed.
```
`arith.rs` gains concrete cast semantics: `zext` (= mask to `to`), `sext(v, from, to)` (sign-extend), `trunc(v, to)` (= `v & bitmask(to)`).

## Soundness wall (the load-bearing part)
`is_uniform_width` is the oracle. Mixed-width subtrees must be walled off **before** entering any signature/truth-table machinery:
1. **semilinear.rs `compute_atom_truth_table` / `eval_expr_bool` (~:107/:123):** if `!is_uniform_width(atom, …)`, register the subtree as a fresh **opaque variable of width `width_of(subtree)`** — do not decompose. This is the single most important wall; with it, signature_eval/spot_check never observe a cast.
2. **bit_partitioner.rs `eval_atom_at_bit_impl`:** add `ZExt|SExt|Trunc|Concat => unreachable!` next to the existing `Add|Mul|Neg => unreachable!`. Keep as `unreachable!` (tripwire — panics in tests if a pass bypasses the wall, rather than silently corrupting in release).
3. **atom_simplifier.rs:118:** extend `has_constant_or_shr` to `has_cast_or_concat`; block complement-merge / constant-fold across these.
4. **classifier.rs:** cast/Concat ⇒ `HAS_UNKNOWN_SHAPE` (steer orchestrator away from algebraic recovery).
5. **lean_cert.rs:934/957:** add `is_uniform_width` to the existing `!= 64` gate.

## Concrete semantics that MUST be correct
- **evaluator.rs / compiled.rs / spot_check.rs eval / expr_utils::eval_constant / signature_eval::eval_sig_recursive:** add cast/concat arms with correct width math. `compiled.rs` is the hardest: its stack machine uses one global `mask`/`bw`; each cast/concat instr must carry its own width(s) in `operand` and apply local masks; same-width ops keep using `bw`. Cast depth = 0 (like Not); Concat depth = 1 (like Add).
- **z3_backend.rs `build_bv`:** per-variable widths via `var_widths[i]`; emit `bvzero_ext`/`bvsign_ext`/`extract`/`concat`.
- **expr_cost.rs:** casts in unary arm, Concat in binary arm.

## Build order (core-first, sequential — type change cascades through crate deps)
1. **cobra-core** foundation (contract everything builds on) → `cargo test -p cobra-core` green, commit.
2. Then `{cobra-parser, cobra-verify, cobra-ir}` (each depends only on cobra-core) — parallelizable.
3. **cobra-passes** (needs cobra-ir) incl. the soundness wall → then orchestrator/cli.
4. `cargo test --workspace -- --test-threads=2` green + new tests.

## Test plan
At-risk (keep green): ast.rs(14), compiled.rs, expr.rs render/arity, z3_backend, bit_partitioner/atom_simplifier. New: `width_of`/`is_uniform_width`; eval of zext/sext/trunc/concat vs hand-computed u64; Z3 mixed-width roundtrip (e.g. `concat(a:u8,b:u8) == zext(a,16)*256 + zext(b,16)`); parser shl/shr kept; a cross-width MBA stays unsimplified (opaque path → output == input).
