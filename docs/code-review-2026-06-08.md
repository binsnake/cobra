# Review: mixed-width support gap + duplication/simplification cleanup

> **Recorded:** 2026-06-08 — code review of CoBRA-rs (Rust port of Trail of Bits' CoBRA).
> **Status:** not blocking. `cargo test --workspace -- --test-threads=2` is green (755 passing, 0 failing).
> **Method:** 17-agent fan-out review across all hand-written source (the 393k-line generated `crates/cobra-passes/src/npn4_table.rs` excluded), each candidate finding adversarially re-verified against the source. 95/99 candidates confirmed — 48 duplication, 26 simplification, 21 mixed-width; severity 1 high / 10 medium / 84 low.

This issue records the results of a code-quality + capability review. **Nothing here is blocking — the test suite is currently green (755 passing).** Findings are recorded for later prioritization. Every claim is tied to a `file:line`. Rejected/speculative items from the raw review were dropped.

---

## Mixed-width operation support

**Headline gap.** The expression IR is *single-width by construction*. `Kind` (`crates/cobra-core/src/expr.rs:14-27`) carries only `Constant(u64)` / `Variable(u32)` / `Shr(u32)` payloads plus arithmetic/bitwise tags — **no width field** — and `Expr` (`crates/cobra-core/src/expr.rs:64-68`) is just `{ kind, children }`. A single global `bitwidth: u32` is threaded end-to-end and every op masks to one `bitmask(bitwidth)` (`crates/cobra-core/src/arith.rs:9-17`, `42-77`).

**What is missing:**
- No per-node / per-operand width — every variable and subtree shares the one run-level width.
- No width-changing node kinds: there is no `ZExt` / `SExt` / `Trunc` / `Concat` / `Slice` in `Kind` (`expr.rs:15-27`), `Opcode` (`crates/cobra-core/src/compiled.rs:11-22`), or the parser's `SweepOp` (`crates/cobra-parser/src/eval.rs:25-39`). The parser also has no surface syntax for a width cast (`crates/cobra-parser/src/token.rs:194-208`).
- The Z3 lowering `build_bv` builds every var/const/op at one `opts.bitwidth` with no `bvzero_ext`/`bvsign_ext`/`extract`/`concat` arm (`crates/cobra-verify/src/z3_backend.rs:69-106`, `61-66`).
- The Lean proof layer is hard-pinned to 64: `try_single_rewrite_64` / `try_single_rewrite_between_64` early-return `None` for `bitwidth != 64` (`crates/cobra-verify/src/lean_cert.rs:934-936`, `957-959`), and the entire theorem corpus is `_64`-suffixed (`lean_cert.rs:166-211`).

**Intentional boundary vs silent-miscompile risk:**
- **Intentional, fails closed (NOT a miscompile).** A mixed-width operand cannot be *constructed* in the first place — there is no API/syntax/node to express one — so no code path silently mishandles a width change. The Lean layer explicitly returns `None` off-64 rather than emitting an unsound cert. Acceptance is independently gated by a full-width evaluator check at the true `ctx.bitwidth` (`crates/cobra-passes/src/verify_candidate.rs:63-93`), so off-64 runs are sound; they just don't get a theorem-backed certificate.
- **The one real (non-mixed-width) behavior bug in this area** is unrelated to representability — see the scheduler fingerprint width mismatch under *Suggested prioritization* (it bypasses dedup, doesn't corrupt results).
- **Latent trap worth noting:** `is_all_ones` matches `Kind::Constant(u64::MAX)` (`crates/cobra-verify/src/lean_cert.rs:861-863`), which is the correct all-ones mask only at width 64. It is currently unreachable off-64 because the `bitwidth != 64` gate fires first, but it would become silently wrong if that gate were ever relaxed.

**Minimal design to add it (only if mixed-width MBA becomes in scope):**
- [ ] Add a per-node result width to `Expr` (`crates/cobra-core/src/expr.rs:64-68`) **or** add explicit `Kind::{ZExt,SExt,Trunc,Concat,Slice}` variants (`expr.rs:15-27`), then thread that through `arity()`/`precedence()` (`expr.rs:33-58`), `compile`/`eval` (`crates/cobra-core/src/compiled.rs`), `SweepOp` + parser (`crates/cobra-parser/src/eval.rs:25-39`, `crates/cobra-parser/src/token.rs`), and `build_bv` via `bvzero_ext`/`bvsign_ext`/`extract`/`concat` (`crates/cobra-verify/src/z3_backend.rs:69-106`).
- [ ] Generalize the `_64` Lean theorem family to width-parametric lemmas and drop the `bitwidth != 64` gates (`lean_cert.rs:934`, `957`).

**Low-cost action regardless of whether mixed-width is ever added:**
- [ ] Document the single-width contract at the IR boundary — `Kind`/`Expr` (`crates/cobra-core/src/expr.rs:14`), the arith module doc (`crates/cobra-core/src/arith.rs:1`), and `is_valid_bitwidth` (`arith.rs:22`) — stating one global bitwidth (1..=64) per run, no per-node width, and that extend/trunc/concat are out of scope. This converts an unstated invariant into an explicit one.

---

## Duplication

**Evaluators / interpreters re-implemented across crates** (canonical target: a single parametric tree-walk in `cobra-core`):
- [ ] `spot_check::eval_expr` (`crates/cobra-core/src/spot_check.rs:178`) and `expr_utils::eval_constant` (`crates/cobra-core/src/expr_utils.rs:20`) are the same 10-arm tree-walk differing only in the `Variable` leaf. Note: `eval_expr` masks And/Or/Xor; `eval_constant` does not — a unifier must keep the masking.
- [ ] `eval_at_point` (`crates/cobra-ir/src/semilinear_signature.rs:159`) duplicates `eval_expr` and additionally hard-codes width `64` in its Neg/Shr arms (`:164`, `:170`); harmless today only due to the trailing `& mask` on pre-masked operands.
- [ ] `eval_bitwise_at` (`crates/cobra-ir/src/structure_recovery.rs:36`) and `eval_expr_bool` (`crates/cobra-ir/src/semilinear.rs:123`) and `eval_atom_at_bit_impl` (`crates/cobra-passes/src/bit_partitioner.rs:29`) are a family of near-identical pure-bitwise interpreters; `flatten_complex_atoms`' two probe evals (`structure_recovery.rs:470`/`:472`) could use `cobra_core::evaluator::Evaluator` (already imported at `multivar_poly_recovery.rs:23`).
- [ ] `parse_and_evaluate`'s hand-rolled 2^n sweep (`crates/cobra-parser/src/eval.rs:153-216`) duplicates `evaluate_boolean_signature` (`crates/cobra-core/src/signature_eval.rs:14-129`) and inlines the `arith.rs:42-77` mod_* helpers; `build_ast` already lowers the parser-only ops it needs (`crates/cobra-parser/src/ast.rs:54`).
- [ ] `prepare_remainder_from_core.rs:95-102` hand-rolls the `{0,1}^n` signature loop already provided by `evaluate_boolean_signature_from_evaluator` (`crates/cobra-core/src/signature_eval.rs:22`); the in-tree replacement already exists at `signature_singleton_poly_recovery.rs:302-304`.

**Math / mask helpers (canonical lives in `cobra-core::arith` or `cobra-ir::math_utils`):**
- [ ] Inline `if w>=64 {u64::MAX} else {(1<<w)-1}` reimplements `cobra_core::arith::bitmask` (`crates/cobra-core/src/arith.rs:9`) at four sites that already import it: `math_utils.rs:50`, `coefficient_splitter.rs:36`, `multivar_poly_recovery.rs:179`, `ghost_residual_solver.rs:170`. Bare low-mask `(1<<t)-1` also at `ghost_residual_solver.rs:157`, `weighted_poly_fit.rs:207`/`:301`, `multivar_poly_recovery.rs:168`, `singleton_power_recovery.rs:103`.
- [ ] **`medium`** `mod_inverse_odd_half(x, w)` (`crates/cobra-ir/src/coefficient_splitter.rs:31`) is verbatim `mod_inverse_odd(x, w-1)` (`crates/cobra-ir/src/math_utils.rs:47`). (Public re-export at `lib.rs:40` + tests at `coefficient_splitter.rs:241-249` are touched by removal.)
- [ ] **`medium`** Precision-band reduction (drop-if `q>=bitwidth`, `band=bitwidth-q`, saturating mask) hand-coded 3× — `poly.rs:72`, `poly_normalizer.rs:21`, `multivar_poly_recovery.rs:163` — and must stay lock-step or `is_valid`/`normalize_polynomial` disagree. Reuse existing `bitmask`; add only a `precision_bits(weight, bitwidth)` band helper.
- [ ] **`medium`** `factorial_to_monomial` (`crates/cobra-passes/src/singleton_power_expr_builder.rs:38`) re-rolls the signed Stirling recurrence of the already-exported `cobra_ir::build_stirling_first_kind` (`crates/cobra-ir/src/math_utils.rs:86`).
- [ ] `z3_backend::build_from_coeffs` (`crates/cobra-verify/src/z3_backend.rs:111-142`) re-implements the AND-monomial bit→variable convention canonical in `cobra_core::expr_rewrite::build_and_product`/`apply_coefficient` (`crates/cobra-core/src/expr_rewrite.rs:17-42`).
- [ ] **`medium`** `solve_2adic_fixed<N>` (`crates/cobra-passes/src/weighted_poly_fit.rs:219-311`) hand-mirrors `solve_2adic` (`weighted_poly_fit.rs:114-217`) — two copies of a subtle 2-adic Gaussian solver for one `N=4` caller at `pattern_matcher.rs:843`.

**Variable-support / remap / boolean-sig helpers (canonical: `cobra_core::expr_utils`):**
- [ ] `collect_support` (`crates/cobra-ir/src/semilinear_normalizer.rs:211`), `collect_var_support` (`crates/cobra-passes/src/lifting.rs:254`) duplicate `collect_vars` (`crates/cobra-core/src/expr_utils.rs:63`).
- [ ] `remap_vars` (`crates/cobra-passes/src/bitwise_decomposer.rs:86`) duplicates `remap_var_indices` (`crates/cobra-core/src/expr_utils.rs:75`) (allocating vs in-place; callers need `clone_tree()` first).
- [ ] `contains_shr` duplicated in `dynamic_mask.rs:61` and `semilinear_normalizer.rs:30` (+ a `has_constant_or_shr` variant at `atom_simplifier.rs:118`).
- [ ] `pattern_matcher::is_boolean_sig` (`crates/cobra-passes/src/pattern_matcher.rs:33`) duplicates `cobra_core::is_boolean_valued` (`crates/cobra-core/src/signature_simplifier.rs:39`).
- [ ] `eval_constant_bitwise`/`eval_constant_arith` (`crates/cobra-ir/src/semilinear_normalizer.rs:119`/`:143`) duplicate `eval_constant` (`crates/cobra-core/src/expr_utils.rs:20`).

**Per-crate copy-paste (canonical: hoist to existing shared module):**
- [ ] `merge_certificate` copy-pasted in 4 files (`atom_identity_rewrite.rs:211`, `atom_simplifier.rs:236`, `lower_not_over_arith.rs:121`, `pattern_matcher.rs:1072`); wrap `LeanCertificate::merge_step_chain` (`crates/cobra-verify/src/lean_cert.rs:1021`).
- [ ] `should_skip_decomposition` + `verified_candidate_decomposition_cost_bound` + `MAX_CANDIDATES` byte-identical across `signature_bitwise_decompose.rs:31` and `signature_hybrid_decompose.rs:43`; hoist into `decomposition_helpers` (`lib.rs:30`).
- [ ] `active_ast_vars` (×4) / `active_ast_evaluator` (×2) across `lift_arithmetic_atoms.rs:38`/`:47`, `lift_repeated_subexpressions.rs:23`/`:32`, `operand_simplify.rs:63`, `product_identity_collapse.rs:126`; hoist into `lifting.rs` (`lib.rs:40`).
- [ ] Active-variable scan written 3× — `count_active` (`bitwise_decomposer.rs:33`), inline in `compact_signature` (`bitwise_decomposer.rs:57`), `count_active_vars` (`hybrid_decomposer.rs:18`).
- [ ] SplitMix64 PRNG implemented 4× — `template_decomposer.rs:895`, `decomposition_helpers.rs:128`, `spot_check.rs:459`, `null_poly_generator.rs:120`.
- [ ] `terminal_rank` duplicated in `main_loop.rs:292` and `ranker.rs:63`.
- [ ] `hash_combine` duplicated in `fingerprint.rs:13` and `semilinear.rs:45` (IR copy is `pub(crate)`).
- [ ] `exprs_equal` (`atom_simplifier.rs:99-116`) reimplements `Expr`'s derived `PartialEq` (`crates/cobra-core/src/expr.rs:64`); canonical idiom already at `atom_identity_rewrite.rs:595`.
- [ ] `node_count` (`mixed_product_rewriter.rs:99`) duplicates `count_nodes` (`lifting.rs:35`) and is unused.
- [ ] `merge_and_store` term-merge tail (HashMap fold + drop-zeros + sort) duplicated 4× — `term_refiner.rs:334`, `structure_recovery.rs:157`/`:421`/`:513`; `rebuild_terms_from_groups` already exists at `structure_recovery.rs:139` but `refine_terms` (`term_refiner.rs:317`) re-inlines it.
- [ ] `pack_bool_sig` (u32, `pattern_matcher.rs:40`) and `pack_bool_sig_64` (u64, `pattern_matcher.rs:102`) are the same loop at two widths.

**Within-crate / structural duplication:**
- [ ] `flatten_add`/`flatten_mul` (`expr_rewrite.rs:135`/`:149`) — extract one `flatten_assoc` parameterized by `Kind`.
- [ ] Drain-map-collect child-recursion prologue in `fold_constant_arithmetic` (`expr_rewrite.rs:172`), `refold_negation` (`:218`), `extract_common_factor` (`:259`) — three round-trip a `SmallVec` through a heap `Vec`.
- [ ] `build_var_support` (`expr_rewrite.rs:46`) duplicates `try_build_var_support`'s index-map (`:63`) — delegate.
- [ ] Wide-buffer scatter (size + zero + scatter) ×3 in `evaluator.rs:170`/`:187`/`:230`; and `remap_via_closure` (`crates/cobra-passes/src/mapped_evaluator.rs:28`) forks the scatter arm of `Evaluator::remap` (`crates/cobra-core/src/evaluator.rs:223`).
- [ ] **`high`** `lean_emit.rs::theorem_eval_args` matchers (`crates/cobra-verify/src/lean_emit.rs:284-454`) duplicate the entire pattern-matcher set in `lean_cert.rs::identify_rewrite_theorem_64` (`crates/cobra-verify/src/lean_cert.rs:532-663`, `833-859`). The two must stay behaviorally identical: cert copies *decide* which theorem fires, emit copies *extract* the operands instantiating it — divergence silently emits a Lean cert whose arguments don't match the rewrite (vacuous/wrong "passing" proof). They have already cosmetically drifted (`not_or_add_self_add_one_operands`: `lean_cert.rs:634` vs `lean_emit.rs:364`). Hoist the 12 matchers into one shared submodule.
- [ ] Case A / Case B ~46-line verified-candidate emission tail duplicated (`signature_singleton_poly_recovery.rs:155` and `:215`).
- [ ] `resolve_bitwise_compose` / `resolve_hybrid_compose` share ~63 lines of verify/record/submit (`resolve_competition.rs:221-285` / `287-350`).
- [ ] `target_vars`/`target_eval` is_empty-fallback idiom copy-pasted across 5 residual passes + helper (`residual_ghost.rs:62`, `residual_poly_recovery.rs:59`, `residual_factored_ghost.rs:73`, `residual_template.rs:44`, `residual_supported.rs:57`, `residual_common.rs:29`); `solved_expr_vars` param to `try_recombine_and_emit` is redundant.
- [ ] Near-identical residual-pass skeleton (Remainder guard, `>6` guard, local `fail()`, recombine/Blocked tail) across `residual_ghost.rs:34`, `residual_factored_ghost.rs:41`, `residual_poly_recovery.rs:37`, `residual_template.rs:33`.
- [ ] Post-order DFS path-bookkeeping skeleton ×4 — `atom_identity_rewrite.rs:133`, `atom_simplifier.rs:253`, `lower_not_over_arith.rs:135`, `mixed_product_rewriter.rs:144` (leaf predicate / return shape diverge, so not a clean drop-in).
- [ ] `collapse_double_not` (`pattern_matcher.rs:439`) duplicates the Not(Not(x)) fold already in `simplify_atom` (`atom_simplifier.rs:145`); extract a shared not-not helper for a zero-behavior-change dedup.
- [ ] `try_single_rewrite_between_64(...).or_else(LeanCertificate::new)` endpoint-fallback idiom verbatim in `verify_candidate.rs:134-146` and `resolve_competition.rs:387-398` (do NOT fold in `main_loop.rs:408-414` — it intentionally omits the unchecked `new` fallback).
- [ ] Base-`base` index→digit decode ×3 in `multivar_poly_recovery.rs:117`/`:154`/`:287`.
- [ ] Factorial-basis forward-difference + divisibility-gate orchestration shared by `multivar_poly_recovery.rs:128` and `singleton_power_recovery.rs:79` (math primitives already shared in `math_utils.rs`; only the loop body duplicates).
- [ ] Square-and-multiply pow recurrence in `ast.rs:149-162` (Expr tree) and `eval.rs:194-206` (u64) — add `arith::mod_pow` as the numeric counterpart.
- [ ] Operator precedence ladder duplicated between lexer (`token.rs:162-207`) and `Kind::precedence` (`expr.rs:47-58`); `token.rs:5-6` even claims the lexer is the "single source of truth."
- [ ] Five-arm `Gate` match ×4 in cobra-simd (`lib.rs:36-43`, `110-116`, `135-142`, `165-173`); `probe0_matches` is the avoidable fourth copy.

---

## Simplification opportunities

**Dead code kept alive by warning-suppression hacks (delete the stub + the touch):**
- [ ] `is_const` + `let _ = is_const;` (`crates/cobra-passes/src/atom_simplifier.rs:31-33`, `:388`).
- [ ] `compact_sig` + `let _ = compact_sig;` (`crates/cobra-passes/src/aux_var.rs:52`, `:232`) — also fix the dangling intra-doc link at `:82`.
- [ ] `_reference_evaluator_type` stub + its false "silence unused import" comment (`crates/cobra-passes/src/build_signature_state.rs:166-170`) — `Evaluator` is already used by `active_eval`'s return type (`:138`).
- [ ] `_classification_anchor` + its sole-purpose `Classification` import (`crates/cobra-passes/src/residual_common.rs:112-117`, `:4`), and repair the split doc sentence at `:18-19`/`:112`.

**Redundant bindings / no-op iterator adapters:**
- [ ] `let _ = c;` discards the constant child in `is_scaled_var_product` (`crates/cobra-passes/src/decomposition_helpers.rs:32-46`) — bind only the non-constant child.
- [ ] `enumerate()` + `let _ = j;` where `j` is unused (`crates/cobra-passes/src/singleton_power_expr_builder.rs:94`, `:104`) — use `iter().skip(1)`.
- [ ] No-op `.take(len)` / `.take(num_vars)` on iterators already sized to their backing vecs (`crates/cobra-parser/src/eval.rs:159-161`).

**Dead branches / unreachable arms:**
- [ ] Unreachable `if sub == 0 { break }` in submask loop (`crates/cobra-ir/src/anf_cleanup.rs:387-389`).
- [ ] Always-true `if !bit_is_zero` guard + dead `None` branch (`crates/cobra-passes/src/signature_singleton_poly_recovery.rs:217`).
- [ ] Unreachable `Kind::Constant`/`Kind::Variable` emit-branch arms in `compile()` (`crates/cobra-core/src/compiled.rs:74-76`) — already drifted (`:75` emits unmasked `*v` vs live `*v & mask` at `:94`). Add `unreachable!` or move leaf construction into the emit branch.
- [ ] Dead `expect_constant` Err arms / double-parse in `build_ast` shift/exponent handling (`crates/cobra-parser/src/ast.rs:128-169`) — already validated by `validate_shifts_and_exponents` (`crates/cobra-parser/src/postfix.rs:63-107`). `intentional` defense-in-depth (`build_ast` is `pub`); at minimum stop re-parsing the literal.

**Redundant allocations / clones / masking:**
- [ ] `repair_product_shadow` round-trips children through an intermediate `SmallVec` (`crates/cobra-core/src/expr_rewrite.rs:92-98`) — collect straight back into `expr.children`.
- [ ] `build_power_expr`/`reduce_add_tree` deep-clone operands then discard originals (`crates/cobra-ir/src/poly_expr_builder.rs:17`, `:39`) — move via `into_iter()` pairs instead of `clone_tree()`.
- [ ] `substitute_bindings` deep-clones the subtree then re-clones each child (`crates/cobra-passes/src/resolve_competition.rs:759-780`) — rewrite as a bottom-up rebuild mirroring `remap_vars` (`bitwise_decomposer.rs:86`).
- [ ] `match_and_via_ornot_lax` allocates a `HashSet` + computes `expr_identity_hash` only for dead inserts (`crates/cobra-passes/src/atom_identity_rewrite.rs:423-448`) — leftover half-removed dedup; drop both.
- [ ] Redundant trailing `& mask` on Or/Xor/Shr in `eval_sig_recursive` (children pre-masked; And arm omits it) (`crates/cobra-core/src/signature_eval.rs:116`/`:124`/`:83-84`) — document the invariant and drop to match And.
- [ ] Inline `prec_mask` duplicates already-imported `bitmask(prec)` (`crates/cobra-passes/src/ghost_residual_solver.rs:170`).
- [ ] `gate_matches_scalar` uses a two-pass body + temp `ProbeVals` where `gate_apply_scalar(...) == *target` suffices (`crates/cobra-simd/src/lib.rs:47-62`); keep the `#[allow(dead_code)]`.

**ExprInfo / classifier cleanups:**
- [ ] `Kind::Not` arm rebuilds an identical `ExprInfo` instead of returning the child verbatim; `Kind::Neg` can use struct-update syntax (`crates/cobra-ir/src/semilinear_normalizer.rs:77`, `:105`).
- [ ] `classify_node`'s u64 `var_mask` silently zeroes for var indices `>= 64` (`crates/cobra-passes/src/classifier.rs:28`, `:17`) — `intentional` single-width boundary (heuristic, not a soundness gate; unreachable given 2^num_vars dense tables). Make the cap explicit with a `debug_assert` + documented invariant rather than the silent `else { 0 }`.

**Quality nits with no real perf impact (n is hard-bounded):**
- [ ] `build_coefficient_candidates` dedups with linear `Vec::contains` per push (`crates/cobra-passes/src/pattern_matcher.rs:685`) — but `sig.len()` is fixed at 4 (only `num_vars == 2` caller). Use `sort_unstable`+`dedup` for intent.
- [ ] Integer pow via `(0..n).fold(1, |a,_| a*base)` is unchecked at `multivar_poly_recovery.rs:111`/`:130` (`base` up to 256, `k` loosely bounded → can overflow `usize`); use `checked_pow` and bail to `Inapplicable`. (`:281` is overflow-safe — cosmetic only.)
- [ ] `match_5var_boolean` (`pattern_matcher.rs:490`) and `match_6var_boolean` (`:533`) are verbatim Shannon-decomposition steps differing only in split-var index, cofactor width, and recursion target — extract a generic `shannon_step`.
- [ ] `SignatureVector` (`crates/cobra-core/src/signature_vector.rs:5`) is dead speculative API: zero production callers (only `lib.rs:65` re-export + its own tests), redundant `from_values` masking (`:47`), constant `is_empty` (`:43`). Delete or trim.
- [ ] `layer2` scans all 5 `ALL_GATES` (re-filtering via `gate_invertible`) twice instead of iterating `[Xor, Add]` directly (`crates/cobra-passes/src/template_decomposer.rs:553-589`). Replace the iterand only — do **not** merge the two loops (the per-loop early-return reorders results).

---

## Suggested prioritization

Ordered by verified severity. No `critical` items found; the single `high` is a maintainability hazard with a latent silent-wrong-proof failure mode, not a current miscompile.

**High**
1. [ ] **`lean_emit` ↔ `lean_cert` matcher duplication** (`lean_emit.rs:284-454` ↔ `lean_cert.rs:532-663`/`833-859`). Two copies of 12 structural matchers that must stay behaviorally identical or proofs get wrong arguments; they have already begun to drift. Hoist to one shared submodule.

**Medium**
2. [ ] **Scheduler attempt-cache fingerprint width mismatch** (`crates/cobra-orchestrator/src/scheduler.rs:199` keys at hard-coded `64` while `main_loop.rs:216` records at `ctx.bitwidth`; cache is keyed on the whole `StateFingerprint` incl. `bitwidth`, `work_item.rs:158`). For any `ctx.bitwidth != 64` the global cross-item dedup is silently a no-op. **This is the one genuine behavior bug** (wasted re-attempts, *not* incorrect output — per-item `attempted_mask` still works). Fix: thread `ctx.bitwidth` into `select_next_pass`.
3. [ ] **Lean cert off-64 silent downgrade to Unverified** (`main_loop.rs:408-414`, `verify_candidate.rs:134-146`, `resolve_competition.rs:387-398`). `intentional` but unsurfaced; fails closed (sound). Make the 64-only boundary explicit with a comment/`debug_assert` so the downgrade isn't incidental.
4. [ ] Math/helper duplications: `mod_inverse_odd_half` (`coefficient_splitter.rs:31`), precision-band ×3 (`poly.rs:72`/`poly_normalizer.rs:21`/`multivar_poly_recovery.rs:163`), `factorial_to_monomial` Stirling (`singleton_power_expr_builder.rs:38`), `solve_2adic_fixed` (`weighted_poly_fit.rs:219`). These carry lock-step-drift risk in subtle modular arithmetic.

**Low**
5. [ ] **Document the single-width IR contract** (`expr.rs:14`, `arith.rs:1`) — converts the headline mixed-width boundary from an unstated invariant into an explicit, defensible one. Cheap, high clarity value.
6. [ ] Delete the four warning-suppression dead-code stubs (`atom_simplifier.rs:31`/`:388`, `aux_var.rs:52`/`:232`, `build_signature_state.rs:166-170`, `residual_common.rs:112-117`).
7. [ ] Consolidate the evaluator family + `bitmask`/`collect_vars`/`remap` helper duplications and the residual-pass / compose-pass skeletons (all `low` severity, no behavioral change).
8. [ ] The remaining simplification nits (redundant clones, no-op `& mask`/`.take()`, dead branches, `enumerate()`/`let _ =` removals) — batchable, behavior-preserving.
