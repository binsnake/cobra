# Cobra Lean Verification Handoff

Status: stopped by user request, not complete.

This handoff records the current formal-verification state and the remaining work needed to reach full pass parity. Be conservative: a pass or transformation is not fully verified unless the actual emitted transformation path has Lean-checkable evidence tied to its real source and output.

Implementation work was stopped at the user's request. Do not infer completion from this document.

## Current State

The repo now has a Lean verification layer for Cobra expression semantics, theorem-backed local rewrites, generated endpoint certificates, finite Boolean-signature certificates, proof coverage drift checks, and CI wiring.

Primary files:

- `formal/lean/Cobra/Core.lean`: Lean expression semantics and theorem pack.
- `crates/cobra-verify/src/lean_cert.rs`: certificate data model and local theorem recognizer.
- `crates/cobra-verify/src/lean_emit.rs`: generated Lean emitter.
- `crates/cobra-passes/tests/generated_lean_replay.rs`: replay harness for generated Lean from real pass outputs.
- `crates/cobra-passes/src/proof_coverage.rs`: pass and internal proof coverage registry.
- `.github/workflows/verification.yml`: CI entry point for verification gates.

The generated replay harness has 89 tests listed in the current tree. With `COBRA_LEAN_REPLAY=1`, replay tests write Lean and run `lake env lean`; without it, they still check metadata, endpoint matching, chain continuity, theorem naming, and coverage invariants.

## What Is Actually Verified

The strongest current evidence is:

- Lean theorem exports replay through `lean_theorem_exports_replays_in_lean`.
- Recognized 64-bit local rewrites replay through `local_rewrite_theorem_matrix_replays_in_lean`.
- The emitter can generate Lean for endpoint certificates, context-frame step chains, and finite Boolean-signature certificates.
- The replay suite includes representative pass outputs across cleanup, atom rewrites, XOR lowering, pattern matching, seed rewriting, semilinear flows, residual recomposition, bitwise/hybrid recomposition, lifted substitution, direct extractor families, signature solver families, and candidate verification.
- Proof coverage tests require every registered pass to have an explicit proof-coverage classification and replay evidence when marked Lean-checked.
- CI is wired to run formatting, workspace checks/tests, proof coverage, Lean build, generated Lean replay, and placeholder scans.

## Recent Additions

- Theorem-backed step-chain emission now avoids `try bv_decide` for recognized local rewrite steps.
- `mul_add_64`, `add_mul_64`, and `two_mul_and_or_sum_eq_two_mul_add_64` exist in Lean and are exported through `LeanTheorem`.
- The pattern matcher scaled sum case is theorem-backed with `TwoMulAndOrSumEqTwoMulAdd64`.
- The pattern matcher De Morgan table case `~(~x | ~y) -> x & y` is theorem-backed with `DemorganNotOrNotNot64`.
- The pattern matcher dual De Morgan table case `~(~x & ~y) -> x | y` is theorem-backed with `DemorganNotAndNotNot64`.
- `const_3_and_1_64` and `LeanTheorem::Const3And1_64` exist, are registered as a recognized local rewrite theorem, and are exercised by the atom simplifier constant-fold replay for `3 & 1 -> 1`.
- Xor lowering and seed production fallbacks were narrowed so they attach endpoint evidence only when theorem-chain reconstruction succeeds.
- Candidate acceptance was hardened so endpoint-only evidence must match the candidate source signature.
- Public-output proof preservation now composes a pass endpoint certificate with final public cleanup evidence when applicable.
- Product-shadow repair is documented/tested as not generally semantics-preserving; the guarded ANF route has replay evidence.

## Current Known Gap

The exact atom simplifier case `3 & 1 -> 1` and the pattern matcher De Morgan table cases `~(~x | ~y) -> x & y` / `~(~x & ~y) -> x | y` are now theorem-backed. `atom_simplifier.rs` and `pattern_matcher.rs` still have residual production fallbacks for rewrites that cannot be assembled as named theorem chains. Those fallbacks are Lean-replayed via endpoint `bv_decide`; this is useful bounded evidence, but it is not yet the desired named-proof architecture for all simplifications.

## Stop-State Summary

What Lean can currently prove or replay:

- The Lean theorem pack exports the named bit-vector identities referenced by Rust certificates.
- Recognized local 64-bit rewrites replay as theorem-backed step chains.
- Generated endpoint certificates replay in Lean, including context-plugged local theorem steps.
- Generated finite Boolean-signature certificates replay in Lean.
- Representative real pass outputs replay for all registered Lean-checked pass families and internal targets listed in `proof_coverage.rs`.
- Drift guards fail if a registered pass lacks proof coverage, if replay evidence is missing, if endpoint fallback constructor counts change without inventory updates, or if generated replay tests are not linked from proof coverage.

What is not proven:

- The full implementation of every pass algorithm.
- Every possible output of pattern/table synthesis.
- Every cleanup helper rewrite as a generated step trace.
- The full-width semantic bridge from finite Boolean signatures to unrestricted bit-vector equivalence.
- The recomposition, variable-remapping, and acceptance-boundary contracts as standalone Lean theorems.
- Absence of all production endpoint fallbacks.

Current replay count: 89 generated replay tests.

## Last Observed Gates

Before this handoff, these gates were reported passing in the prior sweep:

- `cargo fmt --all -- --check`
- `cargo check --workspace --all-targets`
- focused orchestrator proof-level and competition tests
- `cargo test -p cobra-passes proof_coverage -- --nocapture`
- `cargo test -p cobra-passes --test generated_lean_replay -- --nocapture`
- `COBRA_LEAN_REPLAY=1 cargo test -p cobra-passes --test generated_lean_replay -- --nocapture`
- `lake build` from `formal/lean`
- placeholder scan for `sorry`/`admit`

After wiring `Const3And1_64` into the atom simplifier path, these additional focused gates passed:

- `cargo test -p cobra-verify lean_cert -- --nocapture`
- `cargo test -p cobra-verify lean_emit -- --nocapture`
- `cargo test -p cobra-passes certified_atom_simplify_uses_theorem_for_constant_folding -- --nocapture`
- `cargo test -p cobra-passes --test generated_lean_replay local_rewrite_theorem_matrix_replays_in_lean -- --nocapture`
- `COBRA_LEAN_REPLAY=1 cargo test -p cobra-passes --test generated_lean_replay atom_simplifier_constant_fold_generated_certificate_replays_in_lean -- --nocapture`
- `COBRA_LEAN_REPLAY=1 cargo test -p cobra-passes --test generated_lean_replay local_rewrite_theorem_matrix_replays_in_lean -- --nocapture`
- `cargo test -p cobra-passes --test generated_lean_replay lean_theorem_exports_replays_in_lean -- --nocapture`
- `cargo test -p cobra-passes proof_coverage -- --nocapture`
- `cargo fmt --all -- --check`

After wiring `DemorganNotOrNotNot64` into the pattern matcher path, these additional focused gates passed:

- `cargo test -p cobra-verify lean_cert -- --nocapture`
- `cargo test -p cobra-verify lean_emit -- --nocapture`
- `cargo test -p cobra-passes --test generated_lean_replay pattern_matcher_demorgan_table_theorem_replays_in_lean -- --nocapture`
- `COBRA_LEAN_REPLAY=1 cargo test -p cobra-passes --test generated_lean_replay pattern_matcher_demorgan_table_theorem_replays_in_lean -- --nocapture`
- `COBRA_LEAN_REPLAY=1 cargo test -p cobra-passes --test generated_lean_replay local_rewrite_theorem_matrix_replays_in_lean -- --nocapture`
- `cargo test -p cobra-passes --test generated_lean_replay lean_theorem_exports_replays_in_lean -- --nocapture`
- `cargo test -p cobra-passes proof_coverage -- --nocapture`
- `cargo fmt --all -- --check`
- `cargo check --workspace --all-targets`
- `lake build`
- placeholder scan for `sorry`/`admit` in Lean/Rust sources

After wiring `DemorganNotAndNotNot64` into the pattern matcher path, these additional focused gates passed:

- `cargo test -p cobra-verify lean_cert -- --nocapture`
- `cargo test -p cobra-verify lean_emit -- --nocapture`
- `cargo test -p cobra-passes --test generated_lean_replay pattern_matcher_demorgan_dual_table_theorem_replays_in_lean -- --nocapture`
- `COBRA_LEAN_REPLAY=1 cargo test -p cobra-passes --test generated_lean_replay pattern_matcher_demorgan_dual_table_theorem_replays_in_lean -- --nocapture`
- `COBRA_LEAN_REPLAY=1 cargo test -p cobra-passes --test generated_lean_replay local_rewrite_theorem_matrix_replays_in_lean -- --nocapture`
- `cargo test -p cobra-passes --test generated_lean_replay lean_theorem_exports_replays_in_lean -- --nocapture`
- `cargo test -p cobra-passes proof_coverage -- --nocapture`
- `cargo fmt --all -- --check`
- `cargo check --workspace --all-targets`
- `lake build`
- placeholder scan for `sorry`/`admit` in Lean/Rust sources

Rerun the full gate set before committing.

`formal/lean/.lake` is currently absent.

## Worktree Notes

The worktree is dirty and includes important untracked verification files. Do not reset or revert unrelated changes.

Important untracked file:

- `crates/cobra-passes/tests/generated_lean_replay.rs`

This handoff file is also untracked unless it has been added by the next owner.

## Remaining Formalizations

1. Eliminate avoidable production endpoint fallbacks.

   Audit every production `LeanCertificate::new` use. Classify each as identity, named-theorem chain, solver-dispatched bounded certificate, or insufficient. Replace common nontrivial empty-step fallbacks with theorem-backed chains.

2. Continue atom simplifier theorem coverage.

   `Const3And1_64` is wired for `3 & 1 -> 1`. Continue replacing remaining residual atom simplifier endpoint fallbacks with named theorem chains, especially additional constant-folding and mixed bitwise identities used by real passes.

3. Formalize cleanup helpers as traces.

   `cleanup_final_expr` has representative replay coverage, but helper algorithms are not fully proven as algorithms. Add a cleanup trace generator that emits one Lean certificate step per rewrite for constant folding, negation refolding, common-factor extraction, flattening, and rebuilding.

4. Replace vague downstream coverage with explicit contracts.

   `CoveredByDownstreamCertificate` currently means the local state transition is not directly proven. Convert each one into either a semantic identity/routing theorem, an abstraction/refinement relation, or an explicitly untrusted search-state boundary with no semantic claim until final certificate.

5. Separate finite signature evidence from full bit-vector equivalence.

   `LeanSignatureCertificate` proves finite Boolean truth-table agreement. Audit every `VerificationState::Verified` assignment and public proof-level upgrade so signature-domain evidence is not silently treated as full-width endpoint equivalence.

6. Formalize recomposition contracts.

   Add Lean-checkable contracts for residual recombine, bitwise compose, hybrid compose, lifted substitute, operand join rewrite, and product join rewrite. Each contract should tie source expression/signature, child semantics, remapping/substitution, and recomposed candidate.

7. Formalize variable remapping and support reduction.

   Cover `try_build_var_support`, `remap_var_indices`, `verify_in_original_space`, and signature remapping in residual/decomposition flows. Target theorem: reduced-space evaluation agrees with original-space evaluation under the support map.

8. Formalize competition and public acceptance boundaries.

   Model the acceptance rule behind `submit_candidate`, `submit_normalized_candidate`, `group_has_verified_candidate`, `proof_backed_group_verification`, and `to_simplify_outcome`: verified public output must carry matching endpoint evidence, or be explicitly marked as signature-domain evidence.

9. Expand local theorem coverage.

   Continue adding named theorems until every simplification pattern used by passes has a replayed theorem: associativity/commutativity normalization, constant-folding identities, common-factor extraction variants, bitwise/arithmetic mixed identities, and polynomial reconstruction identities.

10. Build a systematic certificate generator.

   The replay suite is broad but curated. Add pass instrumentation that records semantic rewrite traces, converts them to endpoint or signature certificates, emits Lean for every pass family, and fails when a verified transformation lacks Lean-checkable evidence.

## Useful Commands

```powershell
rg -n "LeanCertificate::new\(|emit_bv_decide_certificate|try bv_decide|steps\.is_empty\(" crates formal
cargo test -p cobra-passes proof_coverage -- --nocapture
cargo test -p cobra-passes --test generated_lean_replay -- --nocapture
$env:COBRA_LEAN_REPLAY='1'; cargo test -p cobra-passes --test generated_lean_replay -- --nocapture
Push-Location formal/lean; lake build; Pop-Location
```

Do not run generated Lean replay and standalone `lake build` concurrently. Clean `formal/lean/.lake` afterward if avoiding local artifact churn.
