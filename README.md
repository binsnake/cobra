# Rust port of COBRA

Original project: https://github.com/trailofbits/CoBRA

All credits to kyle-elliot-tob and Trail of Bits.

## Lean Verification Status

This repository now contains a Lean verification layer for part of the Cobra simplification pipeline. It is useful and actively wired into tests/CI, but it is not a complete formal verification of every Cobra pass.

Primary verification files:

- `formal/lean/Cobra/Core.lean`: Lean expression semantics and theorem pack.
- `crates/cobra-verify/src/lean_cert.rs`: Rust certificate model and theorem recognizer.
- `crates/cobra-verify/src/lean_emit.rs`: generated Lean emitter.
- `crates/cobra-passes/tests/generated_lean_replay.rs`: generated-proof replay tests.
- `crates/cobra-passes/src/proof_coverage.rs`: proof coverage registry and drift guards.
- `.github/workflows/verification.yml`: CI verification workflow.

The generated Lean replay suite currently lists 89 tests.

## Formally Checked With Lean

The current Lean layer checks:

- Cobra expression evaluation semantics for the supported expression language.
- Named 64-bit bit-vector rewrite theorems exported from `formal/lean/Cobra/Core.lean`.
- Theorem-backed local rewrite certificates emitted by Rust.
- Context-preserving rewrite-step chains, where a local theorem is applied inside an expression context.
- Generated endpoint certificates, including fallback endpoint proofs replayed through Lean.
- Generated finite Boolean-signature certificates.
- Representative generated pass outputs across cleanup, atom rewrites, XOR lowering, pattern matching, seed rewriting, semilinear flows, residual recomposition, bitwise/hybrid recomposition, lifted substitution, direct extractor families, signature solver families, and candidate verification.
- Proof coverage registry invariants that require registered passes and internal proof targets to declare replay evidence.

Examples of theorem-backed simplifications now covered include:

- `x ^ y = x + y - 2 * (x & y)`
- `(x & y) + (x | y) = x + y`
- `2 * (x & y) + 2 * (x | y) = 2 * x + 2 * y`
- `3 & 1 = 1`
- `~(~x | ~y) = x & y`
- `~(~x & ~y) = x | y`
- common identities such as add-zero, mul-one, xor-zero, double-not, De Morgan, and mask identities

## What Is Not Fully Verified Yet

Do not treat this repository as fully verified.

Remaining gaps include:

- Some production paths still use endpoint `bv_decide` fallback certificates instead of named theorem chains.
- `CoveredByDownstreamCertificate` entries mean the local transition is not directly proven; later accepted candidates must carry fresh evidence.
- Finite Boolean-signature certificates prove truth-table agreement on Boolean inputs, not unrestricted full-width bit-vector equivalence.
- Cleanup helper algorithms are covered by representative replay cases, but not yet by a complete generated trace proof for every helper rewrite.
- Recomposition paths still need explicit contracts for residual recombine, bitwise compose, hybrid compose, lifted substitution, operand joins, and product joins.
- Variable remapping/support-reduction logic still needs direct formal contracts.
- Competition and public acceptance boundaries are hardened by Rust checks and replay cases, but still need a small formal acceptance model.
- The replay suite is broad but curated; a systematic certificate generator for all pass traces is still needed.

See `formal/lean/HANDOFF.md` for the detailed handoff, verified surface, remaining work, and last known gates.

## Useful Verification Commands

```powershell
cargo fmt --all -- --check
cargo check --workspace --all-targets
cargo test -p cobra-passes proof_coverage -- --nocapture
cargo test -p cobra-passes --test generated_lean_replay -- --nocapture
$env:COBRA_LEAN_REPLAY='1'; cargo test -p cobra-passes --test generated_lean_replay -- --nocapture
Push-Location formal/lean; lake build; Pop-Location
rg -n "\b(sorry|admit)\b" formal/lean -g "*.lean" crates -g "*.rs"
```

Do not run generated Lean replay and standalone `lake build` concurrently. Clean `formal/lean/.lake` afterward if avoiding local artifact churn.
