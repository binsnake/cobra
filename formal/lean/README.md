# Cobra Lean Verification

This directory contains the first mechanically checked semantic layer for
CoBRA-rs. It is intentionally small: the Rust optimizer remains heuristic,
while Lean proves reusable expression identities that can become certificate
steps for accepted rewrites.

The project is pinned to Lean `4.29.1` because that toolchain is already
available through `elan` in the current environment.

Build:

```powershell
lake build
```

Current scope:

- Core `Expr` syntax matching `cobra_core::expr::Kind`.
- `BitVec` evaluation semantics for constants, variables, arithmetic,
  bitwise operators, negation, complement, and logical shift-right.
- A first theorem pack for 64-bit rewrite identities used by the Rust
  structural rewrite passes.
- A Lean stack-machine bytecode model plus `Expr.compile_sound`, proving
  that the Lean compiler emits programs whose evaluation matches `Expr.eval`.
- A certificate architecture with expression contexts, local rewrite lifting,
  and chain soundness. This is the intended target for generated certificates:
  a pass can prove or select a local theorem, describe the surrounding context,
  and chain the resulting semantic-equivalence steps.
- Rust-side generator helpers in `cobra-verify` can derive a Lean context from
  an expression path, emit Lean `Expr`/`Ctx` syntax, and identify theorem IDs
  for common local 64-bit rewrites used by the atom simplifier.
- `cobra-verify::emit_bv_decide_certificate` can also emit a complete
  fixed-width Lean theorem for a `LeanCertificate` endpoint pair. This is the
  conservative fallback path for complex generator-produced simplifications:
  Lean checks the final semantic equivalence directly with `bv_decide`, while
  any known local rewrite steps remain attached as certificate metadata.
- `Cobra.Signature` models Boolean truth-table inputs that do not have an
  original expression endpoint. `emit_constant_signature_certificate` can emit
  a Lean theorem proving that an all-constant signature is satisfied by the
  corresponding constant expression.
- `emit_signature_certificate` generalizes that path for finite truth tables:
  it emits a bounded assignment case split and lets Lean check each row against
  `Expr.eval`.
- Rust metadata keeps `LeanSignatureCertificate` separate from endpoint
  `LeanCertificate`. Signature-family solvers can attach Lean-checkable
  reduced truth-table evidence without upgrading public `ProofLevel` to
  `LeanCertified` unless an endpoint semantic-equivalence certificate also
  matches the original expression and final output.
- `crates/cobra-passes/src/proof_coverage.rs` is the registry-level drift
  guard for this layer. Every registered pass must declare whether it emits
  Lean endpoint evidence, emits Lean finite-signature evidence, preserves a
  matching certificate across competition, is covered by a downstream
  reconstruction/substitution certificate, or explicitly invalidates stale
  proof metadata at a non-simplifying analysis boundary.

The 64-bit theorem scope is deliberate. Lean's `bv_decide` discharges these
identities at fixed width; general `1..=64` proofs should be added with
width-parametric bit-level lemmas rather than assumed.
