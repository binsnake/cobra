# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.4.0] - 2026-09-02

### Added

- Python bindings, in `python/`: a `cobra-mba` PyPI package built on PyO3 and
  maturin, importable as `cobra_mba`. It exposes the parser, an immutable
  `Expr` tree with Python operators, the simplifier, its options, and the full
  diagnostic and telemetry bundle. Wheels target CPython 3.10 and newer through
  the stable ABI, so one wheel per platform serves every supported interpreter.
  The binding is a separate Cargo package with `publish = false`, so the
  crates.io publish set is unchanged.
- `cobra_mba.simplify_many`: simplifies a batch on a pool of worker threads,
  about four times faster than a Python loop on six cores. Results keep input
  order, and `on_error="none"` leaves `None` in place of an item that failed to
  parse rather than losing the batch.
- `Expr.evaluate_many`: evaluates one expression at many points in a single
  call, 7x faster than a Python loop with list columns and 25x with bytes in
  and out. Columns are sequences of integers or bytes holding little-endian
  64-bit values, which is the shape `numpy.ndarray.tobytes()` produces and
  `numpy.frombuffer` reads back. There is no zero-copy buffer path because
  Python only added the buffer protocol to its stable ABI in 3.11 and the
  wheels target 3.10.
- Example scripts under `python/examples/`: a batch corpus sweep and a bulk
  evaluation benchmark, both exercised by the test suite, plus IDAPython and
  Binary Ninja templates that translate decompiler output into the
  simplifier's syntax.
- `outcome_expr_in_original_space`: maps a finished `SimplifyOutcome`'s
  expression back into the caller's variable namespace. A result that dropped
  variables is indexed against `real_vars`, so rendering it against the
  caller's table without this step prints the wrong names. `cobra-cli` and the
  Python bindings now share this one helper, and a parity suite compares their
  rendered output byte for byte.
- `tools/check_locks.py`, run in CI: the Python binding has its own
  `Cargo.lock`, and this fails the build if any crate common to both locks
  resolves to a different version. The exact `ahash` pin exists so fixed-seed
  hashing matches across builds, and a binding that drifted from it would
  produce different signatures from the same input.

## [0.3.0] - 2026-08-24

### Added

- Width-generic Lean theorem pack. Every rewrite the certificate machinery
  recognizes now has a `_w` counterpart proved at an arbitrary `BitVec w`, so
  certificates exist at every bitwidth in `1..=64`, not just 64. The bitwise
  and ring identities are proved directly; the arithmetic MBA family
  (`xor_eq_add_sub_two_mul_and` and relatives) is derived from a single carry
  identity, `(a &&& b) + (a ||| b) = a + b`, proved by induction on binary
  digits — no decision procedure, which is what makes it width-generic.
- Mixed-width Lean layer (`formal/lean/Cobra/Mixed.lean`): an `MExpr` model
  mirroring the full expression `Kind` (casts and `Concat` included) with an
  evaluator matching the compiled Rust evaluator arm for arm, width-generic
  cast-rewrite theorems, and a context-congruence theorem. Certificates can
  now be issued and replayed for cast-bearing (non-uniform-width) trees.
- A proved carry bridge (`ofExpr`, `evalW_ofExpr`, `semEqW_of_semEq`) embedding
  the uniform `BitVec w` world into the mixed evaluator, so a mixed-chain step
  on a cast-free redex cites the named uniform theorem rather than falling back
  to a decision procedure.
- `try_compile` and `Evaluator::try_from_expr`: fallible compilation that
  rejects trees whose node widths do not validate, instead of silently
  producing a program that evaluates to zero everywhere.
- `Options::require_lean_certificate` (default `true`): when set, a
  simplification is discarded unless a replayable certificate covers its exact
  output. Turning it off accepts probe-only assurance and raises the
  simplification rate on non-adversarial input.

### Fixed

- Closed a soundness hole in the eval-side acceptance gate: probe derivation
  now includes the original's constants and their pairwise products, catching
  trap candidates that differ from the original only at an unprobed point, and
  no longer truncates away high-magnitude probes.
- Corrected cast width validation and Z3 cast lowering (narrowing casts were
  silently no-ops), unified three tree-walking evaluators onto the compiled
  evaluator so casts use one width model, and replaced a degenerate `ValMap`
  identity key that made the all-ones atom invisible.
- Balanced competition-handle accounting across clone, fan-out, and resolve;
  revalidated stale mask pairings; made `AtomId` assignment deterministic;
  stopped counting associative chains against the expression-depth budget (the
  sole dataset error case now completes).
- Added absorption, complement, and constant-reassociation rewrites with their
  Lean theorems, so `x & (x | y)`, `x & ~x`, `(a | b) & a` and similar simplify
  with a replayable certificate.

### Changed

- Certificate generation is no longer gated to 64-bit: multi-step certified
  chains are produced at every width.
- The `require_lean_certificate` gate replaces the previous unconditional
  discard of uncertified rewrites; see **Added**.

### Performance

- Batch throughput for repeated `simplify_expr` calls improved ~25% on trivial
  input via identity fast paths (equal-endpoint certificates, skipped probing
  of unchanged candidates), a candidate-normalization memo, and per-bitwidth
  caching of the singleton-recovery degree table.
- Cut redundant work in the pipeline: deferred phase-2 verification past its
  loop nest, dropped a whole-tree replay re-scan, carried a width stack through
  `compile`, capped the inner-composition table, and collapsed a redundant
  interpolation-table dimension.


## [0.2.0] - 2026-08-24

### Fixed

- `full_width_check_eval` now derives its probe points from the original's
  constants as well as the candidate's. It previously passed `None` for the
  original, so a candidate differing from the original only at a constant that
  appears solely in the original was accepted. Three rewrite sites use this
  check as their only acceptance gate. The original's constants are recovered
  from its compiled program via the new
  `Evaluator::collect_constants_and_shifts`.

### Changed

- `clap` is now an optional dependency behind the new `cli` feature, which is
  off by default. The library's default dependency graph no longer contains
  `clap`, `clap_derive`, or their transitive crates.
- The `cobra-cli` and `cobra-sweep` binaries declare
  `required-features = ["cli"]`. Building, testing, or installing them now needs
  `--features cli`, for example
  `cargo install cobra-mba --bin cobra-cli --features cli`.

## [0.1.0] - 2026-07-19

### Added

- Initial public `cobra-mba` library and `cobra-cli`/`cobra-sweep` binaries in
  one Cargo package.
- Rust `rlib` and `dylib` outputs, selectable with `-C prefer-dynamic`.
- MBA parsing, simplification, diagnostics, and optional Z3 verification.
- Lean certificate generation, replay tests, and proof-coverage checks.
- In-process Rust/C++ semantic-parity and stage-timing harness with exhaustive
  Boolean signatures, deterministic full-width probes, and reproducible
  comparison manifests.
- C++ v1.3 compatibility and performance report with exact baselines,
  validation policy, and explicit whole-product exclusions.

### Changed

- Synchronized the targeted core simplifier changes from upstream C++ v1.3,
  including inclusion-exclusion recovery, XOR self-cancellation,
  target-derived template constants, the single-product guard, and the global
  output-cost gate.
- Aligned polynomial and signature hot paths with v1.3: stronger modular-inverse
  seeding, block Möbius interpolation, incremental grid reuse, and odd-factorial
  precomputation.
- Made masked-atom reconstruction order deterministic across randomized map
  layouts.
- Clarified the supported core-parity scope and the dynamic-linking and Z3 CLI
  commands in the README.

### Fixed

- Kept full-width-live variables during auxiliary-variable elimination by
  aligning the deterministic 64-probe liveness check with upstream.
- Preserved the candidate signature and structured `CostRejected` diagnostic
  when the global size guard declines a pathological expansion.

[Unreleased]: https://github.com/binsnake/cobra/compare/v0.4.0...HEAD
[0.4.0]: https://github.com/binsnake/cobra/compare/v0.3.0...v0.4.0
[0.3.0]: https://github.com/binsnake/cobra/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/binsnake/cobra/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/binsnake/cobra/releases/tag/v0.1.0
