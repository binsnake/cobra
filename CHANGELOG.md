# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

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

[Unreleased]: https://github.com/binsnake/cobra/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/binsnake/cobra/releases/tag/v0.1.0
