# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.1.0] - 2026-07-17

### Added

- Initial public `cobra-mba` library and `cobra-cli`/`cobra-sweep` binaries in
  one Cargo package.
- Rust `rlib` and `dylib` outputs, selectable with `-C prefer-dynamic`.
- MBA parsing, simplification, diagnostics, and optional Z3 verification.
- Lean certificate generation, replay tests, and proof-coverage checks.

[Unreleased]: https://github.com/binsnake/cobra/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/binsnake/cobra/releases/tag/v0.1.0
