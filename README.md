# CoBRA

[![CI](https://github.com/binsnake/cobra/actions/workflows/verification.yml/badge.svg)](https://github.com/binsnake/cobra/actions/workflows/verification.yml)
[![crates.io](https://img.shields.io/crates/v/cobra-mba.svg)](https://crates.io/crates/cobra-mba)
[![docs.rs](https://docs.rs/cobra-mba/badge.svg)](https://docs.rs/cobra-mba)

CoBRA is a Rust simplifier for mixed Boolean-arithmetic (MBA) expressions. It is
a port of [Trail of Bits' CoBRA](https://github.com/trailofbits/CoBRA), with a
worklist-driven simplification pipeline and a Lean verification layer for
selected rewrites.

The project provides:

- one `cobra-mba` Cargo package, imported as `cobra`;
- the `cobra-cli` and `cobra-sweep` command-line programs from that package;
- static and dynamic Rust library outputs for fast consumer rebuilds.

The minimum supported Rust version is 1.88.

## Library

The crates.io package is named `cobra-mba` because the `cobra` package name is
owned by an unrelated project. Rename the dependency to keep the natural Rust
crate name:

```toml
[dependencies]
cobra = { package = "cobra-mba", version = "0.1" }
```

```rust
use cobra::{parse_to_ast, render, simplify_expr, Options};

fn main() -> cobra::Result<()> {
    let parsed = parse_to_ast("(x ^ y) + 2 * (x & y)", 64)?;
    let outcome = simplify_expr(&parsed.expr, &parsed.vars, Options::default())?;
    let simplified = outcome.expr.as_deref().unwrap_or(&parsed.expr);

    println!("{}", render(simplified, &parsed.vars, 64));
    Ok(())
}
```

The package emits both an `rlib` and a Rust `dylib`. Rust selects the `rlib`
by default, so normal builds retain static linkage.

## Dynamic linking

During iterative development, ask rustc to prefer the package's dynamic output.
Consumer-only changes then have substantially less CoBRA code to relink:

```powershell
# Run this in the consumer project, using its binary name.
$env:RUSTFLAGS='-C prefer-dynamic'
cargo run --bin your-consumer-bin
```

For a persistent consumer-project setting, add this to `.cargo/config.toml`:

```toml
[build]
rustflags = ["-C", "prefer-dynamic"]
```

On Windows this uses `cobra.dll`; Linux and macOS use `libcobra.so` or
`libcobra.dylib`. `cargo run` and `cargo test` configure their runtime search
paths. The flag applies to the whole build, so Rust's dynamically linked
standard library may also be used.

This is a Rust `dylib`, not a C-compatible `cdylib`:

- it does not expose a stable C ABI;
- it must be built with the same Rust toolchain as the consumer;
- the CoBRA dylib and the toolchain's dynamic Rust standard library must be on
  the runtime library search path when launching a binary directly;
- release/distribution builds should normally use the default static mode
  unless those runtime libraries are deliberately shipped with the product.

This repository exercises the mode with:

```powershell
cargo --config .cargo/dynamic.toml run --bin cobra-cli -- --mba "(x ^ y) + 2 * (x & y)"
```

## Upstream compatibility

The core compatibility target for this revision is upstream C++ v1.3.0
(`ccba252`), also validated against C++ checkout `f9dd212` (whose later changes
are documentation-only). The targeted v1.3 simplifier and math hot-path changes
are tracked with an in-process [Rust/C++ parity harness](tools/parity/README.md).
All 18 targeted cases match semantically. A wider 58-case corpus found one
input that the upstream C++ CLI rejects while Rust returns a
sampled-full-width-equivalent result, so literal every-input identity is not
claimed.

This is semantic parity for the core simplifier, not a claim of whole-repository
1:1 parity or identical rendered output. The Rust project has no LLVM plugin,
and its CLI observability, proof metadata, and foreign-function surface differ.
See the
[parity and performance report](docs/parity-and-performance-2026-07-17.md)
for exact commits, validation policy, results, and exclusions.

## Command line

Install or run the CLI:

```powershell
cargo install cobra-mba --bin cobra-cli
cobra-cli --mba "(x ^ y) + 2 * (x & y)"
```

Useful flags include `--bitwidth`, `--max-vars`, `--verbose`, and `--verify`.
The `--verify` flag uses Z3 only when the CLI was built with its `z3` feature.
For a local build:

```powershell
cargo build --release --bin cobra-cli --features z3
.\target\release\cobra-cli.exe --mba "(x ^ y) + 2 * (x & y)" --verify
```

To install that variant, use
`cargo install cobra-mba --bin cobra-cli --features z3`. The Z3 library must be
available to the linker.

## Verification status

The Lean layer is active in tests and CI, but it does not formally verify every
CoBRA pass. It currently checks expression semantics, named 64-bit bit-vector
rewrites, theorem-backed local rewrite certificates, context-preserving
rewrite chains, generated endpoint certificates, finite Boolean signatures,
and representative outputs across the major pass families.

Important remaining limits:

- some paths use endpoint `bv_decide` fallback certificates;
- downstream-certificate coverage is not a local transition proof;
- finite Boolean signatures cover Boolean inputs, not unrestricted full-width
  bit-vector equivalence;
- several recomposition and variable-remapping paths still need direct formal
  contracts;
- the replay suite is broad but curated rather than exhaustive.

See the
[Lean verification handoff](https://github.com/binsnake/cobra/blob/main/formal/lean/HANDOFF.md)
for the detailed verified surface and remaining work.

## Development

The main checks are:

```powershell
cargo fmt --all -- --check
cargo clippy --all-targets -- -D warnings
cargo test
cargo --config .cargo/dynamic.toml run --bin cobra-cli -- --mba "x"
```

Lean verification:

```powershell
cargo test proof_coverage -- --nocapture
cargo test --test generated_lean_replay -- --nocapture
$env:COBRA_LEAN_REPLAY='1'; cargo test --test generated_lean_replay -- --nocapture
Push-Location formal/lean; lake build; Pop-Location
rg -n "\b(sorry|admit)\b" formal/lean -g "*.lean" crates -g "*.rs"
```

Do not run generated Lean replay and standalone `lake build` concurrently.
Clean `formal/lean/.lake` afterward if avoiding local artifact churn.

Release maintainers should follow [RELEASING.md](RELEASING.md). Tagged releases
publish the single Cargo package and attach checksummed static CLI archives to
GitHub.

## License and attribution

Licensed under Apache-2.0. CoBRA was originally developed by Kyle Elliott and
Trail of Bits; see the upstream project linked above.
