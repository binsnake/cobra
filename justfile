default: test

fmt:
    cargo fmt --all

fmt-check:
    cargo fmt --all -- --check

lint:
    cargo clippy --all-targets --features cli -- -D warnings

release-check:
    python tools/release.py check

# The Python binding is a separate Cargo package, so nothing forces its lock
# file to agree with the root one. This is what does.
check-locks:
    python tools/check_locks.py

test:
    cargo test --features cli

test-all:
    cargo test --all-features

test-dynamic:
    cargo --config .cargo/dynamic.toml run --bin cobra-cli --features cli -- --mba "x"

build:
    cargo build --features cli

build-release:
    cargo build --features cli --release

build-dynamic:
    cargo --config .cargo/dynamic.toml build --lib

clean:
    cargo clean

# Python bindings. They live in their own Cargo package under python/, so the
# root fmt, clippy, and test recipes do not reach them.
py-dev:
    cd python && uv run maturin develop --release --locked

py-test:
    cd python && uv run pytest

py-lint:
    cd python && cargo fmt -- --check
    cd python && cargo clippy --all-targets --locked -- -D warnings
    cd python && uv run mypy
    cd python && uv run python -m mypy.stubtest cobra_mba._native --ignore-disjoint-bases --ignore-positional-only

py-ci: py-dev py-lint py-test

# Mirrors CI: checks formatting instead of mutating files.
ci: fmt-check lint test check-locks
