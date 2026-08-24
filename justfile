default: test

fmt:
    cargo fmt --all

fmt-check:
    cargo fmt --all -- --check

lint:
    cargo clippy --all-targets --features cli -- -D warnings

release-check:
    python tools/release.py check

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

# Mirrors CI: checks formatting instead of mutating files.
ci: fmt-check lint test
