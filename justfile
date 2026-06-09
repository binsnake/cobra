default: test

fmt:
    cargo fmt --all

fmt-check:
    cargo fmt --all -- --check

lint:
    cargo clippy --workspace --all-targets -- -D warnings

test:
    cargo test --workspace

test-all:
    cargo test --workspace --all-features

build:
    cargo build --workspace

build-release:
    cargo build --workspace --release

clean:
    cargo clean

# Mirrors CI: checks formatting instead of mutating files.
ci: fmt-check lint test
