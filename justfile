default: test

fmt:
    cargo fmt --all

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

ci: fmt lint test
