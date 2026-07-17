default: test

fmt:
    cargo fmt --all

fmt-check:
    cargo fmt --all -- --check

lint:
    cargo clippy --all-targets -- -D warnings

release-check:
    python tools/release.py check

test:
    cargo test

test-all:
    cargo test --all-features

test-dynamic:
    cargo --config .cargo/dynamic.toml run --bin cobra-cli -- --mba "x"

build:
    cargo build

build-release:
    cargo build --release

build-dynamic:
    cargo --config .cargo/dynamic.toml build --lib

clean:
    cargo clean

# Mirrors CI: checks formatting instead of mutating files.
ci: fmt-check lint test
