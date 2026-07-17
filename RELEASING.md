# Releasing CoBRA

Releases are driven by version tags. A successful `v<version>` workflow:

1. validates the tag, manifest, changelog, formatting, Clippy, tests, dynamic
   linking, and the Cargo package;
2. builds static CLI archives for Windows, Linux, and macOS;
3. publishes the single `cobra-mba` package to crates.io;
4. creates a GitHub release with the archives and `SHA256SUMS`.

The GitHub release is not created unless crates.io publication and every
platform build succeed.

## One-time GitHub setup

1. Generate a crates.io API token for the maintainer account that will own and
   publish `cobra-mba`. Use the narrowest publishing permissions that can
   create the initial package.
2. In the GitHub repository, create an environment named `release`.
3. Add `CARGO_REGISTRY_TOKEN` as an environment secret.
4. Recommended: require a reviewer for the `release` environment and restrict
   deployments to protected version tags.

Never commit or print the token. The workflow supplies it only to the publish
step.

Trusted publishing is the preferred long-term configuration because it uses a
short-lived OIDC token instead of a stored secret. crates.io requires the
package's first version to exist before a trusted publisher can be configured.
After the initial release:

1. configure a trusted publisher for `cobra-mba`, matching repository
   `binsnake/cobra`, workflow `release.yml`, and environment `release`;
2. replace `CARGO_REGISTRY_TOKEN` with `rust-lang/crates-io-auth-action`;
3. grant `id-token: write` only to the `crates-io` job;
4. remove the long-lived GitHub secret.

See the official
[crates.io trusted publishing documentation](https://crates.io/docs/trusted-publishing).

## Preparing a version

1. Update `package.version` in the root `Cargo.toml`.
2. Move changelog entries from `Unreleased` into a dated version section.
3. Update public dependency examples when the displayed minor version changes.
4. Run:

   ```powershell
   python tools/release.py check
   cargo fmt --all -- --check
   cargo clippy --all-targets -- -D warnings
   cargo test --locked
   cargo --config .cargo/dynamic.toml run --bin cobra-cli --locked -- --mba "x"
   cargo build --bin cobra-cli --release --locked
   cargo package --locked
   ```

5. Run the Lean gates documented in `README.md`.
6. Commit the release preparation and merge it to the release branch.

The release checker enforces the one-package publish set and rejects an
unexpected workspace member, registry changes, a missing changelog section, an
invalid tag, a tag/version mismatch, or a dirty release checkout.

## Publishing

From a clean release commit:

```powershell
python tools/release.py check --tag v0.1.0 --require-clean
git tag -s v0.1.0 -m "CoBRA 0.1.0"
git push origin v0.1.0
```

Pushing the tag starts `.github/workflows/release.yml`. Do not publish the
package manually at the same time.

## Recovery

crates.io versions are immutable.

- If the publish job is rerun after an upload, the release script detects and
  skips the existing version.
- If a published version is defective, yank it and release a fixed patch
  version. Never reuse or move the release tag.
- If only a platform build fails, fix the build and create a patch release.

## Dynamic-linking compatibility

`cobra-mba` emits a Rust `dylib`, not a stable-ABI distribution artifact. Do
not attach it to GitHub releases by itself. Consumers build it with their own
pinned Rust toolchain and select it with `-C prefer-dynamic`. Static linkage
remains the binary release default.
