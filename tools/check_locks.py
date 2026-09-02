#!/usr/bin/env python3
"""Check that the root and Python lock files resolve shared crates the same way.

The Python binding is a separate Cargo package with its own `Cargo.lock`, so
nothing forces the two to agree. They have to: `ahash` is pinned exactly
because fixed-seed hashing must hash identically across builds, and a binding
that resolved a different `ahash` would produce different signatures from the
same input. This fails the build when any crate common to both locks resolves
to a different version.
"""

from __future__ import annotations

import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LOCKS = {
    "root": ROOT / "Cargo.lock",
    "python": ROOT / "python" / "Cargo.lock",
}


def versions(path: Path) -> dict[str, set[str]]:
    with path.open("rb") as handle:
        data = tomllib.load(handle)
    resolved: dict[str, set[str]] = {}
    for package in data.get("package", []):
        resolved.setdefault(package["name"], set()).add(package["version"])
    return resolved


def main() -> int:
    missing = [str(path) for path in LOCKS.values() if not path.exists()]
    if missing:
        print(f"lock file not found: {', '.join(missing)}", file=sys.stderr)
        return 1

    root = versions(LOCKS["root"])
    python = versions(LOCKS["python"])

    mismatches = sorted(
        (name, root[name], python[name])
        for name in root.keys() & python.keys()
        if root[name] != python[name]
    )

    if mismatches:
        print("Cargo.lock files disagree on shared crates:", file=sys.stderr)
        for name, in_root, in_python in mismatches:
            root_versions = ", ".join(sorted(in_root))
            python_versions = ", ".join(sorted(in_python))
            print(
                f"  {name}: root has {root_versions}, python has {python_versions}",
                file=sys.stderr,
            )
        print(
            "\nRun `cargo update --workspace` in python/ to re-resolve, or pin "
            "the crate in both manifests.",
            file=sys.stderr,
        )
        return 1

    shared = len(root.keys() & python.keys())
    print(f"both lock files agree on all {shared} shared crates")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
