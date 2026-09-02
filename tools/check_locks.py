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
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LOCKS = {
    "root": ROOT / "Cargo.lock",
    "python": ROOT / "python" / "Cargo.lock",
}


PACKAGE_HEADER = "[[package]]"


class ReleaseFormatError(RuntimeError):
    """A lock file did not look the way this script expects."""


def quoted_value(line: str) -> str:
    return line.split("=", 1)[1].strip().strip('"')


def versions(path: Path) -> dict[str, set[str]]:
    """Read the name and version of every package in a lock file.

    Parsed line by line rather than with `tomllib`, which only joined the
    standard library in 3.11. This script runs under whichever interpreter is
    being tested, and the matrix includes 3.10.
    """
    resolved: dict[str, set[str]] = {}
    name: str | None = None
    in_package = False

    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line == PACKAGE_HEADER:
            in_package, name = True, None
        elif line.startswith("["):
            in_package, name = False, None
        elif in_package and line.startswith("name = "):
            name = quoted_value(line)
        elif in_package and name is not None and line.startswith("version = "):
            resolved.setdefault(name, set()).add(quoted_value(line))
            name = None

    if not resolved:
        raise ReleaseFormatError(
            f"found no packages in {path}; has the lock file format changed?"
        )
    return resolved


def main() -> int:
    missing = [str(path) for path in LOCKS.values() if not path.exists()]
    if missing:
        print(f"lock file not found: {', '.join(missing)}", file=sys.stderr)
        return 1

    try:
        root = versions(LOCKS["root"])
        python = versions(LOCKS["python"])
    except ReleaseFormatError as error:
        print(error, file=sys.stderr)
        return 1

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
