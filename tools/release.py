#!/usr/bin/env python3
"""Validate and publish the single CoBRA Cargo package."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tomllib
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PACKAGE_NAME = "cobra-mba"
SEMVER_TAG = re.compile(
    r"^v(?P<version>(?:0|[1-9]\d*)\.(?:0|[1-9]\d*)\.(?:0|[1-9]\d*)"
    r"(?:-[0-9A-Za-z.-]+)?(?:\+[0-9A-Za-z.-]+)?)$"
)
USER_AGENT = "cobra-release-publisher/0.1 (https://github.com/binsnake/cobra)"


class ReleaseError(RuntimeError):
    """A release invariant failed."""


def run(
    args: list[str],
    *,
    check: bool = True,
    capture_output: bool = False,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=ROOT,
        check=check,
        capture_output=capture_output,
        text=True,
    )


def cargo_metadata() -> dict[str, Any]:
    result = run(
        ["cargo", "metadata", "--format-version", "1", "--no-deps"],
        capture_output=True,
    )
    return json.loads(result.stdout)


def package_version() -> str:
    with (ROOT / "Cargo.toml").open("rb") as manifest:
        package = tomllib.load(manifest)["package"]
    if package["name"] != PACKAGE_NAME:
        raise ReleaseError(
            f"root package is {package['name']!r}, expected {PACKAGE_NAME!r}"
        )
    return package["version"]


def check_tag(tag: str, version: str) -> None:
    match = SEMVER_TAG.fullmatch(tag)
    if match is None:
        raise ReleaseError(
            f"release tag {tag!r} is invalid; expected v<major>.<minor>.<patch>"
        )
    if match.group("version") != version:
        raise ReleaseError(
            f"tag {tag!r} does not match package version {version!r}"
        )


def check_clean_tree() -> None:
    result = run(
        ["git", "status", "--porcelain", "--untracked-files=normal"],
        capture_output=True,
    )
    if result.stdout.strip():
        raise ReleaseError("release checkout is not clean:\n" + result.stdout.rstrip())


def validate(tag: str | None, require_clean: bool) -> str:
    metadata = cargo_metadata()
    version = package_version()
    packages = metadata["packages"]

    if len(packages) != 1 or packages[0]["name"] != PACKAGE_NAME:
        names = [package["name"] for package in packages]
        raise ReleaseError(
            f"release must contain exactly one Cargo package ({PACKAGE_NAME}); found {names}"
        )

    package = packages[0]
    if package["version"] != version:
        raise ReleaseError(
            f"Cargo metadata version {package['version']} does not match {version}"
        )
    if package["publish"] != ["crates-io"]:
        raise ReleaseError('package.publish must be ["crates-io"]')

    changelog = (ROOT / "CHANGELOG.md").read_text(encoding="utf-8")
    version_heading = (
        rf"^## \[{re.escape(version)}\](?: - \d{{4}}-\d{{2}}-\d{{2}})?$"
    )
    if re.search(version_heading, changelog, re.MULTILINE) is None:
        raise ReleaseError(f"CHANGELOG.md has no section for {version}")

    if tag is not None:
        check_tag(tag, version)
    if require_clean:
        check_clean_tree()

    print(f"release metadata is consistent for {PACKAGE_NAME} {version}")
    print("publish set: cobra-mba (one package)")
    return version


def crates_io_has_version(name: str, version: str) -> bool:
    quoted_name = urllib.parse.quote(name, safe="")
    quoted_version = urllib.parse.quote(version, safe="")
    request = urllib.request.Request(
        f"https://crates.io/api/v1/crates/{quoted_name}/{quoted_version}",
        headers={"User-Agent": USER_AGENT},
    )
    try:
        with urllib.request.urlopen(request, timeout=30):
            return True
    except urllib.error.HTTPError as error:
        if error.code == 404:
            return False
        raise ReleaseError(
            f"crates.io lookup for {name} {version} failed with HTTP {error.code}"
        ) from error
    except urllib.error.URLError as error:
        raise ReleaseError(
            f"crates.io lookup for {name} {version} failed: {error.reason}"
        ) from error


def publish(tag: str) -> None:
    version = validate(tag, require_clean=True)
    if not os.environ.get("CARGO_REGISTRY_TOKEN"):
        raise ReleaseError("CARGO_REGISTRY_TOKEN is not set")
    if crates_io_has_version(PACKAGE_NAME, version):
        print(f"skipping {PACKAGE_NAME} {version}: already published")
        return

    print(f"publishing {PACKAGE_NAME} {version}")
    result = run(
        [
            "cargo",
            "publish",
            "--package",
            PACKAGE_NAME,
            "--locked",
            "--registry",
            "crates-io",
        ],
        check=False,
    )
    if result.returncode != 0:
        # Cargo can fail while polling after a successful upload. A visible
        # immutable version means the release is complete and rerunnable.
        if crates_io_has_version(PACKAGE_NAME, version):
            print(f"{PACKAGE_NAME} {version} was uploaded despite Cargo's exit status")
            return
        raise ReleaseError(
            f"cargo publish failed for {PACKAGE_NAME} with exit code {result.returncode}"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    check_parser = subparsers.add_parser("check", help="validate release metadata")
    check_parser.add_argument("--tag", help="release tag to validate")
    check_parser.add_argument(
        "--require-clean",
        action="store_true",
        help="fail when the Git working tree is dirty",
    )

    publish_parser = subparsers.add_parser(
        "publish", help="publish the release package to crates.io"
    )
    publish_parser.add_argument("--tag", required=True, help="release tag")

    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        if args.command == "check":
            validate(args.tag, args.require_clean)
        elif args.command == "publish":
            publish(args.tag)
        else:
            raise AssertionError(f"unknown command {args.command}")
    except ReleaseError as error:
        print(f"release error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
