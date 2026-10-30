#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Updates `version` and `[package.metadata.exocrate.<os>.<arch>]` in Cargo.toml."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
import tomllib

EXPECTED_PLATFORMS = (
    ("linux", "x86_64"),
    ("linux", "aarch64"),
    ("macos", "x86_64"),
    ("macos", "aarch64"),
)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


def load_metadata_dir(metadata_dir: Path) -> dict[tuple[str, str], dict[str, str]]:
    records: dict[tuple[str, str], dict[str, str]] = {}
    for path in sorted(metadata_dir.glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        os_name = data["os"]
        arch = data["arch"]
        sha256 = data["sha256"]
        url = data["url"]
        key = (os_name, arch)
        if key not in EXPECTED_PLATFORMS:
            raise ValueError(f"{path}: unsupported platform {os_name}-{arch}")
        if key in records:
            raise ValueError(f"{path}: duplicate metadata for {os_name}-{arch}")
        if not SHA256_RE.match(sha256):
            raise ValueError(f"{path}: invalid sha256 {sha256!r}")
        if not url.startswith("https://"):
            raise ValueError(f"{path}: expected https:// URL, got {url!r}")
        records[key] = {"sha256": sha256, "url": url}

    missing = [
        f"{os_name}-{arch}"
        for (os_name, arch) in EXPECTED_PLATFORMS
        if (os_name, arch) not in records
    ]
    if missing:
        raise ValueError(
            "missing release metadata for platform(s): " + ", ".join(missing)
        )
    return records


def update_manifest_text(
    cargo_toml_text: str,
    version: str,
    records: dict[tuple[str, str], dict[str, str]],
) -> str:
    if not version or any(ch.isspace() for ch in version):
        raise ValueError(f"invalid version {version!r}")

    updated, count = re.subn(
        r'(?m)^(\[package\]\n(?:[^\[]*\n)*?version\s*=\s*)"[^"]*"',
        rf'\g<1>"{version}"',
        cargo_toml_text,
        count=1,
    )
    if count != 1:
        raise ValueError("failed to locate [package] version in Cargo.toml")

    for (os_name, arch), entry in records.items():
        header = re.escape(f"[package.metadata.exocrate.{os_name}.{arch}]")
        pattern = re.compile(
            rf"(?m)^({header}\n"
            r'sha256\s*=\s*)"[^"]*"(\n'
            r'url\s*=\s*)"[^"]*"'
        )
        updated, count = pattern.subn(
            rf'\g<1>"{entry["sha256"]}"\g<2>"{entry["url"]}"',
            updated,
            count=1,
        )
        if count != 1:
            raise ValueError(
                f"failed to update [package.metadata.exocrate.{os_name}.{arch}]"
            )

    parsed = tomllib.loads(updated)
    if parsed["package"]["version"] != version:
        raise ValueError("updated TOML version did not round-trip")
    exocrate_meta = parsed["package"]["metadata"]["exocrate"]
    for (os_name, arch), entry in records.items():
        if exocrate_meta[os_name][arch] != entry:
            raise ValueError(
                f"updated TOML metadata for {os_name}.{arch} did not round-trip"
            )
    return updated


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cargo-toml", type=Path, required=True)
    parser.add_argument("--version", required=True)
    parser.add_argument("--metadata-dir", type=Path, required=True)
    args = parser.parse_args()

    records = load_metadata_dir(args.metadata_dir)
    original = args.cargo_toml.read_text(encoding="utf-8")
    updated = update_manifest_text(original, args.version, records)
    args.cargo_toml.write_text(updated, encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
