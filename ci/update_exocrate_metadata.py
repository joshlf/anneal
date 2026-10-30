#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Update [[package.metadata.exocrate]] URLs and hashes in Cargo.toml."""

import argparse
import json
import re
from pathlib import Path

EXPECTED_PLATFORMS = {
    ("linux", "x86_64"),
    ("linux", "aarch64"),
    ("macos", "x86_64"),
    ("macos", "aarch64"),
}

EXPECTED_TARGETS = {
    ("linux", "x86_64"): "linux-x86_64",
    ("linux", "aarch64"): "linux-aarch64",
    ("macos", "x86_64"): "macos-x86_64",
    ("macos", "aarch64"): "macos-aarch64",
}

ARRAY_HEADER_RE = re.compile(r"^\[\[package\.metadata\.exocrate\]\]\s*$")
ANY_HEADER_RE = re.compile(r"^\[.*\]\s*$")
OS_RE = re.compile(r'^\s*os\s*=\s*"([^"]+)"\s*$')
ARCH_RE = re.compile(r'^\s*arch\s*=\s*"([^"]+)"\s*$')
SHA_RE = re.compile(r'^\s*sha256\s*=\s*"[0-9a-fA-F]{64}"\s*$')
URL_RE = re.compile(r'^\s*url\s*=\s*".*"\s*$')


def load_metadata(
    paths: list[Path], expected_release_tag: str | None
) -> dict[tuple[str, str], dict[str, str]]:
    metadata = {}
    for path in paths:
        value = json.loads(path.read_text())
        try:
            target = value["target"]
            os_name = value["os"]
            arch = value["arch"]
            sha256 = value["sha256"]
            url = value["url"]
        except KeyError as e:
            raise SystemExit(f"{path}: missing required key {e.args[0]!r}") from e
        if not all(
            isinstance(field, str)
            for field in (target, os_name, arch, sha256, url)
        ):
            raise SystemExit(
                f"{path}: target, os, arch, sha256, and url must all be strings"
            )
        if not re.fullmatch(r"[0-9a-f]{64}", sha256):
            raise SystemExit(
                f"{path}: sha256 must be 64 lowercase hex characters"
            )
        platform = (os_name, arch)
        expected_target = EXPECTED_TARGETS.get(platform)
        if expected_target is not None and target != expected_target:
            raise SystemExit(
                f"{path}: target {target!r} does not match platform "
                f"{os_name}.{arch}; expected {expected_target!r}"
            )
        if expected_release_tag is not None:
            expected_url_component = (
                f"/releases/download/{expected_release_tag}/"
            )
            if expected_url_component not in url:
                raise SystemExit(
                    f"{path}: url does not point at release tag "
                    f"{expected_release_tag!r}: {url}"
                )
        if platform in metadata:
            raise SystemExit(f"duplicate metadata for {os_name}.{arch}")
        metadata[platform] = {"sha256": sha256, "url": url}
    return metadata


def metadata_files(metadata_dir: Path) -> list[Path]:
    return sorted(
        path for path in metadata_dir.glob("*.json") if path.is_file()
    )


def update_manifest(
    cargo_toml: Path, metadata: dict[tuple[str, str], dict[str, str]]
) -> None:
    lines = cargo_toml.read_text().splitlines()
    blocks: list[tuple[int, int]] = []
    i = 0
    while i < len(lines):
        if ARRAY_HEADER_RE.match(lines[i].strip()):
            start = i
            j = i + 1
            while j < len(lines) and not ANY_HEADER_RE.match(lines[j].strip()):
                j += 1
            blocks.append((start, j))
            i = j
        else:
            i += 1

    seen = set()
    updated = {platform: set() for platform in metadata}

    for start, end in blocks:
        os_name = None
        arch_name = None
        for idx in range(start + 1, end):
            m_os = OS_RE.match(lines[idx])
            if m_os:
                os_name = m_os.group(1)
            m_arch = ARCH_RE.match(lines[idx])
            if m_arch:
                arch_name = m_arch.group(1)
        if os_name is None or arch_name is None:
            continue
        platform = (os_name, arch_name)
        if platform not in metadata:
            continue
        seen.add(platform)
        values = metadata[platform]
        for idx in range(start + 1, end):
            if SHA_RE.match(lines[idx]):
                lines[idx] = f'sha256 = "{values["sha256"]}"'
                updated[platform].add("sha256")
            elif URL_RE.match(lines[idx]):
                lines[idx] = f'url = "{values["url"]}"'
                updated[platform].add("url")

    missing_sections = set(metadata) - seen
    if missing_sections:
        formatted = ", ".join(
            f"{os_name}.{arch}" for os_name, arch in sorted(missing_sections)
        )
        raise SystemExit(
            f"Cargo.toml is missing [[package.metadata.exocrate]] blocks for: {formatted}"
        )

    incomplete = {
        platform: {"sha256", "url"} - fields
        for platform, fields in updated.items()
        if {"sha256", "url"} - fields
    }
    if incomplete:
        formatted = ", ".join(
            f"{os_name}.{arch} missing {','.join(sorted(fields))}"
            for (os_name, arch), fields in sorted(incomplete.items())
        )
        raise SystemExit(
            f"Cargo.toml has incomplete [[package.metadata.exocrate]] blocks: {formatted}"
        )

    cargo_toml.write_text("\n".join(lines) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cargo-toml",
        default="trusted/cargo-anneal/Cargo.toml",
        type=Path,
    )
    parser.add_argument("--metadata-dir", type=Path)
    parser.add_argument("--metadata", action="append", default=[], type=Path)
    parser.add_argument("--expected-release-tag")
    parser.add_argument("--require-all", action="store_true")
    args = parser.parse_args()

    paths = list(args.metadata)
    if args.metadata_dir is not None:
        paths.extend(metadata_files(args.metadata_dir))
    if not paths:
        raise SystemExit("no metadata JSON files provided")

    metadata = load_metadata(paths, args.expected_release_tag)
    if args.require_all and set(metadata) != EXPECTED_PLATFORMS:
        missing = EXPECTED_PLATFORMS - set(metadata)
        extra = set(metadata) - EXPECTED_PLATFORMS
        messages = []
        if missing:
            messages.append(
                "missing "
                + ", ".join(
                    f"{os_name}.{arch}" for os_name, arch in sorted(missing)
                )
            )
        if extra:
            messages.append(
                "unexpected "
                + ", ".join(
                    f"{os_name}.{arch}" for os_name, arch in sorted(extra)
                )
            )
        raise SystemExit("; ".join(messages))

    update_manifest(args.cargo_toml, metadata)


if __name__ == "__main__":
    main()
