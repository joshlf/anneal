#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `ci/update_release_manifest.py`."""

from __future__ import annotations

import json
from pathlib import Path
import tempfile
import tomllib
import unittest

from update_release_manifest import (
    EXPECTED_PLATFORMS,
    load_metadata_dir,
    update_manifest_text,
)

SAMPLE_CARGO_TOML = """\
[package]
name = "cargo-anneal"
version = "0.1.0-alpha.1"
edition = "2024"

[package.metadata.exocrate.linux.x86_64]
sha256 = "0000000000000000000000000000000000000000000000000000000000000000"
url = "https://example.com/linux-x86_64.tar.zst"

[package.metadata.exocrate.linux.aarch64]
sha256 = "0000000000000000000000000000000000000000000000000000000000000000"
url = "https://example.com/linux-aarch64.tar.zst"

[package.metadata.exocrate.macos.x86_64]
sha256 = "0000000000000000000000000000000000000000000000000000000000000000"
url = "https://example.com/macos-x86_64.tar.zst"

[package.metadata.exocrate.macos.aarch64]
sha256 = "0000000000000000000000000000000000000000000000000000000000000000"
url = "https://example.com/macos-aarch64.tar.zst"
"""


class UpdateReleaseManifestTests(unittest.TestCase):
    def test_loads_metadata_and_updates_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            meta_dir = Path(tmp)
            for idx, (os_name, arch) in enumerate(EXPECTED_PLATFORMS, start=1):
                record = {
                    "os": os_name,
                    "arch": arch,
                    "sha256": str(idx) * 64,
                    "url": (
                        "https://github.com/joshlf/anneal/releases/download/"
                        f"tag/anneal-toolchain-{os_name}-{arch}.tar.zst"
                    ),
                }
                (meta_dir / f"{os_name}-{arch}.json").write_text(
                    json.dumps(record), encoding="utf-8"
                )

            records = load_metadata_dir(meta_dir)
            updated = update_manifest_text(SAMPLE_CARGO_TOML, "0.2.0", records)
            parsed = tomllib.loads(updated)
            self.assertEqual(parsed["package"]["version"], "0.2.0")
            self.assertEqual(
                parsed["package"]["metadata"]["exocrate"]["macos"]["aarch64"][
                    "sha256"
                ],
                "4" * 64,
            )

    def test_rejects_missing_platform_metadata(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            meta_dir = Path(tmp)
            (meta_dir / "linux-x86_64.json").write_text(
                json.dumps(
                    {
                        "os": "linux",
                        "arch": "x86_64",
                        "sha256": "a" * 64,
                        "url": "https://github.com/joshlf/anneal/releases/download/t/a.tar.zst",
                    }
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                ValueError, "missing release metadata"
            ):
                load_metadata_dir(meta_dir)


if __name__ == "__main__":
    unittest.main()
