#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for the Anneal exocrate release metadata helper scripts."""

import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
COLLECT_SCRIPT = REPO_ROOT / "ci" / "collect_release_archive_metadata.py"
UPDATE_SCRIPT = REPO_ROOT / "ci" / "update_exocrate_metadata.py"
CARGO_TOML = REPO_ROOT / "trusted" / "cargo-anneal" / "Cargo.toml"


class ExocrateMetadataHelpersTest(unittest.TestCase):
    def test_collect_and_update_all_four_platforms(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            cargo_toml_copy = tmp_dir / "Cargo.toml"
            shutil.copyfile(CARGO_TOML, cargo_toml_copy)

            metadata_dir = tmp_dir / "metadata"
            metadata_dir.mkdir()
            tag = "anneal-toolchains-v0.1.0-12345-abcdef123456"

            platforms = [
                ("linux-x86_64", "linux", "x86_64"),
                ("linux-aarch64", "linux", "aarch64"),
                ("macos-x86_64", "macos", "x86_64"),
                ("macos-aarch64", "macos", "aarch64"),
            ]

            expected_urls = {}
            for target, os_name, arch in platforms:
                archive = tmp_dir / f"anneal-toolchain-{target}.tar.zst"
                archive.write_bytes(f"mock-archive-{target}".encode("utf-8"))
                url = f"https://github.com/joshlf/anneal/releases/download/{tag}/anneal-toolchain-{target}.tar.zst"
                expected_urls[target] = url
                out_json = metadata_dir / f"{target}.json"
                subprocess.run(
                    [
                        sys.executable,
                        str(COLLECT_SCRIPT),
                        "--archive",
                        str(archive),
                        "--target",
                        target,
                        "--os",
                        os_name,
                        "--arch",
                        arch,
                        "--url",
                        url,
                        "--out",
                        str(out_json),
                    ],
                    check=True,
                )
                parsed = json.loads(out_json.read_text())
                self.assertEqual(parsed["target"], target)
                self.assertEqual(parsed["os"], os_name)
                self.assertEqual(parsed["arch"], arch)
                self.assertEqual(parsed["url"], url)
                self.assertEqual(len(parsed["sha256"]), 64)

            subprocess.run(
                [
                    sys.executable,
                    str(UPDATE_SCRIPT),
                    "--cargo-toml",
                    str(cargo_toml_copy),
                    "--metadata-dir",
                    str(metadata_dir),
                    "--expected-release-tag",
                    tag,
                    "--require-all",
                ],
                check=True,
            )

            updated_text = cargo_toml_copy.read_text()
            for target, url in expected_urls.items():
                self.assertIn(url, updated_text)


if __name__ == "__main__":
    unittest.main()
