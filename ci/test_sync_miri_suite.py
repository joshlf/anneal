# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `tests/miri-diff/sync_miri_suite.py` manifest/corpus checks."""

import importlib.util
from pathlib import Path
import re
import tempfile
import unittest


REPO_ROOT = Path(__file__).resolve().parent.parent
SYNC_SCRIPT = REPO_ROOT / "tests" / "miri-diff" / "sync_miri_suite.py"


def _load_sync_module():
    spec = importlib.util.spec_from_file_location("sync_miri_suite", SYNC_SCRIPT)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


SYNC = _load_sync_module()


def _write_fixture(
    root: Path,
    *,
    manifest_toml: str,
    lib_rs: str,
    eval_rs: str,
) -> tuple[Path, Path]:
    manifest_path = root / "manifest.toml"
    corpus_dir = root / "corpus"
    (corpus_dir / "src").mkdir(parents=True, exist_ok=True)
    (corpus_dir / "examples").mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(manifest_toml, encoding="utf-8")
    (corpus_dir / "src" / "lib.rs").write_text(lib_rs, encoding="utf-8")
    (corpus_dir / "examples" / "miri_eval.rs").write_text(eval_rs, encoding="utf-8")
    return manifest_path, corpus_dir


_BASE_MANIFEST = """\
schema_version = 1

[[tests]]
name = "pass_demo"
category = "tree_borrows"
upstream_path = "tests/pass/demo.rs"
miri_verdict = "pass:scalar:1:4"
fuel = 64
"""


class SyncMiriSuiteTests(unittest.TestCase):
    def test_live_repo_manifest_and_corpus_pass(self) -> None:
        manifest = SYNC.check_manifest_and_corpus(
            REPO_ROOT / "tests" / "miri-diff" / "manifest.toml",
            REPO_ROOT / "tests" / "miri-diff" / "corpus",
        )
        self.assertEqual(len(manifest["tests"]), 112)

    def test_accepts_str_and_unit_model_markers_and_ignores_commented_items(self) -> None:
        lib_rs = """\
#![no_std]
/* Nested /* block comment:
pub fn fake_in_comment() -> u32 { 0 }
pub const __ANNEAL_MODEL_ghost: &str = "wrong";
*/ end */
// pub fn fake_line_comment() -> u32 { 0 }
pub const DOC_RAW: &str = r#"
pub fn fake_in_raw_string() -> u32 { 0 }
"#;

pub const __ANNEAL_MODEL_STATIC_DEMO: &str = "STATIC_DEMO";
pub static mut STATIC_DEMO: u32 = 1;

pub const __ANNEAL_MODEL_probe_unit: () = ();
pub unsafe fn probe_unit() -> u32 { 2 }

pub const __ANNEAL_MODEL_probe_lifetime: &'static str = "probe_lifetime";
pub const fn probe_lifetime() -> u32 { 3 }

pub fn pass_demo() -> u32 { 1 }
"""
        eval_rs = """\
fn main() {
    match "pass_demo" {
        "pass_demo" => {}
        // "probe_unit" => {}
        _ => {}
    }
}
"""
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path, corpus_dir = _write_fixture(
                Path(tmp),
                manifest_toml=_BASE_MANIFEST,
                lib_rs=lib_rs,
                eval_rs=eval_rs,
            )
            manifest = SYNC.check_manifest_and_corpus(manifest_path, corpus_dir)
            self.assertEqual([t["name"] for t in manifest["tests"]], ["pass_demo"])

    def test_rejects_mismatched_duplicate_and_stale_model_markers(self) -> None:
        cases = [
            (
                "mismatched-str",
                'pub const __ANNEAL_MODEL_probe_a: &str = "other";\n'
                "pub fn probe_a() -> u32 { 0 }\n"
                "pub fn pass_demo() -> u32 { 1 }\n",
                "neither `&str = \"<name>\"` nor `() = ()`",
            ),
            (
                "bad-type",
                "pub const __ANNEAL_MODEL_probe_a: u32 = 1;\n"
                "pub fn probe_a() -> u32 { 0 }\n"
                "pub fn pass_demo() -> u32 { 1 }\n",
                "neither `&str = \"<name>\"` nor `() = ()`",
            ),
            (
                "duplicate-marker",
                'pub const __ANNEAL_MODEL_probe_a: &str = "probe_a";\n'
                "pub const __ANNEAL_MODEL_probe_a: () = ();\n"
                "pub fn probe_a() -> u32 { 0 }\n"
                "pub fn pass_demo() -> u32 { 1 }\n",
                "duplicate __ANNEAL_MODEL_* markers",
            ),
            (
                "stale-marker",
                'pub const __ANNEAL_MODEL_missing_item: &str = "missing_item";\n'
                "pub fn pass_demo() -> u32 { 1 }\n",
                "name no top-level item",
            ),
        ]
        eval_rs = 'fn main() { match "" { "pass_demo" => {}, _ => {} } }\n'
        for label, lib_rs, expected_msg in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                manifest_path, corpus_dir = _write_fixture(
                    Path(tmp),
                    manifest_toml=_BASE_MANIFEST,
                    lib_rs=lib_rs,
                    eval_rs=eval_rs,
                )
                with self.assertRaisesRegex(ValueError, re.escape(expected_msg)):
                    SYNC.check_manifest_and_corpus(manifest_path, corpus_dir)

    def test_rejects_unmarked_pub_unsafe_fn_and_orphaned_or_commented_eval_arms(self) -> None:
        # 1. Unmarked `pub unsafe fn` must not silently escape manifest parity.
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path, corpus_dir = _write_fixture(
                Path(tmp),
                manifest_toml=_BASE_MANIFEST,
                lib_rs=(
                    "pub fn pass_demo() -> u32 { 1 }\n"
                    "pub unsafe fn ub_unmarked_unsafe() -> u32 { 0 }\n"
                ),
                eval_rs='fn main() { match "" { "pass_demo" => {}, _ => {} } }\n',
            )
            with self.assertRaisesRegex(ValueError, "ub_unmarked_unsafe"):
                SYNC.check_manifest_and_corpus(manifest_path, corpus_dir)

        # 2. Model-marked probe accidentally wired into `miri_eval.rs` must fail.
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path, corpus_dir = _write_fixture(
                Path(tmp),
                manifest_toml=_BASE_MANIFEST,
                lib_rs=(
                    'pub const __ANNEAL_MODEL_probe_x: &str = "probe_x";\n'
                    "pub fn probe_x() -> u32 { 0 }\n"
                    "pub fn pass_demo() -> u32 { 1 }\n"
                ),
                eval_rs=(
                    'fn main() { match "" { '
                    '"pass_demo" => {}, "probe_x" => {}, _ => {} } }\n'
                ),
            )
            with self.assertRaisesRegex(ValueError, "absent from manifest.toml"):
                SYNC.check_manifest_and_corpus(manifest_path, corpus_dir)

        # 3. Commented-out dispatch arm in `miri_eval.rs` must fail.
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path, corpus_dir = _write_fixture(
                Path(tmp),
                manifest_toml=_BASE_MANIFEST,
                lib_rs="pub fn pass_demo() -> u32 { 1 }\n",
                eval_rs='fn main() { match "" { // "pass_demo" => {}\n _ => {} } }\n',
            )
            with self.assertRaisesRegex(ValueError, "missing a dispatch arm"):
                SYNC.check_manifest_and_corpus(manifest_path, corpus_dir)


if __name__ == "__main__":
    unittest.main()
