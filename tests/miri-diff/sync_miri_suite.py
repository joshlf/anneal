#!/usr/bin/env python3
"""Validate and synchronize the hermetic Miri differential test corpus.

This script checks two invariants for `tests/miri-diff/`:

1. Manifest <-> Corpus consistency (`--check-manifest`, always enabled):
   Verifies that every `[[tests]]` entry in `tests/miri-diff/manifest.toml`
   matches a `pub fn <name>()` in `tests/miri-diff/corpus/src/lib.rs` and an
   entry in `tests/miri-diff/corpus/examples/miri_eval.rs`, that all
   `upstream_path` values are clean relative paths (`tests/pass/...`,
   `tests/panic/...`, `tests/fail/...`), and that all `[tests.known_anneal_bug]`
   entries are marked `status = "open_bug"` with `observed_anneal_tag`
   diverging from `miri_verdict`.

2. Upstream public Miri checkout verification (`--miri-tests-dir <path>`):
   When pointed at a local clone of `https://github.com/rust-lang/rust`
   (`src/tools/miri/tests`) or `https://github.com/rust-lang/miri` (`tests`)
   at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, verifies the upstream
   suite layout (`pass/`, `panic/`, `fail/`).

3. Live Miri oracle execution (`--eval-miri`):
   Compiles `tests/miri-diff/corpus` and runs `miri -Zmiri-tree-borrows` on
   every test entry via `examples/miri_eval.rs`, asserting that live Miri
   produces the exact `miri_verdict` recorded in `manifest.toml`.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import tomllib


def parse_args() -> argparse.Namespace:
    script_dir = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=script_dir / "manifest.toml",
        help="Path to tests/miri-diff/manifest.toml",
    )
    parser.add_argument(
        "--corpus-dir",
        type=Path,
        default=script_dir / "corpus",
        help="Path to tests/miri-diff/corpus",
    )
    parser.add_argument(
        "--miri-tests-dir",
        type=Path,
        default=os.environ.get("MIRI_TESTS_DIR"),
        help=(
            "Optional path to a checkout of upstream Miri tests "
            "(e.g. <rust-checkout>/src/tools/miri/tests or <miri-checkout>/tests)"
        ),
    )
    parser.add_argument(
        "--eval-miri",
        action="store_true",
        help="Run live Miri on all corpus tests and verify every miri_verdict in manifest.toml",
    )
    parser.add_argument(
        "--rustc-bin",
        type=Path,
        default=None,
        help="Explicit path to rustc (defaults to nightly-2026-06-01 rustc in ~/.rustup)",
    )
    parser.add_argument(
        "--miri-bin",
        type=Path,
        default=None,
        help="Explicit path to miri driver (defaults to nightly-2026-06-01 miri in ~/.rustup)",
    )
    parser.add_argument(
        "--miri-sysroot",
        type=Path,
        default=None,
        help="Explicit path to Miri sysroot (defaults to ~/.cache/miri)",
    )
    return parser.parse_args()


def resolve_default_toolchain_bin(tool_name: str) -> Path:
    home = Path.home()
    candidates = sorted(
        home.glob(f".rustup/toolchains/nightly-2026-06-01-*/bin/{tool_name}")
    )
    if candidates:
        return candidates[0]
    return Path(tool_name)


def check_manifest_and_corpus(manifest_path: Path, corpus_dir: Path) -> dict:
    with manifest_path.open("rb") as f:
        manifest = tomllib.load(f)

    if manifest.get("schema_version") != 1:
        raise ValueError(f"Unsupported schema_version: {manifest.get('schema_version')}")

    lib_rs = (corpus_dir / "src" / "lib.rs").read_text(encoding="utf-8")
    eval_rs = (corpus_dir / "examples" / "miri_eval.rs").read_text(encoding="utf-8")

    fn_names_in_lib = [
        m.group(1)
        for m in re.finditer(r"^pub fn ([a-z0-9_]+)\(\)", lib_rs, re.MULTILINE)
        if m.group(1) != "helper_add_ten"
    ]

    tests = manifest.get("tests", [])
    manifest_names = [t["name"] for t in tests]
    if manifest_names != fn_names_in_lib:
        missing_in_manifest = set(fn_names_in_lib) - set(manifest_names)
        missing_in_lib = set(manifest_names) - set(fn_names_in_lib)
        raise ValueError(
            f"Manifest test list does not match corpus/src/lib.rs: "
            f"missing_in_manifest={sorted(missing_in_manifest)}, "
            f"missing_in_lib={sorted(missing_in_lib)}"
        )

    for entry in tests:
        name = entry["name"]
        upstream_path = entry["upstream_path"]
        if not upstream_path.startswith(("tests/pass/", "tests/panic/", "tests/fail/")):
            raise ValueError(
                f"Test '{name}' has invalid upstream_path '{upstream_path}'; "
                "must start with tests/pass/, tests/panic/, or tests/fail/"
            )
        if f'"{name}" =>' not in eval_rs:
            raise ValueError(
                f"Test '{name}' is missing a dispatch arm in corpus/examples/miri_eval.rs"
            )
        bug = entry.get("known_anneal_bug")
        if bug is not None:
            if bug.get("status") != "open_bug":
                raise ValueError(
                    f"Test '{name}' known_anneal_bug must have status = 'open_bug'"
                )
            if bug.get("observed_anneal_tag") == entry["miri_verdict"]:
                raise ValueError(
                    f"Test '{name}' has stale known_anneal_bug: "
                    f"observed_anneal_tag == miri_verdict ({entry['miri_verdict']})"
                )

    return manifest


def check_upstream_miri_dir(miri_tests_dir: Path, manifest: dict) -> None:
    root = miri_tests_dir.resolve()
    if (root / "tests" / "pass").is_dir():
        tests_root = root / "tests"
    elif (root / "pass").is_dir():
        tests_root = root
    else:
        raise ValueError(
            f"Directory {root} does not contain Miri's pass/, panic/, and fail/ subdirectories"
        )

    for subdir in ("pass", "panic", "fail"):
        if not (tests_root / subdir).is_dir():
            raise ValueError(f"Missing expected Miri test subdirectory: {tests_root / subdir}")

    verified_files = 0
    for entry in manifest["tests"]:
        rel = entry["upstream_path"].removeprefix("tests/")
        candidate = tests_root / rel
        if candidate.is_file():
            verified_files += 1

    print(
        f"Verified upstream Miri test directory structure at {tests_root} "
        f"({verified_files}/{len(manifest['tests'])} exact upstream file paths present)."
    )


def eval_miri_oracle(
    corpus_dir: Path,
    manifest: dict,
    rustc_bin: Path,
    miri_bin: Path,
    miri_sysroot: Path,
) -> None:
    lib_rs = corpus_dir / "src" / "lib.rs"
    eval_rs = corpus_dir / "examples" / "miri_eval.rs"
    miri_flags = manifest.get("miri_flags", ["-Zmiri-tree-borrows"])

    with tempfile.TemporaryDirectory(prefix="anneal-miri-oracle-") as tmp:
        rlib_path = Path(tmp) / "libmiri_diff_corpus.rlib"
        compile_cmd = [
            str(rustc_bin),
            "--sysroot",
            str(miri_sysroot),
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=miri_diff_corpus",
            "-Zalways-encode-mir",
            "-Zmir-opt-level=0",
            "-C",
            "debug-assertions=off",
            "-C",
            "overflow-checks=on",
            str(lib_rs),
            "-o",
            str(rlib_path),
        ]
        subprocess.run(compile_cmd, check=True)

        for entry in manifest["tests"]:
            name = entry["name"]
            expected = entry["miri_verdict"]
            env = os.environ.copy()
            env["MIRI_DIFF_TEST"] = name
            cmd = [
                str(miri_bin),
                "--sysroot",
                str(miri_sysroot),
                *miri_flags,
                "-Zmiri-disable-isolation",
                "--edition=2024",
                str(eval_rs),
                "--extern",
                f"miri_diff_corpus={rlib_path}",
            ]
            proc = subprocess.run(cmd, env=env, capture_output=True, text=True)
            stdout = proc.stdout.strip()
            stderr = proc.stderr

            if proc.returncode == 0:
                actual = None
                for line in stdout.splitlines():
                    if line.startswith("MIRI_PASS:"):
                        actual = "pass:" + line.removeprefix("MIRI_PASS:")
                        break
                if actual is None:
                    raise RuntimeError(
                        f"Miri succeeded on '{name}' without MIRI_PASS line:\n{stdout}\n{stderr}"
                    )
            elif "Undefined Behavior:" in stderr:
                actual = "ub"
            elif "panicked at" in stderr or "explicit panic" in stderr:
                actual = "panic"
            else:
                raise RuntimeError(
                    f"Unexpected Miri failure on '{name}' (exit {proc.returncode}):\n{stderr}"
                )

            if actual != expected:
                raise AssertionError(
                    f"Miri oracle mismatch on '{name}': manifest expects '{expected}', "
                    f"live Miri produced '{actual}'"
                )

    print(
        f"Live Miri oracle verified all {len(manifest['tests'])} corpus tests "
        f"with flags {miri_flags}."
    )


def main() -> int:
    args = parse_args()
    manifest = check_manifest_and_corpus(args.manifest, args.corpus_dir)
    bug_count = sum(1 for t in manifest["tests"] if "known_anneal_bug" in t)
    print(
        f"Validated {args.manifest.name}: {len(manifest['tests'])} tests "
        f"({len(manifest['tests']) - bug_count} matching Miri, "
        f"{bug_count} tracked open Anneal bugs)."
    )

    if args.miri_tests_dir is not None:
        check_upstream_miri_dir(args.miri_tests_dir, manifest)

    if args.eval_miri:
        rustc_bin = args.rustc_bin or resolve_default_toolchain_bin("rustc")
        miri_bin = args.miri_bin or resolve_default_toolchain_bin("miri")
        miri_sysroot = args.miri_sysroot or (Path.home() / ".cache" / "miri")
        eval_miri_oracle(args.corpus_dir, manifest, rustc_bin, miri_bin, miri_sysroot)

    return 0


if __name__ == "__main__":
    sys.exit(main())
