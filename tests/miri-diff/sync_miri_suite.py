#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Validate and synchronize the hermetic Miri differential test corpus.

This script checks three invariants for `tests/miri-diff/`:

1. Manifest <-> Corpus consistency (`--check-manifest`, always enabled):
   Verifies that every `[[tests]]` entry in `tests/miri-diff/manifest.toml`
   matches a `pub fn <name>()` in `tests/miri-diff/corpus/src/lib.rs` and an
   entry in `tests/miri-diff/corpus/examples/miri_eval.rs`, that every
   `miri_verdict = "ub"` entry records a valid `miri_ub_span`, that all
   `upstream_path` values are clean relative paths (`tests/pass/...`,
   `tests/panic/...`, `tests/fail/...`), and that all `[tests.known_anneal_bug]`
   entries are marked `status = "open_bug"` with either `observed_anneal_tag`
   diverging from `miri_verdict` or `bug_class = "ub_location_mismatch"` whose
   `observed_anneal_ub_span` does not contain `miri_ub_span`.

2. Upstream public Miri checkout verification (`--miri-tests-dir <path>`):
   When pointed at a local clone of `https://github.com/rust-lang/rust`
   (`src/tools/miri/tests`) or `https://github.com/rust-lang/miri` (`tests`)
   at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, verifies the upstream
   suite layout (`pass/`, `panic/`, `fail/`).

3. Live Miri oracle execution (`--eval-miri`):
   Compiles `tests/miri-diff/corpus` and runs `miri -Zmiri-tree-borrows` on
   every test entry via `examples/miri_eval.rs`, asserting that live Miri
   produces the exact `miri_verdict` and (for `"ub"` entries) `miri_ub_span`
   recorded in `manifest.toml`.
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
        help=(
            "Run live Miri on all corpus tests and verify every miri_verdict "
            "and miri_ub_span in manifest.toml"
        ),
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


def parse_rustc_pos(raw: str) -> tuple[str, int, int]:
    parts = raw.strip().rstrip(":").rsplit(":", 2)
    if len(parts) != 3:
        raise ValueError(f"Invalid source position '{raw}'; expected <file>:<line>:<col>")
    file_part, line_str, col_str = parts[0].strip(), parts[1].strip(), parts[2].strip()
    if not file_part:
        raise ValueError(f"Empty file in source position '{raw}'")
    line = int(line_str)
    col = int(col_str)
    if line <= 0 or col <= 0:
        raise ValueError(f"Non-positive line/col in source position '{raw}'")
    return file_part, line, col


def parse_anneal_span(raw: str) -> tuple[str, int, int, int, int]:
    trimmed = raw.strip()
    if ": " not in trimmed:
        raise ValueError(
            f"Invalid Anneal span '{raw}'; expected '<file>:<sline>:<scol>: <eline>:<ecol>'"
        )
    left, right = trimmed.split(": ", 1)
    file_part, start_line, start_col = parse_rustc_pos(left)
    end_parts = right.strip().split(":")
    if len(end_parts) != 2:
        raise ValueError(f"Invalid Anneal span end '{raw}'")
    end_line = int(end_parts[0].strip())
    end_col = int(end_parts[1].strip())
    if end_line <= 0 or end_col <= 0:
        raise ValueError(f"Non-positive end line/col in Anneal span '{raw}'")
    return file_part, start_line, start_col, end_line, end_col


def normalize_file(path_str: str) -> str:
    s = path_str.replace("\\", "/").strip()
    if s.startswith("./"):
        s = s[2:]
    return s


def files_match(a: str, b: str) -> bool:
    na = normalize_file(a)
    nb = normalize_file(b)
    if not na or not nb:
        return False
    return na == nb or na.endswith("/" + nb) or nb.endswith("/" + na)


def span_contains_pos(
    span: tuple[str, int, int, int, int], pos: tuple[str, int, int]
) -> bool:
    s_file, s_line, s_col, e_line, e_col = span
    p_file, p_line, p_col = pos
    if not files_match(s_file, p_file):
        return False
    return (s_line, s_col) <= (p_line, p_col) <= (e_line, e_col)


def is_stdlib_or_driver_path(path_str: str) -> bool:
    s = normalize_file(path_str)
    return (
        "/.rustup/" in s
        or "/library/core/" in s
        or "/library/std/" in s
        or "/library/alloc/" in s
        or s.endswith("miri_eval.rs")
    )


def extract_ub_span_from_stderr(stderr: str) -> str:
    idx = stderr.find("error: Undefined Behavior:")
    if idx < 0:
        raise RuntimeError(f"Missing 'error: Undefined Behavior:' header in:\n{stderr}")
    after = stderr[idx:]
    arrows: list[str] = []
    backtraces: list[str] = []
    for raw_line in after.splitlines()[1:]:
        trimmed = raw_line.strip()
        if trimmed.startswith("warning:") or trimmed.startswith("error: aborting"):
            break
        if "-->" in trimmed:
            cand = trimmed.split("-->", 1)[1].strip()
            try:
                parse_rustc_pos(cand)
                arrows.append(cand)
            except ValueError:
                pass
        elif trimmed.startswith("= note:") and " at " in trimmed:
            cand = trimmed.rsplit(" at ", 1)[1].strip()
            try:
                parse_rustc_pos(cand)
                backtraces.append(cand)
            except ValueError:
                pass
    for a in arrows:
        f, _, _ = parse_rustc_pos(a)
        if not is_stdlib_or_driver_path(f):
            return a
    for b in backtraces:
        f, _, _ = parse_rustc_pos(b)
        if not is_stdlib_or_driver_path(f):
            return b
    if arrows:
        return arrows[0]
    if backtraces:
        return backtraces[0]
    raise RuntimeError(f"Could not extract UB source span from Miri stderr:\n{stderr}")


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

    allowed_test_keys = {
        "name",
        "category",
        "upstream_path",
        "miri_verdict",
        "miri_ub_span",
        "fuel",
        "known_anneal_bug",
    }
    allowed_bug_keys = {
        "status",
        "bug_class",
        "observed_anneal_tag",
        "observed_anneal_ub_span",
        "suspected_component",
        "summary",
    }

    for entry in tests:
        name = entry["name"]
        unknown_test = sorted(set(entry.keys()) - allowed_test_keys)
        if unknown_test:
            raise ValueError(
                f"Test '{name}' has unknown keys in [[tests]]: {unknown_test}"
            )
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

        verdict = entry["miri_verdict"]
        miri_ub_span_raw = entry.get("miri_ub_span")
        miri_pos = None
        if verdict == "ub":
            if not miri_ub_span_raw:
                raise ValueError(
                    f"Test '{name}' has miri_verdict = 'ub' but is missing 'miri_ub_span'"
                )
            miri_pos = parse_rustc_pos(miri_ub_span_raw)
        elif miri_ub_span_raw is not None:
            raise ValueError(
                f"Test '{name}' has miri_ub_span '{miri_ub_span_raw}' "
                f"but miri_verdict is '{verdict}'"
            )

        bug = entry.get("known_anneal_bug")
        if bug is not None:
            unknown_bug = sorted(set(bug.keys()) - allowed_bug_keys)
            if unknown_bug:
                raise ValueError(
                    f"Test '{name}' has unknown keys in [tests.known_anneal_bug]: "
                    f"{unknown_bug}"
                )
            if bug.get("status") != "open_bug":
                raise ValueError(
                    f"Test '{name}' known_anneal_bug must have status = 'open_bug'"
                )
            bug_class = bug.get("bug_class", "")
            obs_tag = bug.get("observed_anneal_tag")
            obs_span_raw = bug.get("observed_anneal_ub_span")
            if obs_span_raw is not None and obs_tag != "ub":
                raise ValueError(
                    f"Test '{name}' has observed_anneal_ub_span '{obs_span_raw}' "
                    f"but observed_anneal_tag is '{obs_tag}' (expected 'ub')"
                )
            obs_span = parse_anneal_span(obs_span_raw) if obs_span_raw else None

            if bug_class == "ub_location_mismatch":
                if verdict != "ub" or obs_tag != "ub" or obs_span is None or miri_pos is None:
                    raise ValueError(
                        f"Test '{name}' with bug_class = 'ub_location_mismatch' requires "
                        "miri_verdict = 'ub', observed_anneal_tag = 'ub', miri_ub_span, "
                        "and observed_anneal_ub_span"
                    )
                if span_contains_pos(obs_span, miri_pos):
                    raise ValueError(
                        f"Test '{name}' has stale ub_location_mismatch: "
                        f"observed_anneal_ub_span '{obs_span_raw}' contains "
                        f"miri_ub_span '{miri_ub_span_raw}'"
                    )
            elif obs_tag == verdict:
                raise ValueError(
                    f"Test '{name}' has stale known_anneal_bug: "
                    f"observed_anneal_tag == miri_verdict ({verdict})"
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
    if not (miri_sysroot / "lib" / "rustlib").is_dir():
        raise RuntimeError(
            f"Miri sysroot is missing lib/rustlib at {miri_sysroot}; "
            "missing Miri sysroot is a hard error"
        )

    lib_rs = Path("src/lib.rs")
    eval_rs = Path("examples/miri_eval.rs")
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
        subprocess.run(compile_cmd, cwd=corpus_dir, check=True)

        ub_span_checked = 0
        for entry in manifest["tests"]:
            name = entry["name"]
            expected = entry["miri_verdict"]
            expected_ub_span = entry.get("miri_ub_span")
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
            proc = subprocess.run(
                cmd, cwd=corpus_dir, env=env, capture_output=True, text=True
            )
            stdout = proc.stdout.strip()
            stderr = proc.stderr

            actual_ub_span = None
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
            elif "error: Undefined Behavior:" in stderr:
                actual = "ub"
                actual_ub_span = extract_ub_span_from_stderr(stderr)
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
            if expected == "ub":
                if actual_ub_span != expected_ub_span:
                    raise AssertionError(
                        f"Miri UB span mismatch on '{name}': manifest expects "
                        f"'{expected_ub_span}', live Miri produced '{actual_ub_span}'"
                    )
                ub_span_checked += 1

    print(
        f"Live Miri oracle verified all {len(manifest['tests'])} corpus tests "
        f"(including {ub_span_checked} UB fault spans) with flags {miri_flags}."
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
