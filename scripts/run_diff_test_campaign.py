#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
# https://www.apache.org/licenses/LICENSE-2.0>, the MIT license
# <LICENSE-MIT or https://opensource.org/licenses/MIT>, or the BSD-2-Clause
# license <LICENSE-BSD or https://opensource.org/license/bsd-2-clause>, at your
# option. This file may not be copied, modified, or distributed except
# according to those terms.

"""Anneal differential-testing campaign orchestrator.

Runs `miri-difftest` (live Miri + Anneal MIR-in-Lean oracle with Lean 4 kernel
confirmation) and `itree-difftest` under a campaign profile, validates red-flag
vacuity checks, deduplicates and optionally quarantines divergence findings,
updates the persistent campaign ledger, and writes Markdown, JSON, and JUnit
XML reports.

Exit status:
  0  `miri-difftest` performed real oracle comparisons, passed all red-flag
     vacuity checks, had oracle errors within threshold, and produced zero
     unquarantined divergences (and `itree-difftest`, if enabled, did not fail);
  1  internal error, such as a ledger that is not a valid JSON object;
  2  invalid command line, harness crash, missing Miri/Lean toolchain,
     malformed harness JSON, red-flag vacuity failure (`zero_compared_items`,
     `impossible_wall_clock`, `identical_metrics_across_seeds`,
     `oracle_not_invoked`), or oracle errors above `--max-oracle-errors`;
  3  compile-only mode (`--compile-only`): neither harness crashed, and both
     harnesses reported `"oracle_comparison": "not_performed"`;
  4  one or more unquarantined divergences were detected by a live oracle run.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import datetime
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
from typing import Any
import xml.etree.ElementTree as ET


FILEUTIL_BIN = "/usr/bin/fileutil"
FILEUTIL_X20_FLAG = "--x20_force_client_creation_at_head"

EXIT_SUCCESS = 0
EXIT_INTERNAL_ERROR = 1
EXIT_HARNESS_FAILED = 2
EXIT_NOT_EVALUATED = 3
EXIT_DIVERGENCE_DETECTED = 4

DEFAULT_MIN_ORACLE_ELAPSED_MS = 50.0
DEFAULT_MAX_ORACLE_ERRORS = 0

VALID_DIVERGENCE_CLASSES = (
    "wrong_value",
    "false_positive_ub",
    "missed_ub",
    "ub_location_mismatch",
    "panic_vs_return",
    "return_vs_panic",
    "panic_site_mismatch",
)

VALID_NOT_COMPARED_REASONS = (
    "compile_failed",
    "capture_failed",
    "miri_oracle_error",
    "unsupported",
    "out_of_fuel",
    "external_call",
)

# Integer count keys that a harness JSON summary may carry.
HARNESS_INT_KEYS = (
    "batches",
    "batch_size",
    "total_candidates",
    "compiled_candidates",
    "compile_failed_candidates",
    "compared_candidates",
    "agree_count",
    "diverge_count",
    "not_compared_count",
    "kernel_confirmed_divergences",
    "unsafe_token_violations",
    "opt_level_0_compiled",
    "opt_level_2_compiled",
    "opt_level_0_and_2_compiled",
    "instrumented_compiled",
)

# Ledger keys that earlier compile-only versions of this runner dropped when
# running without an oracle.
OBSOLETE_LEDGER_KEYS = (
    "total_miri_candidates_evaluated",
    "total_itree_candidates_evaluated",
    "total_itree_inputs_evaluated",
    "cumulative_distinct_obs_paths",
    "active_fingerprints",
)


@dataclass(frozen=True)
class CampaignProfile:
    name: str
    miri_batches: int
    miri_batch_size: int
    itree_batches: int
    itree_batch_size: int


PROFILES: dict[str, CampaignProfile] = {
    "smoke": CampaignProfile("smoke", 2, 8, 2, 8),
    "quick": CampaignProfile("quick", 5, 32, 5, 32),
    "nightly": CampaignProfile("nightly", 25, 32, 25, 32),
    "weekend": CampaignProfile("weekend", 100, 32, 100, 32),
}


@dataclass(frozen=True)
class RedFlagResult:
    passed: bool
    checks: dict[str, bool]
    failure_reasons: list[str]


@dataclass
class DeduplicatedFinding:
    fingerprint: str
    cause: str
    seed_name: str
    divergence_class: str
    normalized_anneal_tag: str
    quarantined: bool
    occurrences: int
    primary_fn_name: str
    primary_repro_path: str
    all_repro_paths: list[str]
    miri_outcome: str
    anneal_outcome: str
    kernel_confirmed: bool

    def to_dict(self) -> dict[str, Any]:
        return {
            "fingerprint": self.fingerprint,
            "cause": self.cause,
            "seed_name": self.seed_name,
            "divergence_class": self.divergence_class,
            "normalized_anneal_tag": self.normalized_anneal_tag,
            "quarantined": self.quarantined,
            "occurrences": self.occurrences,
            "primary_fn_name": self.primary_fn_name,
            "primary_repro_path": self.primary_repro_path,
            "all_repro_paths": list(self.all_repro_paths),
            "miri_outcome": self.miri_outcome,
            "anneal_outcome": self.anneal_outcome,
            "kernel_confirmed": self.kernel_confirmed,
        }


def utc_now_iso() -> str:
    return (
        datetime.datetime.now(datetime.timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def utc_date_prefix() -> str:
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")


def has_x20_fileutil() -> bool:
    return os.path.isfile(FILEUTIL_BIN) and os.access(FILEUTIL_BIN, os.X_OK)


def run_fileutil(args: list[str]) -> subprocess.CompletedProcess[str]:
    cmd = [FILEUTIL_BIN, FILEUTIL_X20_FLAG, *args]
    return subprocess.run(cmd, text=True, capture_output=True, check=False)


def check_x20_uri(x20_uri: str) -> None:
    if x20_uri.startswith("/google/data/rw/"):
        raise ValueError(
            f"Refusing FUSE path `{x20_uri}`; always use `/x20/...` URIs with "
            f"`{FILEUTIL_BIN} {FILEUTIL_X20_FLAG}`."
        )


def sync_state_from_x20(x20_uri: str, state_dir: Path) -> None:
    """Pulls the ledger from `/x20/` via `fileutil` RPC."""
    if not x20_uri or not has_x20_fileutil():
        return
    check_x20_uri(x20_uri)
    (state_dir / "state").mkdir(parents=True, exist_ok=True)
    run_fileutil(
        [
            "cp",
            "-f",
            f"{x20_uri.rstrip('/')}/state/campaign_ledger.json",
            str(state_dir / "state" / "campaign_ledger.json"),
        ]
    )


def sync_state_to_x20(state_dir: Path, x20_uri: str, written: list[Path]) -> None:
    """Uploads the files this run wrote under `state_dir` to `/x20/`.

    Only `written` is uploaded, so stale files in a reused state directory are
    never republished.
    """
    if not x20_uri or not has_x20_fileutil():
        return
    check_x20_uri(x20_uri)
    base = x20_uri.rstrip("/")
    created_dirs: set[str] = set()
    for subdir in ["state", "reports"]:
        remote_dir = f"{base}/{subdir}"
        run_fileutil(["mkdir", "-p", remote_dir])
        created_dirs.add(remote_dir)
    for local_file in written:
        rel = local_file.relative_to(state_dir)
        remote_parent = f"{base}/{rel.parent}"
        if remote_parent not in created_dirs:
            run_fileutil(["mkdir", "-p", remote_parent])
            created_dirs.add(remote_parent)
        run_fileutil(["cp", "-f", str(local_file), f"{base}/{rel}"])


def load_ledger(ledger_path: Path) -> dict[str, Any]:
    if not ledger_path.is_file():
        return {}
    try:
        ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as e:
        raise ValueError(f"cannot read {ledger_path}: {e}") from e
    if not isinstance(ledger, dict):
        raise ValueError(f"{ledger_path} is not a JSON object")
    return ledger


def parse_seed_int(raw: str) -> int:
    clean = raw.strip().replace("_", "")
    if not clean:
        raise ValueError("empty seed")
    val = int(clean, 16) if clean.lower().startswith("0x") else int(clean, 10)
    if val < 0 or val > 0xFFFF_FFFF_FFFF_FFFF:
        raise ValueError(f"seed out of u64 range: {raw!r}")
    return val


def ledger_seed_int(ledger: dict[str, Any], key: str, default: str) -> int:
    raw = ledger.get(key, default)
    if isinstance(raw, bool) or not isinstance(raw, (int, str)):
        raise ValueError(f"ledger field {key!r} must be a seed string or integer")
    if isinstance(raw, int):
        if raw < 0 or raw > 0xFFFF_FFFF_FFFF_FFFF:
            raise ValueError(f"ledger field {key!r} is out of u64 range")
        return raw
    return parse_seed_int(raw)


def ledger_counter(ledger: dict[str, Any], key: str) -> int:
    raw = ledger.get(key, 0)
    if isinstance(raw, bool) or not isinstance(raw, int) or raw < 0:
        raise ValueError(f"ledger field {key!r} must be a non-negative integer")
    return raw


def advance_seed(seed_val: int) -> int:
    return (seed_val + 0x9E37_79B9) & 0xFFFF_FFFF


def is_nonneg_int(val: Any) -> bool:
    return not isinstance(val, bool) and isinstance(val, int) and val >= 0


def is_int_map(val: Any, expected_keys: tuple[str, ...] | None = None) -> bool:
    if not isinstance(val, dict):
        return False
    if expected_keys is not None and set(val.keys()) != set(expected_keys):
        return False
    return all(isinstance(k, str) and is_nonneg_int(v) for k, v in val.items())


def run_harness(
    repo_root: Path, bin_name: str, harness_args: list[str], json_path: Path
) -> dict[str, Any] | None:
    """Runs one harness binary; returns its JSON summary, or None on failure."""
    cargo_bin = shutil.which("cargo") or os.path.expanduser("~/.cargo/bin/cargo")
    cmd = [
        cargo_bin,
        "run",
        "--quiet",
        "--locked",
        "--manifest-path",
        str(repo_root / "crates" / "anneal-difftest" / "Cargo.toml"),
        "--bin",
        bin_name,
        "--",
        *harness_args,
        "--output-json",
        str(json_path),
    ]
    env = dict(os.environ)
    env["ANNEAL_CALLER_PATH"] = env.get("PATH", "")
    res = subprocess.run(
        cmd, cwd=str(repo_root), env=env, text=True, capture_output=True
    )
    if res.returncode != 0:
        sys.stderr.write(f"{bin_name} failed (exit {res.returncode}):\n{res.stderr}\n")
        return None
    try:
        summary = json.loads(json_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as e:
        sys.stderr.write(f"{bin_name} produced unreadable JSON: {e}\n")
        return None
    if not isinstance(summary, dict):
        sys.stderr.write(f"{bin_name} produced a non-object JSON summary\n")
        return None
    for key in HARNESS_INT_KEYS:
        val = summary.get(key)
        if val is not None and (isinstance(val, bool) or not isinstance(val, int)):
            sys.stderr.write(f"{bin_name} produced non-integer {key}={val!r}\n")
            return None
    elapsed = summary.get("elapsed_ms")
    if elapsed is not None and (
        isinstance(elapsed, bool) or not isinstance(elapsed, (int, float))
    ):
        sys.stderr.write(f"{bin_name} produced non-numeric elapsed_ms={elapsed!r}\n")
        return None
    return summary


def validate_performed_miri_summary(summary: dict[str, Any]) -> tuple[bool, str]:
    """Checks that a `miri-difftest` summary claiming `performed` is complete."""
    if summary.get("harness") != "miri-difftest":
        return False, f"expected harness='miri-difftest', got {summary.get('harness')!r}"
    if summary.get("oracle_comparison") != "performed":
        return (
            False,
            f"expected oracle_comparison='performed', got {summary.get('oracle_comparison')!r}",
        )

    req_ints = (
        "batches",
        "batch_size",
        "total_candidates",
        "compiled_candidates",
        "compile_failed_candidates",
        "compared_candidates",
        "agree_count",
        "diverge_count",
        "not_compared_count",
        "kernel_confirmed_divergences",
    )
    for k in req_ints:
        if not is_nonneg_int(summary.get(k)):
            return False, f"missing or invalid integer field {k!r}"

    elapsed = summary.get("elapsed_ms")
    if isinstance(elapsed, bool) or not isinstance(elapsed, (int, float)):
        return False, "missing or invalid numeric field 'elapsed_ms'"

    if not is_int_map(summary.get("miri_verdicts"), ("pass", "panic", "ub", "error")):
        return False, "missing or invalid 'miri_verdicts' map"
    if not is_int_map(
        summary.get("anneal_outcomes"),
        ("pass", "panic", "ub", "unsupported", "out_of_fuel", "external_call", "error"),
    ):
        return False, "missing or invalid 'anneal_outcomes' map"
    if not is_int_map(summary.get("divergence_classes"), VALID_DIVERGENCE_CLASSES):
        return False, "missing or invalid 'divergence_classes' map"
    if not is_int_map(summary.get("not_compared_reasons"), VALID_NOT_COMPARED_REASONS):
        return False, "missing or invalid 'not_compared_reasons' map"
    if not is_int_map(summary.get("unmodeled_external_calls")):
        return False, "missing or invalid 'unmodeled_external_calls' map"
    if not is_int_map(summary.get("mutator_applications")):
        return False, "missing or invalid 'mutator_applications' map"

    findings = summary.get("findings")
    if not isinstance(findings, list):
        return False, "missing or invalid 'findings' list"
    not_compared_prefixes = ("error:", "unsupported:", "out_of_fuel", "external_call:")
    for idx, f in enumerate(findings):
        if not isinstance(f, dict):
            return False, f"finding[{idx}] is not a JSON object"
        for str_key in (
            "finding_id",
            "fn_name",
            "seed_name",
            "divergence_class",
            "miri_outcome",
            "anneal_outcome",
            "anneal_lean_tag",
            "miri_excerpt",
            "repro_path",
        ):
            val = f.get(str_key)
            if not isinstance(val, str) or not val.strip():
                return False, f"finding[{idx}] has missing or empty {str_key!r}"
        if f["divergence_class"] not in VALID_DIVERGENCE_CLASSES:
            return (
                False,
                f"finding[{idx}] has unknown divergence_class {f['divergence_class']!r}",
            )
        if f["miri_outcome"] == f["anneal_outcome"]:
            return (
                False,
                f"finding[{idx}] is not a divergence: miri_outcome == anneal_outcome",
            )
        if f["miri_outcome"].startswith(not_compared_prefixes) or f[
            "anneal_outcome"
        ].startswith(not_compared_prefixes):
            return (
                False,
                f"finding[{idx}] has a not-compared outcome instead of a divergence",
            )
        if not isinstance(f.get("kernel_confirmed"), bool):
            return False, f"finding[{idx}] has non-boolean 'kernel_confirmed'"

    return True, "ok"


def miri_signature_for_seed_check(summary: dict[str, Any]) -> dict[str, Any]:
    return {
        "miri_verdicts": dict(summary.get("miri_verdicts", {})),
        "anneal_outcomes": dict(summary.get("anneal_outcomes", {})),
        "mutator_applications": dict(summary.get("mutator_applications", {})),
    }


def evaluate_miri_red_flags(
    summary: dict[str, Any],
    miri_seed: int,
    ledger: dict[str, Any],
    min_oracle_elapsed_ms: float,
    max_oracle_errors: int,
) -> RedFlagResult:
    """Runs red-flag vacuity checks on a `miri-difftest` oracle summary."""
    reasons: list[str] = []

    total = int(summary["total_candidates"])
    compiled = int(summary["compiled_candidates"])
    compile_failed = int(summary["compile_failed_candidates"])
    compared = int(summary["compared_candidates"])
    agreed = int(summary["agree_count"])
    diverged = int(summary["diverge_count"])
    not_compared = int(summary["not_compared_count"])
    kernel_confirmed = int(summary["kernel_confirmed_divergences"])
    elapsed_ms = float(summary["elapsed_ms"])

    miri_verdicts: dict[str, int] = summary["miri_verdicts"]
    anneal_outcomes: dict[str, int] = summary["anneal_outcomes"]
    div_classes: dict[str, int] = summary["divergence_classes"]
    nc_reasons: dict[str, int] = summary["not_compared_reasons"]
    findings: list[dict[str, Any]] = summary["findings"]

    # 1. Miri and Lean actually invoked and accounting consistent.
    oracle_invoked = True
    if compiled <= 0 or compiled + compile_failed != total:
        oracle_invoked = False
        reasons.append(
            f"oracle_not_invoked: compiled ({compiled}) + compile_failed ({compile_failed}) != total ({total})"
        )
    if sum(miri_verdicts.values()) != compiled:
        oracle_invoked = False
        reasons.append(
            f"oracle_not_invoked: sum(miri_verdicts)={sum(miri_verdicts.values())} != compiled ({compiled})"
        )
    if sum(anneal_outcomes.values()) != compiled:
        oracle_invoked = False
        reasons.append(
            f"oracle_not_invoked: sum(anneal_outcomes)={sum(anneal_outcomes.values())} != compiled ({compiled})"
        )
    if compared + not_compared != total:
        oracle_invoked = False
        reasons.append(
            f"oracle_not_invoked: compared ({compared}) + not_compared ({not_compared}) != total ({total})"
        )
    if agreed + diverged != compared:
        oracle_invoked = False
        reasons.append(
            f"oracle_not_invoked: agree ({agreed}) + diverge ({diverged}) != compared ({compared})"
        )
    if sum(div_classes.values()) != diverged:
        oracle_invoked = False
        reasons.append(
            f"oracle_not_invoked: sum(divergence_classes)={sum(div_classes.values())} != diverge_count ({diverged})"
        )
    if sum(nc_reasons.values()) != not_compared:
        oracle_invoked = False
        reasons.append(
            f"oracle_not_invoked: sum(not_compared_reasons)={sum(nc_reasons.values())} != not_compared_count ({not_compared})"
        )
    if len(findings) != diverged or kernel_confirmed != diverged:
        oracle_invoked = False
        reasons.append(
            f"oracle_not_invoked: findings ({len(findings)}) or kernel_confirmed ({kernel_confirmed}) != diverge_count ({diverged})"
        )
    miri_executed = (
        int(miri_verdicts.get("pass", 0))
        + int(miri_verdicts.get("panic", 0))
        + int(miri_verdicts.get("ub", 0))
    )
    anneal_executed = (
        int(anneal_outcomes.get("pass", 0))
        + int(anneal_outcomes.get("panic", 0))
        + int(anneal_outcomes.get("ub", 0))
    )
    if (
        miri_executed <= 0
        or anneal_executed <= 0
        or miri_executed < compared
        or anneal_executed < compared
    ):
        oracle_invoked = False
        reasons.append(
            f"oracle_not_invoked: executed verdicts (miri={miri_executed}, "
            f"anneal={anneal_executed}) must be > 0 and >= compared ({compared})"
        )
    if int(nc_reasons.get("compile_failed", 0)) != compile_failed:
        oracle_invoked = False
        reasons.append(
            f"oracle_not_invoked: not_compared_reasons.compile_failed "
            f"({nc_reasons.get('compile_failed')}) != compile_failed ({compile_failed})"
        )
    for f in findings:
        repro_p = Path(f["repro_path"])
        if not f.get("kernel_confirmed") or not repro_p.is_file():
            oracle_invoked = False
            reasons.append(
                f"oracle_not_invoked: finding {f.get('finding_id')!r} missing "
                f"kernel confirmation or repro.rs ({repro_p})"
            )

    # 2. Non-zero compared items.
    non_zero_compared = compared > 0
    if not non_zero_compared:
        reasons.append("zero_compared_items: compared_candidates is 0")

    # 3. Plausible wall-clock time.
    plausible_wall_clock = elapsed_ms >= min_oracle_elapsed_ms
    if not plausible_wall_clock:
        reasons.append(
            f"impossible_wall_clock: elapsed_ms ({elapsed_ms:.2f} ms) < min_oracle_elapsed_ms ({min_oracle_elapsed_ms:.2f} ms)"
        )

    # 4. Seed sensitivity across consecutive distinct seeds.
    seed_sensitive = True
    seed_hex = f"0x{miri_seed:08x}"
    prev_seed = ledger.get("last_miri_seed")
    prev_sig = ledger.get("last_miri_signature")
    cur_sig = miri_signature_for_seed_check(summary)
    if (
        summary.get("mode") != "identity"
        and isinstance(prev_seed, str)
        and prev_seed.lower() != seed_hex.lower()
        and isinstance(prev_sig, dict)
        and prev_sig == cur_sig
    ):
        seed_sensitive = False
        reasons.append(
            f"identical_metrics_across_seeds: seed {seed_hex} produced identical verdicts/outcomes/mutators to prior seed {prev_seed}"
        )

    # 5. Oracle error count within threshold.
    oracle_errors = (
        int(nc_reasons.get("miri_oracle_error", 0))
        + int(nc_reasons.get("capture_failed", 0))
        + int(miri_verdicts.get("error", 0))
        + int(anneal_outcomes.get("error", 0))
    )
    within_error_threshold = oracle_errors <= max_oracle_errors
    if not within_error_threshold:
        reasons.append(
            f"oracle_errors_exceeded: {oracle_errors} oracle/capture errors > max_oracle_errors ({max_oracle_errors})"
        )

    checks = {
        "oracle_invoked": oracle_invoked,
        "non_zero_compared": non_zero_compared,
        "plausible_wall_clock": plausible_wall_clock,
        "seed_sensitivity": seed_sensitive,
        "oracle_error_threshold": within_error_threshold,
    }
    return RedFlagResult(
        passed=all(checks.values()),
        checks=checks,
        failure_reasons=reasons,
    )


def load_known_corpus_bug_seeds(repo_root: Path) -> set[str]:
    manifest_path = repo_root / "tests" / "miri-diff" / "manifest.toml"
    if not manifest_path.is_file():
        return set()
    try:
        data = tomllib.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError):
        return set()
    seeds: set[str] = set()
    for entry in data.get("tests", []):
        if isinstance(entry, dict) and "known_anneal_bug" in entry:
            name = entry.get("name")
            if isinstance(name, str):
                seeds.add(name)
    return seeds


def load_quarantine_rules(quarantine_file: Path | None) -> set[str]:
    """Loads quarantine tokens from a JSON or TOML file."""
    if quarantine_file is None:
        return set()
    if not quarantine_file.is_file():
        raise ValueError(f"quarantine file does not exist: {quarantine_file}")
    text = quarantine_file.read_text(encoding="utf-8")
    rules: set[str] = set()
    if quarantine_file.suffix.lower() == ".toml":
        try:
            data = tomllib.loads(text)
        except tomllib.TOMLDecodeError as e:
            raise ValueError(f"invalid TOML in {quarantine_file}: {e}") from e
        for item in data.get("quarantined", []):
            if isinstance(item, str):
                rules.add(item)
        for entry in data.get("tests", []):
            if isinstance(entry, dict) and "known_anneal_bug" in entry:
                name = entry.get("name")
                bug = entry.get("known_anneal_bug")
                if isinstance(name, str):
                    rules.add(name)
                    if isinstance(bug, dict) and isinstance(bug.get("divergence_class"), str):
                        rules.add(f"{name}:{bug['divergence_class']}")
    else:
        try:
            data = json.loads(text)
        except json.JSONDecodeError as e:
            raise ValueError(f"invalid JSON in {quarantine_file}: {e}") from e
        if isinstance(data, list):
            for item in data:
                if isinstance(item, str):
                    rules.add(item)
        elif isinstance(data, dict):
            for k in ("quarantined", "fingerprints", "seeds", "mutators"):
                vals = data.get(k, [])
                if isinstance(vals, list):
                    for item in vals:
                        if isinstance(item, str):
                            rules.add(item)
        else:
            raise ValueError(f"unsupported quarantine JSON root in {quarantine_file}")
    return rules


def normalize_anneal_tag(raw_tag: str) -> str:
    clean = raw_tag.strip()
    while clean.startswith("(") and clean.endswith(")"):
        clean = clean[1:-1].strip()
    if clean.startswith("MirDiffTag.normalScalar"):
        return "MirDiffTag.normalScalar"
    return clean


def extract_fault_line_text(finding: dict[str, Any]) -> str:
    """Returns the source line at the earliest fault (`miri_pos` or `anneal_span`).

    When Anneal faults inside the unmutated seed body at an earlier line than a
    subsequent Miri fault in an appended mutator tail (or vice versa), the
    earliest line number is the point where the two executions first diverged.
    """
    src = finding.get("mutant_source")
    if not isinstance(src, str) or not src:
        return ""
    src_lines = src.splitlines()
    earliest_line_no: int | None = None
    for loc_key in ("miri_pos", "anneal_span"):
        loc = finding.get(loc_key)
        if not isinstance(loc, str) or ":" not in loc:
            continue
        parts = loc.split(":")
        if len(parts) >= 2 and parts[1].strip().isdigit():
            line_no = int(parts[1].strip())
            if 1 <= line_no <= len(src_lines):
                if earliest_line_no is None or line_no < earliest_line_no:
                    earliest_line_no = line_no
    if earliest_line_no is None:
        return ""
    return src_lines[earliest_line_no - 1]


def infer_finding_cause(
    finding: dict[str, Any], known_corpus_bug_seeds: set[str]
) -> str:
    """Identifies the seed or mutator responsible for a divergence finding."""
    seed_name = str(finding["seed_name"])
    mutators = finding.get("applied_mutators")
    first_mutator = (
        str(mutators[0])
        if isinstance(mutators, list)
        and len(mutators) > 0
        and isinstance(mutators[0], str)
        else ""
    )
    fault_text = extract_fault_line_text(finding)
    if fault_text:
        if any(
            tok in fault_text
            for tok in ("__miri_ptr_", "__oob_", "__neg_", "__ptr_pair", "__base_ptr")
        ):
            return "RawPtrOffsetMutator"
        if any(tok in fault_text for tok in ("__miri_tb_", "__tb_")):
            return "TreeBorrowsRetagInterleaver"
        if any(
            tok in fault_text
            for tok in (
                "__miri_valid_",
                "__valid_",
                "__bad_",
                "__uninit_",
                "__padded",
                "__pad_bytes",
                "__ptr_b",
                "__raw_u8",
            )
        ):
            return "BitValidityTransmuteMutator"
        if any(tok in fault_text for tok in ("__miri_arith_", "__miri_wide")):
            return "ArithmeticCastMutator"
        if any(tok in fault_text for tok in ("__miri_proj_", "__proj_")):
            return "PlaceProjectionWrapper"

    if seed_name in known_corpus_bug_seeds or not first_mutator:
        return seed_name
    return first_mutator


def deduplicate_and_quarantine_findings(
    findings: list[dict[str, Any]],
    known_corpus_bug_seeds: set[str],
    quarantine_rules: set[str],
) -> tuple[
    list[DeduplicatedFinding], list[DeduplicatedFinding], list[DeduplicatedFinding]
]:
    """Deduplicates raw findings and splits into unquarantined and quarantined."""
    by_fp: dict[str, DeduplicatedFinding] = {}
    for f in findings:
        seed_name = str(f["seed_name"])
        fn_name = str(f["fn_name"])
        div_class = str(f["divergence_class"])
        norm_tag = normalize_anneal_tag(str(f["anneal_lean_tag"]))
        cause = infer_finding_cause(f, known_corpus_bug_seeds)

        fp = f"{cause}:{div_class}:{norm_tag}"
        is_quarantined = bool(
            quarantine_rules
            and (
                fp in quarantine_rules
                or cause in quarantine_rules
                or seed_name in quarantine_rules
                or fn_name in quarantine_rules
                or f"{seed_name}:{div_class}" in quarantine_rules
                or f"{cause}:{div_class}" in quarantine_rules
            )
        )
        repro_path = str(f["repro_path"])

        if fp in by_fp:
            existing = by_fp[fp]
            existing.occurrences += 1
            if repro_path not in existing.all_repro_paths:
                existing.all_repro_paths.append(repro_path)
            existing.kernel_confirmed = existing.kernel_confirmed and bool(
                f.get("kernel_confirmed", False)
            )
            # An unquarantined instance of a fingerprint must never be swallowed
            # by an earlier instance that happened to be quarantined by
            # `seed_name` or `fn_name`.
            if not is_quarantined and existing.quarantined:
                existing.quarantined = False
                existing.seed_name = seed_name
                existing.primary_fn_name = fn_name
                existing.primary_repro_path = repro_path
                existing.miri_outcome = str(f["miri_outcome"])
                existing.anneal_outcome = str(f["anneal_outcome"])
        else:
            by_fp[fp] = DeduplicatedFinding(
                fingerprint=fp,
                cause=cause,
                seed_name=seed_name,
                divergence_class=div_class,
                normalized_anneal_tag=norm_tag,
                quarantined=is_quarantined,
                occurrences=1,
                primary_fn_name=fn_name,
                primary_repro_path=repro_path,
                all_repro_paths=[repro_path],
                miri_outcome=str(f["miri_outcome"]),
                anneal_outcome=str(f["anneal_outcome"]),
                kernel_confirmed=bool(f.get("kernel_confirmed", False)),
            )

    all_dedup = list(by_fp.values())
    unquarantined = [d for d in all_dedup if not d.quarantined]
    quarantined = [d for d in all_dedup if d.quarantined]
    return all_dedup, unquarantined, quarantined


def collect_finding_bundle_files(findings: list[dict[str, Any]], state_dir: Path) -> list[Path]:
    """Collects all `repro.rs`, `finding.json`, and `SUMMARY.md` files under `state_dir`."""
    files: list[Path] = []
    seen: set[Path] = set()
    for f in findings:
        repro = Path(f["repro_path"]).resolve()
        bundle_dir = repro.parent
        for name in ("repro.rs", "finding.json", "SUMMARY.md"):
            candidate = bundle_dir / name
            if candidate.is_file() and candidate not in seen:
                try:
                    candidate.relative_to(state_dir)
                except ValueError:
                    continue
                seen.add(candidate)
                files.append(candidate)
    return sorted(files)


def compile_summary(name: str, summary: dict[str, Any] | None) -> str:
    """Describes how many candidates a harness generated and compiled."""
    if summary is None:
        return "no candidates"
    key = "compiled_candidates" if name == "miri-difftest" else "opt_level_0_and_2_compiled"
    return (
        f"{summary.get('total_candidates', 'an unknown number of')} candidates, "
        f"{summary.get(key, 'an unknown number')} of which compiled"
    )


def write_not_evaluated_junit_xml(
    junit_path: Path,
    profile_name: str,
    summaries: dict[str, dict[str, Any] | None],
    ran_without_oracle: dict[str, bool],
    elapsed_sec: float,
) -> None:
    """Writes JUnit XML when neither harness performed an oracle comparison."""
    junit_path.parent.mkdir(parents=True, exist_ok=True)
    suites = ET.Element("testsuites")
    suite = ET.SubElement(
        suites,
        "testsuite",
        attrib={
            "name": f"anneal_diff_test_{profile_name}",
            "tests": str(len(ran_without_oracle)),
            "failures": str(len(ran_without_oracle)),
            "time": f"{elapsed_sec:.3f}",
        },
    )
    for name, ran in ran_without_oracle.items():
        case = ET.SubElement(
            suite,
            "testcase",
            attrib={"classname": "anneal_difftest", "name": name},
        )
        if not ran:
            failure = ET.SubElement(case, "failure", attrib={"message": "harness failed"})
            failure.text = (
                f"{name} exited with an error, wrote unreadable JSON, or reported "
                "an oracle status this runner cannot present."
            )
        else:
            failure = ET.SubElement(
                case, "failure", attrib={"message": "oracle comparison not performed"}
            )
            failure.text = (
                f"{name} generated {compile_summary(name, summaries[name])}, but "
                "it did not compare Anneal with Miri or with native execution, "
                "so this run is not evidence about Anneal."
            )
    tree = ET.ElementTree(suites)
    ET.indent(tree, space="  ")
    tree.write(junit_path, encoding="utf-8", xml_declaration=True)


def render_not_evaluated_report(
    profile: CampaignProfile,
    date_prefix: str,
    miri: dict[str, Any] | None,
    itree: dict[str, Any] | None,
    ran_without_oracle: dict[str, bool],
    miri_seed: int,
    itree_seed: int,
    elapsed_sec: float,
) -> str:
    """Renders the 25-line report when no oracle comparison was performed."""
    def cell(summary: dict[str, Any] | None, key: str, fmt: str = "{}") -> str:
        if summary is None or key not in summary:
            return "n/a"
        return fmt.format(summary[key])

    def oracle(name: str) -> str:
        return "**not performed**" if ran_without_oracle.get(name, False) else "harness failed"

    itree_compiled = (
        "n/a"
        if itree is None or "opt_level_0_and_2_compiled" not in itree
        else f"{itree['opt_level_0_and_2_compiled']} at both `-O0` and `-O2` (compile only)"
    )

    status = "NOT EVALUATED" if all(ran_without_oracle.values()) else "HARNESS FAILED"
    lines = [
        f"# Anneal Differential Testing Campaign Report (`{profile.name}` — `{date_prefix}`)",
        "",
        f"> **Status: {status}.** Neither harness compared Anneal with an oracle.",
        "> `miri-difftest` and `itree-difftest` generate candidate programs and",
        "> compile them with `rustc`; they do not run Miri, Anneal's Lean model, or",
        "> the generated programs. This report therefore contains no agreement",
        "> figures and no divergence findings.",
        "",
        "| Metric | `miri-difftest` | `itree-difftest` |",
        "| :--- | :--- | :--- |",
        f"| Seed | `0x{miri_seed:08x}` | `0x{itree_seed:08x}` |",
        f"| Candidates generated | {cell(miri, 'total_candidates')} | "
        f"{cell(itree, 'total_candidates')} |",
        f"| Compiled with `rustc` | {cell(miri, 'compiled_candidates')} | {itree_compiled} |",
        f"| Instrumented copies compiled (never executed) | n/a | "
        f"{cell(itree, 'instrumented_compiled')} |",
        f"| Candidates containing `unsafe` | n/a | {cell(itree, 'unsafe_token_violations')} |",
        f"| Oracle comparison | {oracle('miri-difftest')} | {oracle('itree-difftest')} |",
        f"| Harness wall-clock | {cell(miri, 'elapsed_ms', '{:.1f} ms')} | "
        f"{cell(itree, 'elapsed_ms', '{:.1f} ms')} |",
        "",
        f"Total campaign wall-clock: {elapsed_sec:.2f} s.",
        "",
        "## Divergences",
        "",
        "No oracle comparison was performed, so this campaign cannot report",
        "divergences. The absence of findings is not evidence that Anneal agrees",
        "with Miri or with native execution.",
    ]
    return "\n".join(lines) + "\n"


def write_oracle_junit_xml(
    junit_path: Path,
    profile_name: str,
    miri: dict[str, Any] | None,
    miri_red_flags: RedFlagResult | None,
    unquarantined: list[DeduplicatedFinding],
    quarantined: list[DeduplicatedFinding],
    include_itree: bool,
    itree: dict[str, Any] | None,
    itree_ran_without_oracle: bool,
    elapsed_sec: float,
) -> None:
    """Writes JUnit XML for a live oracle campaign."""
    junit_path.parent.mkdir(parents=True, exist_ok=True)
    # Each entry is (name, failure_tuple_or_none, skipped_message_or_none).
    cases: list[tuple[str, tuple[str, str] | None, str | None]] = []

    if miri is None or miri_red_flags is None:
        cases.append(
            (
                "miri-difftest",
                (
                    "harness failed",
                    "miri-difftest exited with an error or produced invalid oracle JSON.",
                ),
                None,
            )
        )
    elif not miri_red_flags.passed:
        cases.append(
            (
                "miri-difftest",
                (
                    "red-flag vacuity check failed",
                    "; ".join(miri_red_flags.failure_reasons),
                ),
                None,
            )
        )
    elif len(unquarantined) > 0:
        summary_lines = [
            f"{d.fingerprint} (occurrences={d.occurrences}, repro={d.primary_repro_path})"
            for d in unquarantined
        ]
        cases.append(
            (
                "miri-difftest",
                (
                    f"unquarantined divergences detected ({len(unquarantined)} distinct, {miri['diverge_count']} total)",
                    "\n".join(summary_lines),
                ),
                None,
            )
        )
    else:
        cases.append(("miri-difftest", None, None))

    if include_itree:
        if itree is None or not itree_ran_without_oracle:
            cases.append(
                (
                    "itree-difftest",
                    (
                        "harness failed",
                        "itree-difftest exited with an error or wrote unreadable JSON.",
                    ),
                    None,
                )
            )
        else:
            cases.append(
                (
                    "itree-difftest",
                    None,
                    f"itree-difftest generated {compile_summary('itree-difftest', itree)}, "
                    "but its runtime trace oracle is not yet active.",
                )
            )

    failures_count = sum(1 for _, fail, _ in cases if fail is not None)
    skipped_count = sum(1 for _, _, skip in cases if skip is not None)
    suites = ET.Element("testsuites")
    suite = ET.SubElement(
        suites,
        "testsuite",
        attrib={
            "name": f"anneal_diff_test_{profile_name}",
            "tests": str(len(cases)),
            "failures": str(failures_count),
            "skipped": str(skipped_count),
            "time": f"{elapsed_sec:.3f}",
        },
    )
    for name, fail, skip in cases:
        case = ET.SubElement(
            suite,
            "testcase",
            attrib={"classname": "anneal_difftest", "name": name},
        )
        if fail is not None:
            msg, text = fail
            failure = ET.SubElement(case, "failure", attrib={"message": msg})
            failure.text = text
        elif skip is not None:
            ET.SubElement(case, "skipped", attrib={"message": skip})
    tree = ET.ElementTree(suites)
    ET.indent(tree, space="  ")
    tree.write(junit_path, encoding="utf-8", xml_declaration=True)


def render_oracle_campaign_report(
    profile: CampaignProfile,
    date_prefix: str,
    miri: dict[str, Any],
    miri_red_flags: RedFlagResult,
    all_dedup: list[DeduplicatedFinding],
    unquarantined: list[DeduplicatedFinding],
    quarantined: list[DeduplicatedFinding],
    include_itree: bool,
    itree: dict[str, Any] | None,
    itree_ran_without_oracle: bool,
    miri_seed: int,
    itree_seed: int,
    elapsed_sec: float,
) -> str:
    """Renders the full Markdown report for a live `miri-difftest` oracle campaign."""
    if not miri_red_flags.passed or (include_itree and not itree_ran_without_oracle):
        status = "RED FLAG / HARNESS FAILED"
    elif len(unquarantined) > 0:
        status = (
            f"DIVERGENCE DETECTED ({len(unquarantined)} unquarantined distinct, "
            f"{miri['diverge_count']} raw)"
        )
    elif include_itree and len(quarantined) > 0:
        status = (
            f"MIRI PASS ({len(quarantined)} quarantined known bug fingerprints) "
            "/ ITREE NOT EVALUATED"
        )
    elif include_itree:
        status = "MIRI PASS (0 divergences) / ITREE NOT EVALUATED"
    elif len(quarantined) > 0:
        status = f"PASS ({len(quarantined)} quarantined known bug fingerprints)"
    else:
        status = "PASS (0 divergences)"

    itree_seed_cell = f"`0x{itree_seed:08x}`" if include_itree else "skipped (`--miri-only`)"
    itree_total_cell = (
        str(itree.get("total_candidates", "n/a")) if (include_itree and itree) else "n/a"
    )
    itree_compiled_cell = (
        f"{itree['opt_level_0_and_2_compiled']} (`-O0` & `-O2`, compile only)"
        if (include_itree and itree and "opt_level_0_and_2_compiled" in itree)
        else "n/a"
    )
    itree_oracle_cell = (
        "**not performed**"
        if (include_itree and itree_ran_without_oracle)
        else ("harness failed" if include_itree else "skipped")
    )
    itree_elapsed_cell = (
        f"{float(itree['elapsed_ms']):.1f} ms"
        if (include_itree and itree and "elapsed_ms" in itree)
        else "n/a"
    )

    lines: list[str] = [
        f"# Anneal Differential Testing Campaign Report (`{profile.name}` — `{date_prefix}`)",
        "",
        f"> **Status: {status}.**",
        f"> `miri-difftest` evaluated `{miri['compared_candidates']}/{miri['total_candidates']}` "
        f"candidates against live Miri (`-Zmiri-tree-borrows`) and Anneal's `MirSemantics` "
        f"oracle (`{miri['agree_count']}` agreed, `{miri['diverge_count']}` diverged, "
        f"`{miri['not_compared_count']}` not compared).",
        "",
        "## Campaign Summary",
        "",
        "| Metric | `miri-difftest` | `itree-difftest` |",
        "| :--- | :--- | :--- |",
        f"| Mode | `{miri.get('mode', 'seeded')}` | `compile-only` |",
        f"| Seed | `0x{miri_seed:08x}` | {itree_seed_cell} |",
        f"| Candidates generated | {miri['total_candidates']} | {itree_total_cell} |",
        f"| Compiled with `rustc` | {miri['compiled_candidates']} ({miri['compile_failed_candidates']} failed) | {itree_compiled_cell} |",
        f"| Oracle comparison | **performed** | {itree_oracle_cell} |",
        f"| Compared | {miri['compared_candidates']} | 0 |",
        f"| Agreed | {miri['agree_count']} | n/a |",
        f"| Diverged (raw / distinct) | {miri['diverge_count']} ({len(all_dedup)} distinct: {len(unquarantined)} unquarantined, {len(quarantined)} quarantined) | n/a |",
        f"| Kernel-confirmed divergences (`by rfl`) | {miri['kernel_confirmed_divergences']} | n/a |",
        f"| Not compared | {miri['not_compared_count']} | {itree_total_cell} |",
        f"| Harness wall-clock | {float(miri['elapsed_ms']):.1f} ms | {itree_elapsed_cell} |",
        "",
        f"Total campaign wall-clock: {elapsed_sec:.2f} s.",
        "",
        "## Miri & Anneal Outcome Breakdown (`miri-difftest`)",
        "",
        "| Miri Verdict | Count | Anneal Outcome | Count | Divergence Class | Count |",
        "| :--- | ---: | :--- | ---: | :--- | ---: |",
    ]

    miri_v = sorted(miri["miri_verdicts"].items())
    anneal_o = sorted(miri["anneal_outcomes"].items())
    div_c = sorted(miri["divergence_classes"].items())
    row_count = max(len(miri_v), len(anneal_o), len(div_c))
    for i in range(row_count):
        mv_k, mv_v = miri_v[i] if i < len(miri_v) else ("", "")
        ao_k, ao_v = anneal_o[i] if i < len(anneal_o) else ("", "")
        dc_k, dc_v = div_c[i] if i < len(div_c) else ("", "")
        mv_label = f"`{mv_k}`" if mv_k else ""
        ao_label = f"`{ao_k}`" if ao_k else ""
        dc_label = f"`{dc_k}`" if dc_k else ""
        lines.append(
            f"| {mv_label} | {mv_v} | {ao_label} | {ao_v} | {dc_label} | {dc_v} |"
        )

    lines.extend(
        [
            "",
            "## Not-Compared Breakdown by Reason (`miri-difftest`)",
            "",
            "| Reason | Count |",
            "| :--- | ---: |",
        ]
    )
    for reason, count in sorted(miri["not_compared_reasons"].items()):
        lines.append(f"| `{reason}` | {count} |")

    ext_calls: dict[str, int] = miri.get("unmodeled_external_calls", {})
    if ext_calls:
        lines.extend(
            [
                "",
                "### Unmodeled External Calls",
                "",
                "| Callee `def_path` | Count |",
                "| :--- | ---: |",
            ]
        )
        for callee, count in sorted(ext_calls.items(), key=lambda kv: (-kv[1], kv[0])):
            lines.append(f"| `{callee}` | {count} |")

    lines.extend(
        [
            "",
            "## Red-Flag Vacuity Checks",
            "",
            "| Check | Status |",
            "| :--- | :--- |",
        ]
    )
    for check_name, ok in miri_red_flags.checks.items():
        lines.append(f"| `{check_name}` | {'PASS' if ok else '**FAIL**'} |")
    if miri_red_flags.failure_reasons:
        lines.append("")
        for reason in miri_red_flags.failure_reasons:
            lines.append(f"- **Red-flag failure**: {reason}")

    lines.extend(
        [
            "",
            "## Divergences",
            "",
            f"### Unquarantined Divergences ({len(unquarantined)} distinct)",
            "",
        ]
    )
    if not unquarantined:
        lines.append("None.")
    else:
        lines.extend(
            [
                "| Fingerprint | Class | Occurrences | Miri | Anneal | Kernel Confirmed | Reproducer |",
                "| :--- | :--- | ---: | :--- | :--- | :--- | :--- |",
            ]
        )
        for d in unquarantined:
            lines.append(
                f"| `{d.fingerprint}` | `{d.divergence_class}` | {d.occurrences} | "
                f"`{d.miri_outcome}` | `{d.anneal_outcome}` | `{str(d.kernel_confirmed).lower()}` | "
                f"`{d.primary_repro_path}` |"
            )

    lines.extend(
        [
            "",
            f"### Quarantined Divergences ({len(quarantined)} distinct)",
            "",
        ]
    )
    if not quarantined:
        lines.append("None.")
    else:
        lines.extend(
            [
                "| Fingerprint | Class | Occurrences | Miri | Anneal | Kernel Confirmed | Reproducer |",
                "| :--- | :--- | ---: | :--- | :--- | :--- | :--- |",
            ]
        )
        for d in quarantined:
            lines.append(
                f"| `{d.fingerprint}` | `{d.divergence_class}` | {d.occurrences} | "
                f"`{d.miri_outcome}` | `{d.anneal_outcome}` | `{str(d.kernel_confirmed).lower()}` | "
                f"`{d.primary_repro_path}` |"
            )

    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Anneal differential-testing campaign orchestrator. Runs live Miri + "
            "Anneal oracle comparisons for miri-difftest, validates red-flag "
            "vacuity checks, and deduplicates divergence findings."
        )
    )
    parser.add_argument("--profile", choices=sorted(PROFILES), default="quick")
    parser.add_argument(
        "--state-dir",
        type=Path,
        default=None,
        help="Local directory for the ledger, findings, and reports (default: a temporary directory).",
    )
    parser.add_argument(
        "--x20-uri",
        type=str,
        default="",
        help="x20 directory to synchronize the ledger and reports with (default: no x20 sync).",
    )
    parser.add_argument("--miri-seed", type=str, default=None)
    parser.add_argument("--itree-seed", type=str, default=None)
    parser.add_argument(
        "--miri-identity",
        action="store_true",
        help="Run miri-difftest in 77-function identity corpus mode (--identity).",
    )
    parser.add_argument(
        "--miri-only",
        action="store_true",
        help="Run only miri-difftest (skipping itree-difftest).",
    )
    parser.add_argument(
        "--compile-only",
        action="store_true",
        help="Run miri-difftest with --compile-only (no oracle execution).",
    )
    parser.add_argument(
        "--quarantine-file",
        type=Path,
        default=None,
        help="Optional TOML or JSON file listing quarantined divergence fingerprints or seed names.",
    )
    parser.add_argument(
        "--max-oracle-errors",
        type=int,
        default=DEFAULT_MAX_ORACLE_ERRORS,
        help="Maximum allowed Miri/capture oracle errors before failing (default: 0).",
    )
    parser.add_argument(
        "--min-oracle-elapsed-ms",
        type=float,
        default=DEFAULT_MIN_ORACLE_ELAPSED_MS,
        help="Minimum plausible elapsed_ms for a live oracle run (default: 50.0).",
    )
    parser.add_argument(
        "--junit-xml",
        type=Path,
        default=None,
        help="Optional path for JUnit XML (`sponge_log.xml`).",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    profile = PROFILES[args.profile]
    repo_root = Path(__file__).resolve().parent.parent
    start_time = time.monotonic()

    x20_uri = args.x20_uri.strip()
    try:
        check_x20_uri(x20_uri)
        cli_miri_seed = parse_seed_int(args.miri_seed) if args.miri_seed is not None else None
        cli_itree_seed = parse_seed_int(args.itree_seed) if args.itree_seed is not None else None
        quarantine_rules = load_quarantine_rules(args.quarantine_file)
        if args.max_oracle_errors < 0 or args.min_oracle_elapsed_ms < 0:
            raise ValueError("thresholds must be non-negative")
    except ValueError as e:
        sys.stderr.write(f"error: {e}\n")
        return EXIT_HARNESS_FAILED

    temp_ctx = (
        tempfile.TemporaryDirectory(prefix="anneal-diff-test-campaign-")
        if args.state_dir is None
        else None
    )
    state_dir = Path(temp_ctx.name) if temp_ctx is not None else args.state_dir.resolve()

    try:
        sync_state_from_x20(x20_uri, state_dir)
        (state_dir / "state").mkdir(parents=True, exist_ok=True)
        (state_dir / "reports").mkdir(parents=True, exist_ok=True)

        ledger_path = state_dir / "state" / "campaign_ledger.json"
        try:
            ledger = load_ledger(ledger_path)
            miri_seed = (
                cli_miri_seed
                if cli_miri_seed is not None
                else ledger_seed_int(ledger, "next_miri_seed", "0x5eed0001")
            )
            itree_seed = (
                cli_itree_seed
                if cli_itree_seed is not None
                else ledger_seed_int(ledger, "next_itree_seed", "0x5eed0002")
            )
            prev_campaigns = ledger_counter(ledger, "total_campaigns_run")
            prev_miri_gen = ledger_counter(ledger, "total_miri_candidates_generated")
            prev_itree_gen = ledger_counter(ledger, "total_itree_candidates_generated")
            prev_miri_eval = ledger_counter(ledger, "total_miri_candidates_evaluated")
        except ValueError as e:
            sys.stderr.write(f"error: {e}\n")
            return EXIT_INTERNAL_ERROR

        date_prefix = utc_date_prefix()
        findings_dir = state_dir / "findings" / f"{date_prefix}_{profile.name}_miri"
        if not args.compile_only:
            shutil.rmtree(findings_dir, ignore_errors=True)

        with tempfile.TemporaryDirectory(prefix="anneal-diff-test-run-") as run_tmp:
            run_tmp_path = Path(run_tmp)
            if args.compile_only:
                miri_args = [
                    "--batches",
                    str(profile.miri_batches),
                    "--batch-size",
                    str(profile.miri_batch_size),
                    "--seed",
                    f"0x{miri_seed:08x}",
                    "--compile-only",
                ]
            elif args.miri_identity:
                miri_args = [
                    "--identity",
                    "--seed",
                    f"0x{miri_seed:08x}",
                    "--findings-dir",
                    str(findings_dir),
                ]
            else:
                miri_args = [
                    "--batches",
                    str(profile.miri_batches),
                    "--batch-size",
                    str(profile.miri_batch_size),
                    "--seed",
                    f"0x{miri_seed:08x}",
                    "--findings-dir",
                    str(findings_dir),
                ]

            miri = run_harness(
                repo_root,
                "miri-difftest",
                miri_args,
                run_tmp_path / "miri_difftest_out.json",
            )
            itree = (
                None
                if args.miri_only
                else run_harness(
                    repo_root,
                    "itree-difftest",
                    [
                        "--compile-only",
                        "--batches",
                        str(profile.itree_batches),
                        "--batch-size",
                        str(profile.itree_batch_size),
                        "--seed",
                        f"0x{itree_seed:08x}",
                    ],
                    run_tmp_path / "itree_difftest_out.json",
                )
            )

        miri_status = miri.get("oracle_comparison") if isinstance(miri, dict) else None
        itree_status = itree.get("oracle_comparison") if isinstance(itree, dict) else None

        # Case 1: Neither harness performed an oracle comparison (compile-only mode
        # or stubbed non-oracle harnesses). When `--compile-only` was not passed,
        # `miri-difftest` returning `"not_performed"` is treated as a harness
        # failure (`EXIT_HARNESS_FAILED`).
        if miri_status != "performed":
            summaries = {"miri-difftest": miri, "itree-difftest": itree}
            ran_without_oracle = {
                name: (
                    isinstance(s, dict)
                    and s.get("oracle_comparison") == "not_performed"
                    and (args.compile_only or name != "miri-difftest")
                )
                for name, s in summaries.items()
            }
            for name, s in summaries.items():
                if isinstance(s, dict) and not ran_without_oracle[name]:
                    sys.stderr.write(
                        f"{name} reported unsupported oracle_comparison={s.get('oracle_comparison')!r}\n"
                    )
            harness_failed = not all(ran_without_oracle.values())

            written: list[Path] = []
            if not harness_failed and miri is not None and itree is not None:
                for key in OBSOLETE_LEDGER_KEYS:
                    ledger.pop(key, None)
                ledger["next_miri_seed"] = f"0x{advance_seed(miri_seed):08x}"
                ledger["next_itree_seed"] = f"0x{advance_seed(itree_seed):08x}"
                ledger["total_campaigns_run"] = prev_campaigns + 1
                ledger["total_miri_candidates_generated"] = prev_miri_gen + int(
                    miri.get("total_candidates", 0)
                )
                ledger["total_itree_candidates_generated"] = prev_itree_gen + int(
                    itree.get("total_candidates", 0)
                )
                ledger["last_run_utc"] = utc_now_iso()
                ledger["last_profile"] = profile.name
                ledger["last_oracle_comparison"] = "not_performed"
                ledger_path.write_text(
                    json.dumps(ledger, indent=2, sort_keys=True) + "\n", encoding="utf-8"
                )
                written.append(ledger_path)

            elapsed_sec = time.monotonic() - start_time
            report_md = render_not_evaluated_report(
                profile,
                date_prefix,
                miri,
                itree,
                ran_without_oracle,
                miri_seed,
                itree_seed,
                elapsed_sec,
            )
            for report_path in [
                state_dir / "reports" / f"{date_prefix}_{profile.name}_campaign_report.md",
                state_dir / "reports" / "LATEST_REPORT.md",
            ]:
                report_path.write_text(report_md, encoding="utf-8")
                written.append(report_path)

            if args.junit_xml:
                write_not_evaluated_junit_xml(
                    args.junit_xml.resolve(),
                    profile.name,
                    summaries,
                    ran_without_oracle,
                    elapsed_sec,
                )

            sync_state_to_x20(state_dir, x20_uri, written)
            print(report_md)
            return EXIT_HARNESS_FAILED if harness_failed else EXIT_NOT_EVALUATED

        # Case 2: `miri-difftest` reported `"oracle_comparison": "performed"`.
        assert miri is not None
        valid_miri, err_reason = validate_performed_miri_summary(miri)
        include_itree = not args.miri_only
        itree_ran_without_oracle = (
            isinstance(itree, dict) and itree_status == "not_performed"
        )
        if not valid_miri:
            sys.stderr.write(f"miri-difftest produced invalid oracle summary: {err_reason}\n")
            elapsed_sec = time.monotonic() - start_time
            ran_without_oracle = {
                "miri-difftest": False,
                "itree-difftest": itree_ran_without_oracle if include_itree else False,
            }
            report_md = render_not_evaluated_report(
                profile,
                date_prefix,
                miri,
                itree,
                ran_without_oracle,
                miri_seed,
                itree_seed,
                elapsed_sec,
            )
            written = []
            for report_path in [
                state_dir / "reports" / f"{date_prefix}_{profile.name}_campaign_report.md",
                state_dir / "reports" / "LATEST_REPORT.md",
            ]:
                report_path.write_text(report_md, encoding="utf-8")
                written.append(report_path)
            if args.junit_xml:
                write_not_evaluated_junit_xml(
                    args.junit_xml.resolve(),
                    profile.name,
                    {"miri-difftest": miri, "itree-difftest": itree},
                    ran_without_oracle,
                    elapsed_sec,
                )
            sync_state_to_x20(state_dir, x20_uri, written)
            print(report_md)
            return EXIT_HARNESS_FAILED

        miri_red_flags = evaluate_miri_red_flags(
            miri,
            miri_seed,
            ledger,
            args.min_oracle_elapsed_ms,
            args.max_oracle_errors,
        )
        if not miri_red_flags.passed:
            for reason in miri_red_flags.failure_reasons:
                sys.stderr.write(f"red-flag check failed: {reason}\n")

        known_corpus_bug_seeds = load_known_corpus_bug_seeds(repo_root)
        all_dedup, unquarantined, quarantined = deduplicate_and_quarantine_findings(
            miri["findings"],
            known_corpus_bug_seeds,
            quarantine_rules,
        )

        harness_or_red_flag_failed = (not miri_red_flags.passed) or (
            include_itree and not itree_ran_without_oracle
        )

        written = collect_finding_bundle_files(miri["findings"], state_dir)
        if not harness_or_red_flag_failed:
            ledger["next_miri_seed"] = f"0x{advance_seed(miri_seed):08x}"
            if include_itree and itree is not None:
                ledger["next_itree_seed"] = f"0x{advance_seed(itree_seed):08x}"
                ledger["total_itree_candidates_generated"] = prev_itree_gen + int(
                    itree.get("total_candidates", 0)
                )
            ledger["total_campaigns_run"] = prev_campaigns + 1
            ledger["total_miri_candidates_generated"] = prev_miri_gen + int(
                miri.get("total_candidates", 0)
            )
            ledger["total_miri_candidates_evaluated"] = prev_miri_eval + int(
                miri.get("compared_candidates", 0)
            )
            ledger["last_miri_seed"] = f"0x{miri_seed:08x}"
            ledger["last_miri_signature"] = miri_signature_for_seed_check(miri)
            ledger["active_fingerprints"] = [d.fingerprint for d in unquarantined]
            ledger["quarantined_fingerprints"] = [d.fingerprint for d in quarantined]
            ledger["last_run_utc"] = utc_now_iso()
            ledger["last_profile"] = profile.name
            ledger["last_oracle_comparison"] = (
                "performed" if not include_itree else "miri_performed_itree_not_performed"
            )
            ledger_path.write_text(
                json.dumps(ledger, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
            written.append(ledger_path)

        elapsed_sec = time.monotonic() - start_time
        report_md = render_oracle_campaign_report(
            profile,
            date_prefix,
            miri,
            miri_red_flags,
            all_dedup,
            unquarantined,
            quarantined,
            include_itree,
            itree,
            itree_ran_without_oracle,
            miri_seed,
            itree_seed,
            elapsed_sec,
        )
        for report_path in [
            state_dir / "reports" / f"{date_prefix}_{profile.name}_campaign_report.md",
            state_dir / "reports" / "LATEST_REPORT.md",
        ]:
            report_path.write_text(report_md, encoding="utf-8")
            written.append(report_path)

        campaign_summary = {
            "profile": profile.name,
            "date_utc": date_prefix,
            "miri_seed": f"0x{miri_seed:08x}",
            "itree_seed": f"0x{itree_seed:08x}" if include_itree else None,
            "miri_oracle_comparison": "performed",
            "itree_oracle_comparison": (
                "not_performed"
                if (include_itree and itree_ran_without_oracle)
                else ("failed" if include_itree else "skipped")
            ),
            "red_flags": {
                "passed": miri_red_flags.passed,
                "checks": miri_red_flags.checks,
                "failure_reasons": miri_red_flags.failure_reasons,
            },
            "miri_summary": miri,
            "deduplicated_findings": [d.to_dict() for d in all_dedup],
            "unquarantined_findings": [d.to_dict() for d in unquarantined],
            "quarantined_findings": [d.to_dict() for d in quarantined],
            "elapsed_sec": round(elapsed_sec, 3),
        }
        summary_json_text = json.dumps(campaign_summary, indent=2) + "\n"
        for summary_path in [
            state_dir / "reports" / f"{date_prefix}_{profile.name}_campaign_summary.json",
            state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json",
        ]:
            summary_path.write_text(summary_json_text, encoding="utf-8")
            written.append(summary_path)

        if args.junit_xml:
            write_oracle_junit_xml(
                args.junit_xml.resolve(),
                profile.name,
                miri,
                miri_red_flags,
                unquarantined,
                quarantined,
                include_itree,
                itree,
                itree_ran_without_oracle,
                elapsed_sec,
            )

        sync_state_to_x20(state_dir, x20_uri, written)
        print(report_md)

        if harness_or_red_flag_failed:
            return EXIT_HARNESS_FAILED
        if len(unquarantined) > 0:
            return EXIT_DIVERGENCE_DETECTED
        return EXIT_SUCCESS
    finally:
        if temp_ctx is not None:
            temp_ctx.cleanup()


if __name__ == "__main__":
    raise SystemExit(main())
