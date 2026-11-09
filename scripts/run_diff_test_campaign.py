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

VALID_ITREE_DIAG_TAGS = (
    "ok",
    "outcome_mismatch",
    "unexpected_ext_call",
    "call_arg_mismatch",
    "branch_tag_mismatch",
    "unconsumed_events",
    "step_faulted",
    "decode_arg_failed",
    "decode_event_failed",
    "decode_outcome_failed",
    "out_of_fuel",
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
    "trials_per_candidate",
    "agree_candidates",
    "diverge_candidates",
    "not_compared_candidates",
    "total_traces_executed",
    "distinct_traces_checked",
    "agree_traces",
    "diverge_traces",
    "kernel_confirmed_traces",
    "distinct_obs_paths",
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
    # Legacy prefixes plus the tags the Rust harness actually emits for not-compared
    # outcomes (`AnnealOutcome::summary_tag` / `MiriOutcome::summary_tag`): a finding
    # whose outcome is an error, `unsupported`, external call, or fuel exhaustion is a
    # masked not-compared item, never a divergence.
    not_compared_prefixes = (
        "error:",
        "unsupported:",
        "out_of_fuel",
        "external_call:",
        "unsupported",
        "capture_error",
        "externalCall",
        "outOfFuel",
        "oracle_error",
    )
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


def validate_performed_itree_summary(summary: dict[str, Any]) -> tuple[bool, str]:
    """Checks that an `itree-difftest` summary claiming `performed` is complete."""
    if summary.get("harness") != "itree-difftest":
        return False, f"expected harness='itree-difftest', got {summary.get('harness')!r}"
    if summary.get("oracle_comparison") != "performed":
        return (
            False,
            f"expected oracle_comparison='performed', got {summary.get('oracle_comparison')!r}",
        )

    req_ints = (
        "batches",
        "batch_size",
        "trials_per_candidate",
        "total_candidates",
        "unsafe_token_violations",
        "opt_level_0_compiled",
        "opt_level_2_compiled",
        "opt_level_0_and_2_compiled",
        "instrumented_compiled",
        "compared_candidates",
        "agree_candidates",
        "diverge_candidates",
        "not_compared_candidates",
        "total_traces_executed",
        "distinct_traces_checked",
        "agree_traces",
        "diverge_traces",
        "kernel_confirmed_traces",
        "kernel_confirmed_divergences",
        "distinct_obs_paths",
    )
    for k in req_ints:
        if not is_nonneg_int(summary.get(k)):
            return False, f"missing or invalid integer field {k!r}"

    elapsed = summary.get("elapsed_ms")
    if isinstance(elapsed, bool) or not isinstance(elapsed, (int, float)):
        return False, "missing or invalid numeric field 'elapsed_ms'"

    if not is_int_map(summary.get("diag_tag_counts"), VALID_ITREE_DIAG_TAGS):
        return False, "missing or invalid 'diag_tag_counts' map"
    if not is_int_map(summary.get("per_candidate_distinct_traces")):
        return False, "missing or invalid 'per_candidate_distinct_traces' map"
    if not is_int_map(summary.get("mutator_applications")):
        return False, "missing or invalid 'mutator_applications' map"

    findings = summary.get("findings")
    if not isinstance(findings, list):
        return False, "missing or invalid 'findings' list"
    for idx, f in enumerate(findings):
        if not isinstance(f, dict):
            return False, f"itree finding[{idx}] is not a JSON object"
        for str_key in (
            "finding_id",
            "fn_name",
            "case_ident",
            "diag_tag",
            "diag_repr",
            "trace_hex",
            "checked_mir_module",
            "repro_path",
        ):
            val = f.get(str_key)
            if not isinstance(val, str) or not val.strip():
                return False, f"itree finding[{idx}] has missing or empty {str_key!r}"
        if f["diag_tag"] == "ok" or f["diag_tag"] not in VALID_ITREE_DIAG_TAGS:
            return (
                False,
                f"itree finding[{idx}] has invalid divergence diag_tag {f['diag_tag']!r}",
            )
        if not isinstance(f.get("kernel_confirmed"), bool):
            return False, f"itree finding[{idx}] has non-boolean 'kernel_confirmed'"

    return True, "ok"


def itree_signature_for_seed_check(summary: dict[str, Any]) -> dict[str, Any]:
    return {
        "diag_tag_counts": dict(summary.get("diag_tag_counts", {})),
        "distinct_obs_paths": int(summary.get("distinct_obs_paths", 0)),
        "mutator_applications": dict(summary.get("mutator_applications", {})),
    }


def evaluate_itree_red_flags(
    summary: dict[str, Any],
    itree_seed: int,
    ledger: dict[str, Any],
    min_oracle_elapsed_ms: float,
) -> RedFlagResult:
    """Runs red-flag vacuity checks on an `itree-difftest` oracle summary."""
    reasons: list[str] = []

    total = int(summary["total_candidates"])
    unsafe_violations = int(summary["unsafe_token_violations"])
    opt_both = int(summary["opt_level_0_and_2_compiled"])
    compared = int(summary["compared_candidates"])
    agree_cands = int(summary["agree_candidates"])
    diverge_cands = int(summary["diverge_candidates"])
    not_compared_cands = int(summary["not_compared_candidates"])
    total_traces = int(summary["total_traces_executed"])
    distinct_traces = int(summary["distinct_traces_checked"])
    agree_traces = int(summary["agree_traces"])
    diverge_traces = int(summary["diverge_traces"])
    kc_traces = int(summary["kernel_confirmed_traces"])
    kc_divergences = int(summary["kernel_confirmed_divergences"])
    distinct_obs = int(summary["distinct_obs_paths"])
    elapsed_ms = float(summary["elapsed_ms"])
    diag_counts: dict[str, int] = summary["diag_tag_counts"]
    findings: list[dict[str, Any]] = summary["findings"]

    oracle_invoked = True
    if unsafe_violations != 0:
        oracle_invoked = False
        reasons.append(
            f"itree_oracle_not_invoked: unsafe_token_violations={unsafe_violations} != 0"
        )
    if compared <= 0 or compared != opt_both or compared + not_compared_cands != total:
        oracle_invoked = False
        reasons.append(
            f"itree_oracle_not_invoked: compared ({compared}), opt_both ({opt_both}), "
            f"not_compared ({not_compared_cands}), total ({total}) inconsistent"
        )
    if agree_cands + diverge_cands != compared:
        oracle_invoked = False
        reasons.append(
            f"itree_oracle_not_invoked: agree_candidates ({agree_cands}) + "
            f"diverge_candidates ({diverge_cands}) != compared_candidates ({compared})"
        )
    if (
        total_traces < compared
        or distinct_traces <= 0
        or distinct_traces > total_traces
        or distinct_obs <= 0
    ):
        oracle_invoked = False
        reasons.append(
            f"itree_oracle_not_invoked: traces (total={total_traces}, "
            f"distinct={distinct_traces}, obs_paths={distinct_obs}) invalid"
        )
    if (
        agree_traces + diverge_traces != distinct_traces
        or sum(diag_counts.values()) != distinct_traces
        or int(diag_counts.get("ok", 0)) != agree_traces
    ):
        oracle_invoked = False
        reasons.append(
            f"itree_oracle_not_invoked: agree_traces ({agree_traces}) + "
            f"diverge_traces ({diverge_traces}) != distinct_traces ({distinct_traces})"
        )
    if (
        kc_traces != distinct_traces
        or kc_divergences != diverge_traces
        or len(findings) != diverge_traces
    ):
        oracle_invoked = False
        reasons.append(
            f"itree_oracle_not_invoked: kernel_confirmed_traces ({kc_traces}), "
            f"kernel_confirmed_divergences ({kc_divergences}), findings ({len(findings)}) "
            f"do not match distinct_traces ({distinct_traces}) / diverge_traces ({diverge_traces})"
        )
    for f in findings:
        repro_p = Path(f["repro_path"])
        if not f.get("kernel_confirmed") or not repro_p.is_file():
            oracle_invoked = False
            reasons.append(
                f"itree_oracle_not_invoked: finding {f.get('finding_id')!r} missing "
                f"kernel confirmation or repro.rs ({repro_p})"
            )

    non_zero_compared = compared > 0 and distinct_traces > 0
    if not non_zero_compared:
        reasons.append(
            f"itree_zero_compared_items: compared_candidates={compared}, distinct_traces_checked={distinct_traces}"
        )

    plausible_wall_clock = elapsed_ms >= min_oracle_elapsed_ms
    if not plausible_wall_clock:
        reasons.append(
            f"itree_impossible_wall_clock: elapsed_ms ({elapsed_ms:.2f} ms) < min_oracle_elapsed_ms ({min_oracle_elapsed_ms:.2f} ms)"
        )

    seed_sensitive = True
    seed_hex = f"0x{itree_seed:08x}"
    prev_seed = ledger.get("last_itree_seed")
    prev_sig = ledger.get("last_itree_signature")
    cur_sig = itree_signature_for_seed_check(summary)
    if (
        isinstance(prev_seed, str)
        and prev_seed.lower() != seed_hex.lower()
        and isinstance(prev_sig, dict)
        and prev_sig == cur_sig
    ):
        seed_sensitive = False
        reasons.append(
            f"itree_identical_metrics_across_seeds: seed {seed_hex} produced identical trace metrics/mutators to prior seed {prev_seed}"
        )

    checks = {
        "itree_oracle_invoked": oracle_invoked,
        "itree_non_zero_compared": non_zero_compared,
        "itree_plausible_wall_clock": plausible_wall_clock,
        "itree_seed_sensitivity": seed_sensitive,
    }
    return RedFlagResult(
        passed=all(checks.values()),
        checks=checks,
        failure_reasons=reasons,
    )


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

    # 5. Oracle error count within threshold & `error` vs. `unsupported` boundary.
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

    boundary_ok, boundary_reasons = validate_error_vs_unsupported_boundary(
        summary, max_oracle_errors=max_oracle_errors
    )
    for br in boundary_reasons:
        if br not in reasons:
            reasons.append(br)

    checks = {
        "oracle_invoked": oracle_invoked,
        "non_zero_compared": non_zero_compared,
        "plausible_wall_clock": plausible_wall_clock,
        "seed_sensitivity": seed_sensitive,
        "oracle_error_threshold": within_error_threshold,
        "error_vs_unsupported_boundary": boundary_ok,
    }
    return RedFlagResult(
        passed=all(checks.values()),
        checks=checks,
        failure_reasons=reasons,
    )


ERROR_MASKED_AS_UNSUPPORTED_MARKERS: tuple[str, ...] = (
    "internal panic",
    "sigabrt",
    "sigsegv",
    "capture_failed",
    "capture_error",
    "miri_oracle_error",
    "oracle_error",
    "parse error",
    "syntax error",
    "malformed",
    "nat.shiftl exponent is too big",
    "lean crashed",
    "rustc crashed",
)

# Fields of a finding / item / diagnostic record that state its own classification.
_CLASSIFICATION_FIELDS: tuple[str, ...] = (
    "anneal_outcome",
    "anneal_lean_tag",
    "reason",
    "not_compared_reason",
    "verdict",
    "classification",
)

# Fields whose text is searched for crash / malformed-input markers.
_DIAGNOSTIC_TEXT_FIELDS: tuple[str, ...] = (
    *_CLASSIFICATION_FIELDS,
    "miri_outcome",
    "miri_excerpt",
    "diagnostic",
    "message",
    "error",
    "stderr",
)


def _record_bucket(item: dict[str, Any]) -> str:
    """Returns the bucket a record classifies itself into: an explicit not-compared
    reason / verdict when present (for example `miri_oracle_error` shadows an Anneal
    `unsupported` outcome under the comparator's precedence), otherwise its Anneal
    outcome and Lean tag."""
    for key in ("not_compared_reason", "reason", "classification", "verdict"):
        val = item.get(key)
        if isinstance(val, str) and val.strip():
            return val
    return " ".join(str(item.get(k, "")) for k in ("anneal_outcome", "anneal_lean_tag"))


def _int_field(counts: Any, key: str) -> int:
    if not isinstance(counts, dict):
        return 0
    val = counts.get(key, 0)
    return val if isinstance(val, int) and not isinstance(val, bool) else 0


def validate_error_vs_unsupported_boundary(
    summary: dict[str, Any],
    max_oracle_errors: int = DEFAULT_MAX_ORACLE_ERRORS,
) -> tuple[bool, list[str]]:
    """Enforces that malformed inputs, capture/Lean crashes, and oracle errors are
    classified as `error` rather than masked under `unsupported`.

    Three independent checks, all fail-closed:

    1. Oracle-error budget: the number of errored items (each lands in exactly one of
       `not_compared_reasons.miri_oracle_error` / `capture_failed` under the
       comparator's precedence, so they are not double counted; raw
       `miri_verdicts.error` / `anneal_outcomes.error` are used as lower bounds in
       case the not-compared map under-reports) must not exceed `max_oracle_errors`.
    2. Accounting invariants implied by `compare_miri_and_anneal`'s precedence
       (Miri error > capture/Lean error > external call > unsupported > fuel):
       every Miri error is a `miri_oracle_error`, every Anneal error is a
       `capture_failed` or shadowed by a Miri error, and `unsupported` never exceeds
       the Anneal `unsupported` outcomes. A violation means an error was routed into
       another bucket (`error_masked_as_unsupported`) or the counts are inconsistent
       (`error_accounting_mismatch`).
    3. Any finding, item report, not-compared item, or diagnostic whose *own*
       classification is `unsupported` but whose text carries a crash or
       malformed-input marker (`INTERNAL PANIC`, `SIGABRT`, `capture_failed`,
       `parse error`, `malformed`, ...) is rejected as `error_masked_as_unsupported`.
    """
    reasons: list[str] = []
    miri_verdicts = summary.get("miri_verdicts")
    anneal_outcomes = summary.get("anneal_outcomes")
    nc_reasons = summary.get("not_compared_reasons")

    miri_err = _int_field(miri_verdicts, "error")
    anneal_err = _int_field(anneal_outcomes, "error")
    anneal_unsupported = _int_field(anneal_outcomes, "unsupported")
    nc_miri_err = _int_field(nc_reasons, "miri_oracle_error")
    nc_cap_err = _int_field(nc_reasons, "capture_failed")
    nc_unsupported = _int_field(nc_reasons, "unsupported")

    # 1. Oracle-error budget over distinct errored items.
    errored_items = max(nc_miri_err + nc_cap_err, miri_err, anneal_err)
    if errored_items > max_oracle_errors:
        reasons.append(
            f"oracle_errors_exceeded: {errored_items} errored items (miri_oracle_error="
            f"{nc_miri_err}, capture_failed={nc_cap_err}, miri_verdicts.error={miri_err}, "
            f"anneal_outcomes.error={anneal_err}) > max_oracle_errors ({max_oracle_errors})"
        )

    # 2. Accounting invariants (only when the maps are present).
    have_maps = (
        isinstance(nc_reasons, dict)
        and isinstance(miri_verdicts, dict)
        and isinstance(anneal_outcomes, dict)
    )
    if have_maps:
        if miri_err > nc_miri_err:
            reasons.append(
                f"error_masked_as_unsupported: {miri_err - nc_miri_err} Miri oracle error(s) "
                f"not reported as not_compared_reasons.miri_oracle_error "
                f"(miri_verdicts.error={miri_err}, miri_oracle_error={nc_miri_err})"
            )
        elif nc_miri_err > miri_err:
            reasons.append(
                f"error_accounting_mismatch: not_compared_reasons.miri_oracle_error "
                f"({nc_miri_err}) > miri_verdicts.error ({miri_err})"
            )
        if anneal_err > nc_cap_err + nc_miri_err:
            reasons.append(
                f"error_masked_as_unsupported: {anneal_err - nc_cap_err - nc_miri_err} Anneal "
                f"capture/Lean error(s) not reported as capture_failed "
                f"(anneal_outcomes.error={anneal_err}, capture_failed={nc_cap_err}, "
                f"miri_oracle_error={nc_miri_err})"
            )
        if nc_cap_err > anneal_err:
            reasons.append(
                f"error_accounting_mismatch: not_compared_reasons.capture_failed "
                f"({nc_cap_err}) > anneal_outcomes.error ({anneal_err})"
            )
        if nc_unsupported > anneal_unsupported:
            reasons.append(
                f"error_masked_as_unsupported: not_compared_reasons.unsupported ({nc_unsupported}) > "
                f"anneal_outcomes.unsupported ({anneal_unsupported})"
            )

    # 3. Records classified as `unsupported` that carry crash / malformed markers.
    def _crash_marker(text: str) -> str | None:
        lowered = text.lower()
        for marker in ERROR_MASKED_AS_UNSUPPORTED_MARKERS:
            if marker in lowered:
                return marker
        return None

    for list_key in ("findings", "item_reports", "not_compared_items", "diagnostics"):
        items = summary.get(list_key)
        if not isinstance(items, list):
            continue
        for idx, item in enumerate(items):
            if isinstance(item, str):
                classification, text = item, item
                label: Any = idx
            elif isinstance(item, dict):
                classification = _record_bucket(item)
                text = " ".join(str(item.get(k, "")) for k in _DIAGNOSTIC_TEXT_FIELDS)
                label = item.get("fn_name", item.get("name", idx))
            else:
                continue
            if "unsupported" not in classification.lower():
                continue
            # Ignore the classification word itself; only other markers count.
            hit = _crash_marker(text)
            if hit is not None:
                reasons.append(
                    f"error_masked_as_unsupported: {list_key}[{idx}] ({label}) masks '{hit}' "
                    f"under unsupported"
                )

    failed = any(
        r.startswith(("error_masked_as_unsupported", "error_accounting_mismatch"))
        for r in reasons
    )
    return (not failed and errored_items <= max_oracle_errors), reasons


def _is_valid_iso_date(raw: str) -> bool:
    if not isinstance(raw, str) or len(raw) != 10:
        return False
    try:
        datetime.date.fromisoformat(raw)
        return True
    except ValueError:
        return False


def _is_well_formed_quarantine_token(token: str) -> bool:
    if not isinstance(token, str):
        return False
    clean = token.strip()
    if not clean or any(ch.isspace() for ch in clean):
        return False
    parts = clean.split(":")
    if any(not p.strip() for p in parts):
        return False
    return True


def quarantine_entry_harness(token: str) -> str | None:
    """Returns `"itree"` / `"miri"` when a quarantine token can only match findings of
    that harness, or `None` when it could match either (for example a bare seed name)."""
    if "itree_" in token or "TraceReplayDiag." in token:
        return "itree"
    parts = token.split(":")
    if any(p in VALID_DIVERGENCE_CLASSES for p in parts) or "MirDiffTag." in token:
        return "miri"
    return None


def verify_no_stale_quarantine_or_known_bugs(
    quarantine_file: Path | None = None,
    manifest_path: Path | None = None,
    ledger: dict[str, Any] | None = None,
    evaluated_fingerprints: set[str] | list[str] | None = None,
    manifest_eval_results: dict[str, Any] | None = None,
    reference_date: str | None = None,
    observed_quarantine_keys: set[str] | list[str] | None = None,
    covered_harnesses: set[str] | list[str] | None = None,
) -> dict[str, Any]:
    """Fail-closed ratchet audit flagging stale `quarantine.toml` entries and stale
    `tests/miri-diff/manifest.toml` `known_anneal_bug` entries.

    The "0 matching divergences" staleness rule only applies when an evaluated run
    was supplied (`evaluated_fingerprints` and/or `observed_quarantine_keys`, the
    latter being every key `deduplicate_and_quarantine_findings` /
    `deduplicate_and_quarantine_itree_findings` would match a quarantine token
    against) and only to entries whose harness the run covered (`covered_harnesses`,
    `{"miri", "itree"}` when omitted): a `--miri-only` run says nothing about ITree
    quarantine entries.
    """
    ref_date = reference_date if reference_date is not None else utc_date_prefix()
    ledger_obj = ledger if isinstance(ledger, dict) else {}
    eval_fp_set: set[str] | None = (
        set(evaluated_fingerprints) if evaluated_fingerprints is not None else None
    )

    resolved_fps: set[str] = set()
    for hist_key in ("resolved_history", "resolved_fingerprints"):
        hist = ledger_obj.get(hist_key, [])
        if isinstance(hist, list):
            for item in hist:
                if isinstance(item, str) and item.strip():
                    resolved_fps.add(item.strip())
                elif isinstance(item, dict) and isinstance(item.get("fingerprint"), str):
                    resolved_fps.add(item["fingerprint"].strip())
    active_fps: set[str] = set(
        fp for fp in ledger_obj.get("active_fingerprints", []) if isinstance(fp, str)
    )
    active_fps.update(
        fp for fp in ledger_obj.get("quarantined_fingerprints", []) if isinstance(fp, str)
    )
    if eval_fp_set is not None:
        active_fps.update(eval_fp_set)
    observed_keys: set[str] | None = (
        set(observed_quarantine_keys) if observed_quarantine_keys is not None else None
    )
    if observed_keys is not None:
        active_fps.update(observed_keys)
    covered: set[str] = (
        set(covered_harnesses) if covered_harnesses is not None else {"miri", "itree"}
    )
    run_evaluated = eval_fp_set is not None or observed_keys is not None

    stale_quarantine: list[dict[str, Any]] = []
    checked_quarantine_count = 0

    if quarantine_file is not None:
        if not quarantine_file.is_file():
            stale_quarantine.append(
                {
                    "source": str(quarantine_file),
                    "entry": "<file>",
                    "reason": f"quarantine_file_missing: {quarantine_file}",
                }
            )
        else:
            raw_text = quarantine_file.read_text(encoding="utf-8")
            try:
                if quarantine_file.suffix.lower() == ".toml":
                    q_data = tomllib.loads(raw_text)
                else:
                    q_data = json.loads(raw_text)
            except (tomllib.TOMLDecodeError, json.JSONDecodeError) as e:
                q_data = None
                stale_quarantine.append(
                    {
                        "source": str(quarantine_file),
                        "entry": "<parse>",
                        "reason": f"malformed_quarantine_file: {e}",
                    }
                )

            raw_entries: list[Any] = []
            if isinstance(q_data, list):
                raw_entries.extend(q_data)
            elif isinstance(q_data, dict):
                for key in ("quarantined", "entries", "rules", "fingerprints"):
                    val = q_data.get(key)
                    if isinstance(val, list):
                        raw_entries.extend(val)

            for idx, entry in enumerate(raw_entries):
                checked_quarantine_count += 1
                if isinstance(entry, str):
                    fp = entry.strip()
                    expires = None
                elif isinstance(entry, dict):
                    raw_fp = entry.get("fingerprint", entry.get("id", ""))
                    fp = raw_fp.strip() if isinstance(raw_fp, str) else ""
                    expires = entry.get("expires")
                else:
                    stale_quarantine.append(
                        {
                            "source": str(quarantine_file),
                            "entry": repr(entry),
                            "reason": f"malformed_quarantine_entry[{idx}]: expected string or table",
                        }
                    )
                    continue

                if not _is_well_formed_quarantine_token(fp) or (
                    isinstance(entry, dict) and ":" not in fp
                ):
                    stale_quarantine.append(
                        {
                            "source": str(quarantine_file),
                            "entry": fp or f"<entry[{idx}]>",
                            "reason": f"malformed_or_missing_fingerprint: {fp!r}",
                        }
                    )
                    continue

                if expires is not None:
                    if not isinstance(expires, str) or not _is_valid_iso_date(expires):
                        stale_quarantine.append(
                            {
                                "source": str(quarantine_file),
                                "entry": fp,
                                "reason": f"malformed_expires_date: {expires!r}",
                            }
                        )
                    elif expires < ref_date:
                        stale_quarantine.append(
                            {
                                "source": str(quarantine_file),
                                "entry": fp,
                                "reason": f"expired_quarantine_entry: expires {expires} < {ref_date}",
                            }
                        )

                if fp in resolved_fps and fp not in active_fps:
                    stale_quarantine.append(
                        {
                            "source": str(quarantine_file),
                            "entry": fp,
                            "reason": "already_resolved_in_ledger: fingerprint in resolved_history and absent from active findings",
                        }
                    )

                entry_harness = quarantine_entry_harness(fp)
                harness_covered = entry_harness is None or entry_harness in covered
                if run_evaluated and harness_covered:
                    matched_eval = (observed_keys is not None and fp in observed_keys) or any(
                        obs == fp
                        or obs.startswith(f"{fp}:")
                        or f":{fp}:" in obs
                        for obs in (eval_fp_set or set())
                    )
                    if not matched_eval:
                        stale_quarantine.append(
                            {
                                "source": str(quarantine_file),
                                "entry": fp,
                                "reason": "unobserved_quarantine_entry: 0 matching divergences in evaluated run",
                            }
                        )

    stale_manifest: list[dict[str, Any]] = []
    checked_known_bug_count = 0

    if manifest_path is not None:
        if not manifest_path.is_file():
            stale_manifest.append(
                {
                    "source": str(manifest_path),
                    "entry": "<file>",
                    "reason": f"manifest_file_missing: {manifest_path}",
                }
            )
        else:
            try:
                m_data = tomllib.loads(manifest_path.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as e:
                m_data = None
                stale_manifest.append(
                    {
                        "source": str(manifest_path),
                        "entry": "<parse>",
                        "reason": f"malformed_manifest_toml: {e}",
                    }
                )

            if isinstance(m_data, dict):
                for idx, test_entry in enumerate(m_data.get("tests", [])):
                    if not isinstance(test_entry, dict) or "known_anneal_bug" not in test_entry:
                        continue
                    checked_known_bug_count += 1
                    test_name = test_entry.get("name")
                    if not isinstance(test_name, str) or not test_name.strip():
                        stale_manifest.append(
                            {
                                "source": str(manifest_path),
                                "entry": f"tests[{idx}]",
                                "reason": "missing_test_name_on_known_anneal_bug",
                            }
                        )
                        continue
                    bug = test_entry.get("known_anneal_bug")
                    if not isinstance(bug, dict):
                        stale_manifest.append(
                            {
                                "source": str(manifest_path),
                                "entry": test_name,
                                "reason": "malformed_known_anneal_bug: expected table",
                            }
                        )
                        continue

                    obs_tag = bug.get("observed_anneal_tag")
                    reason_text = bug.get("summary") or bug.get("reason")
                    if not isinstance(obs_tag, str) or not obs_tag.strip():
                        stale_manifest.append(
                            {
                                "source": str(manifest_path),
                                "entry": test_name,
                                "reason": "missing_known_anneal_bug_metadata: missing observed_anneal_tag",
                            }
                        )
                    if not isinstance(reason_text, str) or not reason_text.strip():
                        stale_manifest.append(
                            {
                                "source": str(manifest_path),
                                "entry": test_name,
                                "reason": "missing_known_anneal_bug_metadata: missing summary/reason",
                            }
                        )

                    if isinstance(manifest_eval_results, dict) and test_name in manifest_eval_results:
                        ev = manifest_eval_results[test_name]
                        if isinstance(ev, str):
                            ev_lower = ev.strip().lower()
                            if ev_lower in ("agree", "pass", "pass:unit") or ev_lower.startswith("pass:scalar"):
                                stale_manifest.append(
                                    {
                                        "source": str(manifest_path),
                                        "entry": test_name,
                                        "reason": f"stale_known_anneal_bug_now_passes: observed {ev!r}",
                                    }
                                )
                            elif isinstance(obs_tag, str) and obs_tag.strip():
                                if normalize_anneal_tag(ev) != normalize_anneal_tag(obs_tag):
                                    stale_manifest.append(
                                        {
                                            "source": str(manifest_path),
                                            "entry": test_name,
                                            "reason": f"stale_known_anneal_bug_tag_mismatch: expected {obs_tag!r}, got {ev!r}",
                                        }
                                    )
                        elif isinstance(ev, dict):
                            verdict = str(ev.get("verdict", "")).strip().lower()
                            actual_tag = ev.get(
                                "observed_anneal_tag",
                                ev.get("anneal_outcome", ev.get("anneal_lean_tag")),
                            )
                            if verdict == "agree":
                                stale_manifest.append(
                                    {
                                        "source": str(manifest_path),
                                        "entry": test_name,
                                        "reason": "stale_known_anneal_bug_now_passes: verdict is Agree",
                                    }
                                )
                            elif (
                                isinstance(obs_tag, str)
                                and obs_tag.strip()
                                and isinstance(actual_tag, str)
                                and actual_tag.strip()
                                and normalize_anneal_tag(actual_tag) != normalize_anneal_tag(obs_tag)
                            ):
                                stale_manifest.append(
                                    {
                                        "source": str(manifest_path),
                                        "entry": test_name,
                                        "reason": (
                                            f"stale_known_anneal_bug_tag_mismatch: expected {obs_tag!r}, "
                                            f"got {actual_tag!r}"
                                        ),
                                    }
                                )

    stale_entries = [*stale_quarantine, *stale_manifest]
    return {
        "passed": len(stale_entries) == 0,
        "reference_date": ref_date,
        "checked_quarantine_count": checked_quarantine_count,
        "checked_known_bug_count": checked_known_bug_count,
        "stale_quarantine_entries": stale_quarantine,
        "stale_known_anneal_bugs": stale_manifest,
        "stale_entries": stale_entries,
    }


def _parse_src_pos(raw: str) -> tuple[str, int, int] | None:
    """Parses `file:line:col` (a Miri `SourcePos::display_short`)."""
    parts = raw.rsplit(":", 2)
    if len(parts) != 3 or not parts[1].isdigit() or not parts[2].isdigit():
        return None
    return parts[0], int(parts[1]), int(parts[2])


def _parse_src_span(raw: str) -> tuple[str, int, int, int, int] | None:
    """Parses `file:start_line:start_col:end_line:end_col` (`SourceSpan::display_short`)."""
    parts = raw.rsplit(":", 4)
    if len(parts) != 5 or not all(p.isdigit() for p in parts[1:]):
        return None
    return parts[0], int(parts[1]), int(parts[2]), int(parts[3]), int(parts[4])


def _span_contains_pos(span_raw: str, pos_raw: str) -> bool:
    span = _parse_src_span(span_raw)
    pos = _parse_src_pos(pos_raw)
    if span is None or pos is None or span[0] != pos[0]:
        return False
    return (span[1], span[2]) <= (pos[1], pos[2]) <= (span[3], span[4])


def classify_oracle_outcome_tags(miri_outcome: str, anneal_outcome: str) -> tuple[str, str]:
    """Python model of `compare_miri_and_anneal` over harness summary tags.

    Returns `("agree", "")`, `("diverge", <divergence class>)`, or
    `("not_compared", <not-compared reason>)`, using the same precedence as the Rust
    comparator: a Miri oracle error wins over everything, then Anneal capture/Lean
    errors, external calls, `unsupported`, and fuel exhaustion; only then are executed
    outcomes compared (with span containment for panic and UB locations).
    """
    if miri_outcome.startswith("oracle_error"):
        return "not_compared", "miri_oracle_error"
    for prefix, reason in (
        ("capture_error", "capture_failed"),
        ("externalCall", "external_call"),
        ("unsupported", "unsupported"),
        ("outOfFuel", "out_of_fuel"),
    ):
        if anneal_outcome.startswith(prefix):
            return "not_compared", reason

    m_kind, _, m_loc = miri_outcome.partition("@")
    a_kind, _, a_loc = anneal_outcome.partition("@")
    m_pass = m_kind.startswith("pass:")
    a_pass = a_kind.startswith("pass:") or a_kind == "abort"

    if m_pass:
        if a_kind == "panic":
            return "diverge", "return_vs_panic"
        if a_kind == "ub":
            return "diverge", "false_positive_ub"
        if a_kind.startswith("pass:") and m_kind == a_kind:
            return "agree", ""
        return "diverge", "wrong_value"
    if m_kind == "panic":
        if a_pass:
            return "diverge", "panic_vs_return"
        if a_kind == "ub":
            return "diverge", "false_positive_ub"
        if _span_contains_pos(a_loc, m_loc):
            return "agree", ""
        return "diverge", "panic_site_mismatch"
    if m_kind == "ub":
        if a_kind == "ub":
            if _span_contains_pos(a_loc, m_loc):
                return "agree", ""
            return "diverge", "ub_location_mismatch"
        return "diverge", "missed_ub"
    return "not_compared", "miri_oracle_error"


def _bump(counts: dict[str, int], key: str) -> None:
    counts[key] = counts.get(key, 0) + 1


def build_simulated_miri_summary(
    probe_id: str,
    miri_outcome: str,
    anneal_outcome: str,
    anneal_lean_tag: str,
    repro_path: Path,
    background_agreeing: int = 3,
    diagnostics: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Builds a self-consistent `miri-difftest` summary for one probe candidate plus
    `background_agreeing` agreeing candidates, deriving the probe's verdict with
    `classify_oracle_outcome_tags` exactly as the Rust harness would.
    """
    total = background_agreeing + 1
    miri_verdicts = {"pass": background_agreeing, "panic": 0, "ub": 0, "error": 0}
    anneal_outcomes = {
        "pass": background_agreeing,
        "panic": 0,
        "ub": 0,
        "unsupported": 0,
        "out_of_fuel": 0,
        "external_call": 0,
        "error": 0,
    }
    m_kind = miri_outcome.partition("@")[0]
    _bump(
        miri_verdicts,
        "error"
        if miri_outcome.startswith("oracle_error")
        else ("pass" if m_kind.startswith("pass:") else m_kind),
    )
    a_kind = anneal_outcome.partition("@")[0]
    if anneal_outcome.startswith("capture_error"):
        _bump(anneal_outcomes, "error")
    elif anneal_outcome.startswith("externalCall"):
        _bump(anneal_outcomes, "external_call")
    elif anneal_outcome.startswith("outOfFuel"):
        _bump(anneal_outcomes, "out_of_fuel")
    elif a_kind == "abort":
        _bump(anneal_outcomes, "panic")
    elif a_kind.startswith("pass:"):
        _bump(anneal_outcomes, "pass")
    else:
        _bump(anneal_outcomes, a_kind)

    verdict, detail = classify_oracle_outcome_tags(miri_outcome, anneal_outcome)
    div_map = {k: 0 for k in VALID_DIVERGENCE_CLASSES}
    nc_reasons = {k: 0 for k in VALID_NOT_COMPARED_REASONS}
    findings: list[dict[str, Any]] = []
    if verdict == "diverge":
        div_map[detail] = 1
        findings.append(
            {
                "finding_id": f"finding_0000_probe_{probe_id}",
                "fn_name": f"probe_{probe_id}",
                "seed_name": f"probe_{probe_id}",
                "applied_mutators": [],
                "divergence_class": detail,
                "miri_outcome": miri_outcome,
                "anneal_outcome": anneal_outcome,
                "anneal_lean_tag": anneal_lean_tag,
                "miri_excerpt": f"semantic mutant probe {probe_id}",
                "repro_path": str(repro_path),
                "kernel_confirmed": True,
            }
        )
    elif verdict == "not_compared":
        nc_reasons[detail] = 1
    compared = background_agreeing + (0 if verdict == "not_compared" else 1)
    summary: dict[str, Any] = {
        "harness": "miri-difftest",
        "oracle_comparison": "performed",
        "mode": "seeded",
        "seed": "0x5eed0001",
        "batches": 1,
        "batch_size": total,
        "total_candidates": total,
        "compiled_candidates": total,
        "compile_failed_candidates": 0,
        "compared_candidates": compared,
        "agree_count": background_agreeing + (1 if verdict == "agree" else 0),
        "diverge_count": len(findings),
        "not_compared_count": 1 if verdict == "not_compared" else 0,
        "kernel_confirmed_divergences": len(findings),
        "miri_verdicts": miri_verdicts,
        "anneal_outcomes": anneal_outcomes,
        "divergence_classes": div_map,
        "not_compared_reasons": nc_reasons,
        "unmodeled_external_calls": {},
        "mutator_applications": {"ArithmeticCastMutator": total},
        "findings": findings,
        "elapsed_ms": 10.0 * DEFAULT_MIN_ORACLE_ELAPSED_MS,
    }
    if diagnostics:
        summary["diagnostics"] = diagnostics
    return summary


def campaign_exit_for_miri_summary(summary: dict[str, Any]) -> tuple[int, str, str]:
    """Runs a performed `miri-difftest` summary through the campaign's verdict pipeline
    (`validate_performed_miri_summary`, `evaluate_miri_red_flags` including the
    `error` vs. `unsupported` boundary, and `deduplicate_and_quarantine_findings`).

    Returns `(exit_code, kill_class, detail)`: `EXIT_HARNESS_FAILED` with
    `"harness_error"`, `EXIT_DIVERGENCE_DETECTED` with the unquarantined divergence
    class, or `EXIT_SUCCESS` with `"agree"`.
    """
    valid, reason = validate_performed_miri_summary(summary)
    if not valid:
        return EXIT_HARNESS_FAILED, "harness_error", reason
    rf = evaluate_miri_red_flags(
        summary, 0x5EED0001, {}, DEFAULT_MIN_ORACLE_ELAPSED_MS, DEFAULT_MAX_ORACLE_ERRORS
    )
    if not rf.passed:
        return EXIT_HARNESS_FAILED, "harness_error", "; ".join(rf.failure_reasons)
    _, unquarantined, _ = deduplicate_and_quarantine_findings(summary["findings"], set(), set())
    if unquarantined:
        return EXIT_DIVERGENCE_DETECTED, unquarantined[0].divergence_class, unquarantined[0].fingerprint
    return EXIT_SUCCESS, "agree", "no divergence"


SEEDED_SEMANTIC_MUTANTS: tuple[dict[str, Any], ...] = (
    {
        "id": "bool_valid_range",
        "name": "bool_valid_range",
        "bug_class": "scalar_validity_bool_range",
        "target_component": "Trusted.Rustc.V2026_06_01.MirSemantics.BitValidity",
        "description": "Omit bool validRange [0, 1] check on typed scalar load of 2u8 as bool",
        "expected_kill_classes": ("missed_ub",),
        "reference_miri_outcome": "ub@src/lib.rs:5:5",
        "baseline_anneal_outcome": "ub@src/lib.rs:5:5:5:13",
        "baseline_anneal_lean_tag": "MirDiffTag.ub",
        "mutant_variants": (
            {
                "label": "validity_check_omitted",
                "anneal_outcome": "pass:scalar:2:4",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 2 4)",
            },
        ),
        "probe_rust_source": (
            "pub fn probe_bool_valid_range() -> u32 {\n"
            "    let mut b: bool = false;\n"
            "    let p: *mut u8 = (&raw mut b) as *mut u8;\n"
            "    unsafe { *p = 2u8; }\n"
            "    b as u32\n"
            "}\n"
        ),
    },
    {
        "id": "storage_dead_tag",
        "name": "storage_dead_tag",
        "bug_class": "dangling_pointer_after_storage_dead",
        "target_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Memory",
        "description": "Omit allocation liveness / StorageDead deallocation check on raw pointer dereference",
        "expected_kill_classes": ("missed_ub",),
        "reference_miri_outcome": "ub@src/lib.rs:6:14",
        "baseline_anneal_outcome": "ub@src/lib.rs:6:14:6:24",
        "baseline_anneal_lean_tag": "MirDiffTag.ub",
        "mutant_variants": (
            {
                "label": "liveness_check_omitted",
                "anneal_outcome": "pass:scalar:42:4",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 42 4)",
            },
        ),
        "probe_rust_source": (
            "pub fn probe_storage_dead_tag() -> u32 {\n"
            "    let dangling: *const u32 = {\n"
            "        let dead_local: u32 = 42u32;\n"
            "        &raw const dead_local\n"
            "    };\n"
            "    unsafe { *dangling }\n"
            "}\n"
        ),
    },
    {
        "id": "provenance_frag",
        "name": "provenance_frag",
        "bug_class": "partial_pointer_overwrite_provenance_strip",
        "target_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Memory",
        "description": "Omit pointer fragment provenance invalidation on partial byte overwrite",
        "expected_kill_classes": ("missed_ub", "false_positive_ub"),
        "reference_miri_outcome": "ub@src/lib.rs:8:9",
        "baseline_anneal_outcome": "ub@src/lib.rs:8:9:8:11",
        "baseline_anneal_lean_tag": "MirDiffTag.ub",
        "mutant_variants": (
            {
                "label": "fragment_provenance_check_omitted",
                "anneal_outcome": "pass:scalar:7:4",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 7 4)",
            },
        ),
        "probe_rust_source": (
            "pub fn probe_provenance_frag() -> u32 {\n"
            "    let x: u32 = 7u32;\n"
            "    let mut p: *const u32 = &raw const x;\n"
            "    let byte_ptr: *mut u8 = (&raw mut p) as *mut u8;\n"
            "    unsafe {\n"
            "        let b0: u8 = *byte_ptr;\n"
            "        *byte_ptr = b0;\n"
            "        *p\n"
            "    }\n"
            "}\n"
        ),
    },
    {
        "id": "div_by_zero",
        "name": "div_by_zero",
        "bug_class": "checked_div_rem_zero_and_int_min_overflow",
        "target_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Eval",
        "description": "Omit divisor == 0 and INT_MIN / -1 guard in checked integer division",
        "expected_kill_classes": ("panic_vs_return", "wrong_value", "missed_ub"),
        "reference_miri_outcome": "panic@src/lib.rs:4:5",
        "baseline_anneal_outcome": "panic@src/lib.rs:4:5:4:14",
        "baseline_anneal_lean_tag": "MirDiffTag.panic",
        "mutant_variants": (
            {
                "label": "zero_divisor_guard_omitted",
                "anneal_outcome": "pass:scalar:0:4",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 0 4)",
            },
        ),
        "probe_rust_source": (
            "pub fn probe_div_by_zero() -> u32 {\n"
            "    let num: u32 = 100u32;\n"
            "    let den: u32 = 0u32;\n"
            "    num / den\n"
            "}\n"
        ),
    },
    {
        "id": "wide_shift",
        "name": "wide_shift",
        "bug_class": "wide_bitvec_shift_exponent_bounds_guard",
        "target_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Eval",
        "description": "Omit rhs.toNat < w guard on 64/128-bit shift with rhs >= 2^32 (GMP lean_nat_shiftl abort)",
        "expected_kill_classes": ("missed_ub", "harness_error"),
        "reference_miri_outcome": "ub@src/lib.rs:4:14",
        "baseline_anneal_outcome": "ub@src/lib.rs:4:14:4:36",
        "baseline_anneal_lean_tag": "MirDiffTag.ub",
        "mutant_variants": (
            {
                # Without the guard, `lean_nat_shiftl` aborts the Lean probe process.
                "label": "guard_omitted_lean_abort",
                "anneal_outcome": "capture_error:INTERNAL PANIC: Nat.shiftl exponent is too big (SIGABRT)",
                "anneal_lean_tag": "none",
            },
            {
                # The same abort misreported as an unmodeled construct must still fail.
                "label": "guard_omitted_abort_masked_as_unsupported",
                "anneal_outcome": "unsupported@src/lib.rs:4:14:4:36",
                "anneal_lean_tag": "MirDiffTag.unsupported",
                "diagnostics": (
                    {
                        "fn_name": "probe_wide_shift",
                        "not_compared_reason": "unsupported",
                        "message": "SIGABRT: INTERNAL PANIC: Nat.shiftl exponent is too big",
                    },
                ),
            },
            {
                # A guard that silently masks the exponent returns a value instead of UB.
                "label": "guard_masks_exponent_silently",
                "anneal_outcome": "pass:scalar:1:8",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 1 8)",
            },
        ),
        "probe_rust_source": (
            "pub fn probe_wide_shift() -> u64 {\n"
            "    let lhs: u64 = 1u64;\n"
            "    let rhs: u64 = 1u64 << 32;\n"
            "    unsafe { unchecked_shl(lhs, rhs) }\n"
            "}\n"
        ),
    },
)


def _simulate_mutant_through_campaign_pipeline(mutant: dict[str, Any]) -> dict[str, Any]:
    """Differential (baseline vs. mutant) simulation of one seeded semantic mutant.

    The probe is first evaluated with the *unmutated* Anneal semantics
    (`baseline_anneal_outcome`), which must agree with the reference Miri outcome and
    pass the full campaign pipeline with `EXIT_SUCCESS`; otherwise the probe proves
    nothing and the mutant is reported as not killed. Each mutant variant (the Anneal
    outcome with the guard omitted or mutated) must then be rejected by the campaign
    pipeline (`EXIT_DIVERGENCE_DETECTED` or `EXIT_HARNESS_FAILED`) with an expected kill
    class. Verdicts are derived by `classify_oracle_outcome_tags`, never hard-coded.
    """
    mutant_id = str(mutant["id"])
    expected = tuple(mutant.get("expected_kill_classes", ()))
    miri_outcome = str(mutant["reference_miri_outcome"])
    with tempfile.TemporaryDirectory(prefix=f"anneal-mutant-{mutant_id}-") as tmp:
        repro_path = Path(tmp) / "repro.rs"
        repro_path.write_text(str(mutant["probe_rust_source"]), encoding="utf-8")

        baseline_summary = build_simulated_miri_summary(
            mutant_id,
            miri_outcome,
            str(mutant["baseline_anneal_outcome"]),
            str(mutant["baseline_anneal_lean_tag"]),
            repro_path,
        )
        base_exit, base_class, base_detail = campaign_exit_for_miri_summary(baseline_summary)
        result: dict[str, Any] = {
            "id": mutant_id,
            "baseline_verdict": classify_oracle_outcome_tags(
                miri_outcome, str(mutant["baseline_anneal_outcome"])
            )[0],
            "baseline_exit_code": base_exit,
            "variants": [],
        }
        if base_exit != EXIT_SUCCESS:
            result.update(
                killed=False,
                kill_class="baseline_not_clean",
                exit_code=base_exit,
                detail=f"unmutated semantics fail the probe ({base_class}): {base_detail}",
            )
            return result

        variant_results: list[dict[str, Any]] = []
        for variant in mutant.get("mutant_variants", ()):
            diagnostics = [dict(d) for d in variant.get("diagnostics", ())]
            summary = build_simulated_miri_summary(
                mutant_id,
                miri_outcome,
                str(variant["anneal_outcome"]),
                str(variant["anneal_lean_tag"]),
                repro_path,
                diagnostics=diagnostics or None,
            )
            v_exit, v_class, v_detail = campaign_exit_for_miri_summary(summary)
            v_killed = v_exit in (EXIT_DIVERGENCE_DETECTED, EXIT_HARNESS_FAILED) and (
                not expected or v_class in expected
            )
            variant_results.append(
                {
                    "label": str(variant.get("label", "")),
                    "verdict": classify_oracle_outcome_tags(
                        miri_outcome, str(variant["anneal_outcome"])
                    ),
                    "exit_code": v_exit,
                    "kill_class": v_class,
                    "killed": v_killed,
                    "detail": v_detail,
                }
            )
        result["variants"] = variant_results
        all_killed = bool(variant_results) and all(v["killed"] for v in variant_results)
        survivors = [v for v in variant_results if not v["killed"]]
        first = survivors[0] if survivors else variant_results[0] if variant_results else None
        result.update(
            killed=all_killed,
            kill_class=(first["kill_class"] if first else "no_variants"),
            exit_code=(first["exit_code"] if first else EXIT_SUCCESS),
        )
        if survivors:
            result["survived_variants"] = [v["label"] for v in survivors]
        return result


def _normalize_evaluator_result(
    mutant_id: str, expected_classes: tuple[str, ...], raw_res: Any
) -> dict[str, Any]:
    """Normalizes a custom evaluator's result (bool, exit code, verdict string, or dict)."""
    if isinstance(raw_res, bool):
        return {
            "id": mutant_id,
            "killed": raw_res,
            "kill_class": expected_classes[0] if (raw_res and expected_classes) else "survived",
            "exit_code": EXIT_DIVERGENCE_DETECTED if raw_res else EXIT_SUCCESS,
        }
    if isinstance(raw_res, int):
        is_killed = raw_res in (EXIT_DIVERGENCE_DETECTED, EXIT_HARNESS_FAILED)
        return {
            "id": mutant_id,
            "killed": is_killed,
            "kill_class": (
                expected_classes[0]
                if (is_killed and expected_classes)
                else ("harness_error" if is_killed else "survived")
            ),
            "exit_code": raw_res,
        }
    if isinstance(raw_res, str):
        clean = raw_res.strip().lower()
        is_killed = clean not in ("agree", "pass", "survived", "ok", "")
        return {
            "id": mutant_id,
            "killed": is_killed,
            "kill_class": raw_res.strip() if is_killed else "survived",
            "exit_code": EXIT_DIVERGENCE_DETECTED if is_killed else EXIT_SUCCESS,
        }
    if isinstance(raw_res, dict):
        if "killed" in raw_res:
            is_killed = bool(raw_res["killed"])
            k_class = str(
                raw_res.get(
                    "kill_class",
                    expected_classes[0] if (is_killed and expected_classes) else "survived",
                )
            )
            exit_c = int(
                raw_res.get("exit_code", EXIT_DIVERGENCE_DETECTED if is_killed else EXIT_SUCCESS)
            )
        elif "verdict" in raw_res:
            verdict_str = str(raw_res["verdict"]).strip().lower()
            is_killed = verdict_str in ("diverge", "error", "harness_error")
            k_class = str(
                raw_res.get(
                    "divergence_class",
                    raw_res.get("kill_class", "harness_error" if is_killed else "survived"),
                )
            )
            exit_c = EXIT_DIVERGENCE_DETECTED if is_killed else EXIT_SUCCESS
        elif "diverge_count" in raw_res or "miri_verdicts" in raw_res:
            exit_c, k_class, _ = campaign_exit_for_miri_summary(raw_res)
            is_killed = exit_c in (EXIT_DIVERGENCE_DETECTED, EXIT_HARNESS_FAILED)
            if not is_killed:
                k_class = "survived"
        else:
            is_killed = False
            k_class = "survived"
            exit_c = EXIT_SUCCESS
        return {"id": mutant_id, "killed": is_killed, "kill_class": k_class, "exit_code": exit_c}
    return {"id": mutant_id, "killed": False, "kill_class": "survived", "exit_code": EXIT_SUCCESS}


def run_semantic_mutant_self_check(
    evaluator: Any = None,
    mutants: tuple[dict[str, Any], ...] | list[dict[str, Any]] = SEEDED_SEMANTIC_MUTANTS,
) -> dict[str, Any]:
    """Runs all 5 seeded semantic mutant probes (`bool_valid_range`, `storage_dead_tag`,
    `provenance_frag`, `div_by_zero`, `wide_shift`) through the campaign oracle verdict
    pipeline and fails closed (`EXIT_HARNESS_FAILED = 2`) if any mutant survives.

    Without `evaluator`, each mutant is checked differentially by
    `_simulate_mutant_through_campaign_pipeline` (unmutated semantics must pass, every
    mutated variant must be rejected). A custom `evaluator(mutant)` (for example a live
    run against mutated Lean sources) may return a bool, an exit code, a verdict string,
    a result dict, or a full `miri-difftest` summary; an exception raised by the
    evaluator counts as a surviving mutant (`evaluator_error`), never as a kill.
    """
    killed_mutants: list[str] = []
    survived_mutants: list[str] = []
    per_mutant_results: list[dict[str, Any]] = []

    for mutant in mutants:
        mutant_id = str(mutant["id"])
        expected_classes = tuple(mutant.get("expected_kill_classes", ()))
        if evaluator is None:
            outcome = _simulate_mutant_through_campaign_pipeline(mutant)
        else:
            try:
                raw_res = evaluator(mutant)
            except Exception as e:  # noqa: BLE001 - fail closed on any evaluator crash
                outcome = {
                    "id": mutant_id,
                    "killed": False,
                    "kill_class": "evaluator_error",
                    "exit_code": EXIT_INTERNAL_ERROR,
                    "detail": f"{type(e).__name__}: {e}",
                }
            else:
                outcome = _normalize_evaluator_result(mutant_id, expected_classes, raw_res)

        if (
            outcome["killed"]
            and expected_classes
            and outcome.get("kill_class") not in expected_classes
        ):
            outcome["killed"] = False
            outcome["unexpected_kill_class"] = outcome.get("kill_class")

        per_mutant_results.append(outcome)
        if outcome["killed"]:
            killed_mutants.append(mutant_id)
        else:
            survived_mutants.append(mutant_id)

    total = len(mutants)
    passed = len(survived_mutants) == 0 and len(killed_mutants) == total and total > 0
    return {
        "passed": passed,
        "total_mutants": total,
        "killed_count": len(killed_mutants),
        "killed_mutants": killed_mutants,
        "survived_mutants": survived_mutants,
        "results": per_mutant_results,
        "exit_code": EXIT_SUCCESS if passed else EXIT_HARNESS_FAILED,
    }


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


def _quarantine_table_token(item: dict[str, Any], today: str) -> str | None:
    """Returns the token of a `{fingerprint|id, expires?, reason?}` quarantine table,
    or `None` when the entry must not suppress findings (missing token, malformed or
    past `expires`): an expired quarantine fails open to reporting, never to hiding."""
    token = item.get("fingerprint", item.get("id"))
    if not isinstance(token, str) or not token.strip():
        return None
    expires = item.get("expires")
    if expires is not None and (
        not isinstance(expires, str) or not _is_valid_iso_date(expires) or expires < today
    ):
        return None
    return token.strip()


def load_quarantine_rules(quarantine_file: Path | None) -> set[str]:
    """Loads quarantine tokens from a JSON or TOML file.

    Entries may be plain strings or `{fingerprint = "...", expires = "YYYY-MM-DD",
    reason = "..."}` tables (the format audited by
    `verify_no_stale_quarantine_or_known_bugs`); expired or malformed table entries
    are ignored so they can never suppress a finding."""
    today = utc_date_prefix()
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
            elif isinstance(item, dict):
                token = _quarantine_table_token(item, today)
                if token is not None:
                    rules.add(token)
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
                        elif isinstance(item, dict):
                            token = _quarantine_table_token(item, today)
                            if token is not None:
                                rules.add(token)
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
            for tok in (
                "__miri_ptr_",
                "__oob_",
                "__neg_",
                "__ptr_pair",
                "__base_ptr",
                "__null_p",
                "__unaligned_",
                "__u8_base",
            )
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
                "__panic_arr",
                "__panic_idx",
            )
        ):
            return "BitValidityTransmuteMutator"
        if any(
            tok in fault_text
            for tok in (
                "__miri_arith_",
                "__miri_wide",
                "__ovf_",
                "__udf_",
                "__div_",
                "__shl_",
                "__ub_",
            )
        ):
            return "ArithmeticCastMutator"
        if any(
            tok in fault_text
            for tok in ("__miri_proj_", "__proj_", "__dangling_ptr", "__dead_slot")
        ):
            return "PlaceProjectionWrapper"
        return seed_name

    if seed_name in known_corpus_bug_seeds or not first_mutator:
        return seed_name
    return first_mutator


def quarantine_match_keys_for_miri_finding(
    finding: dict[str, Any], known_corpus_bug_seeds: set[str]
) -> tuple[str, set[str]]:
    """Returns `(fingerprint, keys)` where `keys` is every quarantine token that
    quarantines this `miri-difftest` finding."""
    seed_name = str(finding["seed_name"])
    fn_name = str(finding["fn_name"])
    div_class = str(finding["divergence_class"])
    norm_tag = normalize_anneal_tag(str(finding["anneal_lean_tag"]))
    cause = infer_finding_cause(finding, known_corpus_bug_seeds)
    fp = f"{cause}:{div_class}:{norm_tag}"
    keys = {fp, cause, seed_name, fn_name, f"{seed_name}:{div_class}", f"{cause}:{div_class}"}
    return fp, keys


def quarantine_match_keys_for_itree_finding(finding: dict[str, Any]) -> tuple[str, set[str]]:
    """Returns `(fingerprint, keys)` where `keys` is every quarantine token that
    quarantines this `itree-difftest` finding."""
    fn_name = str(finding["fn_name"])
    seed_name = f"itree_seed_{finding.get('seed_index', 0)}"
    mutators = finding.get("applied_mutators")
    cause = (
        str(mutators[0])
        if isinstance(mutators, list) and len(mutators) > 0 and isinstance(mutators[0], str)
        else seed_name
    )
    diag_tag = str(finding["diag_tag"])
    div_class = f"itree_{diag_tag}"
    fp = f"{cause}:{div_class}:TraceReplayDiag.{diag_tag}"
    keys = {
        fp,
        cause,
        seed_name,
        fn_name,
        diag_tag,
        div_class,
        f"{cause}:{div_class}",
        f"{cause}:{diag_tag}",
    }
    return fp, keys


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

        fp, match_keys = quarantine_match_keys_for_miri_finding(f, known_corpus_bug_seeds)
        is_quarantined = bool(quarantine_rules and (match_keys & quarantine_rules))
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


def deduplicate_and_quarantine_itree_findings(
    findings: list[dict[str, Any]],
    quarantine_rules: set[str],
) -> tuple[
    list[DeduplicatedFinding], list[DeduplicatedFinding], list[DeduplicatedFinding]
]:
    """Deduplicates raw ITree findings and splits into unquarantined and quarantined."""
    by_fp: dict[str, DeduplicatedFinding] = {}
    for f in findings:
        fn_name = str(f["fn_name"])
        seed_idx = f.get("seed_index", 0)
        seed_name = f"itree_seed_{seed_idx}"
        mutators = f.get("applied_mutators")
        cause = (
            str(mutators[0])
            if isinstance(mutators, list)
            and len(mutators) > 0
            and isinstance(mutators[0], str)
            else seed_name
        )
        diag_tag = str(f["diag_tag"])
        div_class = f"itree_{diag_tag}"
        norm_tag = f"TraceReplayDiag.{diag_tag}"
        fp, match_keys = quarantine_match_keys_for_itree_finding(f)
        is_quarantined = bool(quarantine_rules and (match_keys & quarantine_rules))
        repro_path = str(f["repro_path"])
        native_outcome = f"trace:{f.get('case_ident', fn_name)}"
        anneal_outcome = str(f.get("diag_repr", diag_tag))

        if fp in by_fp:
            existing = by_fp[fp]
            existing.occurrences += 1
            if repro_path not in existing.all_repro_paths:
                existing.all_repro_paths.append(repro_path)
            existing.kernel_confirmed = existing.kernel_confirmed and bool(
                f.get("kernel_confirmed", False)
            )
            if not is_quarantined and existing.quarantined:
                existing.quarantined = False
                existing.seed_name = seed_name
                existing.primary_fn_name = fn_name
                existing.primary_repro_path = repro_path
                existing.miri_outcome = native_outcome
                existing.anneal_outcome = anneal_outcome
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
                miri_outcome=native_outcome,
                anneal_outcome=anneal_outcome,
                kernel_confirmed=bool(f.get("kernel_confirmed", False)),
            )

    all_dedup = list(by_fp.values())
    unquarantined = [d for d in all_dedup if not d.quarantined]
    quarantined = [d for d in all_dedup if d.quarantined]
    return all_dedup, unquarantined, quarantined


def collect_finding_bundle_files(findings: list[dict[str, Any]], state_dir: Path) -> list[Path]:
    """Collects all finding bundle files under `state_dir`."""
    files: list[Path] = []
    seen: set[Path] = set()
    for f in findings:
        repro = Path(f["repro_path"]).resolve()
        bundle_dir = repro.parent
        for name in (
            "repro.rs",
            "repro_trace.txt",
            "repro_mir.lean",
            "finding.json",
            "SUMMARY.md",
        ):
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
    miri_unquarantined: list[DeduplicatedFinding],
    include_itree: bool,
    itree: dict[str, Any] | None,
    itree_red_flags: RedFlagResult | None,
    itree_unquarantined: list[DeduplicatedFinding],
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
    elif len(miri_unquarantined) > 0:
        summary_lines = [
            f"{d.fingerprint} (occurrences={d.occurrences}, repro={d.primary_repro_path})"
            for d in miri_unquarantined
        ]
        cases.append(
            (
                "miri-difftest",
                (
                    f"unquarantined divergences detected ({len(miri_unquarantined)} distinct, {miri['diverge_count']} total)",
                    "\n".join(summary_lines),
                ),
                None,
            )
        )
    else:
        cases.append(("miri-difftest", None, None))

    if include_itree:
        if itree is None:
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
        elif itree_ran_without_oracle:
            cases.append(
                (
                    "itree-difftest",
                    None,
                    f"itree-difftest generated {compile_summary('itree-difftest', itree)}, "
                    "but its runtime trace oracle was not performed.",
                )
            )
        elif itree_red_flags is None or not itree_red_flags.passed:
            reasons = (
                "; ".join(itree_red_flags.failure_reasons)
                if itree_red_flags is not None
                else "itree-difftest produced invalid oracle JSON."
            )
            cases.append(
                (
                    "itree-difftest",
                    ("red-flag vacuity check failed", reasons),
                    None,
                )
            )
        elif len(itree_unquarantined) > 0:
            summary_lines = [
                f"{d.fingerprint} (occurrences={d.occurrences}, repro={d.primary_repro_path})"
                for d in itree_unquarantined
            ]
            cases.append(
                (
                    "itree-difftest",
                    (
                        f"unquarantined ITree divergences detected ({len(itree_unquarantined)} distinct, {itree['diverge_traces']} total)",
                        "\n".join(summary_lines),
                    ),
                    None,
                )
            )
        else:
            cases.append(("itree-difftest", None, None))

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
    itree_red_flags: RedFlagResult | None,
    itree_all_dedup: list[DeduplicatedFinding],
    itree_unquarantined: list[DeduplicatedFinding],
    itree_quarantined: list[DeduplicatedFinding],
    itree_ran_without_oracle: bool,
    miri_seed: int,
    itree_seed: int,
    elapsed_sec: float,
) -> str:
    """Renders the full Markdown report for a live oracle campaign."""
    itree_performed = (
        include_itree
        and itree is not None
        and itree.get("oracle_comparison") == "performed"
        and itree_red_flags is not None
    )
    itree_failed = include_itree and not (
        itree_ran_without_oracle or (itree_performed and itree_red_flags.passed)
    )
    raw_divergences = int(miri["diverge_count"]) + (
        int(itree["diverge_traces"]) if itree_performed and itree is not None else 0
    )

    if not miri_red_flags.passed or itree_failed:
        status = "RED FLAG / HARNESS FAILED"
    elif len(unquarantined) > 0:
        status = (
            f"DIVERGENCE DETECTED ({len(unquarantined)} unquarantined distinct, "
            f"{raw_divergences} raw)"
        )
    elif include_itree and itree_ran_without_oracle and len(quarantined) > 0:
        status = (
            f"MIRI PASS ({len(quarantined)} quarantined known bug fingerprints) "
            "/ ITREE NOT EVALUATED"
        )
    elif include_itree and itree_ran_without_oracle:
        status = "MIRI PASS (0 divergences) / ITREE NOT EVALUATED"
    elif len(quarantined) > 0:
        status = f"PASS ({len(quarantined)} quarantined known bug fingerprints)"
    else:
        status = "PASS (0 divergences)"

    itree_mode_cell = (
        f"`{itree.get('mode', 'seeded')}`"
        if itree_performed and itree is not None
        else ("`compile-only`" if include_itree else "skipped")
    )
    itree_seed_cell = f"`0x{itree_seed:08x}`" if include_itree else "skipped (`--miri-only`)"
    itree_total_cell = (
        str(itree.get("total_candidates", "n/a")) if (include_itree and itree) else "n/a"
    )
    if itree_performed and itree is not None:
        itree_compiled_cell = (
            f"{itree['opt_level_0_and_2_compiled']} (`-O0` & `-O2`, "
            f"{itree['instrumented_compiled']} instrumented)"
        )
        itree_oracle_cell = "**performed**"
        itree_compared_cell = (
            f"{itree['compared_candidates']} ({itree['distinct_traces_checked']} distinct traces, "
            f"{itree['total_traces_executed']} total)"
        )
        itree_agreed_cell = (
            f"{itree['agree_candidates']} ({itree['agree_traces']} traces)"
        )
        itree_diverged_cell = (
            f"{itree['diverge_traces']} ({len(itree_all_dedup)} distinct: "
            f"{len(itree_unquarantined)} unquarantined, {len(itree_quarantined)} quarantined)"
        )
        itree_kc_cell = (
            f"{itree['kernel_confirmed_divergences']} "
            f"({itree['kernel_confirmed_traces']} traces confirmed)"
        )
        itree_not_compared_cell = str(itree["not_compared_candidates"])
    else:
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
        itree_compared_cell = "0"
        itree_agreed_cell = "n/a"
        itree_diverged_cell = "n/a"
        itree_kc_cell = "n/a"
        itree_not_compared_cell = itree_total_cell

    itree_elapsed_cell = (
        f"{float(itree['elapsed_ms']):.1f} ms"
        if (include_itree and itree and "elapsed_ms" in itree)
        else "n/a"
    )

    banner_lines = [
        f"> **Status: {status}.**",
        f"> `miri-difftest` evaluated `{miri['compared_candidates']}/{miri['total_candidates']}` "
        f"candidates against live Miri (`-Zmiri-tree-borrows`) and Anneal's `MirSemantics` "
        f"oracle (`{miri['agree_count']}` agreed, `{miri['diverge_count']}` diverged, "
        f"`{miri['not_compared_count']}` not compared).",
    ]
    if itree_performed and itree is not None:
        banner_lines.append(
            f"> `itree-difftest` evaluated `{itree['compared_candidates']}/{itree['total_candidates']}` "
            f"candidates (`{itree['distinct_traces_checked']}` distinct traces across "
            f"`{itree['total_traces_executed']}` native `-O0`/`-O2` executions, "
            f"`{itree['agree_traces']}` agreed, `{itree['diverge_traces']}` diverged, "
            f"`{itree['distinct_obs_paths']}` distinct observable paths)."
        )

    lines: list[str] = [
        f"# Anneal Differential Testing Campaign Report (`{profile.name}` — `{date_prefix}`)",
        "",
        *banner_lines,
        "",
        "## Campaign Summary",
        "",
        "| Metric | `miri-difftest` | `itree-difftest` |",
        "| :--- | :--- | :--- |",
        f"| Mode | `{miri.get('mode', 'seeded')}` | {itree_mode_cell} |",
        f"| Seed | `0x{miri_seed:08x}` | {itree_seed_cell} |",
        f"| Candidates generated | {miri['total_candidates']} | {itree_total_cell} |",
        f"| Compiled with `rustc` | {miri['compiled_candidates']} ({miri['compile_failed_candidates']} failed) | {itree_compiled_cell} |",
        f"| Oracle comparison | **performed** | {itree_oracle_cell} |",
        f"| Compared | {miri['compared_candidates']} | {itree_compared_cell} |",
        f"| Agreed | {miri['agree_count']} | {itree_agreed_cell} |",
        f"| Diverged (raw / distinct) | {miri['diverge_count']} ({len(all_dedup) - len(itree_all_dedup)} distinct: {len(unquarantined) - len(itree_unquarantined)} unquarantined, {len(quarantined) - len(itree_quarantined)} quarantined) | {itree_diverged_cell} |",
        f"| Kernel-confirmed divergences (`by rfl`) | {miri['kernel_confirmed_divergences']} | {itree_kc_cell} |",
        f"| Not compared | {miri['not_compared_count']} | {itree_not_compared_cell} |",
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

    if itree_performed and itree is not None:
        lines.extend(
            [
                "",
                "## ITree Native vs. Lean `TraceCheck` Breakdown (`itree-difftest`)",
                "",
                "| `TraceReplayDiag` Tag | Count |",
                "| :--- | ---: |",
            ]
        )
        for tag, count in sorted(itree["diag_tag_counts"].items()):
            lines.append(f"| `{tag}` | {count} |")

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
    if itree_red_flags is not None:
        for check_name, ok in itree_red_flags.checks.items():
            lines.append(f"| `{check_name}` | {'PASS' if ok else '**FAIL**'} |")
    all_red_flag_reasons = list(miri_red_flags.failure_reasons)
    if itree_red_flags is not None:
        all_red_flag_reasons.extend(itree_red_flags.failure_reasons)
    if all_red_flag_reasons:
        lines.append("")
        for reason in all_red_flag_reasons:
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


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Anneal differential-testing campaign orchestrator. Runs live Miri + "
            "Anneal oracle comparisons for miri-difftest, validates red-flag "
            "vacuity checks, and deduplicates divergence findings."
        )
    )
    parser.add_argument("--profile", choices=sorted(PROFILES), default=None)
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
        "--manifest-path",
        type=Path,
        default=None,
        help="Optional path to `tests/miri-diff/manifest.toml` for stale `known_anneal_bug` ratchet checks.",
    )
    parser.add_argument(
        "--check-stale-ratchet",
        action="store_true",
        help="Run fail-closed ratchet audit for stale quarantine and `known_anneal_bug` entries.",
    )
    parser.add_argument(
        "--self-check-mutants",
        action="store_true",
        help="Run the 5-mutant semantic-mutant killing probe (`SEEDED_SEMANTIC_MUTANTS`).",
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
    ns = parser.parse_args(argv)
    ns._explicit_profile = ns.profile is not None
    if ns.profile is None:
        ns.profile = "quick"
    return ns


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    profile = PROFILES[args.profile]
    repo_root = Path(__file__).resolve().parent.parent
    start_time = time.monotonic()

    x20_uri = args.x20_uri.strip()
    try:
        check_x20_uri(x20_uri)
        cli_miri_seed = parse_seed_int(args.miri_seed) if args.miri_seed is not None else None
        cli_itree_seed = parse_seed_int(args.itree_seed) if args.itree_seed is not None else None
        if not args.check_stale_ratchet:
            quarantine_rules = load_quarantine_rules(args.quarantine_file)
        else:
            try:
                quarantine_rules = load_quarantine_rules(args.quarantine_file)
            except ValueError:
                quarantine_rules = set()
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
            prev_itree_eval = ledger_counter(ledger, "total_itree_candidates_evaluated")
            prev_itree_traces = ledger_counter(ledger, "total_itree_traces_checked")
        except ValueError as e:
            sys.stderr.write(f"error: {e}\n")
            return EXIT_INTERNAL_ERROR

        default_manifest = repo_root / "tests" / "miri-diff" / "manifest.toml"
        eff_manifest_path = (
            args.manifest_path
            if args.manifest_path is not None
            else (default_manifest if default_manifest.is_file() else None)
        )

        standalone_gate_only = (
            (args.self_check_mutants or args.check_stale_ratchet)
            and not getattr(args, "_explicit_profile", False)
            and args.miri_seed is None
            and args.itree_seed is None
            and not args.miri_identity
            and not args.miri_only
            and not args.compile_only
            and not x20_uri
            and args.junit_xml is None
        )
        if standalone_gate_only:
            date_prefix = utc_date_prefix()
            mutant_report = (
                run_semantic_mutant_self_check() if args.self_check_mutants else None
            )
            ratchet_report = (
                verify_no_stale_quarantine_or_known_bugs(
                    quarantine_file=args.quarantine_file,
                    manifest_path=eff_manifest_path,
                    ledger=ledger,
                )
                if args.check_stale_ratchet
                else None
            )
            gate_ok = (mutant_report is None or mutant_report["passed"]) and (
                ratchet_report is None or ratchet_report["passed"]
            )
            standalone_summary: dict[str, Any] = {
                "profile": profile.name,
                "date_utc": date_prefix,
                "mode": "standalone_gate",
                "passed": gate_ok,
                "semantic_mutant_self_check": mutant_report,
                "stale_ratchet_audit": ratchet_report,
            }
            summary_json_text = json.dumps(standalone_summary, indent=2) + "\n"
            for summary_path in [
                state_dir / "reports" / f"{date_prefix}_{profile.name}_campaign_summary.json",
                state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json",
            ]:
                summary_path.write_text(summary_json_text, encoding="utf-8")
            md_lines = [
                f"# Anneal Differential Testing Gate Report (`{date_prefix}`)",
                "",
                f"- **Gate status**: `{'PASS' if gate_ok else 'FAIL'}`",
            ]
            if mutant_report is not None:
                md_lines.append(
                    f"- **Semantic mutant self-check**: `{mutant_report['killed_count']}/{mutant_report['total_mutants']}` killed "
                    f"(`passed={mutant_report['passed']}`)"
                )
            if ratchet_report is not None:
                md_lines.append(
                    f"- **Stale ratchet audit**: `{len(ratchet_report['stale_entries'])}` stale entries "
                    f"(`passed={ratchet_report['passed']}`)"
                )
            report_md = "\n".join(md_lines) + "\n"
            for report_path in [
                state_dir / "reports" / f"{date_prefix}_{profile.name}_campaign_report.md",
                state_dir / "reports" / "LATEST_REPORT.md",
            ]:
                report_path.write_text(report_md, encoding="utf-8")
            print(report_md)
            return EXIT_SUCCESS if gate_ok else EXIT_HARNESS_FAILED

        date_prefix = utc_date_prefix()
        findings_dir = state_dir / "findings" / f"{date_prefix}_{profile.name}_miri"
        itree_findings_dir = state_dir / "findings" / f"{date_prefix}_{profile.name}_itree"
        if not args.compile_only:
            shutil.rmtree(findings_dir, ignore_errors=True)
            shutil.rmtree(itree_findings_dir, ignore_errors=True)

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

            if args.compile_only:
                itree_args = [
                    "--compile-only",
                    "--batches",
                    str(profile.itree_batches),
                    "--batch-size",
                    str(profile.itree_batch_size),
                    "--seed",
                    f"0x{itree_seed:08x}",
                ]
            else:
                itree_args = [
                    "--batches",
                    str(profile.itree_batches),
                    "--batch-size",
                    str(profile.itree_batch_size),
                    "--seed",
                    f"0x{itree_seed:08x}",
                    "--findings-dir",
                    str(itree_findings_dir),
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
                    itree_args,
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
            summaries = {"miri-difftest": miri}
            if not args.miri_only:
                summaries["itree-difftest"] = itree
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
            if not harness_failed and miri is not None and (args.miri_only or itree is not None):
                for key in OBSOLETE_LEDGER_KEYS:
                    ledger.pop(key, None)
                ledger["next_miri_seed"] = f"0x{advance_seed(miri_seed):08x}"
                if itree is not None:
                    ledger["next_itree_seed"] = f"0x{advance_seed(itree_seed):08x}"
                    ledger["total_itree_candidates_generated"] = prev_itree_gen + int(
                        itree.get("total_candidates", 0)
                    )
                ledger["total_campaigns_run"] = prev_campaigns + 1
                ledger["total_miri_candidates_generated"] = prev_miri_gen + int(
                    miri.get("total_candidates", 0)
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
        itree_performed = isinstance(itree, dict) and itree_status == "performed"
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

        itree_red_flags: RedFlagResult | None = None
        itree_all_dedup: list[DeduplicatedFinding] = []
        itree_unquarantined: list[DeduplicatedFinding] = []
        itree_quarantined: list[DeduplicatedFinding] = []
        if include_itree and itree_performed and itree is not None:
            valid_itree, itree_err = validate_performed_itree_summary(itree)
            if not valid_itree:
                sys.stderr.write(
                    f"itree-difftest produced invalid oracle summary: {itree_err}\n"
                )
                itree_red_flags = RedFlagResult(
                    passed=False,
                    checks={"itree_oracle_invoked": False},
                    failure_reasons=[f"itree_invalid_summary: {itree_err}"],
                )
            else:
                itree_red_flags = evaluate_itree_red_flags(
                    itree,
                    itree_seed,
                    ledger,
                    args.min_oracle_elapsed_ms,
                )
                if not itree_red_flags.passed:
                    for reason in itree_red_flags.failure_reasons:
                        sys.stderr.write(f"red-flag check failed: {reason}\n")
                (
                    itree_all_dedup,
                    itree_unquarantined,
                    itree_quarantined,
                ) = deduplicate_and_quarantine_itree_findings(
                    itree["findings"],
                    quarantine_rules,
                )

        known_corpus_bug_seeds = load_known_corpus_bug_seeds(repo_root)
        miri_all_dedup, miri_unquarantined, miri_quarantined = (
            deduplicate_and_quarantine_findings(
                miri["findings"],
                known_corpus_bug_seeds,
                quarantine_rules,
            )
        )
        all_dedup = [*miri_all_dedup, *itree_all_dedup]
        unquarantined = [*miri_unquarantined, *itree_unquarantined]
        quarantined = [*miri_quarantined, *itree_quarantined]

        mutant_self_check_report = (
            run_semantic_mutant_self_check() if args.self_check_mutants else None
        )
        observed_quarantine_keys: set[str] = set()
        for f in miri["findings"]:
            observed_quarantine_keys |= quarantine_match_keys_for_miri_finding(
                f, known_corpus_bug_seeds
            )[1]
        covered_harnesses = {"miri"}
        if include_itree and itree_performed and itree is not None:
            covered_harnesses.add("itree")
            if isinstance(itree.get("findings"), list):
                for f in itree["findings"]:
                    observed_quarantine_keys |= quarantine_match_keys_for_itree_finding(f)[1]
        stale_ratchet_report = (
            verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=args.quarantine_file,
                manifest_path=eff_manifest_path,
                ledger=ledger,
                evaluated_fingerprints=[d.fingerprint for d in all_dedup],
                observed_quarantine_keys=observed_quarantine_keys,
                covered_harnesses=covered_harnesses,
            )
            if args.check_stale_ratchet
            else None
        )
        extra_gates_failed = (
            mutant_self_check_report is not None and not mutant_self_check_report["passed"]
        ) or (stale_ratchet_report is not None and not stale_ratchet_report["passed"])

        itree_ok = (not include_itree) or itree_ran_without_oracle or (
            itree_performed and itree_red_flags is not None and itree_red_flags.passed
        )
        harness_or_red_flag_failed = (
            (not miri_red_flags.passed) or (not itree_ok) or extra_gates_failed
        )

        written = collect_finding_bundle_files(miri["findings"], state_dir)
        if include_itree and itree_performed and itree is not None and isinstance(itree.get("findings"), list):
            written.extend(collect_finding_bundle_files(itree["findings"], state_dir))
        if not harness_or_red_flag_failed:
            ledger["next_miri_seed"] = f"0x{advance_seed(miri_seed):08x}"
            if include_itree and itree is not None:
                ledger["next_itree_seed"] = f"0x{advance_seed(itree_seed):08x}"
                ledger["total_itree_candidates_generated"] = prev_itree_gen + int(
                    itree.get("total_candidates", 0)
                )
                if itree_performed:
                    ledger["total_itree_candidates_evaluated"] = prev_itree_eval + int(
                        itree.get("compared_candidates", 0)
                    )
                    ledger["total_itree_traces_checked"] = prev_itree_traces + int(
                        itree.get("distinct_traces_checked", 0)
                    )
                    ledger["last_itree_seed"] = f"0x{itree_seed:08x}"
                    ledger["last_itree_signature"] = itree_signature_for_seed_check(itree)
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
                "performed"
                if (not include_itree or itree_performed)
                else "miri_performed_itree_not_performed"
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
            itree_red_flags,
            itree_all_dedup,
            itree_unquarantined,
            itree_quarantined,
            itree_ran_without_oracle,
            miri_seed,
            itree_seed,
            elapsed_sec,
        )
        if mutant_self_check_report is not None:
            report_md += (
                "\n## Semantic-Mutant Self-Check (`--self-check-mutants`)\n\n"
                f"- **Passed**: `{mutant_self_check_report['passed']}` "
                f"(`{mutant_self_check_report['killed_count']}/{mutant_self_check_report['total_mutants']}` killed)\n"
                f"- **Survived mutants**: `{mutant_self_check_report['survived_mutants']}`\n"
            )
        if stale_ratchet_report is not None:
            report_md += (
                "\n## Stale Quarantine & Known-Bug Ratchet Audit (`--check-stale-ratchet`)\n\n"
                f"- **Passed**: `{stale_ratchet_report['passed']}` "
                f"(`{len(stale_ratchet_report['stale_entries'])}` stale entries)\n"
            )
        for report_path in [
            state_dir / "reports" / f"{date_prefix}_{profile.name}_campaign_report.md",
            state_dir / "reports" / "LATEST_REPORT.md",
        ]:
            report_path.write_text(report_md, encoding="utf-8")
            written.append(report_path)

        combined_checks = dict(miri_red_flags.checks)
        combined_reasons = list(miri_red_flags.failure_reasons)
        if itree_red_flags is not None:
            combined_checks.update(itree_red_flags.checks)
            combined_reasons.extend(itree_red_flags.failure_reasons)

        campaign_summary = {
            "profile": profile.name,
            "date_utc": date_prefix,
            "miri_seed": f"0x{miri_seed:08x}",
            "itree_seed": f"0x{itree_seed:08x}" if include_itree else None,
            "miri_oracle_comparison": "performed",
            "itree_oracle_comparison": (
                "performed"
                if (include_itree and itree_performed and itree_red_flags is not None and itree_red_flags.passed)
                else (
                    "not_performed"
                    if (include_itree and itree_ran_without_oracle)
                    else ("failed" if include_itree else "skipped")
                )
            ),
            "red_flags": {
                "passed": miri_red_flags.passed and (itree_red_flags is None or itree_red_flags.passed),
                "checks": combined_checks,
                "failure_reasons": combined_reasons,
            },
            "miri_summary": miri,
            "itree_summary": itree if include_itree else None,
            "deduplicated_findings": [d.to_dict() for d in all_dedup],
            "unquarantined_findings": [d.to_dict() for d in unquarantined],
            "quarantined_findings": [d.to_dict() for d in quarantined],
            "elapsed_sec": round(elapsed_sec, 3),
        }
        if mutant_self_check_report is not None:
            campaign_summary["semantic_mutant_self_check"] = mutant_self_check_report
        if stale_ratchet_report is not None:
            campaign_summary["stale_ratchet_audit"] = stale_ratchet_report
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
                miri_unquarantined,
                include_itree,
                itree,
                itree_red_flags,
                itree_unquarantined,
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
