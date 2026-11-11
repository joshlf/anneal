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
     `oracle_not_invoked`), or oracle errors above `--max-oracle-errors`
     (in either suite). Ledger state of a suite that completed a healthy live
     oracle run is still committed when the other suite fails;
  3  compile-only mode (`--compile-only`): neither harness crashed, and both
     harnesses reported `"oracle_comparison": "not_performed"`;
  4  one or more unquarantined divergences were detected by a live oracle run.
"""

from __future__ import annotations

import argparse
import copy
from dataclasses import dataclass
import datetime
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import tomllib
from typing import Any
import xml.etree.ElementTree as ET


REMOTE_SYNC_BIN = "/usr/bin/remote-sync"
REMOTE_SYNC_FLAG = "--force_client_creation_at_head"

EXIT_SUCCESS = 0
EXIT_INTERNAL_ERROR = 1
EXIT_HARNESS_FAILED = 2
EXIT_NOT_EVALUATED = 3
EXIT_DIVERGENCE_DETECTED = 4

DEFAULT_MIN_ORACLE_ELAPSED_MS = 50.0
DEFAULT_MAX_ORACLE_ERRORS = 0
_MAX_SAFE_NONNEG_INT = (1 << 63) - 1

_NON_ABSENT_RPC_STATUS_RE = re.compile(
    r"(?:^|[\s(\[=])(?:"
    r"cancelled|canceled|unknown|invalid_argument|deadline_exceeded|"
    r"already_exists|permission_denied|resource_exhausted|failed_precondition|"
    r"aborted|out_of_range|unimplemented|internal|unavailable|data_loss|"
    r"unauthenticated"
    r")(?:\s*:|[\])]|\s+desc\b|$)",
    re.IGNORECASE | re.MULTILINE,
)


def _reject_json_constant(token: str) -> Any:
    raise ValueError(f"non-standard JSON constant {token!r}")


def _strict_json_loads(raw_text: str) -> Any:
    return json.loads(raw_text, parse_constant=_reject_json_constant)


def _atomic_write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp_path = path.parent / f".tmp_{os.getpid()}_{path.name}"
    try:
        tmp_path.write_text(content, encoding="utf-8")
        os.replace(tmp_path, path)
    except BaseException:
        try:
            tmp_path.unlink(missing_ok=True)
        except OSError:
            pass
        raise

# Module-level diagnostic store populated by `run_harness` (preserving its
# 4-positional-argument signature for unit-test monkey-patching).
LAST_HARNESS_DIAGNOSTICS: dict[str, dict[str, Any]] = {}

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

# `itree-difftest` per-candidate not-compared reasons (`ITREE_NOT_COMPARED_REASON_NAMES`).
VALID_ITREE_NOT_COMPARED_REASONS = (
    "compile_failed",
    "staging_failed",
    "trace_collect_failed",
    "opt_level_trace_mismatch",
    "empty_trace",
    "lean_build_failed",
    "lean_probe_failed",
    "lean_confirm_failed",
)

# Not-compared reasons that mean the ITree oracle pipeline (staging, native trace
# capture, `-O0`/`-O2` trace agreement, or Lean `Mir` build / `TraceCheck` probe /
# kernel confirmation) failed on a candidate that compiled: every reason except
# `compile_failed`. Like Miri oracle/capture errors, these count against
# `--max-oracle-errors` so isolated per-candidate failures can never silently
# shrink the compared set of a run that still reports itself as healthy.
ITREE_ORACLE_ERROR_REASONS = tuple(
    r for r in VALID_ITREE_NOT_COMPARED_REASONS if r != "compile_failed"
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
# running without an oracle. Live-oracle history (`fingerprint_history`,
# `resolved_history`, `quarantined_fingerprints`, `last_*_signature`,
# `per_suite_runs`, `schema_version`, ...) is deliberately NOT listed: the
# capsule launcher uploads `state/` after every run, so stripping it on a
# pass-through `--compile-only` run would erase the shared remote ledger's aging
# history and seed-sensitivity baselines.
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


def has_remote_sync() -> bool:
    return os.path.isfile(REMOTE_SYNC_BIN) and os.access(REMOTE_SYNC_BIN, os.X_OK)


def run_remote_sync(args: list[str]) -> subprocess.CompletedProcess[str]:
    cmd = [REMOTE_SYNC_BIN, REMOTE_SYNC_FLAG, *args]
    return subprocess.run(cmd, text=True, capture_output=True, check=False)


def check_remote_uri(remote_uri: str) -> None:
    if not remote_uri:
        return
    norm = os.path.normpath(remote_uri)
    if (
        remote_uri.startswith("/mnt/fuse/rw/")
        or norm == "/mnt/fuse/rw"
        or norm.startswith("/mnt/fuse/rw/")
    ):
        raise ValueError(
            f"Refusing FUSE path `{remote_uri}`; always use `/remote/...` URIs with "
            f"`{REMOTE_SYNC_BIN} {REMOTE_SYNC_FLAG}`."
        )
    if not remote_uri.startswith("/remote/"):
        try:
            real = os.path.realpath(remote_uri)
        except OSError:
            real = norm
        if real == "/mnt/fuse/rw" or real.startswith("/mnt/fuse/rw/"):
            raise ValueError(
                f"Refusing FUSE path `{remote_uri}` (resolves to `{real}`); always use "
                f"`/remote/...` URIs with `{REMOTE_SYNC_BIN} {REMOTE_SYNC_FLAG}`."
            )


def _is_absent_remote_error(err_text: str) -> bool:
    lower = err_text.lower()
    if _NON_ABSENT_RPC_STATUS_RE.search(lower):
        return False
    if (
        "permission denied" in lower
        or "access denied" in lower
        or "deadline exceeded" in lower
    ):
        return False
    return any(
        tok in lower
        for tok in ("not_found", "no files matched", "no such file")
    )


def sync_state_from_remote(
    remote_uri: str, state_dir: Path, include_ratchet: bool = True
) -> bool:
    """Pulls the ledger (and coverage ratchet in live mode) from `/remote/` via `remote-sync` RPC.

    Each file is staged into a sibling temporary path and atomically moved into
    place only on success so transient remote read errors never clobber valid
    pre-existing files in a reused `--state-dir`.

    Returns `False` if any remote state file failed to read with a non-absent
    error so callers can avoid overwriting `/remote/.../state/` at upload time.
    """
    if not remote_uri or not has_remote_sync():
        return True
    check_remote_uri(remote_uri)
    state_subdir = state_dir / "state"
    state_subdir.mkdir(parents=True, exist_ok=True)
    names = ["campaign_ledger.json"]
    if include_ratchet:
        names.append("coverage_ratchet.json")
    base = remote_uri.rstrip("/")
    pid = os.getpid()
    all_reads_ok = True
    for name in names:
        dst = state_subdir / name
        tmp_dst = state_subdir / f".sync_tmp_{pid}_{name}"
        tmp_dst.unlink(missing_ok=True)
        remote_src = f"{base}/state/{name}"
        res = run_remote_sync(["cp", "-f", remote_src, str(tmp_dst)])
        if res.returncode != 0:
            tmp_dst.unlink(missing_ok=True)
            err_detail = (res.stderr or res.stdout or "").strip()
            if not err_detail or not _is_absent_remote_error(err_detail):
                all_reads_ok = False
                suffix = f": {err_detail}" if err_detail else ""
                sys.stderr.write(
                    f"warning: failed to fetch `{remote_src}` (exit {res.returncode}){suffix}; "
                    f"preserving local {dst}\n"
                )
        elif tmp_dst.is_file():
            os.replace(tmp_dst, dst)
    return all_reads_ok


def _filter_written_for_remote(
    state_dir: Path, remote_uri: str, written: list[Path], remote_state_ok: bool
) -> list[Path]:
    if remote_state_ok or not remote_uri or not has_remote_sync():
        return written
    filtered: list[Path] = []
    for p in written:
        try:
            in_state = p.relative_to(state_dir).parts[:1] == ("state",)
        except ValueError:
            in_state = False
        if not in_state:
            filtered.append(p)
    if len(filtered) != len(written):
        sys.stderr.write(
            "warning: could not read shared remote state; skipping upload of state/\n"
        )
    return filtered


def sync_state_to_remote(state_dir: Path, remote_uri: str, written: list[Path]) -> None:
    """Uploads the files this run wrote under `state_dir` to `/remote/`.

    Only `written` is uploaded, so stale files in a reused state directory are
    never republished.
    """
    if not remote_uri or not has_remote_sync():
        return
    check_remote_uri(remote_uri)
    base = remote_uri.rstrip("/")
    created_dirs: set[str] = set()
    for subdir in ["state", "reports"]:
        remote_dir = f"{base}/{subdir}"
        run_remote_sync(["mkdir", "-p", remote_dir])
        created_dirs.add(remote_dir)
    for local_file in written:
        rel = local_file.relative_to(state_dir)
        remote_parent = f"{base}/{rel.parent}"
        if remote_parent not in created_dirs:
            run_remote_sync(["mkdir", "-p", remote_parent])
            created_dirs.add(remote_parent)
        run_remote_sync(["cp", "-f", str(local_file), f"{base}/{rel}"])


def load_ledger(ledger_path: Path) -> dict[str, Any]:
    try:
        if not ledger_path.is_file():
            return {}
        ledger = _strict_json_loads(ledger_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, ValueError) as e:
        raise ValueError(f"cannot read {ledger_path}: {e}") from e
    if not isinstance(ledger, dict):
        raise ValueError(f"{ledger_path} is not a JSON object")
    return ledger


def parse_seed_int(raw: str) -> int:
    clean = raw.strip().replace("_", "")
    if not clean or len(clean) > 66:
        raise ValueError("empty or oversized seed")
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
    if (
        isinstance(raw, bool)
        or not isinstance(raw, int)
        or raw < 0
        or raw > _MAX_SAFE_NONNEG_INT
    ):
        raise ValueError(f"ledger field {key!r} must be a non-negative integer")
    return raw


def advance_seed(seed_val: int) -> int:
    return (seed_val + 0x9E37_79B9) & 0xFFFF_FFFF


def is_nonneg_int(val: Any) -> bool:
    return (
        not isinstance(val, bool)
        and isinstance(val, int)
        and 0 <= val <= _MAX_SAFE_NONNEG_INT
    )


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
    t0 = time.monotonic()
    res = subprocess.run(
        cmd, cwd=str(repo_root), env=env, text=True, capture_output=True
    )
    elapsed_s = round(time.monotonic() - t0, 3)
    stderr_lines = res.stderr.strip().splitlines() if res.stderr else []
    stderr_tail = "\n".join(stderr_lines[-20:])
    if res.returncode != 0:
        LAST_HARNESS_DIAGNOSTICS[bin_name] = {
            "exit_code": res.returncode,
            "oracle_error_reason": f"process_exit_{res.returncode}",
            "stderr_tail": stderr_tail,
            "elapsed_s": elapsed_s,
        }
        sys.stderr.write(f"{bin_name} failed (exit {res.returncode}):\n{res.stderr}\n")
        return None
    try:
        summary = _strict_json_loads(json_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, ValueError) as e:
        LAST_HARNESS_DIAGNOSTICS[bin_name] = {
            "exit_code": res.returncode,
            "oracle_error_reason": f"unreadable_json: {e}",
            "stderr_tail": stderr_tail,
            "elapsed_s": elapsed_s,
        }
        sys.stderr.write(f"{bin_name} produced unreadable JSON: {e}\n")
        return None
    if not isinstance(summary, dict):
        LAST_HARNESS_DIAGNOSTICS[bin_name] = {
            "exit_code": res.returncode,
            "oracle_error_reason": "non_object_json",
            "stderr_tail": stderr_tail,
            "elapsed_s": elapsed_s,
        }
        sys.stderr.write(f"{bin_name} produced a non-object JSON summary\n")
        return None
    for key in HARNESS_INT_KEYS:
        val = summary.get(key)
        if val is not None and (isinstance(val, bool) or not isinstance(val, int)):
            LAST_HARNESS_DIAGNOSTICS[bin_name] = {
                "exit_code": res.returncode,
                "oracle_error_reason": f"non_integer_{key}",
                "stderr_tail": stderr_tail,
                "elapsed_s": elapsed_s,
            }
            sys.stderr.write(f"{bin_name} produced non-integer {key}={val!r}\n")
            return None
    elapsed = summary.get("elapsed_ms")
    if elapsed is not None and (
        isinstance(elapsed, bool) or not isinstance(elapsed, (int, float))
    ):
        LAST_HARNESS_DIAGNOSTICS[bin_name] = {
            "exit_code": res.returncode,
            "oracle_error_reason": "non_numeric_elapsed_ms",
            "stderr_tail": stderr_tail,
            "elapsed_s": elapsed_s,
        }
        sys.stderr.write(f"{bin_name} produced non-numeric elapsed_ms={elapsed!r}\n")
        return None
    LAST_HARNESS_DIAGNOSTICS[bin_name] = {
        "exit_code": 0,
        "oracle_error_reason": None,
        "stderr_tail": stderr_tail,
        "elapsed_s": elapsed_s,
    }
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
    if "obs_path_signatures" in summary:
        sigs = summary.get("obs_path_signatures")
        if not isinstance(sigs, list) or not all(
            isinstance(s, str) and s.strip() for s in sigs
        ):
            return False, "invalid 'obs_path_signatures' list"

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
    if "not_compared_reasons" in summary and not is_int_map(
        summary.get("not_compared_reasons"), VALID_ITREE_NOT_COMPARED_REASONS
    ):
        return False, "invalid 'not_compared_reasons' map"
    if "obs_path_signatures" in summary:
        sigs = summary.get("obs_path_signatures")
        if not isinstance(sigs, list) or not all(
            isinstance(s, str) and s.strip() for s in sigs
        ):
            return False, "invalid 'obs_path_signatures' list"

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
    max_oracle_errors: int = DEFAULT_MAX_ORACLE_ERRORS,
) -> RedFlagResult:
    """Runs red-flag vacuity checks on an `itree-difftest` oracle summary."""
    reasons: list[str] = []

    total = int(summary["total_candidates"])
    unsafe_violations = int(summary["unsafe_token_violations"])
    opt_both = int(summary["opt_level_0_and_2_compiled"])
    instrumented = int(summary["instrumented_compiled"])
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
    nc_reasons_raw = summary.get("not_compared_reasons")
    nc_reasons: dict[str, int] | None = (
        nc_reasons_raw if isinstance(nc_reasons_raw, dict) else None
    )

    oracle_invoked = True
    if unsafe_violations != 0:
        oracle_invoked = False
        reasons.append(
            f"itree_oracle_not_invoked: unsafe_token_violations={unsafe_violations} != 0"
        )
    if nc_reasons is None:
        # Legacy summaries without per-reason accounting: every candidate that
        # compiled at `-O0` and `-O2` must have been compared.
        if compared <= 0 or compared != opt_both or compared + not_compared_cands != total:
            oracle_invoked = False
            reasons.append(
                f"itree_oracle_not_invoked: compared ({compared}), opt_both ({opt_both}), "
                f"not_compared ({not_compared_cands}), total ({total}) inconsistent"
            )
    else:
        # Per-candidate isolation may legitimately leave compiled candidates
        # uncompared, but only with a reason for every one of them.
        eligible_cap = min(opt_both, instrumented)
        nc_sum = sum(int(v) for v in nc_reasons.values())
        compile_failed = int(nc_reasons.get("compile_failed", 0))
        if (
            compared <= 0
            or compared > eligible_cap
            or compared + not_compared_cands != total
            or nc_sum != not_compared_cands
            or compile_failed < total - eligible_cap
        ):
            oracle_invoked = False
            reasons.append(
                f"itree_oracle_not_invoked: compared ({compared}), opt_both ({opt_both}), "
                f"instrumented ({instrumented}), not_compared ({not_compared_cands}), "
                f"sum(not_compared_reasons) ({nc_sum}), compile_failed ({compile_failed}), "
                f"total ({total}) inconsistent"
            )
    if agree_cands + diverge_cands != compared:
        oracle_invoked = False
        reasons.append(
            f"itree_oracle_not_invoked: agree_candidates ({agree_cands}) + "
            f"diverge_candidates ({diverge_cands}) != compared_candidates ({compared})"
        )
    if (diverge_cands == 0) != (diverge_traces == 0) or diverge_cands > diverge_traces:
        oracle_invoked = False
        reasons.append(
            f"itree_oracle_not_invoked: diverge_candidates ({diverge_cands}) inconsistent "
            f"with diverge_traces ({diverge_traces})"
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
    # Every divergence must be kernel-confirmed. Beyond small batches (where every
    # trace is confirmed), `itree-difftest` kernel-confirms every divergence plus
    # at least one trace per compared candidate, so the honest count of
    # kernel-confirmed traces lies in [max(compared, agree_cands + diverge_traces), distinct].
    min_expected_kc_traces = max(compared, agree_cands + diverge_traces)
    if (
        kc_traces > distinct_traces
        or kc_traces < min_expected_kc_traces
        or kc_divergences != diverge_traces
        or len(findings) != diverge_traces
    ):
        oracle_invoked = False
        reasons.append(
            f"itree_oracle_not_invoked: kernel_confirmed_traces ({kc_traces}), "
            f"kernel_confirmed_divergences ({kc_divergences}), findings ({len(findings)}) "
            f"do not match distinct_traces ({distinct_traces}) / diverge_traces ({diverge_traces}) "
            f"/ compared_candidates ({compared})"
        )
    for f in findings:
        raw_repro = f.get("repro_path") if isinstance(f, dict) else None
        repro_p = Path(raw_repro) if isinstance(raw_repro, str) and raw_repro else None
        if not (
            isinstance(f, dict)
            and f.get("kernel_confirmed")
            and repro_p is not None
            and repro_p.is_file()
        ):
            oracle_invoked = False
            reasons.append(
                f"itree_oracle_not_invoked: finding {f.get('finding_id') if isinstance(f, dict) else f!r} missing "
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

    oracle_error_counts = {
        k: int(nc_reasons.get(k, 0)) if nc_reasons is not None else 0
        for k in ITREE_ORACLE_ERROR_REASONS
    }
    itree_oracle_errors = sum(oracle_error_counts.values())
    within_error_threshold = itree_oracle_errors <= max_oracle_errors
    if not within_error_threshold:
        breakdown = ", ".join(f"{k}={v}" for k, v in oracle_error_counts.items() if v)
        reasons.append(
            f"itree_oracle_errors_exceeded: {itree_oracle_errors} candidate(s) dropped by "
            f"ITree staging/trace/Lean oracle errors ({breakdown}) > max_oracle_errors "
            f"({max_oracle_errors})"
        )

    checks = {
        "itree_oracle_invoked": oracle_invoked,
        "itree_non_zero_compared": non_zero_compared,
        "itree_plausible_wall_clock": plausible_wall_clock,
        "itree_seed_sensitivity": seed_sensitive,
        "itree_oracle_error_threshold": within_error_threshold,
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
        raw_repro = f.get("repro_path") if isinstance(f, dict) else None
        repro_p = Path(raw_repro) if isinstance(raw_repro, str) and raw_repro else None
        if not (
            isinstance(f, dict)
            and f.get("kernel_confirmed")
            and repro_p is not None
            and repro_p.is_file()
        ):
            oracle_invoked = False
            reasons.append(
                f"oracle_not_invoked: finding {f.get('finding_id') if isinstance(f, dict) else f!r} missing "
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
    try:
        if not quarantine_file.is_file():
            raise ValueError(f"quarantine file does not exist: {quarantine_file}")
        text = quarantine_file.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as e:
        raise ValueError(f"cannot read quarantine file {quarantine_file}: {e}") from e
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
            data = _strict_json_loads(text)
        except ValueError as e:
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


ALL_MIRI_MUTATOR_TOKENS = (
    "__miri_ptr_",
    "__oob_",
    "__neg_",
    "__ptr_pair",
    "__base_ptr",
    "__miri_tb_",
    "__tb_",
    "__miri_valid_",
    "__valid_",
    "__bad_",
    "__uninit_",
    "__padded",
    "__pad_bytes",
    "__ptr_b",
    "__raw_u8",
    "__miri_arith_",
    "__miri_wide",
    "__miri_proj_",
    "__proj_",
)


def extract_earliest_fault_line_no(finding: dict[str, Any]) -> int | None:
    """Returns the 1-based line number of the earliest fault (`miri_pos` or `anneal_span`)."""
    src = finding.get("mutant_source")
    if not isinstance(src, str) or not src:
        return None
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
    return earliest_line_no


def extract_fault_line_text(finding: dict[str, Any]) -> str:
    """Returns the source line at the earliest fault (`miri_pos` or `anneal_span`).

    When Anneal faults inside the unmutated seed body at an earlier line than a
    subsequent Miri fault in an appended mutator tail (or vice versa), the
    earliest line number is the point where the two executions first diverged.
    """
    src = finding.get("mutant_source")
    if not isinstance(src, str) or not src:
        return ""
    earliest_line_no = extract_earliest_fault_line_no(finding)
    if earliest_line_no is None:
        return ""
    src_lines = src.splitlines()
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

        # If the earliest fault occurred inside the unmutated seed prefix before
        # an appended mutator tail (which only introduces mutator tokens on later
        # lines), attribute the fault to `seed_name`.
        earliest_line_no = extract_earliest_fault_line_no(finding)
        src = finding.get("mutant_source")
        if earliest_line_no is not None and isinstance(src, str):
            src_lines = src.splitlines()
            prefix_text = "\n".join(src_lines[:earliest_line_no])
            suffix_text = "\n".join(src_lines[earliest_line_no:])
            if not any(tok in prefix_text for tok in ALL_MIRI_MUTATOR_TOKENS) and any(
                tok in suffix_text for tok in ALL_MIRI_MUTATOR_TOKENS
            ):
                return seed_name

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
        fp = f"{cause}:{div_class}:{norm_tag}"
        is_quarantined = bool(
            quarantine_rules
            and (
                fp in quarantine_rules
                or cause in quarantine_rules
                or seed_name in quarantine_rules
                or fn_name in quarantine_rules
                or diag_tag in quarantine_rules
                or div_class in quarantine_rules
                or f"{cause}:{div_class}" in quarantine_rules
                or f"{cause}:{diag_tag}" in quarantine_rules
            )
        )
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
                        "itree-difftest exited with an error or produced invalid oracle JSON.",
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


def infer_fingerprint_suite(fp: str, entry: dict[str, Any] | None = None) -> str:
    """Infers which harness suite (`miri-difftest` or `itree-difftest`) owns `fp`."""
    if isinstance(entry, dict):
        s = entry.get("suite") or entry.get("harness")
        if s in ("miri-difftest", "miri"):
            return "miri-difftest"
        if s in ("itree-difftest", "itree"):
            return "itree-difftest"
    if (
        "TraceReplayDiag." in fp
        or ":itree_" in fp
        or fp.startswith(
            (
                "itree:",
                "itree_seed_",
                "CallBoundaryOutliner:",
                "LayoutPaddingPerturber:",
                "BranchLoopWeaver:",
                "ExtOracleInjector:",
            )
        )
    ):
        return "itree-difftest"
    return "miri-difftest"


def _safe_nonneg_int(raw: Any, default: int = 0) -> int:
    """Returns `raw` as a bounded non-negative int, or `default` for corrupt values."""
    if isinstance(raw, bool):
        return default
    if isinstance(raw, int):
        return raw if 0 <= raw <= _MAX_SAFE_NONNEG_INT else default
    if isinstance(raw, str):
        s = raw.strip()
        if s.isascii() and s.isdigit() and len(s) <= 30:
            try:
                val = int(s, 10)
            except ValueError:
                return default
            return val if 0 <= val <= _MAX_SAFE_NONNEG_INT else default
    return default


def update_suite_scoped_fingerprints(
    ledger: dict[str, Any],
    date_prefix: str,
    miri_suite_healthy: bool,
    miri_unquarantined: list[DeduplicatedFinding],
    miri_quarantined: list[DeduplicatedFinding],
    itree_suite_healthy: bool,
    itree_unquarantined: list[DeduplicatedFinding],
    itree_quarantined: list[DeduplicatedFinding],
) -> None:
    """Updates `active_fingerprints`, `quarantined_fingerprints`, `fingerprint_history`,
    and `resolved_history` independently per suite so an unhealthy or skipped suite
    never falsely ages or resolves its fingerprints.

    - A healthy suite increments `campaigns_failing` and refreshes `last_seen_date`
      for each fingerprint it observed unquarantined, and moves its previously
      tracked fingerprints that it no longer observed at all (neither unquarantined
      nor quarantined) to `resolved_history`. A fingerprint that reappears after
      being resolved keeps its original `first_seen_date`.
    - An unhealthy or skipped suite leaves its entries byte-for-byte untouched.
    - Legacy ledgers without `fingerprint_history` get entries for their active
      fingerprints dated by the ledger's `last_run_utc` (when they were last
      observed), never by today's date.
    """
    prev_active_raw = ledger.get("active_fingerprints", [])
    prev_active_list: list[str] = (
        [str(x) for x in prev_active_raw if isinstance(x, str)]
        if isinstance(prev_active_raw, list)
        else []
    )
    prev_quar_raw = ledger.get("quarantined_fingerprints", [])
    prev_quar_list: list[str] = (
        [str(x) for x in prev_quar_raw if isinstance(x, str)]
        if isinstance(prev_quar_raw, list)
        else []
    )
    raw_fp_hist = ledger.get("fingerprint_history", {})
    fp_history: dict[str, dict[str, Any]] = (
        {
            str(k): copy.deepcopy(v)
            for k, v in raw_fp_hist.items()
            if isinstance(k, str) and isinstance(v, dict)
        }
        if isinstance(raw_fp_hist, dict)
        else {}
    )
    raw_res_hist = ledger.get("resolved_history", {})
    resolved_history: dict[str, dict[str, Any]] = (
        {
            str(k): copy.deepcopy(v)
            for k, v in raw_res_hist.items()
            if isinstance(k, str) and isinstance(v, dict)
        }
        if isinstance(raw_res_hist, dict)
        else {}
    )

    last_run = ledger.get("last_run_utc")
    legacy_seen_date = (
        last_run[:10]
        if isinstance(last_run, str) and len(last_run) >= 10
        else date_prefix
    )

    def suite_of(fp: str) -> str:
        return infer_fingerprint_suite(fp, fp_history.get(fp) or resolved_history.get(fp))

    new_active: list[str] = []
    new_quarantined: list[str] = []

    for suite_name, is_healthy, suite_unquar, suite_quar in (
        ("miri-difftest", miri_suite_healthy, miri_unquarantined, miri_quarantined),
        ("itree-difftest", itree_suite_healthy, itree_unquarantined, itree_quarantined),
    ):
        prev_suite_active = [fp for fp in prev_active_list if suite_of(fp) == suite_name]
        prev_suite_quar = [fp for fp in prev_quar_list if suite_of(fp) == suite_name]

        if not is_healthy:
            # Preserve this suite's active/quarantined/history entries untouched.
            for fp in prev_suite_active:
                if fp not in new_active:
                    new_active.append(fp)
            for fp in prev_suite_quar:
                if fp not in new_quarantined:
                    new_quarantined.append(fp)
            continue

        # Healthy suite: materialize legacy history entries before aging them.
        for fp in prev_suite_active:
            if fp not in fp_history:
                fp_history[fp] = {
                    "first_seen_date": legacy_seen_date,
                    "last_seen_date": legacy_seen_date,
                    "campaigns_failing": 1,
                    "suite": suite_name,
                }
        for fp in prev_suite_quar:
            if fp not in fp_history:
                fp_history[fp] = {
                    "first_seen_date": legacy_seen_date,
                    "last_seen_date": legacy_seen_date,
                    "campaigns_failing": 0,
                    "suite": suite_name,
                }

        obs_unquar = {d.fingerprint for d in suite_unquar}
        obs_quar = {d.fingerprint for d in suite_quar} - obs_unquar
        prev_suite_hist_keys = {
            fp for fp, meta in fp_history.items() if infer_fingerprint_suite(fp, meta) == suite_name
        }

        for fp in sorted(obs_unquar):
            prev_meta = fp_history.get(fp)
            if not isinstance(prev_meta, dict):
                # A regression of a previously resolved fingerprint continues its
                # original history instead of restarting it.
                prev_meta = resolved_history.get(fp)
            if isinstance(prev_meta, dict):
                first_seen = str(prev_meta.get("first_seen_date") or date_prefix)
                failing_cnt = _safe_nonneg_int(prev_meta.get("campaigns_failing"), 0) + 1
            else:
                first_seen = date_prefix
                failing_cnt = 1
            fp_history[fp] = {
                "first_seen_date": first_seen,
                "last_seen_date": date_prefix,
                "campaigns_failing": failing_cnt,
                "suite": suite_name,
            }
            resolved_history.pop(fp, None)

        # Still observed, but quarantined: not resolved; refresh `last_seen_date`
        # without counting a failing campaign, and ensure it is tracked in
        # `fp_history` (and removed from `resolved_history` if it regressed).
        for fp in sorted(obs_quar):
            prev_meta = fp_history.get(fp)
            if not isinstance(prev_meta, dict):
                prev_meta = resolved_history.get(fp)
            if isinstance(prev_meta, dict):
                first_seen = str(prev_meta.get("first_seen_date") or date_prefix)
                failing_cnt = _safe_nonneg_int(prev_meta.get("campaigns_failing"), 0)
            else:
                first_seen = date_prefix
                failing_cnt = 0
            fp_history[fp] = {
                "first_seen_date": first_seen,
                "last_seen_date": date_prefix,
                "campaigns_failing": failing_cnt,
                "suite": suite_name,
            }
            resolved_history.pop(fp, None)

        to_resolve = (
            (set(prev_suite_active) | set(prev_suite_quar) | prev_suite_hist_keys)
            - obs_unquar
            - obs_quar
        )
        for fp in sorted(to_resolve):
            prev_meta = fp_history.pop(fp, None) or {}
            resolved_history[fp] = {
                "first_seen_date": str(prev_meta.get("first_seen_date") or legacy_seen_date),
                "last_seen_date": str(prev_meta.get("last_seen_date") or legacy_seen_date),
                "campaigns_failing": _safe_nonneg_int(prev_meta.get("campaigns_failing"), 1),
                "resolved_date": date_prefix,
                "suite": suite_name,
            }

        new_active.extend(sorted(obs_unquar))
        new_quarantined.extend(sorted(obs_quar))

    ledger["active_fingerprints"] = new_active
    ledger["quarantined_fingerprints"] = new_quarantined
    ledger["fingerprint_history"] = fp_history
    ledger["resolved_history"] = resolved_history


def load_coverage_ratchet(ratchet_path: Path) -> dict[str, Any]:
    try:
        if not ratchet_path.is_file():
            return {}
        data = _strict_json_loads(ratchet_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, ValueError) as e:
        sys.stderr.write(
            f"warning: ignoring malformed or unreadable coverage ratchet {ratchet_path}: {e}\n"
        )
        return {}
    if not isinstance(data, dict):
        sys.stderr.write(
            f"warning: ignoring non-object coverage ratchet {ratchet_path} "
            f"(expected JSON object, got {type(data).__name__})\n"
        )
        return {}
    return data


BASELINE_RECOVERY_RECOVERED = "recovered"
BASELINE_RECOVERY_ABSENT = "absent"
BASELINE_RECOVERY_FAILED = "failed"
BASELINE_RECOVERY_SKIPPED = "skipped"


def _merge_ratchet_snapshots(
    baseline: dict[str, Any], overlay: dict[str, Any]
) -> dict[str, Any]:
    """Idempotently union-merges a recovered `baseline` ratchet with a local `overlay`."""
    merged_obs: dict[str, dict[str, Any]] = {}
    for src in (baseline, overlay):
        raw_obs = src.get("observed_paths", {})
        if not isinstance(raw_obs, dict):
            continue
        for k, v in raw_obs.items():
            if not isinstance(k, str) or not isinstance(v, dict):
                continue
            key = str(k)
            prev = merged_obs.get(key)
            if prev is None:
                entry = copy.deepcopy(v)
                entry["hit_count"] = max(1, _safe_nonneg_int(entry.get("hit_count"), 1))
                merged_obs[key] = entry
            else:
                b_first = prev.get("first_seen_utc")
                o_first = v.get("first_seen_utc")
                if (
                    isinstance(o_first, str)
                    and o_first
                    and (not isinstance(b_first, str) or not b_first or o_first < b_first)
                ):
                    prev["first_seen_utc"] = o_first
                    if isinstance(v.get("first_seen_seed"), str) and v["first_seen_seed"]:
                        prev["first_seen_seed"] = v["first_seen_seed"]
                elif (
                    not isinstance(prev.get("first_seen_seed"), str)
                    or not prev.get("first_seen_seed")
                ) and isinstance(v.get("first_seen_seed"), str) and v["first_seen_seed"]:
                    prev["first_seen_seed"] = v["first_seen_seed"]

                b_last = prev.get("last_seen_utc")
                o_last = v.get("last_seen_utc")
                if (
                    isinstance(o_last, str)
                    and o_last
                    and (not isinstance(b_last, str) or not b_last or o_last >= b_last)
                ):
                    prev["last_seen_utc"] = o_last
                    if isinstance(v.get("last_seen_seed"), str) and v["last_seen_seed"]:
                        prev["last_seen_seed"] = v["last_seen_seed"]
                elif (
                    not isinstance(prev.get("last_seen_seed"), str)
                    or not prev.get("last_seen_seed")
                ) and isinstance(v.get("last_seen_seed"), str) and v["last_seen_seed"]:
                    prev["last_seen_seed"] = v["last_seen_seed"]

                if prev.get("suite") not in ("miri", "itree") and v.get("suite") in (
                    "miri",
                    "itree",
                ):
                    prev["suite"] = v["suite"]
                if not (prev.get("derived") is True and v.get("derived") is True):
                    prev.pop("derived", None)
                prev["hit_count"] = max(
                    1,
                    _safe_nonneg_int(prev.get("hit_count"), 1),
                    _safe_nonneg_int(v.get("hit_count"), 1),
                )

    def suite_cnt(sk: str) -> int:
        return sum(
            1
            for k, v in merged_obs.items()
            if (v.get("suite") == sk) or (v.get("suite") is None and k.startswith(f"{sk}:"))
        )

    b_ps = baseline.get("per_suite_distinct_obs_paths")
    o_ps = overlay.get("per_suite_distinct_obs_paths")
    b_ps_dict = b_ps if isinstance(b_ps, dict) else {}
    o_ps_dict = o_ps if isinstance(o_ps, dict) else {}
    per_suite = {
        sk: max(
            _safe_nonneg_int(b_ps_dict.get(sk)),
            _safe_nonneg_int(o_ps_dict.get(sk)),
            suite_cnt(sk),
        )
        for sk in ("miri", "itree")
    }
    total = max(
        _safe_nonneg_int(baseline.get("cumulative_distinct_obs_paths")),
        _safe_nonneg_int(overlay.get("cumulative_distinct_obs_paths")),
        sum(per_suite.values()),
        len(merged_obs),
    )
    updated_candidates = [
        s
        for s in (baseline.get("updated_utc"), overlay.get("updated_utc"))
        if isinstance(s, str) and s
    ]
    out: dict[str, Any] = {
        "schema_version": 1,
        "updated_utc": max(updated_candidates) if updated_candidates else utc_now_iso(),
        "cumulative_distinct_obs_paths": total,
        "per_suite_distinct_obs_paths": per_suite,
        "observed_paths": merged_obs,
    }
    return out


def recover_baseline_coverage_ratchet(baseline_uri: str, ratchet_path: Path) -> str:
    """Populates a missing, corrupt, or incomplete `state/coverage_ratchet.json` from `baseline_uri`.

    Returns one of:
    - `BASELINE_RECOVERY_SKIPPED`: `baseline_uri` is empty or a valid complete local
      ratchet already exists at `ratchet_path`;
    - `BASELINE_RECOVERY_RECOVERED`: `baseline_uri` was parsed and written/merged into
      `ratchet_path`;
    - `BASELINE_RECOVERY_ABSENT`: `baseline_uri` points to a genuinely non-existent
      remote/local file (`not_found` / missing path);
    - `BASELINE_RECOVERY_FAILED`: `baseline_uri` was configured and either failed with
      a non-absent remote/I/O error or contained malformed/non-object JSON.
    """
    clean_uri = baseline_uri.strip()
    if not clean_uri:
        return BASELINE_RECOVERY_SKIPPED
    check_remote_uri(clean_uri)

    incomplete_overlay: dict[str, Any] | None = None
    try:
        local_lstat = os.lstat(ratchet_path)
    except FileNotFoundError:
        local_lstat = None
    except OSError as e:
        sys.stderr.write(
            f"warning: cannot access local coverage ratchet {ratchet_path}: {e}\n"
        )
        return BASELINE_RECOVERY_FAILED

    if local_lstat is not None:
        try:
            local_stat = (
                os.stat(ratchet_path)
                if stat.S_ISLNK(local_lstat.st_mode)
                else local_lstat
            )
        except OSError as e:
            sys.stderr.write(
                f"warning: local coverage ratchet {ratchet_path} is a broken symlink or "
                f"inaccessible ({e}); attempting recovery from baseline `{clean_uri}`\n"
            )
            local_stat = None

        if local_stat is not None:
            if stat.S_ISDIR(local_stat.st_mode):
                sys.stderr.write(
                    f"warning: local coverage ratchet {ratchet_path} is a directory\n"
                )
                return BASELINE_RECOVERY_FAILED
            if not stat.S_ISREG(local_stat.st_mode):
                sys.stderr.write(
                    f"warning: local coverage ratchet {ratchet_path} is not a regular file; "
                    f"attempting recovery from baseline `{clean_uri}`\n"
                )
            else:
                try:
                    existing = _strict_json_loads(
                        ratchet_path.read_text(encoding="utf-8")
                    )
                except (OSError, UnicodeDecodeError, ValueError) as e:
                    sys.stderr.write(
                        f"warning: local coverage ratchet {ratchet_path} is malformed or unreadable "
                        f"({e}); attempting recovery from baseline `{clean_uri}`\n"
                    )
                else:
                    if not isinstance(existing, dict):
                        sys.stderr.write(
                            f"warning: local coverage ratchet {ratchet_path} is not a JSON object "
                            f"(got {type(existing).__name__}); attempting recovery from baseline "
                            f"`{clean_uri}`\n"
                        )
                    elif (
                        existing.get("baseline_missing") is True
                        or existing.get("baseline_unmerged") is True
                    ):
                        incomplete_overlay = existing
                    else:
                        return BASELINE_RECOVERY_SKIPPED

    try:
        ratchet_path.parent.mkdir(parents=True, exist_ok=True)
    except OSError as e:
        sys.stderr.write(
            f"warning: cannot create parent directory for {ratchet_path}: {e}\n"
        )
        return BASELINE_RECOVERY_FAILED

    if clean_uri.startswith("/remote/"):
        if not has_remote_sync():
            sys.stderr.write(
                f"warning: cannot recover baseline coverage ratchet from `{clean_uri}`: "
                f"`{REMOTE_SYNC_BIN}` is not available\n"
            )
            return BASELINE_RECOVERY_FAILED
        fetch_dst = ratchet_path.parent / f".baseline_tmp_{os.getpid()}_coverage_ratchet.json"
        fetch_dst.unlink(missing_ok=True)
        res = run_remote_sync(["cp", "-f", clean_uri, str(fetch_dst)])
        if res.returncode != 0:
            fetch_dst.unlink(missing_ok=True)
            err_detail = (res.stderr or res.stdout or "").strip()
            suffix = f": {err_detail}" if err_detail else ""
            sys.stderr.write(
                f"warning: failed to fetch baseline coverage ratchet from `{clean_uri}` "
                f"(exit {res.returncode}){suffix}\n"
            )
            if err_detail and _is_absent_remote_error(err_detail):
                return BASELINE_RECOVERY_ABSENT
            return BASELINE_RECOVERY_FAILED
        if not fetch_dst.is_file():
            sys.stderr.write(
                f"warning: remote sync from `{clean_uri}` exited 0 without creating "
                f"{fetch_dst}\n"
            )
            return BASELINE_RECOVERY_FAILED
        try:
            parsed = _strict_json_loads(fetch_dst.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, ValueError) as e:
            fetch_dst.unlink(missing_ok=True)
            sys.stderr.write(
                f"warning: baseline coverage ratchet fetched from `{clean_uri}` is "
                f"malformed or unreadable: {e}\n"
            )
            return BASELINE_RECOVERY_FAILED
        fetch_dst.unlink(missing_ok=True)
        if not isinstance(parsed, dict):
            sys.stderr.write(
                f"warning: baseline coverage ratchet fetched from `{clean_uri}` is not "
                f"a JSON object (got {type(parsed).__name__})\n"
            )
            return BASELINE_RECOVERY_FAILED
        merged = _merge_ratchet_snapshots(parsed, incomplete_overlay or {})
        try:
            _atomic_write_text(
                ratchet_path, json.dumps(merged, indent=2, sort_keys=True) + "\n"
            )
        except OSError as e:
            sys.stderr.write(
                f"warning: failed to write recovered baseline coverage ratchet to "
                f"{ratchet_path}: {e}\n"
            )
            return BASELINE_RECOVERY_FAILED
        sys.stderr.write(
            f"info: populated missing {ratchet_path} from baseline `{clean_uri}`\n"
        )
        return BASELINE_RECOVERY_RECOVERED

    src_path = Path(clean_uri)
    try:
        src_lstat = os.lstat(src_path)
    except FileNotFoundError:
        sys.stderr.write(
            f"warning: baseline coverage ratchet `{clean_uri}` does not exist\n"
        )
        return BASELINE_RECOVERY_ABSENT
    except OSError as e:
        sys.stderr.write(
            f"warning: cannot access baseline coverage ratchet `{clean_uri}`: {e}\n"
        )
        return BASELINE_RECOVERY_FAILED

    try:
        src_stat = (
            os.stat(src_path) if stat.S_ISLNK(src_lstat.st_mode) else src_lstat
        )
    except OSError as e:
        sys.stderr.write(
            f"warning: baseline coverage ratchet `{clean_uri}` is a broken symlink or "
            f"inaccessible: {e}\n"
        )
        return BASELINE_RECOVERY_FAILED

    if not stat.S_ISREG(src_stat.st_mode):
        sys.stderr.write(
            f"warning: baseline coverage ratchet `{clean_uri}` is not a readable regular file\n"
        )
        return BASELINE_RECOVERY_FAILED

    try:
        raw_text = src_path.read_text(encoding="utf-8")
        parsed = _strict_json_loads(raw_text)
    except (OSError, UnicodeDecodeError, ValueError) as e:
        sys.stderr.write(
            f"warning: failed to read baseline coverage ratchet `{clean_uri}`: {e}\n"
        )
        return BASELINE_RECOVERY_FAILED
    if not isinstance(parsed, dict):
        sys.stderr.write(
            f"warning: baseline coverage ratchet `{clean_uri}` is not a JSON object "
            f"(got {type(parsed).__name__})\n"
        )
        return BASELINE_RECOVERY_FAILED
    merged = _merge_ratchet_snapshots(parsed, incomplete_overlay or {})
    try:
        _atomic_write_text(
            ratchet_path, json.dumps(merged, indent=2, sort_keys=True) + "\n"
        )
    except OSError as e:
        sys.stderr.write(
            f"warning: failed to write recovered baseline coverage ratchet to "
            f"{ratchet_path}: {e}\n"
        )
        return BASELINE_RECOVERY_FAILED
    sys.stderr.write(
        f"info: populated missing {ratchet_path} from baseline `{clean_uri}`\n"
    )
    return BASELINE_RECOVERY_RECOVERED


def extract_suite_obs_path_signatures(
    suite_key: str, summary: dict[str, Any], seed_val: int
) -> tuple[list[str], bool]:
    """Returns `(signatures, derived)` for a healthy suite summary.

    Live harness summaries carry `obs_path_signatures`, which are used verbatim
    (prefixed with `<suite_key>:` when needed), even when empty. Only summaries
    that omit the key entirely (unit-test mocks, pre-ratchet harness builds) fall
    back to coarse signatures derived from `mutator_applications` /
    `miri_verdicts` or `distinct_obs_paths`; those are flagged `derived=True`.
    """
    raw_sigs = summary.get("obs_path_signatures")
    if isinstance(raw_sigs, list):
        cleaned = sorted(
            {
                (
                    s.strip()
                    if s.strip().startswith(f"{suite_key}:")
                    else f"{suite_key}:{s.strip()}"
                )
                for s in raw_sigs
                if isinstance(s, str) and s.strip()
            }
        )
        return cleaned, False

    seed_hex = f"0x{seed_val:08x}"
    derived: set[str] = set()
    if suite_key == "miri":
        muts = summary.get("mutator_applications", {})
        verdicts = summary.get("miri_verdicts", {})
        active_muts = sorted(
            k
            for k, v in (muts.items() if isinstance(muts, dict) else [])
            if _safe_nonneg_int(v) > 0
        ) or ["identity"]
        active_verdicts = sorted(
            k
            for k, v in (verdicts.items() if isinstance(verdicts, dict) else [])
            if _safe_nonneg_int(v) > 0
        ) or ["pass"]
        for m in active_muts:
            for v in active_verdicts:
                derived.add(f"miri:derived:{m}@{seed_hex}:{v}")
    else:
        n_obs = max(1, _safe_nonneg_int(summary.get("distinct_obs_paths"), 1))
        for idx in range(n_obs):
            derived.add(f"itree:derived:seed@{seed_hex}:obs_{idx:04d}")
    return sorted(derived), True


def update_coverage_ratchet(
    ratchet_path: Path,
    ledger: dict[str, Any],
    miri_suite_healthy: bool,
    miri: dict[str, Any] | None,
    miri_seed: int,
    itree_suite_healthy: bool,
    itree: dict[str, Any] | None,
    itree_seed: int,
    force_baseline_missing: bool = False,
    persist_baseline_unmerged: bool | None = None,
    clear_baseline_unmerged: bool = False,
) -> tuple[Path, bool]:
    """Monotonically merges observation-path signatures from healthy suite(s)
    into `state/coverage_ratchet.json` and updates `ledger['cumulative_distinct_obs_paths']`.

    `observed_paths` only ever grows (set union), so `per_suite_distinct_obs_paths`
    and `cumulative_distinct_obs_paths` count distinct semantic observation paths
    ever observed by a healthy suite. Previous ratchet / ledger totals act as a
    floor if the ratchet file was lost or truncated.

    Returns `(ratchet_path, baseline_missing)`, where `baseline_missing` means the
    updated `observed_paths` union still holds fewer paths than the recorded
    cumulative or per-suite floor (e.g. the capsule launcher copied only
    `campaign_ledger.json` into a fresh state directory), so this run's union
    could not extend the history. The flag is also persisted in the ratchet until
    `observed_paths` catches up with the floor so consumers never mistake a
    partial union for the full cumulative set.
    """
    ratchet = load_coverage_ratchet(ratchet_path)
    raw_obs = ratchet.get("observed_paths", {})
    observed_paths: dict[str, dict[str, Any]] = {}
    if isinstance(raw_obs, dict):
        for k, v in raw_obs.items():
            if isinstance(k, str) and isinstance(v, dict):
                entry_copy = copy.deepcopy(v)
                entry_copy["hit_count"] = max(
                    1, _safe_nonneg_int(entry_copy.get("hit_count"), 1)
                )
                observed_paths[str(k)] = entry_copy
    now_utc = utc_now_iso()

    for suite_key, is_healthy, summary, seed_val in (
        ("miri", miri_suite_healthy, miri, miri_seed),
        ("itree", itree_suite_healthy, itree, itree_seed),
    ):
        if not is_healthy or summary is None:
            continue
        seed_hex = f"0x{seed_val:08x}"
        sigs, derived = extract_suite_obs_path_signatures(suite_key, summary, seed_val)
        for sig in sigs:
            prev = observed_paths.get(sig)
            if isinstance(prev, dict):
                if not isinstance(prev.get("first_seen_utc"), str) or not prev["first_seen_utc"]:
                    prev["first_seen_utc"] = now_utc
                if not isinstance(prev.get("first_seen_seed"), str) or not prev["first_seen_seed"]:
                    prev["first_seen_seed"] = seed_hex
                prev["last_seen_utc"] = now_utc
                prev["last_seen_seed"] = seed_hex
                prev["hit_count"] = max(1, _safe_nonneg_int(prev.get("hit_count"), 1)) + 1
                prev["suite"] = suite_key
                if not derived:
                    prev.pop("derived", None)
            else:
                entry: dict[str, Any] = {
                    "suite": suite_key,
                    "first_seen_utc": now_utc,
                    "last_seen_utc": now_utc,
                    "first_seen_seed": seed_hex,
                    "last_seen_seed": seed_hex,
                    "hit_count": 1,
                }
                if derived:
                    entry["derived"] = True
                observed_paths[sig] = entry

    def suite_count(suite_key: str) -> int:
        return sum(
            1
            for k, v in observed_paths.items()
            if (v.get("suite") == suite_key)
            or (v.get("suite") is None and k.startswith(f"{suite_key}:"))
        )

    prev_per_suite_raw = ratchet.get("per_suite_distinct_obs_paths")
    prev_per_suite = prev_per_suite_raw if isinstance(prev_per_suite_raw, dict) else {}
    per_suite = {
        key: max(_safe_nonneg_int(prev_per_suite.get(key)), suite_count(key))
        for key in ("miri", "itree")
    }

    new_total = max(
        _safe_nonneg_int(ratchet.get("cumulative_distinct_obs_paths")),
        _safe_nonneg_int(ledger.get("cumulative_distinct_obs_paths")),
        sum(per_suite.values()),
        len(observed_paths),
    )

    below_floor = len(observed_paths) < new_total or any(
        suite_count(k) < per_suite[k] for k in ("miri", "itree")
    )
    if persist_baseline_unmerged is None:
        persist_baseline_unmerged = force_baseline_missing
    baseline_unmerged = persist_baseline_unmerged or (
        not clear_baseline_unmerged and ratchet.get("baseline_unmerged") is True
    )
    baseline_missing = below_floor or baseline_unmerged or force_baseline_missing
    if baseline_missing:
        if below_floor:
            sys.stderr.write(
                f"warning: {ratchet_path} holds {len(observed_paths)} observation paths but the "
                f"recorded cumulative floor is {new_total}; this run cannot extend the "
                "cumulative set (provide state/coverage_ratchet.json alongside "
                "state/campaign_ledger.json to accumulate)\n"
            )
        else:
            sys.stderr.write(
                f"warning: {ratchet_path} could not merge a configured or corrupted "
                "prior coverage ratchet baseline; marking baseline_missing=true so "
                "this partial union is not mistaken for the full cumulative set\n"
            )

    updated_ratchet = {
        "schema_version": 1,
        "updated_utc": now_utc,
        "cumulative_distinct_obs_paths": new_total,
        "per_suite_distinct_obs_paths": per_suite,
        "observed_paths": observed_paths,
    }
    if baseline_missing:
        updated_ratchet["baseline_missing"] = True
    if baseline_unmerged:
        updated_ratchet["baseline_unmerged"] = True
    try:
        _atomic_write_text(
            ratchet_path, json.dumps(updated_ratchet, indent=2, sort_keys=True) + "\n"
        )
    except OSError as e:
        sys.stderr.write(
            f"warning: failed to write updated coverage ratchet {ratchet_path}: {e}\n"
        )
    ledger["cumulative_distinct_obs_paths"] = new_total
    return ratchet_path, baseline_missing


def markdown_code_fence_for(text: str) -> str:
    """Returns a backtick fence longer than any backtick run inside `text`."""
    longest = 0
    run = 0
    for ch in text:
        if ch == "`":
            run += 1
            longest = max(longest, run)
        else:
            run = 0
    return "`" * max(3, longest + 1)


def render_oracle_campaign_report(
    profile: CampaignProfile,
    date_prefix: str,
    miri: dict[str, Any] | None,
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
    coverage_ratchet_baseline_missing: bool = False,
) -> str:
    """Renders the full Markdown report for a live oracle campaign."""
    miri_performed = (
        miri is not None and miri.get("oracle_comparison") == "performed"
    )
    itree_performed = (
        include_itree
        and itree is not None
        and itree.get("oracle_comparison") == "performed"
        and itree_red_flags is not None
    )
    itree_failed = include_itree and not (
        itree_ran_without_oracle or (itree_performed and itree_red_flags.passed)
    )
    raw_divergences = (
        int(miri.get("diverge_count", 0)) if miri_performed and miri is not None else 0
    ) + (
        int(itree["diverge_traces"]) if itree_performed and itree is not None else 0
    )

    if not miri_performed or not miri_red_flags.passed or itree_failed:
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

    miri_mode_cell = (
        f"`{miri.get('mode', 'seeded')}`"
        if miri_performed and miri is not None
        else "`harness-failed`"
    )
    itree_mode_cell = (
        f"`{itree.get('mode', 'seeded')}`"
        if itree_performed and itree is not None
        else (
            "`compile-only`"
            if (include_itree and itree_ran_without_oracle)
            else ("`harness-failed`" if include_itree else "skipped")
        )
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

    if miri_performed and miri is not None:
        miri_total_cell = str(miri["total_candidates"])
        miri_compiled_cell = (
            f"{miri['compiled_candidates']} ({miri['compile_failed_candidates']} failed)"
        )
        miri_oracle_cell = "**performed**"
        miri_compared_cell = str(miri["compared_candidates"])
        miri_agreed_cell = str(miri["agree_count"])
        miri_diverged_cell = (
            f"{miri['diverge_count']} ({len(all_dedup) - len(itree_all_dedup)} distinct: "
            f"{len(unquarantined) - len(itree_unquarantined)} unquarantined, "
            f"{len(quarantined) - len(itree_quarantined)} quarantined)"
        )
        miri_kc_cell = str(miri["kernel_confirmed_divergences"])
        miri_not_compared_cell = str(miri["not_compared_count"])
        miri_elapsed_cell = f"{float(miri['elapsed_ms']):.1f} ms"
        banner_lines = [
            f"> **Status: {status}.**",
            f"> `miri-difftest` evaluated `{miri['compared_candidates']}/{miri['total_candidates']}` "
            f"candidates against live Miri (`-Zmiri-tree-borrows`) and Anneal's `MirSemantics` "
            f"oracle (`{miri['agree_count']}` agreed, `{miri['diverge_count']}` diverged, "
            f"`{miri['not_compared_count']}` not compared).",
        ]
    else:
        miri_total_cell = str(miri.get("total_candidates", "n/a")) if miri else "n/a"
        miri_compiled_cell = "n/a"
        miri_oracle_cell = "harness failed"
        miri_compared_cell = "0"
        miri_agreed_cell = "n/a"
        miri_diverged_cell = "n/a"
        miri_kc_cell = "n/a"
        miri_not_compared_cell = miri_total_cell
        miri_elapsed_cell = "n/a"
        banner_lines = [
            f"> **Status: {status}.**",
            "> `miri-difftest` failed to complete a valid live oracle comparison.",
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
        f"| Mode | {miri_mode_cell} | {itree_mode_cell} |",
        f"| Seed | `0x{miri_seed:08x}` | {itree_seed_cell} |",
        f"| Candidates generated | {miri_total_cell} | {itree_total_cell} |",
        f"| Compiled with `rustc` | {miri_compiled_cell} | {itree_compiled_cell} |",
        f"| Oracle comparison | {miri_oracle_cell} | {itree_oracle_cell} |",
        f"| Compared | {miri_compared_cell} | {itree_compared_cell} |",
        f"| Agreed | {miri_agreed_cell} | {itree_agreed_cell} |",
        f"| Diverged (raw / distinct) | {miri_diverged_cell} | {itree_diverged_cell} |",
        f"| Kernel-confirmed divergences (`by rfl`) | {miri_kc_cell} | {itree_kc_cell} |",
        f"| Not compared | {miri_not_compared_cell} | {itree_not_compared_cell} |",
        f"| Harness wall-clock | {miri_elapsed_cell} | {itree_elapsed_cell} |",
        "",
        f"Total campaign wall-clock: {elapsed_sec:.2f} s.",
    ]
    if coverage_ratchet_baseline_missing:
        lines.extend(
            [
                "",
                "> **Coverage ratchet warning**: the prior `state/coverage_ratchet.json` "
                "observation-path set was missing or incomplete, so this run's paths could "
                "not extend the cumulative set (`cumulative_distinct_obs_paths` kept its "
                "recorded floor).",
            ]
        )

    if miri_performed and miri is not None:
        lines.extend(
            [
                "",
                "## Miri & Anneal Outcome Breakdown (`miri-difftest`)",
                "",
                "| Miri Verdict | Count | Anneal Outcome | Count | Divergence Class | Count |",
                "| :--- | ---: | :--- | ---: | :--- | ---: |",
            ]
        )
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

        itree_nc_reasons = itree.get("not_compared_reasons")
        if isinstance(itree_nc_reasons, dict):
            lines.extend(
                [
                    "",
                    "## Not-Compared Breakdown by Reason (`itree-difftest`)",
                    "",
                    "| Reason | Count |",
                    "| :--- | ---: |",
                ]
            )
            for reason, count in sorted(itree_nc_reasons.items()):
                lines.append(f"| `{reason}` | {count} |")

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

    failed_suites = set()
    if not miri_performed or not miri_red_flags.passed:
        failed_suites.add("miri-difftest")
    if itree_failed:
        failed_suites.add("itree-difftest")
    failed_diags = {
        k: v
        for k, v in LAST_HARNESS_DIAGNOSTICS.items()
        if k in failed_suites and isinstance(v, dict)
    }
    if failed_diags:
        lines.extend(
            [
                "",
                "## Harness Subprocess Diagnostics",
                "",
            ]
        )
        for bin_name, diag in sorted(failed_diags.items()):
            lines.append(
                f"- **`{bin_name}`**: exit_code=`{diag.get('exit_code')}`, "
                f"elapsed_s=`{diag.get('elapsed_s')}`, "
                f"reason=`{diag.get('oracle_error_reason')}`"
            )
            tail = str(diag.get("stderr_tail") or "").strip()
            if tail:
                fence = markdown_code_fence_for(tail)
                lines.append(f"{fence}text")
                lines.append(tail)
                lines.append(fence)

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
    parser.add_argument("--profile", choices=sorted(PROFILES), default="quick")
    parser.add_argument(
        "--state-dir",
        type=Path,
        default=None,
        help="Local directory for the ledger, findings, and reports (default: a temporary directory).",
    )
    parser.add_argument(
        "--remote-uri",
        type=str,
        default="",
        help="remote directory to synchronize the ledger and reports with (default: no remote sync).",
    )
    parser.add_argument(
        "--baseline-ratchet-uri",
        type=str,
        default=os.environ.get("ANNEAL_BASELINE_RATCHET_URI", "").strip(),
        help=(
            "Optional fallback `/remote/...` URI or local JSON file path used to "
            "populate a missing `state/coverage_ratchet.json` before union-merging "
            "(default: `ANNEAL_BASELINE_RATCHET_URI`)."
        ),
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
        help=(
            "Maximum allowed oracle errors per suite before failing (default: 0): "
            "Miri/capture errors for miri-difftest, and candidates dropped by "
            "staging, native trace capture, or Lean probe/kernel-confirmation "
            "failures for itree-difftest."
        ),
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
        help="Optional path for JUnit XML (`diff_test_report.xml`).",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    profile = PROFILES[args.profile]
    repo_root = Path(__file__).resolve().parent.parent
    start_time = time.monotonic()

    remote_uri = args.remote_uri.strip()
    baseline_ratchet_uri = args.baseline_ratchet_uri.strip()
    try:
        check_remote_uri(remote_uri)
        check_remote_uri(baseline_ratchet_uri)
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
        LAST_HARNESS_DIAGNOSTICS.clear()
        remote_state_ok = sync_state_from_remote(
            remote_uri, state_dir, include_ratchet=not args.compile_only
        )
        (state_dir / "state").mkdir(parents=True, exist_ok=True)
        (state_dir / "reports").mkdir(parents=True, exist_ok=True)

        ledger_path = state_dir / "state" / "campaign_ledger.json"
        ratchet_path = state_dir / "state" / "coverage_ratchet.json"
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
            if "miri-difftest" not in LAST_HARNESS_DIAGNOSTICS:
                LAST_HARNESS_DIAGNOSTICS["miri-difftest"] = {
                    "exit_code": 0 if miri is not None else 1,
                    "oracle_error_reason": None if miri is not None else "harness_returned_none",
                    "stderr_tail": "",
                    "elapsed_s": (
                        round(float(miri["elapsed_ms"]) / 1000.0, 3)
                        if isinstance(miri, dict) and isinstance(miri.get("elapsed_ms"), (int, float))
                        else 0.0
                    ),
                }
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
            if not args.miri_only and "itree-difftest" not in LAST_HARNESS_DIAGNOSTICS:
                LAST_HARNESS_DIAGNOSTICS["itree-difftest"] = {
                    "exit_code": 0 if itree is not None else 1,
                    "oracle_error_reason": None if itree is not None else "harness_returned_none",
                    "stderr_tail": "",
                    "elapsed_s": (
                        round(float(itree["elapsed_ms"]) / 1000.0, 3)
                        if isinstance(itree, dict) and isinstance(itree.get("elapsed_ms"), (int, float))
                        else 0.0
                    ),
                }

        include_itree = not args.miri_only
        miri_status = miri.get("oracle_comparison") if isinstance(miri, dict) else None
        itree_status = itree.get("oracle_comparison") if isinstance(itree, dict) else None

        # Case 1: Neither harness performed an oracle comparison (compile-only mode
        # or stubbed non-oracle harnesses). When `--compile-only` was not passed,
        # `miri-difftest` returning `"not_performed"` is treated as a harness
        # failure (`EXIT_HARNESS_FAILED`).
        if args.compile_only or (
            miri_status != "performed"
            and (not include_itree or itree_status != "performed")
        ):
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
                    ledger["total_itree_candidates_generated"] = (
                        prev_itree_gen
                        + _safe_nonneg_int(itree.get("total_candidates"), 0)
                    )
                ledger["total_campaigns_run"] = prev_campaigns + 1
                ledger["total_miri_candidates_generated"] = (
                    prev_miri_gen + _safe_nonneg_int(miri.get("total_candidates"), 0)
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

            sync_state_to_remote(
                state_dir,
                remote_uri,
                _filter_written_for_remote(
                    state_dir, remote_uri, written, remote_state_ok
                ),
            )
            print(report_md)
            return EXIT_HARNESS_FAILED if harness_failed else EXIT_NOT_EVALUATED

        # Case 2: At least one harness reported `"oracle_comparison": "performed"`.
        valid_miri, err_reason = (
            validate_performed_miri_summary(miri)
            if isinstance(miri, dict) and miri_status == "performed"
            else (False, "miri-difftest did not perform oracle comparison")
        )
        itree_ran_without_oracle = (
            isinstance(itree, dict) and itree_status == "not_performed"
        )
        itree_claimed_performed = (
            include_itree and isinstance(itree, dict) and itree_status == "performed"
        )
        valid_itree, itree_err = (
            validate_performed_itree_summary(itree)
            if itree_claimed_performed and itree is not None
            else (False, "itree-difftest did not perform oracle comparison")
        )

        if not valid_miri and isinstance(miri, dict) and miri_status == "performed":
            sys.stderr.write(f"miri-difftest produced invalid oracle summary: {err_reason}\n")
            LAST_HARNESS_DIAGNOSTICS.setdefault("miri-difftest", {})[
                "oracle_error_reason"
            ] = f"invalid_summary: {err_reason}"
        elif isinstance(miri, dict) and miri_status != "performed":
            sys.stderr.write(
                f"miri-difftest reported unsupported oracle_comparison={miri_status!r} "
                "in a live oracle campaign\n"
            )
            diag = LAST_HARNESS_DIAGNOSTICS.setdefault("miri-difftest", {})
            if not diag.get("oracle_error_reason"):
                diag["oracle_error_reason"] = f"oracle_comparison={miri_status!r}"
        if not valid_itree and itree_claimed_performed:
            sys.stderr.write(
                f"itree-difftest produced invalid oracle summary: {itree_err}\n"
            )
            LAST_HARNESS_DIAGNOSTICS.setdefault("itree-difftest", {})[
                "oracle_error_reason"
            ] = f"invalid_summary: {itree_err}"
        elif (
            include_itree
            and isinstance(itree, dict)
            and itree_status not in ("performed", "not_performed")
        ):
            sys.stderr.write(
                f"itree-difftest reported unsupported oracle_comparison={itree_status!r}\n"
            )
            diag = LAST_HARNESS_DIAGNOSTICS.setdefault("itree-difftest", {})
            if not diag.get("oracle_error_reason"):
                diag["oracle_error_reason"] = f"oracle_comparison={itree_status!r}"

        # If neither suite produced a structurally valid performed summary, fall back
        # to the 25-line `HARNESS FAILED` report without touching the ledger.
        if not valid_miri and not valid_itree:
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
            sync_state_to_remote(state_dir, remote_uri, written)
            print(report_md)
            return EXIT_HARNESS_FAILED

        miri_performed = valid_miri and miri is not None
        if miri_performed and miri is not None:
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
                LAST_HARNESS_DIAGNOSTICS.setdefault("miri-difftest", {})[
                    "oracle_error_reason"
                ] = "; ".join(miri_red_flags.failure_reasons)
        else:
            miri_red_flags = RedFlagResult(
                passed=False,
                checks={"oracle_invoked": False},
                failure_reasons=[f"miri_harness_failed: {err_reason}"],
            )
            for reason in miri_red_flags.failure_reasons:
                sys.stderr.write(f"red-flag check failed: {reason}\n")

        itree_performed = valid_itree and itree is not None
        itree_red_flags: RedFlagResult | None = None
        itree_all_dedup: list[DeduplicatedFinding] = []
        itree_unquarantined: list[DeduplicatedFinding] = []
        itree_quarantined: list[DeduplicatedFinding] = []
        if include_itree and itree_claimed_performed and itree is not None:
            if not valid_itree:
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
                    args.max_oracle_errors,
                )
                if not itree_red_flags.passed:
                    for reason in itree_red_flags.failure_reasons:
                        sys.stderr.write(f"red-flag check failed: {reason}\n")
                    LAST_HARNESS_DIAGNOSTICS.setdefault("itree-difftest", {})[
                        "oracle_error_reason"
                    ] = "; ".join(itree_red_flags.failure_reasons)
                (
                    itree_all_dedup,
                    itree_unquarantined,
                    itree_quarantined,
                ) = deduplicate_and_quarantine_itree_findings(
                    itree["findings"],
                    quarantine_rules,
                )

        known_corpus_bug_seeds = load_known_corpus_bug_seeds(repo_root)
        miri_all_dedup: list[DeduplicatedFinding] = []
        miri_unquarantined: list[DeduplicatedFinding] = []
        miri_quarantined: list[DeduplicatedFinding] = []
        if miri_performed and miri is not None:
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

        miri_suite_healthy = bool(miri_performed and miri_red_flags.passed)
        itree_suite_healthy = bool(
            include_itree
            and itree_performed
            and itree_red_flags is not None
            and itree_red_flags.passed
        )
        itree_ok = (not include_itree) or itree_ran_without_oracle or itree_suite_healthy
        harness_or_red_flag_failed = (not miri_suite_healthy) or (not itree_ok)

        written: list[Path] = []
        if miri_performed and miri is not None and isinstance(miri.get("findings"), list):
            written.extend(collect_finding_bundle_files(miri["findings"], state_dir))
        if (
            include_itree
            and itree_performed
            and itree is not None
            and isinstance(itree.get("findings"), list)
        ):
            written.extend(collect_finding_bundle_files(itree["findings"], state_dir))

        ratchet_baseline_missing = False
        if miri_suite_healthy or itree_suite_healthy:
            ledger["schema_version"] = 1
            ledger.setdefault("next_miri_seed", f"0x{miri_seed:08x}")
            ledger.setdefault("next_itree_seed", f"0x{itree_seed:08x}")
            ledger.setdefault("total_miri_candidates_generated", prev_miri_gen)
            ledger.setdefault("total_miri_candidates_evaluated", prev_miri_eval)
            ledger.setdefault("total_itree_candidates_generated", prev_itree_gen)
            ledger.setdefault("total_itree_candidates_evaluated", prev_itree_eval)
            ledger.setdefault("total_itree_traces_checked", prev_itree_traces)

            if miri_suite_healthy and miri is not None:
                ledger["next_miri_seed"] = f"0x{advance_seed(miri_seed):08x}"
                ledger["total_miri_candidates_generated"] = prev_miri_gen + int(
                    miri.get("total_candidates", 0)
                )
                ledger["total_miri_candidates_evaluated"] = prev_miri_eval + int(
                    miri.get("compared_candidates", 0)
                )
                ledger["last_miri_seed"] = f"0x{miri_seed:08x}"
                ledger["last_miri_signature"] = miri_signature_for_seed_check(miri)

            if itree_suite_healthy and itree is not None:
                ledger["next_itree_seed"] = f"0x{advance_seed(itree_seed):08x}"
                ledger["total_itree_candidates_generated"] = prev_itree_gen + int(
                    itree.get("total_candidates", 0)
                )
                ledger["total_itree_candidates_evaluated"] = prev_itree_eval + int(
                    itree.get("compared_candidates", 0)
                )
                ledger["total_itree_traces_checked"] = prev_itree_traces + int(
                    itree.get("distinct_traces_checked", 0)
                )
                ledger["last_itree_seed"] = f"0x{itree_seed:08x}"
                ledger["last_itree_signature"] = itree_signature_for_seed_check(itree)
            elif include_itree and itree_ran_without_oracle and itree is not None:
                ledger["next_itree_seed"] = f"0x{advance_seed(itree_seed):08x}"
                ledger["total_itree_candidates_generated"] = prev_itree_gen + _safe_nonneg_int(
                    itree.get("total_candidates"), 0
                )

            prev_per_suite = (
                ledger.get("per_suite_runs")
                if isinstance(ledger.get("per_suite_runs"), dict)
                else {}
            )
            ledger["per_suite_runs"] = {
                "itree": _safe_nonneg_int(prev_per_suite.get("itree"), 0)
                + (1 if itree_suite_healthy else 0),
                "miri": _safe_nonneg_int(prev_per_suite.get("miri"), 0)
                + (1 if miri_suite_healthy else 0),
            }

            update_suite_scoped_fingerprints(
                ledger,
                date_prefix,
                miri_suite_healthy,
                miri_unquarantined,
                miri_quarantined,
                itree_suite_healthy,
                itree_unquarantined,
                itree_quarantined,
            )

            local_ratchet_corrupt = False
            try:
                local_lstat = os.lstat(ratchet_path)
            except FileNotFoundError:
                local_lstat = None
            except OSError:
                local_ratchet_corrupt = True
                local_lstat = None
            if local_lstat is not None:
                try:
                    local_stat = (
                        os.stat(ratchet_path)
                        if stat.S_ISLNK(local_lstat.st_mode)
                        else local_lstat
                    )
                except OSError:
                    local_ratchet_corrupt = True
                else:
                    if not stat.S_ISREG(local_stat.st_mode):
                        local_ratchet_corrupt = True
                    else:
                        try:
                            probe_obj = _strict_json_loads(
                                ratchet_path.read_text(encoding="utf-8")
                            )
                            if not isinstance(probe_obj, dict):
                                local_ratchet_corrupt = True
                        except (OSError, UnicodeDecodeError, ValueError):
                            local_ratchet_corrupt = True

            recovery_status = (
                recover_baseline_coverage_ratchet(baseline_ratchet_uri, ratchet_path)
                if baseline_ratchet_uri
                else BASELINE_RECOVERY_SKIPPED
            )
            configured_baseline_failed = recovery_status == BASELINE_RECOVERY_FAILED
            configured_baseline_absent = recovery_status == BASELINE_RECOVERY_ABSENT
            unrecovered_local_corrupt = (
                local_ratchet_corrupt
                and recovery_status != BASELINE_RECOVERY_RECOVERED
            )

            _, ratchet_baseline_missing = update_coverage_ratchet(
                ratchet_path,
                ledger,
                miri_suite_healthy,
                miri if miri_performed else None,
                miri_seed,
                itree_suite_healthy,
                itree if itree_performed else None,
                itree_seed,
                force_baseline_missing=(
                    configured_baseline_failed or unrecovered_local_corrupt
                ),
                persist_baseline_unmerged=configured_baseline_failed,
                clear_baseline_unmerged=configured_baseline_absent,
            )
            try:
                if ratchet_path.is_file():
                    written.append(ratchet_path)
            except OSError:
                pass

            ledger["total_campaigns_run"] = prev_campaigns + 1
            ledger["last_run_utc"] = utc_now_iso()
            ledger["last_profile"] = profile.name
            if miri_suite_healthy and (not include_itree or itree_suite_healthy):
                ledger["last_oracle_comparison"] = "performed"
            elif miri_suite_healthy and itree_ran_without_oracle:
                ledger["last_oracle_comparison"] = "miri_performed_itree_not_performed"
            elif miri_suite_healthy:
                ledger["last_oracle_comparison"] = "miri_performed_itree_failed"
            else:
                ledger["last_oracle_comparison"] = "miri_failed_itree_performed"

            ledger_path.write_text(
                json.dumps(ledger, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
            written.append(ledger_path)

        elapsed_sec = time.monotonic() - start_time
        # Only structurally valid performed summaries (or honest `not_performed`
        # summaries) are rendered cell-by-cell; an invalid `performed` claim is
        # rendered as `harness-failed` alongside its synthetic red-flag failure.
        itree_for_report = itree if (itree_performed or itree_ran_without_oracle) else None
        report_md = render_oracle_campaign_report(
            profile,
            date_prefix,
            miri if miri_performed else None,
            miri_red_flags,
            all_dedup,
            unquarantined,
            quarantined,
            include_itree,
            itree_for_report,
            itree_red_flags,
            itree_all_dedup,
            itree_unquarantined,
            itree_quarantined,
            itree_ran_without_oracle,
            miri_seed,
            itree_seed,
            elapsed_sec,
            coverage_ratchet_baseline_missing=ratchet_baseline_missing,
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
            "miri_oracle_comparison": (
                "performed" if miri_performed else "failed"
            ),
            "itree_oracle_comparison": (
                "performed"
                if itree_suite_healthy
                else (
                    "not_performed"
                    if (include_itree and itree_ran_without_oracle)
                    else ("failed" if include_itree else "skipped")
                )
            ),
            "red_flags": {
                "passed": miri_suite_healthy and (not include_itree or itree_ran_without_oracle or itree_suite_healthy),
                "checks": combined_checks,
                "failure_reasons": combined_reasons,
            },
            "harness_diagnostics": copy.deepcopy(LAST_HARNESS_DIAGNOSTICS),
            "coverage_ratchet_baseline_missing": ratchet_baseline_missing,
            "miri_summary": miri,
            "itree_summary": itree if include_itree else None,
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
                miri if miri_performed else None,
                miri_red_flags,
                miri_unquarantined,
                include_itree,
                itree_for_report,
                itree_red_flags,
                itree_unquarantined,
                itree_ran_without_oracle,
                elapsed_sec,
            )

        sync_state_to_remote(
            state_dir,
            remote_uri,
            _filter_written_for_remote(
                state_dir, remote_uri, written, remote_state_ok
            ),
        )
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
