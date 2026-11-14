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
vacuity checks (including the `WitnessPolarity` accounting of every
`miri-difftest` non-agreement), deduplicates and optionally quarantines
divergence findings, updates the persistent campaign ledger, and writes Markdown,
JSON, and JUnit XML reports.

Exit status:
  0  `miri-difftest` performed real oracle comparisons, passed all red-flag
     vacuity checks, had oracle errors within threshold, and produced zero
     unquarantined divergences (and `itree-difftest`, if enabled, did not fail);
  1  internal error, such as a ledger that is not a valid JSON object;
  2  invalid command line, harness crash, missing Miri/Lean toolchain,
     malformed harness JSON, red-flag vacuity failure (`zero_compared_items`,
     `impossible_wall_clock`, `identical_metrics_across_seeds`,
     `oracle_not_invoked`, `witness_polarity_accounting_mismatch`), or oracle
     errors above `--max-oracle-errors` (in either suite). Ledger state of a
     suite that completed a healthy live oracle run is still committed when the
     other suite fails;
  3  compile-only mode (`--compile-only`): neither harness crashed, and both
     harnesses reported `"oracle_comparison": "not_performed"`;
  4  one or more unquarantined divergences were detected by a live oracle run.

Gates (`--self-check-mutants`, `--check-stale-ratchet`; both on by default for
`--profile nightly`) run alongside any campaign and turn its exit status into 2
when they fail. Requested without a profile, seeds, `--miri-identity`,
`--miri-only`, `--compile-only`, remote sync, or `--junit-xml`, they run alone
(`standalone_gate` mode: exit 0 when every gate passes, else 2) and leave the
campaign ledger untouched.
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


def _reject_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    obj: dict[str, Any] = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError(f"duplicate JSON object key {key!r}")
        obj[key] = value
    return obj


def _strict_json_loads(raw_text: str, reject_duplicate_keys: bool = False) -> Any:
    """`json.loads` without `NaN` / `Infinity`; with `reject_duplicate_keys` (harness
    summaries, whose maps `miri-difftest` / `itree-difftest` render from unique keys)
    a repeated object key is rejected instead of silently keeping its last value."""
    return json.loads(
        raw_text,
        parse_constant=_reject_json_constant,
        object_pairs_hook=_reject_duplicate_json_keys if reject_duplicate_keys else None,
    )


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

# Canonical `WitnessPolarity` slugs, in `WITNESS_POLARITY_NAMES` order
# (`crates/anneal-difftest/src/miri_eval.rs`). Every non-agreement of a
# `miri-difftest` run has exactly one polarity, and agreement has none:
# - `unsound_missed_fault`: Miri faults (`ub` / `panic`) and Anneal does not
#   report that fault (`missed_ub`, `panic_vs_return`), the P0 soundness direction;
# - `sound_conservative_abstraction`: Miri reports no UB while Anneal reports `ub`
#   (`false_positive_ub`), or Miri returns normally while Anneal is `unsupported`;
# - `value_mismatch`: different values or fault locations (`wrong_value`,
#   `return_vs_panic`, `ub_location_mismatch`, `panic_site_mismatch`);
# - `harness_or_extraction_error`: no semantic comparison was possible (compile,
#   Miri, capture or Lean failure, fuel, external call, or `unsupported` when Miri
#   itself faulted).
WITNESS_POLARITY_UNSOUND = "unsound_missed_fault"
WITNESS_POLARITY_CONSERVATIVE = "sound_conservative_abstraction"
WITNESS_POLARITY_VALUE_MISMATCH = "value_mismatch"
WITNESS_POLARITY_HARNESS = "harness_or_extraction_error"
VALID_WITNESS_POLARITIES = (
    WITNESS_POLARITY_UNSOUND,
    WITNESS_POLARITY_CONSERVATIVE,
    WITNESS_POLARITY_VALUE_MISMATCH,
    WITNESS_POLARITY_HARNESS,
)

# `classify_divergence_kind_polarity`: each divergence class has one polarity.
DIVERGENCE_CLASS_WITNESS_POLARITY: dict[str, str] = {
    "wrong_value": WITNESS_POLARITY_VALUE_MISMATCH,
    "false_positive_ub": WITNESS_POLARITY_CONSERVATIVE,
    "missed_ub": WITNESS_POLARITY_UNSOUND,
    "ub_location_mismatch": WITNESS_POLARITY_VALUE_MISMATCH,
    "panic_vs_return": WITNESS_POLARITY_UNSOUND,
    "return_vs_panic": WITNESS_POLARITY_VALUE_MISMATCH,
    "panic_site_mismatch": WITNESS_POLARITY_VALUE_MISMATCH,
}

# Kill class that the semantic-mutant self-check reports when the campaign
# pipeline rejects a run as a harness failure (`EXIT_HARNESS_FAILED`).
HARNESS_ERROR_KILL_CLASS = "harness_error"

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
    # Whether `--self-check-mutants` and `--check-stale-ratchet` default to on.
    gates_by_default: bool = False


PROFILES: dict[str, CampaignProfile] = {
    "smoke": CampaignProfile("smoke", 2, 8, 2, 8),
    "quick": CampaignProfile("quick", 5, 32, 5, 32),
    "nightly": CampaignProfile("nightly", 25, 32, 25, 32, gates_by_default=True),
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
    # `WitnessPolarity` slug of a `miri-difftest` fingerprint (determined by its
    # divergence class); `None` for `itree-difftest` fingerprints, whose
    # `TraceReplayDiag` tags carry no Miri / Anneal soundness direction.
    witness_polarity: str | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "fingerprint": self.fingerprint,
            "cause": self.cause,
            "seed_name": self.seed_name,
            "divergence_class": self.divergence_class,
            "witness_polarity": self.witness_polarity,
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
        summary = _strict_json_loads(
            json_path.read_text(encoding="utf-8"), reject_duplicate_keys=True
        )
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
    # `miri-difftest` always emits `witness_polarity_counts` with exactly the four
    # `WITNESS_POLARITY_NAMES` keys; a summary without it comes from a stale or
    # foreign harness binary and is rejected rather than trusted.
    if not is_int_map(summary.get("witness_polarity_counts"), VALID_WITNESS_POLARITIES):
        return False, "missing or invalid 'witness_polarity_counts' map"
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
    # Legacy prefixes plus the tags the Rust harness actually emits for not-compared
    # outcomes (`MiriOutcome::summary_tag` / `AnnealOutcome::summary_tag`): a finding
    # whose outcome is an oracle or capture error, `unsupported`, an external call, or
    # fuel exhaustion is a masked not-compared item, never a divergence.
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
        "not_compared",
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
        miri_out_trimmed = _rust_trim(f["miri_outcome"])
        anneal_out_trimmed = _rust_trim(f["anneal_outcome"])
        if miri_out_trimmed == anneal_out_trimmed:
            return (
                False,
                f"finding[{idx}] is not a divergence: miri_outcome == anneal_outcome",
            )
        if miri_out_trimmed.startswith(not_compared_prefixes) or anneal_out_trimmed.startswith(
            not_compared_prefixes
        ):
            return (
                False,
                f"finding[{idx}] has a not-compared outcome instead of a divergence",
            )
        # `applied_mutators` decides the finding's cause, and so its fingerprint and
        # quarantine keys (`infer_finding_cause`); `miri-difftest` always emits a list
        # of mutator names (empty for an unmutated candidate).
        mutators = f.get("applied_mutators")
        if not isinstance(mutators, list) or not all(
            isinstance(m, str) and m.strip() for m in mutators
        ):
            return (
                False,
                f"finding[{idx}] has missing or malformed 'applied_mutators' {mutators!r}",
            )
        if not isinstance(f.get("kernel_confirmed"), bool):
            return False, f"finding[{idx}] has non-boolean 'kernel_confirmed'"
        polarity = f.get("witness_polarity")
        if not isinstance(polarity, str) or polarity not in VALID_WITNESS_POLARITIES:
            return False, f"finding[{idx}] has missing or invalid 'witness_polarity' {polarity!r}"
        expected_polarity = DIVERGENCE_CLASS_WITNESS_POLARITY[f["divergence_class"]]
        if polarity != expected_polarity:
            return (
                False,
                f"finding[{idx}] has witness_polarity {polarity!r}, but its divergence_class "
                f"{f['divergence_class']!r} has polarity {expected_polarity!r}",
            )

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
        if "seed_index" in f and not is_nonneg_int(f.get("seed_index")):
            return (
                False,
                f"itree finding[{idx}] has invalid 'seed_index' {f.get('seed_index')!r}",
            )
        if "applied_mutators" in f:
            it_muts = f.get("applied_mutators")
            if not isinstance(it_muts, list) or not all(
                isinstance(m, str) and m.strip() for m in it_muts
            ):
                return (
                    False,
                    f"itree finding[{idx}] has invalid 'applied_mutators' {it_muts!r}",
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


# The `TraceReplayDiag` constructor behind each `TraceReplayDiag.tagName`
# (`theory/Anneal/Rustc/V2026_06_01/TraceCheck.lean`). A finding's `diag_repr` is
# Lean's `reprStr` of the value, which names the constructor, not the tag.
ITREE_DIAG_TAG_CONSTRUCTORS: dict[str, str] = {
    "ok": "ok",
    "decode_arg_failed": "decodeArgFailed",
    "decode_event_failed": "decodeEventFailed",
    "decode_outcome_failed": "decodeOutcomeFailed",
    "impure_ext_call_ptr_arg": "impureExtCallPtrArg",
    "step_faulted": "stepFaulted",
    "unexpected_ext_call": "unexpectedExtCall",
    "call_arg_mismatch": "callArgMismatch",
    "branch_tag_mismatch": "branchTagMismatch",
    "unconsumed_events": "unconsumedEventsRemaining",
    "outcome_mismatch": "outcomeMismatch",
    "out_of_fuel": "outOfFuel",
}


def _itree_diag_repr_matches_tag(diag_repr: str, tag: str) -> bool:
    """Whether `diag_repr`, Lean's `reprStr` of a `TraceReplayDiag` (for example
    `TraceReplayDiag.unconsumedEventsRemaining 2`, possibly parenthesized or cut
    after the constructor), names the constructor whose `tagName` is `tag`
    (`ITREE_DIAG_TAG_CONSTRUCTORS`). The tag spelling `TraceReplayDiag.<tag>` used
    by synthetic reports is accepted too."""
    clean = diag_repr.strip()
    while clean.startswith("(") and clean.endswith(")"):
        clean = clean[1:-1].strip()
    names = {tag, ITREE_DIAG_TAG_CONSTRUCTORS.get(tag, tag)}
    return any(
        re.fullmatch(rf"TraceReplayDiag\.{re.escape(name)}(?:\s.*)?", clean, re.DOTALL)
        for name in names
    )


def _itree_finding_trace_was_shrunk(finding: dict[str, Any]) -> bool:
    """Whether `itree-difftest` may have replaced this finding's batch trace with a
    trace of its shrink's re-run (`assign_minimized_traces`). That happens whenever
    the shrink shortened the mutator chain: under `shrink_status == "minimized"`, and
    also under `inconclusive_oracle_failure` when some queries failed but a shorter
    chain still reproduced the signature."""
    if finding.get("shrink_status") == "minimized":
        return True
    original = finding.get("original_mutator_chain")
    minimized = finding.get("minimized_mutator_chain")
    return (
        isinstance(original, list)
        and isinstance(minimized, list)
        and len(minimized) < len(original)
    )


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
    # `itree-difftest` emits one finding per diverging distinct trace, tagged with
    # that trace's `TraceReplayDiag` tag, so the findings must reproduce the
    # non-`ok` `diag_tag_counts` exactly, cover `diverge_candidates` distinct
    # `fn_name`s, carry distinct `finding_id`s, and carry a `diag_repr` of their
    # tag's constructor (`_itree_diag_repr_matches_tag`). A finding names its trace
    # by `case_ident` (`case_<fn_name>_t<i>`, so no two candidates ever share one).
    # Findings that kept their batch trace name distinct traces. A shrink that
    # shortened the chain instead substitutes traces of its own staged re-run of
    # the candidate (`assign_minimized_traces`), numbered afresh in the same
    # namespace and reused round-robin when the re-run has fewer witnesses than
    # findings, so such a finding may repeat any `case_ident` of its own candidate
    # (`_itree_finding_trace_was_shrunk`).
    finding_tags: dict[str, int] = {}
    finding_fns: set[str] = set()
    seen_finding_ids: set[str] = set()
    duplicate_finding_ids: set[str] = set()
    case_fns: dict[str, set[str]] = {}
    batch_trace_cases: dict[str, int] = {}
    repr_mismatches: list[str] = []
    for f in findings:
        if not isinstance(f, dict):
            continue
        fid = f.get("finding_id")
        if isinstance(fid, str):
            if fid in seen_finding_ids:
                duplicate_finding_ids.add(fid)
            seen_finding_ids.add(fid)
        fn_name = f.get("fn_name")
        if isinstance(fn_name, str) and fn_name.strip():
            finding_fns.add(fn_name.strip())
        tag = f.get("diag_tag")
        if isinstance(tag, str):
            finding_tags[tag] = finding_tags.get(tag, 0) + 1
            diag_repr = f.get("diag_repr")
            if isinstance(diag_repr, str) and not _itree_diag_repr_matches_tag(diag_repr, tag):
                repr_mismatches.append(f"{fid}:{tag}!={diag_repr!r}")
        case_ident = f.get("case_ident")
        if isinstance(case_ident, str):
            case_fns.setdefault(case_ident, set()).add(str(fn_name))
            if not _itree_finding_trace_was_shrunk(f):
                batch_trace_cases[case_ident] = batch_trace_cases.get(case_ident, 0) + 1
    duplicate_cases = {c for c, fns in case_fns.items() if len(fns) > 1} | {
        c for c, count in batch_trace_cases.items() if count > 1
    }
    tag_mismatches = {
        tag: (finding_tags.get(tag, 0), int(diag_counts.get(tag, 0)))
        for tag in sorted(set(diag_counts) | set(finding_tags))
        if tag != "ok" and finding_tags.get(tag, 0) != int(diag_counts.get(tag, 0))
    }
    if tag_mismatches or duplicate_cases or duplicate_finding_ids or repr_mismatches:
        oracle_invoked = False
        reasons.append(
            f"itree_oracle_not_invoked: findings per diag_tag (findings, diag_tag_counts) "
            f"{tag_mismatches} disagree, repeat traces {sorted(duplicate_cases)}, "
            f"repeat finding_ids {sorted(duplicate_finding_ids)}, or mismatch diag_repr "
            f"{repr_mismatches}"
        )
    if finding_fns and len(finding_fns) != diverge_cands:
        oracle_invoked = False
        reasons.append(
            f"itree_oracle_not_invoked: findings cover {len(finding_fns)} distinct "
            f"candidate fn_name(s) ({sorted(finding_fns)}) != diverge_candidates ({diverge_cands})"
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

    itree_boundary_ok, itree_boundary_reasons = validate_itree_error_boundary(summary)
    reasons.extend(itree_boundary_reasons)

    checks = {
        "itree_oracle_invoked": oracle_invoked,
        "itree_non_zero_compared": non_zero_compared,
        "itree_plausible_wall_clock": plausible_wall_clock,
        "itree_seed_sensitivity": seed_sensitive,
        "itree_oracle_error_threshold": within_error_threshold,
        "itree_error_vs_compile_failed_boundary": itree_boundary_ok,
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

    # 5. Oracle error count within threshold: each errored item counts once, although
    #    a Miri error is both a `miri_verdicts.error` and a `miri_oracle_error`, and a
    #    capture failure both an `anneal_outcomes.error` and a `capture_failed`.
    oracle_errors = count_distinct_miri_errored_items(summary)
    within_error_threshold = oracle_errors <= max_oracle_errors
    if not within_error_threshold:
        reasons.append(
            f"oracle_errors_exceeded: {oracle_errors} oracle/capture errors > max_oracle_errors ({max_oracle_errors})"
        )

    # 6. `error` vs. `unsupported` boundary: precedence-derived accounting, crash
    #    markers masked under `unsupported`, and the per-item verdict audit. (Its
    #    own oracle-error budget reason duplicates check 5 and is dropped here.)
    _, boundary_reasons = validate_error_vs_unsupported_boundary(summary, max_oracle_errors)
    boundary_failures = [
        r for r in boundary_reasons if not r.startswith("oracle_errors_exceeded")
    ]
    for reason in boundary_failures:
        if reason not in reasons:
            reasons.append(reason)

    # 7. `WitnessPolarity` accounting: the identities of Rust's
    #    `witness_polarity_accounting_holds` plus per-finding and (with
    #    `item_outcomes`) per-item recomputation of every polarity from its tags.
    polarity_failures = witness_polarity_accounting_problems(summary)
    for reason in polarity_failures:
        if reason not in reasons:
            reasons.append(reason)

    checks = {
        "oracle_invoked": oracle_invoked,
        "non_zero_compared": non_zero_compared,
        "plausible_wall_clock": plausible_wall_clock,
        "seed_sensitivity": seed_sensitive,
        "oracle_error_threshold": within_error_threshold,
        "error_vs_unsupported_boundary": not boundary_failures,
        "witness_polarity_accounting": not polarity_failures,
    }
    return RedFlagResult(
        passed=all(checks.values()),
        checks=checks,
        failure_reasons=reasons,
    )


# Crash, internal-error, and malformed-input markers that must never appear in a
# record the harness classified as `unsupported` (or, for `itree-difftest`,
# `compile_failed`): such an item errored (Miri, `rustc`, or Lean crashed or
# rejected its input) and belongs in a bucket that counts against
# `--max-oracle-errors`.
ERROR_MASKED_AS_UNSUPPORTED_MARKERS: tuple[str, ...] = (
    "internal panic",
    "internal compiler error",
    "thread 'rustc' panicked",
    "sigabrt",
    "sigsegv",
    "sigkill",
    "segmentation fault",
    "core dumped",
    "out of memory",
    "capture_failed",
    "capture_error",
    "miri_oracle_error",
    "oracle_error",
    "parse error",
    "syntax error",
    "malformed",
    "lean_nat_shiftl",
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
    "stdout",
    "output",
    "detail",
    "details",
    "excerpt",
    "diag_repr",
    "summary",
)

# Record lists a harness summary may carry that the boundary audit scans.
_BOUNDARY_RECORD_LISTS: tuple[str, ...] = (
    "findings",
    "item_reports",
    "not_compared_items",
    "diagnostics",
)

# `miri-difftest` not-compared reasons that mean the item errored.
MIRI_ERROR_NOT_COMPARED_REASONS: tuple[str, ...] = ("miri_oracle_error", "capture_failed")

# Outcome-tag prefixes of an errored Miri run (`MiriOutcome::OracleError`) and of an
# errored Anneal capture / Lean run (`AnnealOutcome::CaptureOrLeanError`), each
# including the legacy `error:` spelling.
MIRI_ERROR_TAG_PREFIXES: tuple[str, ...] = ("oracle_error", "error:")
ANNEAL_ERROR_TAG_PREFIXES: tuple[str, ...] = ("capture_error", "error:")

# Prefixes of the reasons `validate_error_vs_unsupported_boundary` fails on.
_BOUNDARY_FAILURE_PREFIXES: tuple[str, ...] = (
    "error_masked_as_unsupported",
    "error_accounting_mismatch",
    "item_accounting_mismatch",
)

# Standard-library files that define the panic and assertion macros
# (`STD_PANIC_MACRO_FILE_SUFFIXES` in `crates/anneal-difftest/src/miri_eval.rs`):
# the only place an Anneal panic span may lie when the harness reconciles a panic
# site with Miri's `#[track_caller]` call site.
STD_PANIC_MACRO_FILE_SUFFIXES: tuple[str, ...] = (
    "library/core/src/panic.rs",
    "library/core/src/macros/mod.rs",
    "library/core/src/macros/panic.rs",
    "library/std/src/macros.rs",
)


def _record_bucket(item: dict[str, Any]) -> str:
    """Returns the bucket a record classifies itself into: an explicit not-compared
    reason / classification when present (for example `miri_oracle_error` shadows an
    Anneal `unsupported` outcome under the comparator's precedence), otherwise its
    specific verdict or Anneal outcome and Lean tag."""
    for key in ("not_compared_reason", "reason", "classification"):
        val = item.get(key)
        if isinstance(val, str) and val.strip():
            return val
    verdict = item.get("verdict")
    if isinstance(verdict, str) and verdict.strip() and verdict.strip().lower() != "not_compared":
        return verdict
    miri_out = str(item.get("miri_outcome", ""))
    if miri_out.startswith(MIRI_ERROR_TAG_PREFIXES):
        return "miri_oracle_error"
    return " ".join(str(item.get(k, "")) for k in ("anneal_outcome", "anneal_lean_tag"))


def _int_field(counts: Any, key: str) -> int:
    if not isinstance(counts, dict):
        return 0
    val = counts.get(key, 0)
    return val if isinstance(val, int) and not isinstance(val, bool) else 0


def _crash_marker(text: str) -> str | None:
    """Returns the first crash / malformed-input marker in `text`, if any."""
    lowered = text.lower()
    for marker in ERROR_MASKED_AS_UNSUPPORTED_MARKERS:
        if marker in lowered:
            return marker
    return None


def _record_text(item: dict[str, Any]) -> str:
    return " ".join(str(item.get(k, "")) for k in _DIAGNOSTIC_TEXT_FIELDS)


def count_distinct_miri_errored_items(summary: dict[str, Any]) -> int:
    """Counts the distinct items of a `miri-difftest` summary that errored.

    Under `compare_miri_and_anneal`'s precedence every errored item lands in
    exactly one of `not_compared_reasons.miri_oracle_error` / `capture_failed`, so
    their sum counts each errored item once, although a capture failure is also an
    `anneal_outcomes.error` and a Miri error also a `miri_verdicts.error`.
    `miri_verdicts.error`, `anneal_outcomes.error`, and the errored entries of
    `item_outcomes` are lower bounds that take over if the not-compared map
    under-reports.
    """
    nc_reasons = summary.get("not_compared_reasons")
    item_errored = 0
    items = summary.get("item_outcomes")
    if isinstance(items, dict):
        for entry in items.values():
            if not isinstance(entry, dict):
                continue
            m_tag = entry.get("miri_outcome")
            a_tag = entry.get("anneal_outcome")
            lean_tag = entry.get("anneal_lean_tag")
            if (
                (isinstance(m_tag, str) and m_tag.startswith(MIRI_ERROR_TAG_PREFIXES))
                or (isinstance(a_tag, str) and a_tag.startswith(ANNEAL_ERROR_TAG_PREFIXES))
                or (isinstance(lean_tag, str) and normalize_anneal_tag(lean_tag) == "none")
                or (
                    isinstance(m_tag, str)
                    and isinstance(a_tag, str)
                    and classify_oracle_outcome_tags(m_tag, a_tag)
                    in (
                        ("not_compared", "miri_oracle_error"),
                        ("not_compared", "capture_failed"),
                    )
                )
            ):
                item_errored += 1
    return max(
        _int_field(nc_reasons, "miri_oracle_error") + _int_field(nc_reasons, "capture_failed"),
        _int_field(summary.get("miri_verdicts"), "error"),
        _int_field(summary.get("anneal_outcomes"), "error"),
        item_errored,
    )


def validate_error_vs_unsupported_boundary(
    summary: dict[str, Any],
    max_oracle_errors: int = DEFAULT_MAX_ORACLE_ERRORS,
) -> tuple[bool, list[str]]:
    """Enforces that malformed inputs, capture/Lean crashes, and oracle errors of a
    `miri-difftest` summary are classified as errors rather than masked under
    `unsupported` (or any other not-compared bucket).

    Four independent checks, all fail-closed:

    1. Oracle-error budget: the number of distinct errored items
       (`count_distinct_miri_errored_items`) must not exceed `max_oracle_errors`.
    2. Accounting invariants implied by `compare_miri_and_anneal`'s precedence
       (Miri error > capture/Lean error > external call > unsupported > fuel):
       `miri_verdicts.error == not_compared_reasons.miri_oracle_error`,
       `capture_failed <= anneal_outcomes.error <= capture_failed +
       miri_oracle_error`, and the `unsupported`, `external_call`, and
       `out_of_fuel` not-compared counts never exceed the corresponding Anneal
       outcome counts. A violation means an error was routed into another bucket
       (`error_masked_as_unsupported`) or the counts are inconsistent
       (`error_accounting_mismatch`).
    3. Any finding, item report, not-compared item, diagnostic, or `item_outcomes`
       entry whose *own* classification is `unsupported` but whose text carries a
       crash or malformed-input marker (`INTERNAL PANIC`, `SIGABRT`,
       `capture_failed`, `parse error`, `lean_nat_shiftl`, ...) is rejected as
       `error_masked_as_unsupported`.
    4. When the harness emits `item_outcomes`, every item's verdict is recomputed
       from its outcome tags (`audit_item_outcomes_against_summary`) and the
       aggregates must match the recomputation.
    """
    reasons: list[str] = []
    miri_verdicts = summary.get("miri_verdicts")
    anneal_outcomes = summary.get("anneal_outcomes")
    nc_reasons = summary.get("not_compared_reasons")

    miri_err = _int_field(miri_verdicts, "error")
    anneal_err = _int_field(anneal_outcomes, "error")
    anneal_unsupported = _int_field(anneal_outcomes, "unsupported")
    anneal_ext = _int_field(anneal_outcomes, "external_call")
    anneal_oof = _int_field(anneal_outcomes, "out_of_fuel")
    nc_miri_err = _int_field(nc_reasons, "miri_oracle_error")
    nc_cap_err = _int_field(nc_reasons, "capture_failed")
    nc_unsupported = _int_field(nc_reasons, "unsupported")
    nc_ext = _int_field(nc_reasons, "external_call")
    nc_oof = _int_field(nc_reasons, "out_of_fuel")

    # 1. Oracle-error budget over distinct errored items.
    errored_items = count_distinct_miri_errored_items(summary)
    if errored_items > max_oracle_errors:
        reasons.append(
            f"oracle_errors_exceeded: {errored_items} errored items (miri_oracle_error="
            f"{nc_miri_err}, capture_failed={nc_cap_err}, miri_verdicts.error={miri_err}, "
            f"anneal_outcomes.error={anneal_err}) > max_oracle_errors ({max_oracle_errors})"
        )

    # 2. Accounting invariants (only when the maps are present).
    if (
        isinstance(nc_reasons, dict)
        and isinstance(miri_verdicts, dict)
        and isinstance(anneal_outcomes, dict)
    ):
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
        for nc_count, anneal_count, key in (
            (nc_unsupported, anneal_unsupported, "unsupported"),
            (nc_ext, anneal_ext, "external_call"),
            (nc_oof, anneal_oof, "out_of_fuel"),
        ):
            if nc_count > anneal_count:
                reasons.append(
                    f"error_masked_as_unsupported: not_compared_reasons.{key} ({nc_count}) > "
                    f"anneal_outcomes.{key} ({anneal_count})"
                )

    # 3. Records classified as `unsupported` that carry crash / malformed markers.
    for list_key in _BOUNDARY_RECORD_LISTS:
        items = summary.get(list_key)
        if not isinstance(items, list):
            continue
        for idx, item in enumerate(items):
            if isinstance(item, str):
                classification, text = item, item
                label: Any = idx
            elif isinstance(item, dict):
                classification = _record_bucket(item)
                text = _record_text(item)
                label = item.get("fn_name", item.get("name", idx))
            else:
                continue
            if "unsupported" not in classification.lower():
                continue
            hit = _crash_marker(text)
            if hit is not None:
                reasons.append(
                    f"error_masked_as_unsupported: {list_key}[{idx}] ({label}) masks '{hit}' "
                    f"under unsupported"
                )

    item_outcomes_map = summary.get("item_outcomes")
    if isinstance(item_outcomes_map, dict):
        for label, item in sorted(item_outcomes_map.items()):
            if not isinstance(item, dict):
                continue
            if "unsupported" not in _record_bucket(item).lower():
                continue
            hit = _crash_marker(_record_text(item))
            if hit is not None:
                reasons.append(
                    f"error_masked_as_unsupported: item_outcomes[{label!r}] masks '{hit}' "
                    f"under unsupported"
                )

    # 4. Per-item recomputation of verdicts from the reported outcome tags: catches
    #    an error counted as `unsupported` even when every aggregate count is
    #    internally consistent.
    reasons.extend(audit_item_outcomes_against_summary(summary))

    failed = any(r.startswith(_BOUNDARY_FAILURE_PREFIXES) for r in reasons)
    return (not failed and errored_items <= max_oracle_errors), reasons


def validate_itree_error_boundary(summary: dict[str, Any]) -> tuple[bool, list[str]]:
    """`itree-difftest` counterpart of `validate_error_vs_unsupported_boundary`.

    `itree-difftest` has no `unsupported` outcome, and every not-compared reason
    except `compile_failed` already counts against `--max-oracle-errors`
    (`ITREE_ORACLE_ERROR_REASONS`), so the only buckets in which an error can hide
    are `compile_failed` (never counted) and a stray `unsupported`
    classification:
    1. By the union bound over `comp.opt0 && comp.opt2`, `comp.instrumented`, and
       `contains_unsafe_token`, at most `(total - opt_both) + (total - instrumented)
       + unsafe_token_violations` candidates can legitimately land in
       `not_compared_reasons.compile_failed`. Exceeding that bound means an oracle
       or staging failure on a compiled candidate was routed into `compile_failed`.
    2. Any finding, item report, not-compared item, diagnostic, or `item_outcomes`
       record classified as `compile_failed` or `unsupported` whose text carries a
       crash or malformed-input marker (a `rustc` internal compiler error, a Lean
       crash, ...) is rejected as `itree_error_masked_as_compile_failed`.
    """
    reasons: list[str] = []
    nc_reasons = summary.get("not_compared_reasons")
    total = summary.get("total_candidates")
    opt_both = summary.get("opt_level_0_and_2_compiled")
    instrumented = summary.get("instrumented_compiled")
    unsafe_v = _int_field(summary, "unsafe_token_violations")
    if (
        isinstance(nc_reasons, dict)
        and is_nonneg_int(total)
        and is_nonneg_int(opt_both)
        and is_nonneg_int(instrumented)
    ):
        compile_failed = _int_field(nc_reasons, "compile_failed")
        max_compile_failed = max(
            0, (int(total) - int(opt_both)) + (int(total) - int(instrumented)) + unsafe_v
        )
        if compile_failed > max_compile_failed:
            reasons.append(
                f"itree_error_masked_as_compile_failed: not_compared_reasons.compile_failed "
                f"({compile_failed}) exceeds maximum compile/unsafe rejections "
                f"({max_compile_failed}) for total={total}, opt_both={opt_both}, "
                f"instrumented={instrumented}, unsafe_violations={unsafe_v}"
            )

    for list_key in _BOUNDARY_RECORD_LISTS:
        items = summary.get(list_key)
        if not isinstance(items, list):
            continue
        for idx, item in enumerate(items):
            if isinstance(item, str):
                classification, text = item, item
                label: Any = idx
            elif isinstance(item, dict):
                classification = _record_bucket(item)
                text = _record_text(item)
                label = item.get("fn_name", item.get("name", idx))
            else:
                continue
            lowered = classification.lower()
            if "compile_failed" not in lowered and "unsupported" not in lowered:
                continue
            hit = _crash_marker(text)
            if hit is not None:
                reasons.append(
                    f"itree_error_masked_as_compile_failed: {list_key}[{idx}] ({label}) "
                    f"masks '{hit}' under {classification.strip()}"
                )
    item_outcomes_map = summary.get("item_outcomes")
    if isinstance(item_outcomes_map, dict):
        for label, item in sorted(item_outcomes_map.items()):
            if not isinstance(item, dict):
                continue
            classification = _record_bucket(item)
            lowered = classification.lower()
            if "compile_failed" not in lowered and "unsupported" not in lowered:
                continue
            hit = _crash_marker(_record_text(item))
            if hit is not None:
                reasons.append(
                    f"itree_error_masked_as_compile_failed: item_outcomes[{label!r}] "
                    f"masks '{hit}' under {classification.strip()}"
                )
    return not reasons, reasons


_RUST_U32_RE = re.compile(r"\+?[0-9]+")

# Code points with the Unicode `White_Space` property: exactly what Rust's
# `str::trim` (`char::is_whitespace`) strips. Python's `str.strip()` also strips
# U+001C..U+001F (bidi class B/S), which Rust keeps, so every port of a Rust
# parser below trims with `_rust_trim` instead.
_RUST_WHITESPACE = frozenset(
    "\t\n\x0b\x0c\r \x85\xa0\u1680"
    + "".join(chr(c) for c in range(0x2000, 0x200B))
    + "\u2028\u2029\u202f\u205f\u3000"
)


def _rust_trim(raw: str) -> str:
    """Port of `str::trim` (strips Unicode `White_Space` from both ends)."""
    start, end = 0, len(raw)
    while start < end and raw[start] in _RUST_WHITESPACE:
        start += 1
    while end > start and raw[end - 1] in _RUST_WHITESPACE:
        end -= 1
    return raw[start:end]


def _parse_rust_uint(raw: str, bits: int) -> int | None:
    """Port of `str::parse::<u{bits}>`: an optional `+`, ASCII digits only (no
    `-`, no surrounding whitespace), at most `2**bits - 1`."""
    if not _RUST_U32_RE.fullmatch(raw):
        return None
    val = int(raw[1:] if raw.startswith("+") else raw, 10)
    return val if val < (1 << bits) else None


def _parse_rust_u32(raw: str) -> int | None:
    """Port of `str::parse::<u32>`: an optional `+`, ASCII digits, at most `u32::MAX`."""
    return _parse_rust_uint(raw, 32)


def _parse_src_pos(raw: str) -> tuple[str, int, int] | None:
    """Port of `SourcePos::parse_rustc_pos`: 1-based `<file>:<line>:<col>`."""
    parts = _rust_trim(raw).rstrip(":").rsplit(":", 2)
    if len(parts) != 3:
        return None
    file_str = _rust_trim(parts[0])
    line = _parse_rust_u32(_rust_trim(parts[1]))
    col = _parse_rust_u32(_rust_trim(parts[2]))
    if not file_str or line is None or col is None or line == 0 or col == 0:
        return None
    return file_str, line, col


def _parse_src_span(raw: str) -> tuple[str, int, int, int, int] | None:
    """Port of `SourceSpan::parse_anneal_span`: `<file>:<l>:<c>: <l>:<c>` (split at
    the first `": "`, as `SourceSpan::display_short` renders it) or a single point
    `<file>:<line>:<col>`."""
    trimmed = _rust_trim(raw)
    if not trimmed or trimmed == "none":
        return None
    if ": " in trimmed:
        left, right = trimmed.split(": ", 1)
        start = _parse_src_pos(left)
        if start is None:
            return None
        end_parts = _rust_trim(right).split(":")
        if len(end_parts) != 2:
            return None
        end_line = _parse_rust_u32(_rust_trim(end_parts[0]))
        end_col = _parse_rust_u32(_rust_trim(end_parts[1]))
        if end_line is None or end_col is None or end_line == 0 or end_col == 0:
            return None
        return start[0], start[1], start[2], end_line, end_col
    pos = _parse_src_pos(trimmed)
    if pos is None:
        return None
    return pos[0], pos[1], pos[2], pos[1], pos[2]


def _is_valid_pass_scalar_tag(tag: str) -> bool:
    """Returns `True` iff `tag` is `pass:scalar:<bits>:<size_bytes>` with decimal
    `u128` bits and positive `u32` `size_bytes` (`MiriOutcome::PassScalar` /
    `AnnealOutcome::PassScalar`)."""
    parts = tag.split(":")
    if len(parts) != 4 or parts[0] != "pass" or parts[1] != "scalar":
        return False
    bits, size = parts[2], parts[3]
    if not (bits.isascii() and bits.isdigit() and size.isascii() and size.isdigit()):
        return False
    bits_val = int(bits, 10)
    size_val = int(size, 10)
    return 0 <= bits_val <= (1 << 128) - 1 and 0 < size_val <= 0xFFFF_FFFF


def _normalize_file_for_match(raw: str) -> str:
    """Port of `cargo_anneal::miri_oracle::normalize_file_for_match`."""
    trimmed = _rust_trim(raw.replace("\\", "/"))
    return trimmed[2:] if trimmed.startswith("./") else trimmed


def _source_files_match(a: str, b: str) -> bool:
    """Port of `cargo_anneal::source_files_match` (`src/lib.rs` matches an absolute
    `/tmp/.../src/lib.rs` Miri path)."""
    na, nb = _normalize_file_for_match(a), _normalize_file_for_match(b)
    if not na or not nb:
        return False
    return na == nb or na.endswith(f"/{nb}") or nb.endswith(f"/{na}")


def _span_tuple_contains_pos(
    span: tuple[str, int, int, int, int], pos: tuple[str, int, int]
) -> bool:
    """Port of `SourceSpan::contains_pos` over parsed `_parse_src_span` /
    `_parse_src_pos` tuples."""
    if not _source_files_match(span[0], pos[0]):
        return False
    return (span[1], span[2]) <= (pos[1], pos[2]) <= (span[3], span[4])


def _span_contains_pos(span_raw: str, pos_raw: str) -> bool:
    """Port of `SourceSpan::contains_pos`."""
    span = _parse_src_span(span_raw)
    pos = _parse_src_pos(pos_raw)
    if span is None or pos is None:
        return False
    return _span_tuple_contains_pos(span, pos)


def _is_std_panic_macro_file(file: str) -> bool:
    """Port of `miri_eval::is_std_panic_macro_file`."""
    norm = file.replace("\\", "/")
    return any(norm == s or norm.endswith(f"/{s}") for s in STD_PANIC_MACRO_FILE_SUFFIXES)


def classify_oracle_outcome_tags(miri_outcome: str, anneal_outcome: str) -> tuple[str, str]:
    """Python model of `compare_miri_and_anneal` over harness summary tags.

    Returns `("agree", "")`, `("diverge", <divergence class>)`, or
    `("not_compared", <not-compared reason>)`, using the same precedence as the Rust
    comparator: a Miri oracle error (or unrecognized Miri tag) wins over everything,
    then Anneal capture/Lean errors, external calls, `unsupported`, fuel exhaustion,
    and unrecognized Anneal tags; only then are executed outcomes compared (with span
    containment for panic and UB locations). The panic-site reconciliation that
    `compare_difftest_miri_and_anneal` layers on top is audited separately against
    `reconciled_panic_sites`.
    """
    m_kind, m_sep, m_loc = miri_outcome.partition("@")
    m_pass = miri_outcome.startswith("pass:") and not m_sep
    if miri_outcome.startswith(MIRI_ERROR_TAG_PREFIXES) or not (
        m_pass or m_kind in ("panic", "ub")
    ):
        return "not_compared", "miri_oracle_error"

    for prefix, reason in (
        ("capture_error", "capture_failed"),
        ("error:", "capture_failed"),
        ("externalCall", "external_call"),
        ("unsupported", "unsupported"),
        ("outOfFuel", "out_of_fuel"),
    ):
        if anneal_outcome.startswith(prefix):
            return "not_compared", reason

    a_kind, a_sep, a_loc = anneal_outcome.partition("@")
    a_pass = (anneal_outcome.startswith("pass:") and not a_sep) or a_kind == "abort"
    if not (a_pass or a_kind in ("panic", "ub")):
        return "not_compared", "capture_failed"

    if m_pass:
        if a_kind == "panic":
            return "diverge", "return_vs_panic"
        if a_kind == "ub":
            return "diverge", "false_positive_ub"
        if m_kind == a_kind and (m_kind == "pass:unit" or _is_valid_pass_scalar_tag(m_kind)):
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


# ---------------------------------------------------------------------------
# `WitnessPolarity`: exact ports of the classifier and accounting identity in
# `crates/anneal-difftest/src/miri_eval.rs` (`parse_miri_summary_tag`,
# `parse_anneal_summary_tag`, `compare_miri_and_anneal`,
# `classify_verdict_witness_polarity`, `classify_outcome_tags_polarity`, and
# `witness_polarity_accounting_holds`). `classify_oracle_outcome_tags` above
# predates them and tolerates legacy tag spellings; the polarity functions below
# accept exactly the summary tags that the Rust parsers accept, so a tag Rust
# cannot parse is a `harness_or_extraction_error` here too.
# ---------------------------------------------------------------------------

_NOT_THIS_TAG_FAMILY = object()
_PARSED_MIRI_KINDS = ("pass_unit", "pass_scalar", "panic", "ub", "oracle_error")
_PARSED_ANNEAL_KINDS = (
    "pass_unit",
    "pass_scalar",
    "pass_other",
    "panic",
    "abort",
    "ub",
    "unsupported",
    "external_call",
    "out_of_fuel",
    "capture_error",
)
_PARSED_PASS_KINDS = ("pass_unit", "pass_scalar")
# Not-compared reasons that are `harness_or_extraction_error` regardless of the
# Miri outcome (`classify_outcome_tags_polarity`).
_HARNESS_NOT_COMPARED_SLUGS = (
    "compile_failed",
    "external_call",
    "out_of_fuel",
    "miri_oracle_error",
    "capture_failed",
)


def _split_located_outcome_tag(tag: str, family: str) -> Any:
    """Port of `split_located_outcome_tag`: `None` for the bare `family` tag, the
    location text after `<family>@`, or `_NOT_THIS_TAG_FAMILY` for another family
    (so `panicky` and `ubx` are never `panic` / `ub` tags)."""
    if tag == family:
        return None
    if tag.startswith(family) and tag[len(family) :].startswith("@"):
        return tag[len(family) + 1 :]
    return _NOT_THIS_TAG_FAMILY


def _parse_scalar_tag_fields(rest: str) -> tuple[int, int] | None:
    """Port of `parse_scalar_tag_fields`: `<bits>:<size_bytes>` split at the first
    `:`, each field trimmed, `bits` a `u128` and `size_bytes` a `u32` (so leading
    zeros, a `+` sign, and `size_bytes == 0` parse, exactly as in Rust)."""
    bits_raw, sep, size_raw = rest.partition(":")
    if not sep:
        return None
    bits = _parse_rust_uint(_rust_trim(bits_raw), 128)
    size = _parse_rust_uint(_rust_trim(size_raw), 32)
    if bits is None or size is None:
        return None
    return bits, size


def parse_miri_summary_tag(tag: Any) -> tuple[Any, ...] | None:
    """Port of `parse_miri_summary_tag`: parses a `MiriOutcome::summary_tag` into
    `("pass_unit",)`, `("pass_scalar", bits, size_bytes)`, `("panic", pos)`,
    `("ub", pos)` (`pos` a `_parse_src_pos` tuple or `None`), or
    `("oracle_error", message)`. Returns `None` for any other spelling (including
    a malformed location, legacy `pass` / `error:` tags, and non-`str` JSON)."""
    if not isinstance(tag, str):
        return None
    t = _rust_trim(tag)
    if t == "pass:unit":
        return ("pass_unit",)
    if t.startswith("pass:scalar:"):
        fields = _parse_scalar_tag_fields(t[len("pass:scalar:") :])
        return None if fields is None else ("pass_scalar", fields[0], fields[1])
    if t.startswith("oracle_error:"):
        return ("oracle_error", t[len("oracle_error:") :])
    for family in ("panic", "ub"):
        loc = _split_located_outcome_tag(t, family)
        if loc is _NOT_THIS_TAG_FAMILY:
            continue
        if loc is None:
            return (family, None)
        pos = _parse_src_pos(loc)
        return None if pos is None else (family, pos)
    return None


def parse_anneal_summary_tag(tag: Any) -> tuple[Any, ...] | None:
    """Port of `parse_anneal_summary_tag`: parses an `AnnealOutcome::summary_tag`
    into `("pass_unit",)`, `("pass_scalar", bits, size_bytes)`, `("pass_other",)`,
    `(<panic|abort|ub|unsupported>, span)` (`span` a `_parse_src_span` tuple or
    `None`), `("external_call", def_path)`, `("out_of_fuel", None)`, or
    `("capture_error", message)`. Returns `None` for any other spelling."""
    if not isinstance(tag, str):
        return None
    t = _rust_trim(tag)
    if t == "pass:unit":
        return ("pass_unit",)
    if t == "pass:other":
        return ("pass_other",)
    if t == "outOfFuel":
        return ("out_of_fuel", None)
    if t.startswith("pass:scalar:"):
        fields = _parse_scalar_tag_fields(t[len("pass:scalar:") :])
        return None if fields is None else ("pass_scalar", fields[0], fields[1])
    if t.startswith("externalCall:"):
        return ("external_call", t[len("externalCall:") :])
    if t.startswith("capture_error:"):
        return ("capture_error", t[len("capture_error:") :])
    for family in ("panic", "abort", "ub", "unsupported"):
        loc = _split_located_outcome_tag(t, family)
        if loc is _NOT_THIS_TAG_FAMILY:
            continue
        if loc is None:
            return (family, None)
        span = _parse_src_span(loc)
        return None if span is None else (family, span)
    return None


def compare_parsed_outcomes(
    miri: tuple[Any, ...], anneal: tuple[Any, ...]
) -> tuple[str, str]:
    """Port of `compare_miri_and_anneal` over `parse_miri_summary_tag` /
    `parse_anneal_summary_tag` outcomes: `("agree", "")`, `("diverge", <class>)`,
    or `("not_compared", <reason>)`, with span containment for `panic` / `ub`."""
    m_kind, a_kind = miri[0], anneal[0]
    if m_kind not in _PARSED_MIRI_KINDS or a_kind not in _PARSED_ANNEAL_KINDS:
        raise ValueError(f"not a parsed outcome pair: {miri!r}, {anneal!r}")
    if m_kind == "oracle_error":
        return "not_compared", "miri_oracle_error"
    if a_kind == "capture_error":
        return "not_compared", "capture_failed"
    if a_kind == "external_call":
        return "not_compared", "external_call"
    if a_kind == "unsupported":
        return "not_compared", "unsupported"
    if a_kind == "out_of_fuel":
        return "not_compared", "out_of_fuel"
    anneal_returns = a_kind in ("pass_unit", "pass_scalar", "pass_other", "abort")
    if m_kind in _PARSED_PASS_KINDS:
        if m_kind == a_kind == "pass_unit":
            return "agree", ""
        if m_kind == a_kind == "pass_scalar":
            return ("agree", "") if miri[1:] == anneal[1:] else ("diverge", "wrong_value")
        if anneal_returns:
            return "diverge", "wrong_value"
        if a_kind == "panic":
            return "diverge", "return_vs_panic"
        return "diverge", "false_positive_ub"
    def located() -> bool:
        # Only called for a `panic`/`panic` or `ub`/`ub` pair, whose second
        # components are a position and a span (or `None`).
        return (
            miri[1] is not None
            and anneal[1] is not None
            and _span_tuple_contains_pos(anneal[1], miri[1])
        )

    if m_kind == "panic":
        if anneal_returns:
            return "diverge", "panic_vs_return"
        if a_kind == "ub":
            return "diverge", "false_positive_ub"
        return ("agree", "") if located() else ("diverge", "panic_site_mismatch")
    if a_kind == "ub":
        return ("agree", "") if located() else ("diverge", "ub_location_mismatch")
    return "diverge", "missed_ub"


def classify_not_compared_polarity(miri: tuple[Any, ...] | None, reason: str) -> str:
    """Port of `classify_not_compared_polarity`: `unsupported` is a
    `sound_conservative_abstraction` exactly when Miri returned normally; every
    other not-compared case is a `harness_or_extraction_error`."""
    if reason == "unsupported" and miri is not None and miri[0] in _PARSED_PASS_KINDS:
        return WITNESS_POLARITY_CONSERVATIVE
    return WITNESS_POLARITY_HARNESS


def classify_verdict_witness_polarity(
    miri: tuple[Any, ...] | None, verdict: str, detail: str
) -> str | None:
    """Port of `classify_verdict_witness_polarity` over a `compare_parsed_outcomes`
    verdict: `None` on agreement."""
    if verdict == "agree":
        return None
    if verdict == "diverge":
        return DIVERGENCE_CLASS_WITNESS_POLARITY[detail]
    if verdict == "not_compared":
        return classify_not_compared_polarity(miri, detail)
    raise ValueError(f"unknown verdict {verdict!r}")


def classify_witness_polarity_from_tags(
    miri_tag: Any, anneal_tag: Any, divergence_or_reason: Any = None
) -> str | None:
    """Port of `classify_outcome_tags_polarity`: the `WitnessPolarity` slug of a
    serialized `(MiriOutcome, AnnealOutcome)` pair, or `None` on agreement.

    A recognized `divergence_or_reason` slug decides the class (`"agree"`, a
    divergence class, or a not-compared reason, optionally prefixed with
    `not_compared_`; so a panic-site reconciled `"agree"` stays an agreement), and
    `unsupported` additionally consults the Miri tag. Otherwise both tags are parsed
    exactly as Rust parses them and compared with span containment for `panic` and
    `ub`; tags that do not parse (or non-`str` JSON values) cannot be compared and
    classify as `harness_or_extraction_error`.
    """
    miri = parse_miri_summary_tag(miri_tag)
    if isinstance(divergence_or_reason, str):
        slug = _rust_trim(divergence_or_reason)
        if slug:
            if slug.startswith("not_compared_"):
                slug = slug[len("not_compared_") :]
            if slug == "agree":
                return None
            if slug in DIVERGENCE_CLASS_WITNESS_POLARITY:
                return DIVERGENCE_CLASS_WITNESS_POLARITY[slug]
            if slug == "unsupported":
                return classify_not_compared_polarity(miri, "unsupported")
            if slug in _HARNESS_NOT_COMPARED_SLUGS:
                return WITNESS_POLARITY_HARNESS
    anneal = parse_anneal_summary_tag(anneal_tag)
    if miri is None or anneal is None:
        return WITNESS_POLARITY_HARNESS
    verdict, detail = compare_parsed_outcomes(miri, anneal)
    return classify_verdict_witness_polarity(miri, verdict, detail)


def empty_witness_polarity_counts() -> dict[str, int]:
    return {p: 0 for p in VALID_WITNESS_POLARITIES}


def kill_class_witness_polarity(kill_class: Any) -> str | None:
    """Polarity implied by a semantic-mutant kill class: the divergence class's
    polarity, `harness_or_extraction_error` for `harness_error`, else `None`."""
    if kill_class == HARNESS_ERROR_KILL_CLASS:
        return WITNESS_POLARITY_HARNESS
    if isinstance(kill_class, str):
        return DIVERGENCE_CLASS_WITNESS_POLARITY.get(kill_class)
    return None


def fingerprint_witness_polarity(fingerprint: str) -> str | None:
    """Polarity of a `miri-difftest` fingerprint `<cause>:<class>:<tag>` (from its
    divergence class), or `None` for an `itree-difftest` or malformed one."""
    parts = fingerprint.split(":", 2)
    return DIVERGENCE_CLASS_WITNESS_POLARITY.get(parts[1]) if len(parts) >= 2 else None


def count_dedup_witness_polarities(findings: list[DeduplicatedFinding]) -> dict[str, int]:
    """Counts distinct fingerprints by `witness_polarity` (`itree-difftest`
    fingerprints, which carry none, are not counted)."""
    counts = empty_witness_polarity_counts()
    for d in findings:
        if d.witness_polarity in counts:
            counts[d.witness_polarity] += 1
    return counts


def _witness_polarity_identity_problems(summary: dict[str, Any]) -> list[str]:
    """The accounting identities of Rust's `witness_polarity_accounting_holds`, each
    reported as a `witness_polarity_accounting_mismatch` reason: the keys are
    exactly `VALID_WITNESS_POLARITIES` (non-negative, non-`bool` ints); the counts
    sum to `diverge_count + not_compared_count`; `unsound_missed_fault ==
    missed_ub + panic_vs_return`; `value_mismatch == wrong_value +
    return_vs_panic + ub_location_mismatch + panic_site_mismatch`;
    `false_positive_ub <= sound_conservative_abstraction <= false_positive_ub +
    not_compared_reasons.unsupported`; and `sound_conservative_abstraction +
    harness_or_extraction_error == false_positive_ub + sum(not_compared_reasons)`.
    """
    label = "witness_polarity_accounting_mismatch"
    pol_map = summary.get("witness_polarity_counts")
    if not is_int_map(pol_map, VALID_WITNESS_POLARITIES):
        return [
            f"{label}: witness_polarity_counts must map exactly {list(VALID_WITNESS_POLARITIES)} "
            f"to non-negative integers, got {pol_map!r}"
        ]
    div_map = summary.get("divergence_classes")
    nc_map = summary.get("not_compared_reasons")
    diverged = summary.get("diverge_count")
    not_compared = summary.get("not_compared_count")
    if not (
        is_int_map(div_map)
        and is_int_map(nc_map)
        and is_nonneg_int(diverged)
        and is_nonneg_int(not_compared)
    ):
        return [
            f"{label}: divergence_classes, not_compared_reasons, diverge_count, and "
            "not_compared_count must be well-formed to account for witness polarities"
        ]
    pol = dict(pol_map)

    def div(cls: str) -> int:
        return int(div_map.get(cls, 0))

    reasons: list[str] = []
    total = sum(pol.values())
    if total != diverged + not_compared:
        reasons.append(
            f"{label}: sum(witness_polarity_counts)={total} != diverge_count ({diverged}) + "
            f"not_compared_count ({not_compared})"
        )
    unsound = div("missed_ub") + div("panic_vs_return")
    if pol[WITNESS_POLARITY_UNSOUND] != unsound:
        reasons.append(
            f"{label}: unsound_missed_fault={pol[WITNESS_POLARITY_UNSOUND]} != missed_ub + "
            f"panic_vs_return ({unsound})"
        )
    value = (
        div("wrong_value")
        + div("return_vs_panic")
        + div("ub_location_mismatch")
        + div("panic_site_mismatch")
    )
    if pol[WITNESS_POLARITY_VALUE_MISMATCH] != value:
        reasons.append(
            f"{label}: value_mismatch={pol[WITNESS_POLARITY_VALUE_MISMATCH]} != wrong_value + "
            f"return_vs_panic + ub_location_mismatch + panic_site_mismatch ({value})"
        )
    conservative = pol[WITNESS_POLARITY_CONSERVATIVE]
    false_pos = div("false_positive_ub")
    nc_unsupported = int(nc_map.get("unsupported", 0))
    if not false_pos <= conservative <= false_pos + nc_unsupported:
        reasons.append(
            f"{label}: sound_conservative_abstraction={conservative} outside "
            f"[false_positive_ub ({false_pos}), false_positive_ub + "
            f"not_compared_reasons.unsupported ({false_pos + nc_unsupported})]"
        )
    nc_total = sum(int(v) for v in nc_map.values())
    if conservative + pol[WITNESS_POLARITY_HARNESS] != false_pos + nc_total:
        reasons.append(
            f"{label}: sound_conservative_abstraction + harness_or_extraction_error="
            f"{conservative + pol[WITNESS_POLARITY_HARNESS]} != false_positive_ub + "
            f"sum(not_compared_reasons) ({false_pos + nc_total})"
        )
    return reasons


def witness_polarity_accounting_holds(summary: dict[str, Any]) -> bool:
    """Port of `witness_polarity_accounting_holds` over a `miri-difftest` JSON
    summary (`witness_polarity_counts`, `divergence_classes`,
    `not_compared_reasons`, `diverge_count`, `not_compared_count`)."""
    return not _witness_polarity_identity_problems(summary)


def witness_polarity_accounting_problems(summary: dict[str, Any]) -> list[str]:
    """Fail-closed audit of a `miri-difftest` summary's witness polarities.

    1. The accounting identities of `witness_polarity_accounting_holds`, plus the
       `miri_verdicts` bounds on the split of `not_compared_reasons.unsupported`
       between `sound_conservative_abstraction` (Miri `pass`) and
       `harness_or_extraction_error` (Miri `panic`/`ub`).
    2. Every finding carries the `witness_polarity` of its `divergence_class`, and
       its outcome tags (which `miri-difftest` always emits as `summary_tag`s) must
       parse, classify to `witness_polarity`, and reproduce `("diverge",
       divergence_class)`, with or without `item_outcomes`: no tag spelling is
       exempt. The findings' per-polarity tallies must match the divergence classes
       (`unsound_missed_fault` / `value_mismatch` / `sound_conservative_abstraction`
       findings equal their divergence-class sums; no finding is a harness error).
    3. With `item_outcomes` (which must be a `dict` of `compiled_candidates` entries
       when present), every item's polarity and verdict are recomputed from its tags
       (`classify_witness_polarity_from_tags` / `compare_parsed_outcomes`; a panic-site
       pair reported `agree` counts as an agreement only when `reconciled_panic_sites`
       justifies it), the `compile_failed_candidates` (which carry no item outcome) are
       added as `harness_or_extraction_error`, and the result must equal
       `witness_polarity_counts` key by key: a forged map that preserves every
       identity but moves an `unsupported` item between
       `sound_conservative_abstraction` and `harness_or_extraction_error` (or any
       other bucket) is rejected.
    """
    label = "witness_polarity_accounting_mismatch"
    reasons = _witness_polarity_identity_problems(summary)
    pol_map = summary.get("witness_polarity_counts")
    if not is_int_map(pol_map, VALID_WITNESS_POLARITIES):
        return reasons

    div_map = summary.get("divergence_classes")
    nc_map = summary.get("not_compared_reasons")
    miri_verdicts = summary.get("miri_verdicts")
    if (
        is_int_map(div_map)
        and is_int_map(nc_map)
        and is_int_map(miri_verdicts, ("pass", "panic", "ub", "error"))
    ):
        # A Miri oracle error wins over `unsupported` (`compare_miri_and_anneal`), so
        # every `unsupported` item ran under Miri `pass` (conservative) or Miri
        # `panic`/`ub` (harness error); with no such Miri verdict there can be none.
        miri_pass = int(miri_verdicts["pass"])
        miri_faults = int(miri_verdicts["panic"]) + int(miri_verdicts["ub"])
        false_pos = int(div_map.get("false_positive_ub", 0))
        nc_unsupported = int(nc_map.get("unsupported", 0))
        conservative_unsupported = int(pol_map[WITNESS_POLARITY_CONSERVATIVE]) - false_pos
        fault_unsupported = nc_unsupported - conservative_unsupported
        if 0 <= conservative_unsupported <= nc_unsupported:
            if conservative_unsupported > miri_pass:
                reasons.append(
                    f"{label}: sound_conservative_abstraction attributes "
                    f"{conservative_unsupported} unsupported candidate(s) to Miri pass, "
                    f"but miri_verdicts.pass is {miri_pass}"
                )
            if fault_unsupported > miri_faults:
                reasons.append(
                    f"{label}: harness_or_extraction_error attributes "
                    f"{fault_unsupported} unsupported candidate(s) to Miri panic/ub, "
                    f"but miri_verdicts.panic + miri_verdicts.ub is {miri_faults}"
                )

    items = summary.get("item_outcomes")
    if "item_outcomes" in summary and items is not None and not isinstance(items, dict):
        reasons.append(f"{label}: item_outcomes is not a dict")
    has_items = isinstance(items, dict)

    reconciled: dict[str, Any] = {}
    sites = summary.get("reconciled_panic_sites")
    site_count = summary.get("reconciled_panic_sites_count")
    if sites is not None:
        if not isinstance(sites, list):
            reasons.append(f"{label}: reconciled_panic_sites is not a list")
        else:
            for site_idx, site in enumerate(sites):
                name = site.get("fn_name") if isinstance(site, dict) else None
                if not isinstance(name, str) or not name.strip():
                    reasons.append(
                        f"{label}: reconciled_panic_sites[{site_idx}] lacks a fn_name"
                    )
                elif name in reconciled:
                    reasons.append(
                        f"{label}: reconciled_panic_sites lists {name!r} twice"
                    )
                else:
                    reconciled[name] = site
                    if not has_items:
                        m_pos = site.get("batch_miri_pos")
                        a_span = site.get("anneal_span")
                        if not (
                            isinstance(m_pos, str)
                            and isinstance(a_span, str)
                            and _reconciled_panic_site_matches(
                                site, name, f"panic@{m_pos}", f"panic@{a_span}"
                            )
                        ):
                            reasons.append(
                                f"{label}: reconciled_panic_sites[{site_idx}] for {name!r} "
                                "is not a valid kernel-confirmed panic-macro reconciliation"
                            )
            if site_count is not None and (
                not is_nonneg_int(site_count) or site_count != len(sites)
            ):
                reasons.append(
                    f"{label}: reconciled_panic_sites_count is {site_count!r} "
                    f"but reconciled_panic_sites lists {len(sites)}"
                )
    elif site_count is not None and (not is_nonneg_int(site_count) or site_count != 0):
        reasons.append(
            f"{label}: reconciled_panic_sites_count is {site_count!r} "
            "without reconciled_panic_sites"
        )

    findings = summary.get("findings")
    if ("findings" in summary and not isinstance(findings, list)) or (
        findings is None
        and is_nonneg_int(summary.get("diverge_count"))
        and int(summary["diverge_count"]) > 0
    ):
        reasons.append(f"{label}: findings is missing or not a list")
    elif isinstance(findings, list):
        tallies = empty_witness_polarity_counts()
        class_tallies = {cls: 0 for cls in VALID_DIVERGENCE_CLASSES}
        seen_finding_ids: set[str] = set()
        seen_finding_fns: set[str] = set()
        for idx, f in enumerate(findings):
            if not isinstance(f, dict):
                reasons.append(f"{label}: findings[{idx}] is not a JSON object")
                continue
            fid = f.get("finding_id")
            if isinstance(fid, str) and fid.strip():
                if fid.strip() in seen_finding_ids:
                    reasons.append(f"{label}: findings[{idx}] repeats finding_id {fid!r}")
                seen_finding_ids.add(fid.strip())
            fn_name = f.get("fn_name")
            if isinstance(fn_name, str) and fn_name.strip():
                if fn_name.strip() in seen_finding_fns:
                    reasons.append(
                        f"{label}: findings[{idx}] repeats candidate fn_name {fn_name!r}"
                    )
                seen_finding_fns.add(fn_name.strip())
            f_lean_tag = f.get("anneal_lean_tag")
            if isinstance(f_lean_tag, str):
                norm_f_lean = normalize_anneal_tag(f_lean_tag)
                if norm_f_lean == "none":
                    reasons.append(
                        f"{label}: findings[{idx}] has anneal_lean_tag 'none' on a divergence finding"
                    )
                elif norm_f_lean in (
                    "MirDiffTag.unsupported",
                    "MirDiffTag.outOfFuel",
                ) or norm_f_lean.startswith("MirDiffTag.externalCall"):
                    reasons.append(
                        f"{label}: findings[{idx}] has non-divergence anneal_lean_tag "
                        f"{f_lean_tag!r} on a divergence finding"
                    )
            if "applied_mutators" in f:
                f_muts = f.get("applied_mutators")
                if not isinstance(f_muts, list) or not all(
                    isinstance(m, str) and m.strip() for m in f_muts
                ):
                    reasons.append(
                        f"{label}: findings[{idx}] has invalid applied_mutators {f_muts!r}"
                    )
            polarity = f.get("witness_polarity")
            div_cls = f.get("divergence_class")
            if isinstance(div_cls, str) and div_cls in class_tallies:
                class_tallies[div_cls] += 1
            expected = (
                DIVERGENCE_CLASS_WITNESS_POLARITY.get(div_cls) if isinstance(div_cls, str) else None
            )
            if not isinstance(polarity, str) or polarity not in VALID_WITNESS_POLARITIES:
                reasons.append(
                    f"{label}: findings[{idx}] has missing or invalid witness_polarity {polarity!r}"
                )
                continue
            tallies[polarity] += 1
            if polarity != expected:
                reasons.append(
                    f"{label}: findings[{idx}] has witness_polarity {polarity!r}, but its "
                    f"divergence_class {div_cls!r} has polarity {expected!r}"
                )
            f_miri, f_anneal = f.get("miri_outcome"), f.get("anneal_outcome")
            from_tags = classify_witness_polarity_from_tags(f_miri, f_anneal)
            if from_tags != polarity:
                reasons.append(
                    f"{label}: findings[{idx}] has witness_polarity {polarity!r}, but its "
                    f"outcomes ({f_miri!r}, {f_anneal!r}) classify as {from_tags!r}"
                )
            p_miri = parse_miri_summary_tag(f_miri)
            p_anneal = parse_anneal_summary_tag(f_anneal)
            if p_miri is not None and p_anneal is not None:
                tag_verdict, tag_cls = compare_parsed_outcomes(p_miri, p_anneal)
                if (tag_verdict, tag_cls) != ("diverge", div_cls):
                    reasons.append(
                        f"{label}: findings[{idx}] has divergence_class {div_cls!r}, but its "
                        f"outcomes ({f_miri!r}, {f_anneal!r}) classify as "
                        f"{tag_verdict}:{tag_cls}"
                    )
        if is_int_map(div_map):
            expected_tallies = empty_witness_polarity_counts()
            for cls, pol in DIVERGENCE_CLASS_WITNESS_POLARITY.items():
                expected_tallies[pol] += int(div_map.get(cls, 0))
            for pol in VALID_WITNESS_POLARITIES:
                if tallies[pol] != expected_tallies[pol]:
                    reasons.append(
                        f"{label}: {tallies[pol]} findings have witness_polarity {pol!r}, but "
                        f"divergence_classes account for {expected_tallies[pol]}"
                    )
            for cls in VALID_DIVERGENCE_CLASSES:
                if class_tallies[cls] != int(div_map.get(cls, 0)):
                    reasons.append(
                        f"{label}: {class_tallies[cls]} findings have divergence_class {cls!r}, "
                        f"but divergence_classes.{cls} is {int(div_map.get(cls, 0))}"
                    )

    if has_items:
        compiled = summary.get("compiled_candidates")
        if is_nonneg_int(compiled) and len(items) != compiled:
            reasons.append(
                f"{label}: item_outcomes covers {len(items)} items but compiled_candidates "
                f"is {compiled}"
            )
        reconciled_used: set[str] = set()
        recount = empty_witness_polarity_counts()
        for name, entry in items.items():
            if not isinstance(entry, dict):
                reasons.append(f"{label}: item_outcomes[{name!r}] is not a JSON object")
                recount[WITNESS_POLARITY_HARNESS] += 1
                continue
            m_tag = entry.get("miri_outcome")
            a_tag = entry.get("anneal_outcome")
            lean_tag = entry.get("anneal_lean_tag")
            polarity = classify_witness_polarity_from_tags(m_tag, a_tag)
            if (
                isinstance(lean_tag, str)
                and normalize_anneal_tag(lean_tag) == "none"
                and not (isinstance(a_tag, str) and a_tag.startswith(ANNEAL_ERROR_TAG_PREFIXES))
            ):
                reasons.append(
                    f"{label}: item_outcomes[{name!r}] has anneal_lean_tag 'none' masked "
                    f"under anneal_outcome {a_tag!r}"
                )
                polarity = WITNESS_POLARITY_HARNESS
            reported_raw = entry.get("verdict")
            reported = reported_raw.strip().lower() if isinstance(reported_raw, str) else None
            p_miri = parse_miri_summary_tag(m_tag)
            p_anneal = parse_anneal_summary_tag(a_tag)
            expected_verdict = (
                compare_parsed_outcomes(p_miri, p_anneal)[0]
                if p_miri is not None and p_anneal is not None
                else "not_compared"
            )
            if (
                polarity == WITNESS_POLARITY_VALUE_MISMATCH
                and reported == "agree"
                and isinstance(m_tag, str)
                and isinstance(a_tag, str)
                and name in reconciled
                and _reconciled_panic_site_matches(reconciled[name], name, m_tag, a_tag)
            ):
                polarity = None
                expected_verdict = "agree"
                reconciled_used.add(name)
            if reported != expected_verdict:
                reasons.append(
                    f"{label}: item_outcomes[{name!r}] reported verdict {reported_raw!r}, "
                    f"but its outcomes ({m_tag!r}, {a_tag!r}) have verdict {expected_verdict!r}"
                )
            if polarity is not None:
                recount[polarity] += 1
        for unused_name in sorted(set(reconciled) - reconciled_used):
            reasons.append(
                f"{label}: reconciled_panic_sites lists {unused_name!r}, but its item "
                "outcome is not a panic-macro site agreement that the entry justifies"
            )
        compile_failed = summary.get("compile_failed_candidates")
        if is_nonneg_int(compile_failed):
            recount[WITNESS_POLARITY_HARNESS] += compile_failed
        else:
            reasons.append(
                f"{label}: compile_failed_candidates {compile_failed!r} is not a non-negative "
                "integer"
            )
        for pol in VALID_WITNESS_POLARITIES:
            if int(pol_map[pol]) != recount[pol]:
                reasons.append(
                    f"{label}: witness_polarity_counts.{pol} reported {pol_map[pol]} but item "
                    f"outcomes (plus compile failures) classify {recount[pol]}"
                )
    return reasons


def _is_rust_ident_segment(seg: str) -> bool:
    return (
        bool(seg)
        and not seg[0].isdigit()
        and all(c.isascii() and (c.isalnum() or c == "_") for c in seg)
    )


def _is_closure_def_path_segment(seg: str) -> bool:
    if seg == "{closure}":
        return True
    if seg.startswith("{closure#") and seg.endswith("}"):
        num = seg[len("{closure#") : -1]
        return bool(num) and num.isascii() and num.isdigit()
    return False


def _is_valid_reconciled_panic_frame(frame: Any, fn_name: str) -> bool:
    """Port of `miri_eval::frame_matches_scope`: `frame` must be `<user_crate>::<fn_name>`
    (or a nested `fn`, closure, or `panic_cold_*` shim inside `<user_crate>::<fn_name>`)."""
    if not isinstance(frame, str) or not frame.strip():
        return False
    parts = frame.strip().split("::")
    if len(parts) < 2:
        return False
    crate_seg, root_fn = parts[0], parts[1]
    if crate_seg in ("core", "std", "alloc") or not _is_rust_ident_segment(crate_seg):
        return False
    if root_fn != fn_name:
        return False
    return all(
        _is_rust_ident_segment(seg) or _is_closure_def_path_segment(seg) for seg in parts[2:]
    )


def _reconciled_panic_site_matches(
    site: dict[str, Any], fn_name: str, miri_tag: str, anneal_tag: str
) -> bool:
    """Checks that a `reconciled_panic_sites` entry justifies reporting the panic
    pair `(miri_tag, anneal_tag)` as `agree` (`compare_difftest_miri_and_anneal`):
    both panicked with known positions recorded verbatim in the entry, Anneal's
    span lies in a standard panic-macro file, Miri's position lies in the staged
    `src/lib.rs`, Anneal recovered a panic frame inside `<user_crate>::<fn_name>`,
    and the kernel confirmed it."""
    if not (miri_tag.startswith("panic@") and anneal_tag.startswith("panic@")):
        return False
    miri_loc = miri_tag[len("panic@") :]
    anneal_loc = anneal_tag[len("panic@") :]
    if site.get("batch_miri_pos") != miri_loc or site.get("anneal_span") != anneal_loc:
        return False
    pos = _parse_src_pos(miri_loc)
    span = _parse_src_span(anneal_loc)
    frame = site.get("anneal_panic_frame")
    return (
        pos is not None
        and span is not None
        and _is_std_panic_macro_file(span[0])
        and _normalize_file_for_match(pos[0]) == "src/lib.rs"
        and _is_valid_reconciled_panic_frame(frame, fn_name)
        and site.get("kernel_confirmed") is True
    )


def _anneal_lean_tag_problem(name: str, anneal_tag: str, lean_tag: Any) -> str | None:
    """Checks that an `item_outcomes` entry's `anneal_lean_tag` matches its
    `anneal_outcome` (`AnnealOutcome::to_lean_mir_diff_tag`)."""
    if not isinstance(lean_tag, str) or not lean_tag.strip():
        return (
            f"item_accounting_mismatch: item_outcomes[{name!r}] has missing or non-string "
            f"anneal_lean_tag {lean_tag!r}"
        )
    norm_lean = normalize_anneal_tag(lean_tag)
    if anneal_tag.startswith(ANNEAL_ERROR_TAG_PREFIXES):
        if norm_lean != "none":
            return (
                f"item_accounting_mismatch: item_outcomes[{name!r}] has error anneal_outcome "
                f"{anneal_tag!r} but anneal_lean_tag {lean_tag!r}"
            )
        return None
    if norm_lean == "none":
        return (
            f"error_masked_as_unsupported: item_outcomes[{name!r}] has anneal_lean_tag "
            f"'none' (capture/Lean error) masked under anneal_outcome {anneal_tag!r}"
        )
    a_prefix = anneal_tag.partition("@")[0]
    if anneal_tag == "pass:unit":
        ok = norm_lean == "MirDiffTag.normalUnit"
    elif _is_valid_pass_scalar_tag(anneal_tag) and "@" not in anneal_tag:
        _, _, bits, size = anneal_tag.split(":")
        inner = lean_tag.strip()
        while inner.startswith("(") and inner.endswith(")"):
            inner = inner[1:-1].strip()
        ok = inner == f"MirDiffTag.normalScalar {bits} {size}"
    elif anneal_tag == "pass:other":
        ok = norm_lean == "MirDiffTag.normalOther"
    elif a_prefix == "panic":
        ok = norm_lean == "MirDiffTag.panic"
    elif a_prefix == "abort":
        ok = norm_lean == "MirDiffTag.abort"
    elif a_prefix == "ub":
        ok = norm_lean == "MirDiffTag.ub"
    elif anneal_tag.startswith("unsupported"):
        ok = norm_lean == "MirDiffTag.unsupported"
    elif anneal_tag.startswith("externalCall"):
        ok = norm_lean.startswith("MirDiffTag.externalCall")
    elif anneal_tag.startswith("outOfFuel"):
        ok = norm_lean == "MirDiffTag.outOfFuel"
    else:
        ok = False
    if not ok:
        return (
            f"item_accounting_mismatch: item_outcomes[{name!r}] anneal_lean_tag {lean_tag!r} "
            f"does not match anneal_outcome {anneal_tag!r}"
        )
    return None


def audit_item_outcomes_against_summary(summary: dict[str, Any]) -> list[str]:
    """Recomputes every reported item's verdict from its Miri / Anneal outcome tags.

    `item_outcomes` (emitted by `miri-difftest`) carries each evaluated item's
    `verdict` plus the lossless `summary_tag` of both outcomes. Because
    `classify_oracle_outcome_tags` is an exact port of `compare_miri_and_anneal`,
    the harness's per-item verdicts and its aggregate `agree_count`,
    `divergence_classes`, `not_compared_reasons` (except `compile_failed`, which
    carries no item outcome), `miri_verdicts`, and `anneal_outcomes` must equal the
    recomputation. The one sanctioned difference is the panic-site reconciliation of
    `compare_difftest_miri_and_anneal`: a `panic_site_mismatch` pair reported as
    `agree` is accepted only when `reconciled_panic_sites` lists the item with the
    same Miri position and Anneal span inside a standard panic-macro file, and
    every listed site must be such an item. Every finding must name an item whose
    outcomes diverge with the finding's `divergence_class`, and every diverging item
    must have exactly one finding. A capture/Lean or Miri error that the
    harness counted anywhere else (for example under `unsupported`) is reported as
    `error_masked_as_unsupported`; every other disagreement as
    `item_accounting_mismatch`. Summaries without `item_outcomes` are not audited.
    """
    if "item_outcomes" not in summary or summary.get("item_outcomes") is None:
        return []
    items = summary.get("item_outcomes")
    if not isinstance(items, dict):
        return ["item_accounting_mismatch: item_outcomes is not a dict"]
    reasons: list[str] = []

    reconciled: dict[str, dict[str, Any]] = {}
    sites_raw = summary.get("reconciled_panic_sites")
    site_count = summary.get("reconciled_panic_sites_count")
    if sites_raw is not None:
        if not isinstance(sites_raw, list):
            reasons.append("item_accounting_mismatch: reconciled_panic_sites is not a list")
        else:
            for idx, site in enumerate(sites_raw):
                name_val = site.get("fn_name") if isinstance(site, dict) else None
                if not isinstance(name_val, str) or not name_val.strip():
                    reasons.append(
                        f"item_accounting_mismatch: reconciled_panic_sites[{idx}] lacks a fn_name"
                    )
                elif name_val in reconciled:
                    reasons.append(
                        f"item_accounting_mismatch: reconciled_panic_sites lists {name_val!r} twice"
                    )
                else:
                    reconciled[name_val] = site
            if site_count is not None and (
                isinstance(site_count, bool)
                or not isinstance(site_count, int)
                or site_count != len(sites_raw)
            ):
                reasons.append(
                    f"item_accounting_mismatch: reconciled_panic_sites_count is {site_count!r} "
                    f"but reconciled_panic_sites lists {len(sites_raw)}"
                )
    elif site_count is not None and (
        isinstance(site_count, bool) or not isinstance(site_count, int) or site_count != 0
    ):
        reasons.append(
            f"item_accounting_mismatch: reconciled_panic_sites_count is {site_count!r} "
            f"without reconciled_panic_sites"
        )
    reconciled_used: set[str] = set()
    item_verdicts: dict[str, tuple[str, str]] = {}

    agree = 0
    classes: dict[str, int] = {}
    nc_counts: dict[str, int] = {}
    miri_counts: dict[str, int] = {"pass": 0, "panic": 0, "ub": 0, "error": 0}
    anneal_counts: dict[str, int] = {
        "pass": 0,
        "panic": 0,
        "ub": 0,
        "unsupported": 0,
        "out_of_fuel": 0,
        "external_call": 0,
        "error": 0,
    }
    for name, entry in sorted(items.items()):
        miri_tag = entry.get("miri_outcome") if isinstance(entry, dict) else None
        anneal_tag = entry.get("anneal_outcome") if isinstance(entry, dict) else None
        if not isinstance(miri_tag, str) or not isinstance(anneal_tag, str):
            reasons.append(
                f"item_accounting_mismatch: item_outcomes[{name!r}] lacks string "
                f"miri_outcome / anneal_outcome"
            )
            continue
        if "anneal_lean_tag" in entry:
            lean_prob = _anneal_lean_tag_problem(name, anneal_tag, entry.get("anneal_lean_tag"))
            if lean_prob is not None:
                reasons.append(lean_prob)

        m_prefix, m_sep, _ = miri_tag.partition("@")
        if miri_tag.startswith(MIRI_ERROR_TAG_PREFIXES):
            miri_counts["error"] += 1
        elif miri_tag.startswith("pass:") and not m_sep:
            miri_counts["pass"] += 1
        elif m_prefix in ("panic", "ub"):
            miri_counts[m_prefix] += 1
        else:
            miri_counts["error"] += 1

        a_prefix, a_sep, _ = anneal_tag.partition("@")
        if anneal_tag.startswith(ANNEAL_ERROR_TAG_PREFIXES):
            anneal_counts["error"] += 1
        elif anneal_tag.startswith("externalCall"):
            anneal_counts["external_call"] += 1
        elif anneal_tag.startswith("unsupported"):
            anneal_counts["unsupported"] += 1
        elif anneal_tag.startswith("outOfFuel"):
            anneal_counts["out_of_fuel"] += 1
        elif anneal_tag.startswith("pass:") and not a_sep:
            anneal_counts["pass"] += 1
        elif a_prefix in ("panic", "abort"):
            anneal_counts["panic"] += 1
        elif a_prefix == "ub":
            anneal_counts["ub"] += 1
        else:
            anneal_counts["error"] += 1

        verdict, detail = classify_oracle_outcome_tags(miri_tag, anneal_tag)
        reported = str(entry.get("verdict", "")).strip().lower()
        if (
            reported == "agree"
            and (verdict, detail) == ("diverge", "panic_site_mismatch")
            and name in reconciled
            and _reconciled_panic_site_matches(reconciled[name], name, miri_tag, anneal_tag)
        ):
            verdict, detail = "agree", ""
            reconciled_used.add(name)
        if reported != verdict:
            label = (
                "error_masked_as_unsupported"
                if verdict == "not_compared" and detail in MIRI_ERROR_NOT_COMPARED_REASONS
                else "item_accounting_mismatch"
            )
            reasons.append(
                f"{label}: item {name!r} reported {reported!r} but its outcomes "
                f"({miri_tag!r}, {anneal_tag!r}) classify as {verdict}:{detail}"
            )
        if verdict == "agree":
            agree += 1
        elif verdict == "diverge":
            classes[detail] = classes.get(detail, 0) + 1
        else:
            nc_counts[detail] = nc_counts.get(detail, 0) + 1
        item_verdicts[name] = (verdict, detail)

    for name in sorted(set(reconciled) - reconciled_used):
        reasons.append(
            f"item_accounting_mismatch: reconciled_panic_sites lists {name!r}, but its item "
            f"outcome is not a panic-macro site agreement that the entry justifies"
        )

    # `miri-difftest` emits exactly one finding per diverging item, named after the
    # item, attributed to that item's `seed_name` (`fn_name == seed_name` or
    # `fn_name.startswith(f"{seed_name}__")`), and carrying outcome tags and a
    # `anneal_lean_tag` that reproduce the item's `divergence_class`. Dedup and
    # quarantine judge divergences by their findings alone, so a finding attributed
    # to the wrong item/seed/Lean tag, or a divergence without its finding, would
    # hide that divergence.
    findings = summary.get("findings")
    if isinstance(findings, list):
        findings_per_item: dict[str, int] = {}
        is_identity = summary.get("mode") == "identity"
        for idx, finding in enumerate(findings):
            fn_name = finding.get("fn_name") if isinstance(finding, dict) else None
            if not isinstance(fn_name, str):
                continue  # `validate_performed_miri_summary` rejects such findings
            findings_per_item[fn_name] = findings_per_item.get(fn_name, 0) + 1
            seed_name = finding.get("seed_name")
            if (
                not isinstance(seed_name, str)
                or not seed_name.strip()
                or (seed_name != fn_name and (is_identity or seed_name in items))
            ):
                reasons.append(
                    f"item_accounting_mismatch: findings[{idx}] for {fn_name!r} has "
                    f"inconsistent seed_name {seed_name!r}"
                )
            f_miri = finding.get("miri_outcome")
            f_anneal = finding.get("anneal_outcome")
            f_div_cls = finding.get("divergence_class")
            if isinstance(f_miri, str) and isinstance(f_anneal, str):
                f_verdict, f_sub = classify_oracle_outcome_tags(f_miri, f_anneal)
                if f_verdict != "diverge" or f_sub != f_div_cls:
                    reasons.append(
                        f"item_accounting_mismatch: findings[{idx}] outcomes "
                        f"({f_miri!r}, {f_anneal!r}) classify as {f_verdict}:{f_sub} "
                        f"instead of diverge:{f_div_cls}"
                    )
                if "anneal_lean_tag" in finding:
                    f_lean_prob = _anneal_lean_tag_problem(
                        f"findings[{idx}]", f_anneal, finding.get("anneal_lean_tag")
                    )
                    if f_lean_prob is not None:
                        reasons.append(f_lean_prob)
            recomputed = item_verdicts.get(fn_name)
            if recomputed is None:
                if fn_name not in items:
                    reasons.append(
                        f"item_accounting_mismatch: findings[{idx}] names {fn_name!r}, "
                        f"which has no item_outcomes entry"
                    )
            elif recomputed[0] != "diverge":
                reasons.append(
                    f"item_accounting_mismatch: findings[{idx}] reports a divergence of "
                    f"{fn_name!r}, whose outcomes classify as {recomputed[0]}:{recomputed[1]}"
                )
            elif f_div_cls != recomputed[1]:
                reasons.append(
                    f"item_accounting_mismatch: findings[{idx}] gives {fn_name!r} "
                    f"divergence_class {f_div_cls!r}, but its outcomes "
                    f"classify as diverge:{recomputed[1]}"
                )
        for name, (verdict, detail) in sorted(item_verdicts.items()):
            count = findings_per_item.get(name, 0)
            if verdict == "diverge" and count != 1:
                reasons.append(
                    f"item_accounting_mismatch: item {name!r} diverges ({detail}) but has "
                    f"{count} findings instead of exactly 1"
                )
    elif "findings" in summary or any(v == "diverge" for v, _ in item_verdicts.values()):
        reasons.append("item_accounting_mismatch: findings is missing or not a list")

    compiled = summary.get("compiled_candidates")
    if isinstance(compiled, int) and not isinstance(compiled, bool) and len(items) != compiled:
        reasons.append(
            f"item_accounting_mismatch: item_outcomes covers {len(items)} items but "
            f"compiled_candidates is {compiled}"
        )
    reported_agree = summary.get("agree_count")
    if (
        isinstance(reported_agree, int)
        and not isinstance(reported_agree, bool)
        and reported_agree != agree
    ):
        reasons.append(
            f"item_accounting_mismatch: agree_count reported {reported_agree} but item "
            f"outcomes classify {agree} as agree"
        )
    total_diverge = sum(classes.values())
    reported_diverge = summary.get("diverge_count")
    if (
        isinstance(reported_diverge, int)
        and not isinstance(reported_diverge, bool)
        and reported_diverge != total_diverge
    ):
        reasons.append(
            f"item_accounting_mismatch: diverge_count reported {reported_diverge} but item "
            f"outcomes classify {total_diverge} as diverge"
        )
    reported_compared = summary.get("compared_candidates")
    if (
        isinstance(reported_compared, int)
        and not isinstance(reported_compared, bool)
        and reported_compared != agree + total_diverge
    ):
        reasons.append(
            f"item_accounting_mismatch: compared_candidates reported {reported_compared} but item "
            f"outcomes classify {agree + total_diverge} as compared"
        )
    div_map = summary.get("divergence_classes")
    if isinstance(div_map, dict):
        for cls in sorted(set(VALID_DIVERGENCE_CLASSES) | set(classes)):
            rep = _int_field(div_map, cls)
            rec = classes.get(cls, 0)
            if rep != rec:
                reasons.append(
                    f"item_accounting_mismatch: divergence_classes.{cls} reported {rep} but "
                    f"item outcomes classify {rec}"
                )
    nc_map = summary.get("not_compared_reasons")
    if isinstance(nc_map, dict):
        for reason in sorted(set(VALID_NOT_COMPARED_REASONS) | set(nc_counts)):
            if reason == "compile_failed":
                continue  # compile failures are never evaluated, so carry no item outcome
            rep = _int_field(nc_map, reason)
            rec = nc_counts.get(reason, 0)
            if rep != rec:
                label = (
                    "error_masked_as_unsupported"
                    if reason in MIRI_ERROR_NOT_COMPARED_REASONS and rec > rep
                    else "item_accounting_mismatch"
                )
                reasons.append(
                    f"{label}: not_compared_reasons.{reason} reported {rep} but item "
                    f"outcomes classify {rec}"
                )
    for map_key, counts in (("miri_verdicts", miri_counts), ("anneal_outcomes", anneal_counts)):
        reported_map = summary.get(map_key)
        if not isinstance(reported_map, dict):
            continue
        for k, rec in sorted(counts.items()):
            rep = _int_field(reported_map, k)
            if rep != rec:
                label = (
                    "error_masked_as_unsupported"
                    if k == "error" and rec > rep
                    else "item_accounting_mismatch"
                )
                reasons.append(
                    f"{label}: {map_key}.{k} reported {rep} but item outcomes classify {rec}"
                )
    return reasons


def load_known_corpus_bug_seeds(
    repo_root: Path, manifest_path: Path | None = None
) -> set[str]:
    """Names of the manifest tests documented as open Anneal bugs: every
    `[[tests]]` entry with a `[tests.known_anneal_bug]` table.

    These names never quarantine anything. Unless the fault lies on a line that a
    mutator introduced, `infer_finding_cause` attributes a divergence of such a seed
    to the seed itself instead of to its first mutator, which fixes the finding's
    fingerprint and keeps mutator-level quarantine tokens from matching it; manifest
    entries excuse findings only through `load_quarantine_rules`, which applies just
    the entries in force. Attribution therefore ignores an entry's metadata and
    `expires` date: a lapsed or incomplete entry still documents a seed that diverges
    on its own, and reattributing its divergences to a mutator would change their
    fingerprints and widen the quarantine tokens that match them (the stale ratchet
    reports such entries). A non-table `known_anneal_bug` value documents nothing,
    and an unreadable manifest or a non-array `tests` key yields no seeds instead of
    crashing the campaign."""
    eff_path = (
        manifest_path
        if manifest_path is not None
        else repo_root / "tests" / "miri-diff" / "manifest.toml"
    )
    try:
        if not eff_path.is_file():
            return set()
        data = tomllib.loads(eff_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError):
        return set()
    tests = data.get("tests", [])
    if not isinstance(tests, list):
        return set()
    seeds: set[str] = set()
    for entry in tests:
        if isinstance(entry, dict) and isinstance(entry.get("known_anneal_bug"), dict):
            name = entry.get("name")
            if isinstance(name, str) and name.strip():
                seeds.add(name.strip())
    return seeds


QUARANTINE_LIST_KEYS: tuple[str, ...] = (
    "quarantined",
    "entries",
    "rules",
    "fingerprints",
    "seeds",
    "mutators",
)

# Key of the `[[tests]]` array whose `known_anneal_bug` tables quarantine a test
# (the `tests/miri-diff/manifest.toml` format).
QUARANTINE_TESTS_KEY = "tests"

# Top-level metadata keys of `tests/miri-diff/manifest.toml`, accepted so that the
# manifest itself remains a valid quarantine file. Every other top-level key that is
# neither a `QUARANTINE_LIST_KEYS` list nor `tests` fails the ratchet audit closed
# (a misspelled list key would otherwise silently quarantine nothing).
QUARANTINE_METADATA_KEYS: tuple[str, ...] = (
    "schema_version",
    "rustc_commit",
    "rustc_version",
    "upstream_repo_url",
    "upstream_tests_subtree",
    "miri_flags",
    "capture_rustflags",
)

MIRI_MUTATOR_NAMES: tuple[str, ...] = (
    "ArithmeticCastMutator",
    "BitValidityTransmuteMutator",
    "PlaceProjectionWrapper",
    "RawPtrOffsetMutator",
    "TreeBorrowsRetagInterleaver",
)

ITREE_MUTATOR_NAMES: tuple[str, ...] = (
    "BranchLoopWeaver",
    "CallBoundaryOutliner",
    "ExtOracleInjector",
    "LayoutPaddingPerturber",
)


def _is_valid_iso_date(raw: Any) -> bool:
    if not isinstance(raw, str) or len(raw) != 10:
        return False
    try:
        datetime.date.fromisoformat(raw)
    except ValueError:
        return False
    return True


def _is_well_formed_quarantine_token(token: Any) -> bool:
    """A quarantine token is non-empty, contains no whitespace, and has no empty
    `:`-separated segment."""
    if not isinstance(token, str):
        return False
    clean = token.strip()
    if not clean or any(ch.isspace() for ch in clean):
        return False
    return all(part.strip() for part in clean.split(":"))


def _expires_as_iso_text(expires: Any) -> Any:
    """Returns a TOML native date or datetime `expires` value (`expires =
    2027-01-01`, which `tomllib` parses to `datetime.date`) as its `YYYY-MM-DD`
    text, so it is judged exactly like the quoted form; any other value is
    returned unchanged."""
    if isinstance(expires, datetime.datetime):
        if expires.tzinfo is not None:
            expires = expires.astimezone(datetime.timezone.utc)
        return expires.date().isoformat()
    if isinstance(expires, datetime.date):
        return expires.isoformat()
    return expires


def quarantine_expiry_problem(expires: Any, today: str, required: bool) -> str | None:
    """Returns why a quarantine entry with this `expires` value is not in force
    (`missing_quarantine_expiry`, `malformed_expires_date`, or
    `expired_quarantine_entry`), or `None` when it is. A TOML native date counts
    as its ISO text."""
    if expires is None:
        if required:
            return "missing_quarantine_expiry: table entries must carry an expires date"
        return None
    expires = _expires_as_iso_text(expires)
    if not _is_valid_iso_date(expires):
        return f"malformed_expires_date: {expires!r}"
    if expires < today:
        return f"expired_quarantine_entry: expires {expires} < {today}"
    return None


@dataclass(frozen=True)
class QuarantineEntry:
    """One entry of a quarantine file, normalized identically for
    `load_quarantine_rules` (which applies `token` iff the entry is in force) and
    `verify_no_stale_quarantine_or_known_bugs` (which audits it).

    - `location`: where the entry lives (`quarantined[2]`, `tests[5]`, ...).
    - `token`: the exact token the loader applies, or `None` when the entry has no
      well-formed token.
    - `expires`: the raw `expires` value (`None` when absent).
    - `expiry_required`: whether the entry is a `{fingerprint|id, expires, reason}`
      table, which is only in force with a valid, unexpired `expires` date.
    - `defects`: reasons the loader refuses the entry regardless of its expiry
      (malformed token, missing `known_anneal_bug` metadata, invalid
      `divergence_class`).
    - `metadata_warnings`: incomplete documentation that does not stop the loader
      from applying the entry but fails the ratchet audit (a table without
      `reason` / `summary`).
    """

    location: str
    token: str | None
    expires: Any
    expiry_required: bool
    defects: tuple[str, ...]
    metadata_warnings: tuple[str, ...] = ()

    def expiry_problem(self, today: str) -> str | None:
        return quarantine_expiry_problem(self.expires, today, self.expiry_required)

    def in_force(self, today: str) -> bool:
        return self.token is not None and not self.defects and self.expiry_problem(today) is None


def _quarantine_token_witness_polarity_defect(
    token: str | None,
    raw_polarity: Any,
    prefix: str,
    allow_harness_polarity: bool = True,
) -> str | None:
    """Validates an optional `witness_polarity` field on a quarantine or
    `known_anneal_bug` entry against `VALID_WITNESS_POLARITIES`, the entry's harness,
    and any `divergence_class` segment in `token`."""
    if raw_polarity is None:
        return None
    if not isinstance(raw_polarity, str) or raw_polarity.strip() not in VALID_WITNESS_POLARITIES:
        return f"{prefix}: invalid witness_polarity {raw_polarity!r}"
    pol = raw_polarity.strip()
    if not allow_harness_polarity and pol == WITNESS_POLARITY_HARNESS:
        return (
            f"{prefix}: quarantine entry {token!r} cannot have "
            f"witness_polarity {pol!r} (only divergences are quarantined)"
        )
    if token is not None:
        if quarantine_entry_harness(token) == "itree":
            return f"{prefix}: itree entry {token!r} cannot have witness_polarity {pol!r}"
        div_parts = [
            part for part in token.split(":") if part in DIVERGENCE_CLASS_WITNESS_POLARITY
        ]
        if len(set(div_parts)) > 1:
            return (
                f"{prefix}: token {token!r} names conflicting divergence classes "
                f"{div_parts!r}"
            )
        if not allow_harness_polarity and ":" in token and not div_parts:
            return (
                f"{prefix}: token {token!r} lacks a valid divergence_class to confirm "
                f"witness_polarity {pol!r}"
            )
        for part in div_parts:
            expected = DIVERGENCE_CLASS_WITNESS_POLARITY[part]
            if pol != expected:
                return (
                    f"{prefix}: witness_polarity {pol!r} contradicts "
                    f"divergence_class {part!r} ({expected!r})"
                )
    return None


def _quarantine_list_entry(location: str, item: Any) -> QuarantineEntry:
    if isinstance(item, str):
        token = item.strip()
        if _is_well_formed_quarantine_token(token):
            return QuarantineEntry(location, token, None, False, ())
        return QuarantineEntry(
            location, None, None, False, (f"malformed_or_missing_fingerprint: {item!r}",)
        )
    if isinstance(item, dict):
        raw_token = item.get("fingerprint", item.get("id"))
        token = raw_token.strip() if isinstance(raw_token, str) else None
        defects_list: list[str] = []
        if token is None or not _is_well_formed_quarantine_token(token) or ":" not in token:
            defects_list.append(f"malformed_or_missing_fingerprint: {raw_token!r}")
            token = None
        pol_defect = _quarantine_token_witness_polarity_defect(
            token,
            item.get("witness_polarity"),
            "malformed_quarantine_entry",
            allow_harness_polarity=False,
        )
        if pol_defect is not None:
            defects_list.append(pol_defect)
        reason_text = item.get("reason") or item.get("summary")
        warnings: tuple[str, ...] = ()
        if not isinstance(reason_text, str) or not reason_text.strip():
            warnings = (
                "missing_quarantine_metadata: table entries must carry a reason or summary",
            )
        return QuarantineEntry(
            location, token, item.get("expires"), True, tuple(defects_list), warnings
        )
    return QuarantineEntry(
        location,
        None,
        None,
        False,
        (f"malformed_quarantine_entry: expected string or table, got {type(item).__name__}",),
    )


def _quarantine_known_bug_entry(location: str, test_entry: dict[str, Any]) -> QuarantineEntry:
    """Normalizes a `[[tests]]` entry carrying `known_anneal_bug`: the loader applies
    `name:divergence_class` when `divergence_class` is present (a valid
    `VALID_DIVERGENCE_CLASSES` member) and the bare test `name` otherwise, and only
    when the bug carries `observed_anneal_tag` and `summary` / `reason` (and a
    consistent `witness_polarity` when specified)."""
    name = test_entry.get("name")
    bug = test_entry.get("known_anneal_bug")
    if not isinstance(name, str) or not name.strip():
        return QuarantineEntry(
            location,
            None,
            None,
            False,
            ("malformed_or_missing_fingerprint: missing test name on known_anneal_bug",),
        )
    clean_name = name.strip()
    if not isinstance(bug, dict):
        return QuarantineEntry(
            location, None, None, False, ("malformed_known_anneal_bug: expected table",)
        )
    defects: list[str] = []
    obs_tag = bug.get("observed_anneal_tag")
    if not isinstance(obs_tag, str) or not obs_tag.strip():
        defects.append("missing_known_anneal_bug_metadata: missing observed_anneal_tag")
    reason_text = bug.get("summary") or bug.get("reason")
    if not isinstance(reason_text, str) or not reason_text.strip():
        defects.append("missing_known_anneal_bug_metadata: missing summary/reason")
    token = clean_name
    if not _is_well_formed_quarantine_token(clean_name):
        defects.append(f"malformed_or_missing_fingerprint: {name!r}")
    div_cls = bug.get("divergence_class")
    if div_cls is not None:
        if not isinstance(div_cls, str) or div_cls.strip() not in VALID_DIVERGENCE_CLASSES:
            defects.append(f"malformed_known_anneal_bug: invalid divergence_class {div_cls!r}")
        else:
            token = f"{clean_name}:{div_cls.strip()}"
    pol_defect = _quarantine_token_witness_polarity_defect(
        token, bug.get("witness_polarity"), "malformed_known_anneal_bug"
    )
    if pol_defect is not None:
        defects.append(pol_defect)
    return QuarantineEntry(
        f"{location} ({clean_name})", token, bug.get("expires"), False, tuple(defects)
    )


def parse_quarantine_document(data: Any) -> tuple[list[QuarantineEntry], list[str]]:
    """Normalizes a parsed quarantine document (JSON or TOML) into its entries.

    Accepts a top-level list of entries, or a table whose `QUARANTINE_LIST_KEYS`
    lists hold entries (plain token strings or `{fingerprint|id, expires, reason}`
    tables) and whose `tests` array holds `known_anneal_bug` entries. Returns
    `(entries, structural_problems)`: every top-level key that is neither one of
    those nor `QUARANTINE_METADATA_KEYS`, every non-list list key, and every
    non-table `tests` element is a structural problem.
    """
    entries: list[QuarantineEntry] = []
    problems: list[str] = []
    if isinstance(data, list):
        for idx, item in enumerate(data):
            entries.append(_quarantine_list_entry(f"[{idx}]", item))
        return entries, problems
    if not isinstance(data, dict):
        problems.append("malformed_quarantine_file: expected list or table")
        return entries, problems
    for key in QUARANTINE_LIST_KEYS:
        if key not in data:
            continue
        vals = data[key]
        if not isinstance(vals, list):
            problems.append(f"malformed_quarantine_file: key {key!r} must be a list")
            continue
        for idx, item in enumerate(vals):
            entries.append(_quarantine_list_entry(f"{key}[{idx}]", item))
    if QUARANTINE_TESTS_KEY in data:
        tests = data[QUARANTINE_TESTS_KEY]
        if not isinstance(tests, list):
            problems.append("malformed_quarantine_file: key 'tests' must be a list")
        else:
            for idx, test_entry in enumerate(tests):
                if not isinstance(test_entry, dict):
                    problems.append(
                        f"malformed_quarantine_file: tests[{idx}] must be a table"
                    )
                elif "known_anneal_bug" in test_entry:
                    entries.append(_quarantine_known_bug_entry(f"tests[{idx}]", test_entry))
    unknown = sorted(
        str(k)
        for k in data
        if k not in QUARANTINE_LIST_KEYS
        and k != QUARANTINE_TESTS_KEY
        and k not in QUARANTINE_METADATA_KEYS
    )
    if unknown:
        problems.append(f"malformed_quarantine_file: unrecognized quarantine keys {unknown!r}")
    return entries, problems


def read_quarantine_document(quarantine_file: Path) -> Any:
    """Reads and parses a JSON or TOML quarantine file; raises `ValueError` when it
    is missing, unreadable, or syntactically invalid."""
    try:
        if not quarantine_file.is_file():
            raise ValueError(f"quarantine file does not exist: {quarantine_file}")
        text = quarantine_file.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as e:
        raise ValueError(f"cannot read quarantine file {quarantine_file}: {e}") from e
    if quarantine_file.suffix.lower() == ".toml":
        try:
            return tomllib.loads(text)
        except tomllib.TOMLDecodeError as e:
            raise ValueError(f"invalid TOML in {quarantine_file}: {e}") from e
    try:
        return _strict_json_loads(text, reject_duplicate_keys=True)
    except ValueError as e:
        raise ValueError(f"invalid JSON in {quarantine_file}: {e}") from e


def load_quarantine_rules(quarantine_file: Path | None) -> set[str]:
    """Loads the quarantine tokens in force from a JSON or TOML file.

    Entries are plain token strings, `{fingerprint | id, expires, reason}` tables
    (in force only with a valid `expires` date that has not passed), or `[[tests]]`
    `known_anneal_bug` entries (see `parse_quarantine_document`). Malformed,
    incomplete, or expired entries are never applied, so they cannot hide a
    finding; `verify_no_stale_quarantine_or_known_bugs` reports them. Raises
    `ValueError` for a missing or unreadable file, invalid syntax, or a JSON root
    that is neither a list nor an object.
    """
    if quarantine_file is None:
        return set()
    data = read_quarantine_document(quarantine_file)
    if not isinstance(data, (list, dict)):
        raise ValueError(f"unsupported quarantine JSON root in {quarantine_file}")
    today = utc_date_prefix()
    entries, _ = parse_quarantine_document(data)
    return {e.token for e in entries if e.token is not None and e.in_force(today)}


def quarantine_entry_harness(token: str) -> str | None:
    """Returns `"itree"` / `"miri"` when a quarantine token names findings of that
    harness, or `None` for a token without a harness marker (a bare seed or
    candidate name). Every key `quarantine_match_keys_for_itree_finding` produces
    carries an ITree marker (`itree_` seed and class names, `__kernel_step`
    candidates, ITree mutators, diagnostic tags, `TraceReplayDiag.`), so an
    unmarked token can only match `miri-difftest` findings."""
    if (
        "itree_" in token
        or "TraceReplayDiag." in token
        or "__kernel_step" in token
        or token.startswith("itree:")
        or token in VALID_ITREE_DIAG_TAGS
    ):
        return "itree"
    head = token.split(":", 1)[0]
    if head in ITREE_MUTATOR_NAMES:
        return "itree"
    if head in MIRI_MUTATOR_NAMES:
        return "miri"
    parts = token.split(":")
    if any(p in VALID_ITREE_DIAG_TAGS and p != "ok" for p in parts):
        return "itree"
    if any(p in VALID_DIVERGENCE_CLASSES for p in parts) or "MirDiffTag." in token:
        return "miri"
    return None


def _resolved_ledger_fingerprints(ledger: dict[str, Any]) -> set[str]:
    """Fingerprints recorded as resolved: the keys of the per-suite
    `resolved_history` map, plus legacy list-shaped `resolved_history` /
    `resolved_fingerprints` entries (strings or `{fingerprint: ...}` tables)."""
    resolved: set[str] = set()
    for hist_key in ("resolved_history", "resolved_fingerprints"):
        hist = ledger.get(hist_key)
        if isinstance(hist, dict):
            resolved.update(k.strip() for k in hist if isinstance(k, str) and k.strip())
        elif isinstance(hist, list):
            for item in hist:
                if isinstance(item, str) and item.strip():
                    resolved.add(item.strip())
                elif isinstance(item, dict) and isinstance(item.get("fingerprint"), str):
                    resolved.add(item["fingerprint"].strip())
    return resolved


def _strip_outer_parens(raw_tag: str) -> str:
    clean = raw_tag.strip()
    while clean.startswith("(") and clean.endswith(")"):
        clean = clean[1:-1].strip()
    return clean


def _known_bug_tags_match(observed: str, expected_obs: str) -> bool:
    """Checks whether `observed` matches `expected_obs`: outer parentheses are
    stripped on both sides, and `MirDiffTag.normalScalar <bits> <size>` only
    collapses to `MirDiffTag.normalScalar` when `expected_obs` itself is the
    unparameterized `MirDiffTag.normalScalar`."""
    obs_clean = _strip_outer_parens(observed)
    exp_clean = _strip_outer_parens(expected_obs)
    if exp_clean == "MirDiffTag.normalScalar":
        return normalize_anneal_tag(obs_clean) == "MirDiffTag.normalScalar"
    return obs_clean == exp_clean


def _known_bug_eval_problem(
    obs_tag: Any,
    ev: Any,
    expected_div_class: str | None = None,
    expected_polarity: str | None = None,
) -> str | None:
    """Compares a `known_anneal_bug` entry's `observed_anneal_tag` (and optional
    `divergence_class` / `witness_polarity`) with the live evaluation `ev` of its
    test (a verdict string or an `item_outcomes` record). A bare string names no
    divergence class or polarity, so an entry that declares either one cannot be
    confirmed by it (`stale_known_anneal_bug_unconfirmed`)."""
    if isinstance(ev, str):
        ev_clean = ev.strip()
        ev_lower = ev_clean.lower()
        if not ev_clean:
            return "stale_known_anneal_bug_unconfirmed: empty evaluation string"
        if ev_lower in ("agree", "pass", "pass:unit") or ev_lower.startswith("pass:scalar"):
            return f"stale_known_anneal_bug_now_passes: observed {ev!r}"
        if (
            ev_lower in ("not_compared", "error")
            or ev_lower.startswith("oracle_error")
            or ev_lower.startswith("capture_error")
            or ev_lower.startswith("error:")
        ):
            return (
                "stale_known_anneal_bug_unconfirmed: the live evaluation errored "
                f"({ev!r}), so the open bug was not reproduced"
            )
        if isinstance(obs_tag, str) and obs_tag.strip():
            if not _known_bug_tags_match(ev_clean, obs_tag):
                return f"stale_known_anneal_bug_tag_mismatch: expected {obs_tag!r}, got {ev!r}"
        if expected_div_class is not None or expected_polarity is not None:
            return (
                "stale_known_anneal_bug_unconfirmed: the evaluation string "
                f"{ev!r} cannot confirm the declared divergence_class "
                f"{expected_div_class!r} / witness_polarity {expected_polarity!r}"
            )
        return None
    if not isinstance(ev, dict):
        return f"stale_known_anneal_bug_unconfirmed: unreadable evaluation {ev!r}"
    verdict = str(ev.get("verdict", "")).strip().lower()
    if verdict == "agree":
        return "stale_known_anneal_bug_now_passes: verdict is Agree"
    miri_tag = ev.get("miri_outcome")
    anneal_tag = ev.get("anneal_outcome")
    if (
        (isinstance(miri_tag, str) and miri_tag.startswith(MIRI_ERROR_TAG_PREFIXES))
        or (isinstance(anneal_tag, str) and anneal_tag.startswith(ANNEAL_ERROR_TAG_PREFIXES))
        or verdict not in ("diverge", "not_compared")
    ):
        return (
            "stale_known_anneal_bug_unconfirmed: the live evaluation errored or had "
            f"an unrecognized verdict ({verdict!r}, {miri_tag!r}, {anneal_tag!r}), "
            "so the open bug was not reproduced"
        )
    candidate_tags: list[str] = []
    for tag_key in (
        "observed_anneal_tag",
        "anneal_outcome",
        "repro_anneal_outcome",
        "anneal_lean_tag",
    ):
        raw_t = ev.get(tag_key)
        if isinstance(raw_t, str) and raw_t.strip():
            candidate_tags.append(raw_t.strip())
            if "@" in raw_t and isinstance(obs_tag, str) and "@" not in obs_tag:
                candidate_tags.append(raw_t.split("@", 1)[0].strip())
    if isinstance(obs_tag, str) and obs_tag.strip():
        if not candidate_tags:
            return (
                "stale_known_anneal_bug_unconfirmed: evaluation lacks an Anneal outcome tag "
                f"to confirm {obs_tag!r}"
            )
        if not any(_known_bug_tags_match(t, obs_tag) for t in candidate_tags):
            return (
                f"stale_known_anneal_bug_tag_mismatch: expected {obs_tag!r}, "
                f"got {candidate_tags[0]!r}"
            )
    observed_div_cls = ev.get("divergence_class")
    if (
        (not isinstance(observed_div_cls, str) or not observed_div_cls.strip())
        and isinstance(miri_tag, str)
        and isinstance(anneal_tag, str)
    ):
        cls_verdict, cls_sub = classify_oracle_outcome_tags(miri_tag, anneal_tag)
        if cls_verdict == "diverge":
            observed_div_cls = cls_sub
    if expected_div_class is not None:
        if verdict != "diverge":
            return (
                "stale_known_anneal_bug_divergence_class_mismatch: "
                f"expected divergence {expected_div_class!r}, got verdict {verdict!r}"
            )
        if (
            isinstance(observed_div_cls, str)
            and observed_div_cls.strip()
            and observed_div_cls.strip() != expected_div_class
        ):
            return (
                "stale_known_anneal_bug_divergence_class_mismatch: "
                f"expected {expected_div_class!r}, got {observed_div_cls.strip()!r}"
            )
    raw_ev_pol = ev.get("witness_polarity")
    if raw_ev_pol is not None and (
        not isinstance(raw_ev_pol, str) or raw_ev_pol.strip() not in VALID_WITNESS_POLARITIES
    ):
        return (
            "stale_known_anneal_bug_unconfirmed: evaluation has invalid "
            f"witness_polarity {raw_ev_pol!r}"
        )
    if expected_polarity is not None:
        observed_sources: list[str | None] = []
        if isinstance(raw_ev_pol, str) and raw_ev_pol.strip() in VALID_WITNESS_POLARITIES:
            observed_sources.append(raw_ev_pol.strip())
        if (
            isinstance(observed_div_cls, str)
            and observed_div_cls.strip() in DIVERGENCE_CLASS_WITNESS_POLARITY
        ):
            observed_sources.append(
                DIVERGENCE_CLASS_WITNESS_POLARITY[observed_div_cls.strip()]
            )
        if isinstance(miri_tag, str) and isinstance(anneal_tag, str):
            observed_sources.append(classify_witness_polarity_from_tags(miri_tag, anneal_tag))
        if not observed_sources:
            return (
                "stale_known_anneal_bug_witness_polarity_mismatch: "
                f"expected {expected_polarity!r}, got None"
            )
        for obs_pol in observed_sources:
            if obs_pol != expected_polarity:
                return (
                    "stale_known_anneal_bug_witness_polarity_mismatch: "
                    f"expected {expected_polarity!r}, got {obs_pol!r}"
                )
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
    manifest_eval_exhaustive: bool = False,
) -> dict[str, Any]:
    """Fail-closed ratchet audit flagging stale `--quarantine-file` entries and stale
    `tests/miri-diff/manifest.toml` `known_anneal_bug` entries.

    Quarantine entries are normalized by `parse_quarantine_document`, exactly as
    `load_quarantine_rules` reads them. Reported (each as a stale entry):

    - an unreadable or syntactically invalid file, a non-list / non-table root, a
      list key that is not a list, a non-table `[[tests]]` element, and every
      unrecognized top-level key;
    - malformed tokens, incomplete `known_anneal_bug` metadata, invalid
      `divergence_class` values, and tables without a `reason` / `summary`;
    - tables without a valid `expires` date, and every entry past its `expires`;
    - tokens recorded in the ledger's `resolved_history` that no active finding
      carries (`already_resolved_in_ledger`);
    - tokens that matched no finding of an evaluated run
      (`unobserved_quarantine_entry`). This rule only applies when an evaluated run
      was supplied (`evaluated_fingerprints` and/or `observed_quarantine_keys`, the
      latter being every key `deduplicate_and_quarantine_findings` /
      `deduplicate_and_quarantine_itree_findings` matches a token against), and
      only to tokens of a harness the run covered (`covered_harnesses`, `{"miri",
      "itree"}` when omitted; `quarantine_entry_harness`, with unmarked tokens
      counting as Miri tokens): a `--miri-only` run says nothing about ITree
      quarantine entries, nor a run whose Miri suite failed about Miri ones.

    Manifest `known_anneal_bug` entries (any number, including none) need
    `observed_anneal_tag` and `summary` / `reason`; when `manifest_eval_results`
    (from `extract_manifest_eval_results_from_miri_summary`) evaluated a test, an
    agreeing verdict (`stale_known_anneal_bug_now_passes`), a drifted Anneal tag
    (`stale_known_anneal_bug_tag_mismatch`), or an errored evaluation
    (`stale_known_anneal_bug_unconfirmed`) is stale. Tests the run did not evaluate
    are never assumed to agree; when the run evaluated every manifest test
    (`manifest_eval_exhaustive`, see `miri_summary_evaluates_every_manifest_test`),
    a `known_anneal_bug` test it reported nothing for did not reproduce its open bug
    and is stale too (`stale_known_anneal_bug_unconfirmed`).
    """
    ref_date = reference_date if reference_date is not None else utc_date_prefix()
    ledger_obj = ledger if isinstance(ledger, dict) else {}
    eval_fp_set: set[str] | None = (
        set(evaluated_fingerprints) if evaluated_fingerprints is not None else None
    )
    observed_keys: set[str] | None = (
        set(observed_quarantine_keys) if observed_quarantine_keys is not None else None
    )
    resolved_fps = _resolved_ledger_fingerprints(ledger_obj)
    active_fps: set[str] = set()
    for list_key in ("active_fingerprints", "quarantined_fingerprints"):
        vals = ledger_obj.get(list_key)
        if isinstance(vals, list):
            active_fps.update(fp for fp in vals if isinstance(fp, str))
    if eval_fp_set is not None:
        active_fps |= eval_fp_set
    if observed_keys is not None:
        active_fps |= observed_keys
    covered: set[str] = (
        set(covered_harnesses) if covered_harnesses is not None else {"miri", "itree"}
    )
    run_evaluated = eval_fp_set is not None or observed_keys is not None

    stale_quarantine: list[dict[str, Any]] = []
    checked_quarantine_count = 0

    def stale_q(entry: str, reason: str) -> None:
        stale_quarantine.append(
            {"source": str(quarantine_file), "entry": entry, "reason": reason}
        )

    if quarantine_file is not None:
        q_data: Any = None
        try:
            q_data = read_quarantine_document(quarantine_file)
        except ValueError as e:
            try:
                missing = not quarantine_file.is_file()
            except OSError:
                missing = False
            stale_q(
                "<file>" if missing else "<parse>",
                f"quarantine_file_missing: {quarantine_file}"
                if missing
                else f"malformed_quarantine_file: {e}",
            )
        if q_data is not None:
            entries, structural = parse_quarantine_document(q_data)
            for problem in structural:
                stale_q("<structure>", problem)
            for entry in entries:
                checked_quarantine_count += 1
                label = entry.token or entry.location
                for defect in entry.defects:
                    stale_q(label, defect)
                for warning in entry.metadata_warnings:
                    stale_q(label, warning)
                if entry.token is None:
                    continue
                expiry = entry.expiry_problem(ref_date)
                if expiry is not None:
                    stale_q(label, expiry)
                if entry.defects:
                    continue
                token = entry.token
                is_active = token in active_fps or any(
                    act == token or act.startswith(f"{token}:") for act in active_fps
                )
                if token in resolved_fps and not is_active:
                    stale_q(
                        token,
                        "already_resolved_in_ledger: fingerprint in resolved_history and "
                        "absent from active findings",
                    )
                # An unmarked token can only match `miri-difftest` findings.
                harness_covered = (quarantine_entry_harness(token) or "miri") in covered
                if run_evaluated and harness_covered:
                    if observed_keys is not None:
                        matched = token in observed_keys or token in (eval_fp_set or set())
                    else:
                        matched = any(
                            obs == token or obs.startswith(f"{token}:")
                            for obs in (eval_fp_set or set())
                        )
                    if not matched:
                        stale_q(
                            token,
                            "unobserved_quarantine_entry: 0 matching divergences in "
                            "evaluated run",
                        )

    stale_manifest: list[dict[str, Any]] = []
    checked_known_bug_count = 0

    def stale_m(entry: str, reason: str) -> None:
        stale_manifest.append({"source": str(manifest_path), "entry": entry, "reason": reason})

    if manifest_path is not None:
        m_data: Any = None
        try:
            manifest_exists = manifest_path.is_file()
        except OSError as e:
            stale_m("<parse>", f"malformed_manifest_toml: {e}")
            manifest_exists = False
        else:
            if not manifest_exists:
                stale_m("<file>", f"manifest_file_missing: {manifest_path}")
        if manifest_exists:
            try:
                m_data = tomllib.loads(manifest_path.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as e:
                stale_m("<parse>", f"malformed_manifest_toml: {e}")
        if isinstance(m_data, dict):
            tests = m_data.get("tests", [])
            if not isinstance(tests, list):
                stale_m("tests", "malformed_manifest_toml: key 'tests' must be an array of tables")
                tests = []
            for idx, test_entry in enumerate(tests):
                if not isinstance(test_entry, dict):
                    stale_m(f"tests[{idx}]", "malformed_manifest_toml: tests entry must be a table")
                    continue
                if "known_anneal_bug" not in test_entry:
                    continue
                checked_known_bug_count += 1
                test_name = test_entry.get("name")
                if not isinstance(test_name, str) or not test_name.strip():
                    stale_m(f"tests[{idx}]", "missing_test_name_on_known_anneal_bug")
                    continue
                clean_name = test_name.strip()
                if not _is_well_formed_quarantine_token(clean_name):
                    stale_m(clean_name, f"malformed_or_missing_fingerprint: {test_name!r}")
                bug = test_entry.get("known_anneal_bug")
                if not isinstance(bug, dict):
                    stale_m(clean_name, "malformed_known_anneal_bug: expected table")
                    continue
                obs_tag = bug.get("observed_anneal_tag")
                reason_text = bug.get("summary") or bug.get("reason")
                if not isinstance(obs_tag, str) or not obs_tag.strip():
                    stale_m(
                        clean_name,
                        "missing_known_anneal_bug_metadata: missing observed_anneal_tag",
                    )
                if not isinstance(reason_text, str) or not reason_text.strip():
                    stale_m(clean_name, "missing_known_anneal_bug_metadata: missing summary/reason")
                div_cls = bug.get("divergence_class")
                valid_div_cls: str | None = None
                if div_cls is not None:
                    if (
                        not isinstance(div_cls, str)
                        or div_cls.strip() not in VALID_DIVERGENCE_CLASSES
                    ):
                        stale_m(
                            clean_name,
                            f"malformed_known_anneal_bug: invalid divergence_class {div_cls!r}",
                        )
                    else:
                        valid_div_cls = div_cls.strip()
                raw_pol = bug.get("witness_polarity")
                valid_polarity: str | None = None
                if raw_pol is not None:
                    pol_token = f"{clean_name}:{valid_div_cls}" if valid_div_cls else clean_name
                    pol_prob = _quarantine_token_witness_polarity_defect(
                        pol_token, raw_pol, "malformed_known_anneal_bug"
                    )
                    if pol_prob is not None:
                        stale_m(clean_name, pol_prob)
                    elif isinstance(raw_pol, str):
                        valid_polarity = raw_pol.strip()
                expiry_prob = quarantine_expiry_problem(
                    bug.get("expires"), ref_date, required=False
                )
                if expiry_prob is not None:
                    stale_m(clean_name, expiry_prob)
                if isinstance(manifest_eval_results, dict) and clean_name in manifest_eval_results:
                    problem = _known_bug_eval_problem(
                        obs_tag,
                        manifest_eval_results[clean_name],
                        valid_div_cls,
                        valid_polarity,
                    )
                    if problem is not None:
                        stale_m(clean_name, problem)
                elif manifest_eval_exhaustive:
                    stale_m(
                        clean_name,
                        "stale_known_anneal_bug_unconfirmed: the identity run evaluated "
                        "every corpus test but reported no outcome for this one, so the "
                        "open bug was not reproduced",
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


def extract_manifest_eval_results_from_miri_summary(
    miri: dict[str, Any],
    manifest_path: Path | None = None,
) -> dict[str, Any] | None:
    """Extracts per-item evaluation verdicts and tags from a `miri-difftest` summary so
    `verify_no_stale_quarantine_or_known_bugs` can audit `manifest.toml`
    `known_anneal_bug` entries on `--miri-identity --check-stale-ratchet` runs.

    Only items the harness actually reported are returned (`item_outcomes`, plus the
    divergent identity `findings`): a manifest test that was not evaluated is never
    assumed to agree, because inferring `agree` for unreported names would fabricate
    `stale_known_anneal_bug_now_passes` verdicts. `manifest_path` is accepted for
    backward compatibility and is not consulted.
    """
    del manifest_path
    results: dict[str, Any] = {}
    item_outcomes = miri.get("item_outcomes")
    if isinstance(item_outcomes, dict):
        for fn_name, entry in item_outcomes.items():
            if isinstance(fn_name, str) and isinstance(entry, dict):
                results[fn_name] = dict(entry)

    if miri.get("mode") == "identity":
        findings = miri.get("findings")
        if isinstance(findings, list):
            for f in findings:
                if not isinstance(f, dict):
                    continue
                rec = {
                    "verdict": "diverge",
                    "divergence_class": str(f.get("divergence_class", "")),
                    "anneal_outcome": str(f.get("anneal_outcome", "")),
                    "anneal_lean_tag": str(f.get("anneal_lean_tag", "")),
                }
                raw_f_pol = f.get("witness_polarity")
                if isinstance(raw_f_pol, str) and raw_f_pol.strip():
                    rec["witness_polarity"] = raw_f_pol.strip()
                # Identity candidates are the unmutated corpus seeds: `fn_name` is the
                # manifest test name. Merge `divergence_class` and the repro-mapped
                # `anneal_outcome` into any existing `item_outcomes` entry so both
                # raw and repro-mapped tags can be checked.
                name_val = f.get("fn_name")
                if isinstance(name_val, str) and name_val.strip():
                    fn_key = name_val.strip()
                    if fn_key not in results:
                        results[fn_key] = rec
                    else:
                        if rec["divergence_class"] and not results[fn_key].get("divergence_class"):
                            results[fn_key]["divergence_class"] = rec["divergence_class"]
                        if rec.get("witness_polarity") and not results[fn_key].get("witness_polarity"):
                            results[fn_key]["witness_polarity"] = rec["witness_polarity"]
                        if rec["anneal_outcome"]:
                            results[fn_key]["repro_anneal_outcome"] = rec["anneal_outcome"]

    return results if results else None


def miri_summary_evaluates_every_manifest_test(miri: dict[str, Any]) -> bool:
    """True for an identity-mode `miri-difftest` summary carrying `item_outcomes`:
    the identity batch is the unmutated corpus, one candidate per manifest test, and
    `item_outcomes` covers every compiled one, so a manifest test it does not report
    was not evaluated (for example, it failed to compile). Seeded batches and legacy
    summaries without `item_outcomes` say nothing about unreported tests."""
    return miri.get("mode") == "identity" and isinstance(miri.get("item_outcomes"), dict)


def normalize_anneal_tag(raw_tag: str) -> str:
    clean = raw_tag.strip()
    while clean.startswith("(") and clean.endswith(")"):
        clean = clean[1:-1].strip()
    if clean.startswith("MirDiffTag.normalScalar"):
        return "MirDiffTag.normalScalar"
    return clean


# Identifiers that each `miri-difftest` mutator introduces into a candidate (see
# `crates/anneal-difftest/src/mutators_miri.rs`), used to attribute a divergence
# whose earliest fault line contains one of them to that mutator. No token may
# occur in the shared repro prefix (`MIRI_CORPUS_CRATE_HEADER` +
# `MIRI_CORPUS_MODULE_PREAMBLE`, which precedes every finding's `mutant_source`)
# or in the corpus seeds: the preamble's `write_bytes!` macro declares its own
# `__wb_dst`, so `RawPtrOffsetMutator`'s `write_bytes!` template is identified by
# `__wb_src` (which every faulting line of that template names) instead.
RAW_PTR_OFFSET_MUTATOR_TOKENS = (
    "__miri_ptr_",
    "__oob_pair",
    "__oob_base",
    "__oob_step",
    "__oob_",
    "__oob",
    "__neg_",
    "__ptr_pair",
    "__ptr_arr",
    "__base_ptr",
    "__far_ptr",
    "__field_b_ptr",
    "__back_ptr",
    "__null_p",
    "__unaligned_",
    "__u8_base",
    "__wb_src",
    "__cp_src",
    "__cp_dst",
    "__src_p",
    "__dst_p",
    "__ovl_",
)
TREE_BORROWS_MUTATOR_TOKENS = (
    "__miri_tb_",
    "__tb_",
    "__rr_",
    "__mv_",
    "__mp_",
    "__fn_",
    "__fns_",
    "__cp_x",
    "__cp_root",
    "__cp_res",
    "__cp_copied",
    "__rt_",
    "__ub_nc",
    "__ub_prot_",
)
BIT_VALIDITY_MUTATOR_TOKENS = (
    "__miri_valid_",
    "__valid_",
    "__bad_",
    "__uninit_",
    "__padded",
    "__pad_bytes",
    "__pad_idx",
    "__ptr_b",
    "__raw_u8",
    "__panic_arr",
    "__panic_idx",
    "__niche_",
    "__meters",
    "__single",
    "__overlay",
    "__nz_zero",
    "__nzm_zero",
    "__part_slot",
    "__part_read",
)
ARITHMETIC_CAST_MUTATOR_TOKENS = (
    "__miri_arith_",
    "__miri_wide",
    "__intr_",
    "__sat_",
    "__wrap_",
    "__cmp_",
    "__ediv_",
    "__layout_pair",
    "__sz",
    "__al",
    "__ovf_",
    "__udf_",
    "__div_",
    "__shl_",
    "__ub_",
)
PLACE_PROJECTION_MUTATOR_TOKENS = (
    "__miri_proj_",
    "__proj_",
    "__dangling_",
    "__dead_",
    "__oob_arr",
    "__oob_idx",
)

ALL_MIRI_MUTATOR_TOKENS = (
    *RAW_PTR_OFFSET_MUTATOR_TOKENS,
    *TREE_BORROWS_MUTATOR_TOKENS,
    *BIT_VALIDITY_MUTATOR_TOKENS,
    *ARITHMETIC_CAST_MUTATOR_TOKENS,
    *PLACE_PROJECTION_MUTATOR_TOKENS,
)

def _is_src_lib_or_repro_file(file_str: str) -> bool:
    """Returns `True` iff `file_str` names the candidate source (`src/lib.rs` or
    `repro.rs`) rather than a standard-library panic macro or foreign file."""
    norm = _normalize_file_for_match(file_str)
    if not norm or _is_std_panic_macro_file(norm):
        return False
    slashed = f"/{norm.lstrip('/')}"
    if any(seg in slashed for seg in ("/library/core/", "/library/std/", "/library/alloc/")):
        return False
    return _source_files_match(norm, "src/lib.rs") or _source_files_match(norm, "repro.rs")


def _extract_src_lib_fault_line_nos(finding: dict[str, Any], num_lines: int) -> list[int]:
    """Returns 1-based fault line numbers in `mutant_source` (`1..=num_lines`) from
    `("miri_pos", "anneal_span")` (falling back to `@<loc>` on `miri_outcome` /
    `anneal_outcome`), ignoring standard-library panic-macro spans and foreign files."""
    line_nos: list[int] = []
    for loc_key, outcome_key in (
        ("miri_pos", "miri_outcome"),
        ("anneal_span", "anneal_outcome"),
    ):
        loc = finding.get(loc_key)
        if not isinstance(loc, str) or ":" not in loc:
            out_tag = finding.get(outcome_key)
            if isinstance(out_tag, str) and "@" in out_tag:
                loc = out_tag.partition("@")[2]
            else:
                continue
        span = _parse_src_span(loc)
        if span is not None:
            file_str, line_no = span[0], span[1]
        else:
            pos = _parse_src_pos(loc)
            if pos is not None:
                file_str, line_no = pos[0], pos[1]
            else:
                parts = loc.split(":")
                if (
                    len(parts) >= 2
                    and parts[1].strip().isascii()
                    and parts[1].strip().isdigit()
                ):
                    file_str, line_no = parts[0].strip(), int(parts[1].strip())
                else:
                    continue
        if not _is_src_lib_or_repro_file(file_str):
            continue
        if 1 <= line_no <= num_lines and line_no not in line_nos:
            line_nos.append(line_no)
    return line_nos


def _candidate_fn_start_line_no(src_lines: list[str], finding: dict[str, Any]) -> int:
    """Returns the 1-based start line of the candidate `fn` in `src_lines` (after
    any `MIRI_CORPUS_MODULE_PREAMBLE` helpers), or `1` if none is found."""
    fn_name = finding.get("fn_name")
    if isinstance(fn_name, str) and fn_name.strip():
        target = f"fn {fn_name.strip()}("
        for idx, line in enumerate(src_lines):
            if target in line:
                return idx + 1
    last_cand_line = 1
    for idx, line in enumerate(src_lines):
        stripped = line.lstrip()
        for prefix in ("pub fn ", "pub unsafe fn ", "fn "):
            if stripped.startswith(prefix):
                rest = stripped[len(prefix) :].lstrip()
                ident = rest.split("(", 1)[0].strip()
                if _is_rust_ident_segment(ident) and not ident.startswith("helper_"):
                    last_cand_line = idx + 1
                break
    return last_cand_line


def _resolve_preamble_fault_line_no(
    src_lines: list[str], line_no: int, cand_fn_start_line: int
) -> int:
    """Maps a fault line inside a `MIRI_CORPUS_MODULE_PREAMBLE` helper or macro
    (`line_no < cand_fn_start_line`) to its call site inside the candidate function
    when the candidate calls that helper or macro."""
    if line_no >= cand_fn_start_line:
        return line_no
    call_targets: tuple[str, ...] = ()
    always_faults = False
    for idx in range(line_no - 1, -1, -1):
        stripped = src_lines[idx].lstrip()
        if stripped.startswith("macro_rules! write_bytes"):
            call_targets = ("write_bytes!(",)
            break
        if stripped.startswith("pub fn "):
            rest = stripped[len("pub fn ") :].lstrip()
            ident = rest.split("(", 1)[0].strip()
            if ident in (
                "helper_unwind_leaf",
                "helper_unwind_mid",
                "helper_unwind_guarded",
            ):
                call_targets = (
                    "helper_unwind_leaf(",
                    "helper_unwind_mid(",
                    "helper_unwind_guarded(",
                )
                always_faults = True
            elif _is_rust_ident_segment(ident):
                call_targets = (f"{ident}(",)
                always_faults = ident == "helper_frozen_reborrow_write_in_callee"
            break
    if not call_targets:
        return line_no
    first_call_line: int | None = None
    for cand_idx in range(cand_fn_start_line - 1, len(src_lines)):
        text = src_lines[cand_idx]
        if any(t in text for t in call_targets):
            if always_faults:
                return cand_idx + 1
            if first_call_line is None:
                first_call_line = cand_idx + 1
            if any(tok in text for tok in ALL_MIRI_MUTATOR_TOKENS):
                return cand_idx + 1
    return first_call_line if first_call_line is not None else line_no


def _mutator_for_fault_line(fault_text: str) -> str | None:
    """Returns the mutator that owns a token on `fault_text`, or `None`."""
    if not fault_text:
        return None
    for probe_prefix, mutator_name in (
        ("__miri_ptr_", "RawPtrOffsetMutator"),
        ("__miri_tb_", "TreeBorrowsRetagInterleaver"),
        ("__miri_valid_", "BitValidityTransmuteMutator"),
        ("__miri_arith_", "ArithmeticCastMutator"),
        ("__miri_proj_", "PlaceProjectionWrapper"),
    ):
        if probe_prefix in fault_text:
            return mutator_name
    # Check `PlaceProjectionWrapper` (`__oob_arr` / `__oob_idx`) before
    # `RawPtrOffsetMutator`'s `__oob_` prefix, and `TreeBorrowsRetagInterleaver`
    # (`__ub_nc` / `__ub_prot_`) before `ArithmeticCastMutator`'s `__ub_` prefix.
    for mutator_name, tokens in (
        ("PlaceProjectionWrapper", PLACE_PROJECTION_MUTATOR_TOKENS),
        ("RawPtrOffsetMutator", RAW_PTR_OFFSET_MUTATOR_TOKENS),
        ("TreeBorrowsRetagInterleaver", TREE_BORROWS_MUTATOR_TOKENS),
        ("BitValidityTransmuteMutator", BIT_VALIDITY_MUTATOR_TOKENS),
        ("ArithmeticCastMutator", ARITHMETIC_CAST_MUTATOR_TOKENS),
    ):
        if any(tok in fault_text for tok in tokens):
            return mutator_name
    return None


def extract_earliest_fault_line_no(finding: dict[str, Any]) -> int | None:
    """Returns the 1-based line number of the earliest fault (`miri_pos` or `anneal_span`)."""
    src = finding.get("mutant_source")
    if not isinstance(src, str) or not src:
        return None
    src_lines = src.splitlines()
    line_nos = _extract_src_lib_fault_line_nos(finding, len(src_lines))
    return min(line_nos) if line_nos else None


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
    cand_start = _candidate_fn_start_line_no(src_lines, finding)
    resolved = _resolve_preamble_fault_line_no(src_lines, earliest_line_no, cand_start)
    return src_lines[resolved - 1]


def infer_finding_cause(
    finding: dict[str, Any], known_corpus_bug_seeds: set[str]
) -> str:
    """Identifies the seed or mutator responsible for a divergence finding.

    An unmutated candidate (no `applied_mutators`) is always its seed's: no
    mutator introduced any of its code, whatever tokens its fault line (for example
    a fault inside the shared preamble's `write_bytes!` macro) happens to contain.
    """
    seed_name = str(finding["seed_name"])
    mutators = finding.get("applied_mutators")
    first_mutator = (
        next((m.strip() for m in mutators if isinstance(m, str) and m.strip()), "")
        if isinstance(mutators, list)
        else ""
    )
    if not first_mutator:
        return seed_name
    fault_text = extract_fault_line_text(finding)
    if fault_text:
        hit = _mutator_for_fault_line(fault_text)
        if hit is not None:
            return hit

        # If the earliest fault occurred inside the unmutated seed prefix of the
        # candidate function before an appended mutator tail (which only introduces
        # mutator tokens on later lines), attribute the fault to `seed_name`.
        earliest_line_no = extract_earliest_fault_line_no(finding)
        src = finding.get("mutant_source")
        if earliest_line_no is not None and isinstance(src, str):
            src_lines = src.splitlines()
            cand_start = _candidate_fn_start_line_no(src_lines, finding)
            resolved_earliest = _resolve_preamble_fault_line_no(
                src_lines, earliest_line_no, cand_start
            )
            if resolved_earliest >= cand_start:
                prefix_text = "\n".join(src_lines[cand_start - 1 : resolved_earliest])
                suffix_text = "\n".join(src_lines[resolved_earliest:])
                if not any(tok in prefix_text for tok in ALL_MIRI_MUTATOR_TOKENS) and any(
                    tok in suffix_text for tok in ALL_MIRI_MUTATOR_TOKENS
                ):
                    return seed_name
            for raw_ln in _extract_src_lib_fault_line_nos(finding, len(src_lines)):
                resolved_ln = _resolve_preamble_fault_line_no(src_lines, raw_ln, cand_start)
                other_hit = _mutator_for_fault_line(src_lines[resolved_ln - 1])
                if other_hit is not None:
                    return other_hit

    if seed_name in known_corpus_bug_seeds or not first_mutator:
        return seed_name
    return first_mutator


def quarantine_match_keys_for_miri_finding(
    finding: dict[str, Any], known_corpus_bug_seeds: set[str]
) -> tuple[str, set[str]]:
    """Returns `(fingerprint, keys)` where `keys` is every quarantine token that
    quarantines this `miri-difftest` finding in `deduplicate_and_quarantine_findings`."""
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
    quarantines this `itree-difftest` finding in
    `deduplicate_and_quarantine_itree_findings`."""
    fn_name = str(finding["fn_name"])
    seed_name = f"itree_seed_{finding.get('seed_index', 0)}"
    mutators = finding.get("applied_mutators")
    first_mutator = (
        next((m.strip() for m in mutators if isinstance(m, str) and m.strip()), "")
        if isinstance(mutators, list)
        else ""
    )
    cause = first_mutator or seed_name
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
            raw_polarity = f.get("witness_polarity")
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
                # `validate_performed_miri_summary` pins a reported polarity to the
                # class's; findings handed in without one (tests, legacy callers)
                # take the class's polarity, which every finding of `fp` shares.
                witness_polarity=(
                    DIVERGENCE_CLASS_WITNESS_POLARITY[div_class]
                    if div_class in DIVERGENCE_CLASS_WITNESS_POLARITY
                    else (
                        raw_polarity
                        if isinstance(raw_polarity, str) and raw_polarity in VALID_WITNESS_POLARITIES
                        else None
                    )
                ),
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
        first_mutator = (
            next((m.strip() for m in mutators if isinstance(m, str) and m.strip()), "")
            if isinstance(mutators, list)
            else ""
        )
        cause = first_mutator or seed_name
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
        if miri_outcome.startswith(MIRI_ERROR_TAG_PREFIXES)
        else ("pass" if m_kind.startswith("pass:") else m_kind),
    )
    a_kind = anneal_outcome.partition("@")[0]
    if anneal_outcome.startswith(ANNEAL_ERROR_TAG_PREFIXES):
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
    # The probe's polarity comes from the exact Rust-tag classifier, as
    # `miri-difftest` derives it, and is the only non-agreement in the summary.
    probe_polarity = classify_witness_polarity_from_tags(miri_outcome, anneal_outcome)
    polarity_counts = empty_witness_polarity_counts()
    if probe_polarity is not None:
        polarity_counts[probe_polarity] = 1
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
                "witness_polarity": DIVERGENCE_CLASS_WITNESS_POLARITY[detail],
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
        "witness_polarity_counts": polarity_counts,
        "unmodeled_external_calls": {},
        "mutator_applications": {"ArithmeticCastMutator": total},
        "findings": findings,
        "elapsed_ms": 10.0 * DEFAULT_MIN_ORACLE_ELAPSED_MS,
    }
    item_outcomes: dict[str, Any] = {
        f"background_{i}": {
            "verdict": "agree",
            "miri_outcome": "pass:scalar:1:4",
            "anneal_outcome": "pass:scalar:1:4",
            "anneal_lean_tag": "(MirDiffTag.normalScalar 1 4)",
        }
        for i in range(background_agreeing)
    }
    item_outcomes[f"probe_{probe_id}"] = {
        "verdict": verdict,
        "miri_outcome": miri_outcome,
        "anneal_outcome": anneal_outcome,
        "anneal_lean_tag": anneal_lean_tag,
    }
    summary["item_outcomes"] = item_outcomes
    if diagnostics:
        summary["diagnostics"] = diagnostics
    return summary


def campaign_verdict_for_miri_summary(summary: dict[str, Any]) -> dict[str, Any]:
    """Runs a performed `miri-difftest` summary through the campaign's verdict pipeline
    (`validate_performed_miri_summary`, `evaluate_miri_red_flags` including the
    `error` vs. `unsupported` boundary and the witness-polarity accounting, and
    `deduplicate_and_quarantine_findings`).

    Returns `{"exit_code", "kill_class", "detail", "witness_polarity"}`:
    `EXIT_HARNESS_FAILED` with `"harness_error"` and `harness_or_extraction_error`,
    `EXIT_DIVERGENCE_DETECTED` with the first unquarantined fingerprint's divergence
    class and witness polarity, or `EXIT_SUCCESS` with `"agree"` and no polarity.
    """
    valid, reason = validate_performed_miri_summary(summary)
    if not valid:
        return {
            "exit_code": EXIT_HARNESS_FAILED,
            "kill_class": HARNESS_ERROR_KILL_CLASS,
            "detail": reason,
            "witness_polarity": WITNESS_POLARITY_HARNESS,
        }
    rf = evaluate_miri_red_flags(
        summary, 0x5EED0001, {}, DEFAULT_MIN_ORACLE_ELAPSED_MS, DEFAULT_MAX_ORACLE_ERRORS
    )
    if not rf.passed:
        return {
            "exit_code": EXIT_HARNESS_FAILED,
            "kill_class": HARNESS_ERROR_KILL_CLASS,
            "detail": "; ".join(rf.failure_reasons),
            "witness_polarity": WITNESS_POLARITY_HARNESS,
        }
    _, unquarantined, _ = deduplicate_and_quarantine_findings(summary["findings"], set(), set())
    if unquarantined:
        return {
            "exit_code": EXIT_DIVERGENCE_DETECTED,
            "kill_class": unquarantined[0].divergence_class,
            "detail": unquarantined[0].fingerprint,
            "witness_polarity": unquarantined[0].witness_polarity,
        }
    return {
        "exit_code": EXIT_SUCCESS,
        "kill_class": "agree",
        "detail": "no divergence",
        "witness_polarity": None,
    }


def campaign_exit_for_miri_summary(summary: dict[str, Any]) -> tuple[int, str, str]:
    """`(exit_code, kill_class, detail)` of `campaign_verdict_for_miri_summary`:
    `EXIT_HARNESS_FAILED` with `"harness_error"`, `EXIT_DIVERGENCE_DETECTED` with the
    unquarantined divergence class, or `EXIT_SUCCESS` with `"agree"`."""
    verdict = campaign_verdict_for_miri_summary(summary)
    return verdict["exit_code"], verdict["kill_class"], verdict["detail"]


# Each probe below is staged and run through the live, *unmutated* Miri + Anneal
# pipeline by `semantic_mutant_probes_agree_live_and_known_provenance_gaps_stay_pinned`
# (`crates/anneal-difftest/src/miri_eval.rs`), which embeds byte-identical probe
# sources (`SEMANTIC_MUTANT_PROBES`, keyed by probe id: the mutant id, or a
# variant's own `probe["id"]`) and pins, relative to each probe's first line, the
# exact Miri outcome (`reference_miri_outcome`) and Anneal outcome and Lean tag
# (`baseline_anneal_outcome`, `baseline_anneal_lean_tag`) that the simulation below
# replays; `test_run_diff_test_campaign.py` checks that both tables stay identical.
# So every simulated baseline is the real engine's outcome, re-measured on every
# `cargo test -p anneal-difftest`. Partial-pointer-byte provenance variants are not
# probes: the live engine already diverges on them (kernel-confirmed), so a "check
# omitted" mutant would be equivalent to the current engine there and could never be
# killed; the same Rust test pins them as known engine gaps instead (as it pins the
# sub-place `&raw mut x.0` form of `move_triggers_tb_write`, a live
# `false_positive_ub`).
#
# A variant that needs a different program than its mutant's probe carries its own
# `probe` (`id`, `probe_rust_source`, `reference_miri_outcome`,
# `baseline_anneal_outcome`, `baseline_anneal_lean_tag`), whose baseline must pass
# the campaign pipeline too: `protector_release_order` kills both soundness
# directions, so it needs one probe on which Miri returns normally and one on which
# Miri faults. Every variant declares the `expected_kill_class` and the
# `expected_witness_polarity` with which it must be killed; a kill with any other
# class or polarity is a survivor.
SEEDED_SEMANTIC_MUTANTS: tuple[dict[str, Any], ...] = (
    {
        "id": "bool_valid_range",
        "name": "bool_valid_range",
        "bug_class": "scalar_validity_bool_range",
        "target_component": "Trusted.Rustc.V2026_06_01.MirSemantics.BitValidity",
        "description": "Omit bool validRange [0, 1] check on typed scalar load of 2u8 as bool",
        "expected_kill_classes": ("missed_ub",),
        "expected_witness_polarities": (WITNESS_POLARITY_UNSOUND,),
        "reference_miri_outcome": "ub@src/lib.rs:5:5",
        "baseline_anneal_outcome": "ub@src/lib.rs:5:5: 5:6",
        "baseline_anneal_lean_tag": "MirDiffTag.ub",
        "mutant_variants": (
            {
                "label": "validity_check_omitted",
                "anneal_outcome": "pass:scalar:2:4",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 2 4)",
                "expected_kill_class": "missed_ub",
                "expected_witness_polarity": WITNESS_POLARITY_UNSOUND,
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
        "description": (
            "Omit allocation liveness / StorageDead deallocation check on raw pointer dereference"
        ),
        "expected_kill_classes": ("missed_ub",),
        "expected_witness_polarities": (WITNESS_POLARITY_UNSOUND,),
        "reference_miri_outcome": "ub@src/lib.rs:6:14",
        "baseline_anneal_outcome": "ub@src/lib.rs:6:14: 6:23",
        "baseline_anneal_lean_tag": "MirDiffTag.ub",
        "mutant_variants": (
            {
                "label": "liveness_check_omitted",
                "anneal_outcome": "pass:scalar:42:4",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 42 4)",
                "expected_kill_class": "missed_ub",
                "expected_witness_polarity": WITNESS_POLARITY_UNSOUND,
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
        "bug_class": "integer_bytes_strip_pointer_provenance",
        "target_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Memory",
        "description": (
            "Accept a pointer loaded from integer bytes (all 8 bytes of a stored pointer "
            "overwritten with its own address through a `*mut usize` alias) as if it kept "
            "the provenance of the live allocation at that address"
        ),
        "expected_kill_classes": ("missed_ub",),
        "expected_witness_polarities": (WITNESS_POLARITY_UNSOUND,),
        "reference_miri_outcome": "ub@src/lib.rs:8:9",
        "baseline_anneal_outcome": "ub@src/lib.rs:8:9: 8:11",
        "baseline_anneal_lean_tag": "MirDiffTag.ub",
        "mutant_variants": (
            {
                # `x`'s live address survives in the integer bytes: a semantics that
                # accepts the provenance-free pointer reads `x` instead of trapping.
                "label": "integer_bytes_keep_provenance",
                "anneal_outcome": "pass:scalar:7:4",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 7 4)",
                "expected_kill_class": "missed_ub",
                "expected_witness_polarity": WITNESS_POLARITY_UNSOUND,
            },
        ),
        "probe_rust_source": (
            "pub fn probe_provenance_frag() -> u32 {\n"
            "    let x: u32 = 7u32;\n"
            "    let mut p: *const u32 = &raw const x;\n"
            "    let addr: usize = p as usize;\n"
            "    let slot: *mut usize = (&raw mut p) as *mut usize;\n"
            "    unsafe {\n"
            "        *slot = addr;\n"
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
        "expected_kill_classes": ("panic_vs_return",),
        "expected_witness_polarities": (WITNESS_POLARITY_UNSOUND,),
        "reference_miri_outcome": "panic@src/lib.rs:4:5",
        "baseline_anneal_outcome": "panic@src/lib.rs:4:5: 4:14",
        "baseline_anneal_lean_tag": "MirDiffTag.panic",
        "mutant_variants": (
            {
                "label": "zero_divisor_guard_omitted",
                "anneal_outcome": "pass:scalar:0:4",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 0 4)",
                "expected_kill_class": "panic_vs_return",
                "expected_witness_polarity": WITNESS_POLARITY_UNSOUND,
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
        "description": (
            "Omit rhs.toNat < w guard on 64/128-bit shift with rhs >= 2^32 "
            "(GMP lean_nat_shiftl abort)"
        ),
        "expected_kill_classes": ("missed_ub", HARNESS_ERROR_KILL_CLASS),
        "expected_witness_polarities": (WITNESS_POLARITY_UNSOUND, WITNESS_POLARITY_HARNESS),
        "reference_miri_outcome": "ub@src/lib.rs:4:14",
        "baseline_anneal_outcome": "ub@src/lib.rs:4:14: 4:37",
        "baseline_anneal_lean_tag": "MirDiffTag.ub",
        "mutant_variants": (
            {
                # Without the guard, `lean_nat_shiftl` aborts the Lean probe process.
                "label": "guard_omitted_lean_abort",
                "anneal_outcome": (
                    "capture_error:INTERNAL PANIC: Nat.shiftl exponent is too big (SIGABRT)"
                ),
                "anneal_lean_tag": "none",
                "expected_kill_class": HARNESS_ERROR_KILL_CLASS,
                "expected_witness_polarity": WITNESS_POLARITY_HARNESS,
                "expected_detail_substring": "oracle_errors_exceeded",
            },
            {
                # The same abort misreported as an unmodeled construct must still fail
                # (Miri faulted, so this `unsupported` is a harness error, not a
                # conservative abstraction).
                "label": "guard_omitted_abort_masked_as_unsupported",
                "anneal_outcome": "unsupported@src/lib.rs:4:14: 4:37",
                "anneal_lean_tag": "MirDiffTag.unsupported",
                "expected_kill_class": HARNESS_ERROR_KILL_CLASS,
                "expected_witness_polarity": WITNESS_POLARITY_HARNESS,
                "expected_detail_substring": "error_masked_as_unsupported",
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
                "expected_kill_class": "missed_ub",
                "expected_witness_polarity": WITNESS_POLARITY_UNSOUND,
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
    {
        # `let moved: NonCopyU32 = x;` lowers to `_6 = move _1` (`Rvalue::Use(
        # Operand::Move)`, since `NonCopyU32` is not `Copy`). Miri evaluates the move
        # as a read, a foreign read of `r` that leaves the `Reserved` reborrow
        # usable, so the later write through `r` is valid and the probe returns
        # `32 + 10`. A semantics that also emits a foreign `.Write` on the moved
        # place (`tb_write_on_move_breaks_borrow_tree_equiv`) disables `r` and faults
        # at that write.
        "id": "move_triggers_tb_write",
        "name": "move_triggers_tb_write",
        "bug_class": "operand_move_emits_tree_borrows_write",
        "target_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Places",
        "description": (
            "Emit a Tree Borrows `.Write` foreign access on `Rvalue::Use(Operand::Move)` of a "
            "non-`Copy` wrapper (`let moved: NonCopyU32 = x;`), disabling the `Reserved` "
            "`&mut NonCopyU32` child `r` reborrowed from `&raw mut x`, so the valid child "
            "write `*r = NonCopyU32(32u32)` faults with spurious Tree Borrows UB"
        ),
        "expected_kill_classes": ("false_positive_ub",),
        "expected_witness_polarities": (WITNESS_POLARITY_CONSERVATIVE,),
        "reference_miri_outcome": "pass:scalar:42:4",
        "baseline_anneal_outcome": "pass:scalar:42:4",
        "baseline_anneal_lean_tag": "(MirDiffTag.normalScalar 42 4)",
        "mutant_variants": (
            {
                # The disabled `r` faults at `*r = NonCopyU32(32u32)` (line 6).
                "label": "move_emits_foreign_write",
                "anneal_outcome": "ub@src/lib.rs:6:5: 6:27",
                "anneal_lean_tag": "MirDiffTag.ub",
                "expected_kill_class": "false_positive_ub",
                "expected_witness_polarity": WITNESS_POLARITY_CONSERVATIVE,
            },
        ),
        "probe_rust_source": (
            "pub fn probe_move_triggers_tb_write() -> u32 {\n"
            "    let mut x: NonCopyU32 = NonCopyU32(10u32);\n"
            "    let root: *mut NonCopyU32 = &raw mut x;\n"
            "    let r: &mut NonCopyU32 = unsafe { &mut *root };\n"
            "    let moved: NonCopyU32 = x;\n"
            "    *r = NonCopyU32(32u32);\n"
            "    (*r).0 + moved.0\n"
            "}\n"
        ),
    },
    {
        # Each probe calls the inline intrinsic (`exact_div::<u32>`,
        # `exact_div::<i8>`, `ctlz_nonzero::<u32>` call terminators) on operands that
        # violate exactly one precondition; the live engine reports UB at the call,
        # and a semantics without that guard returns the unguarded result.
        "id": "exact_div_rem_omitted",
        "name": "exact_div_rem_omitted",
        "bug_class": "inline_intrinsic_ub_guard_omitted",
        "target_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Terminators",
        "description": (
            "Omit the inline intrinsic UB guards: the `lhs % rhs == 0` remainder guard of "
            "`exact_div(7u32, 2u32)`, the signed `INT_MIN / -1` overflow guard of "
            "`exact_div(i8::MIN, -1i8)`, and the zero guard of `ctlz_nonzero(0u32)`"
        ),
        "expected_kill_classes": ("missed_ub",),
        "expected_witness_polarities": (WITNESS_POLARITY_UNSOUND,),
        "reference_miri_outcome": "ub@src/lib.rs:4:14",
        "baseline_anneal_outcome": "ub@src/lib.rs:4:14: 4:33",
        "baseline_anneal_lean_tag": "MirDiffTag.ub",
        "mutant_variants": (
            {
                # Truncating `7 / 2`.
                "label": "remainder_guard_omitted",
                "anneal_outcome": "pass:scalar:3:4",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 3 4)",
                "expected_kill_class": "missed_ub",
                "expected_witness_polarity": WITNESS_POLARITY_UNSOUND,
            },
            {
                # `i8::MIN % -1 == 0` passes the remainder guard; without the overflow
                # guard `-128 / -1` wraps to `i8::MIN` (bits `0x80`).
                "label": "signed_overflow_guard_omitted",
                "probe": {
                    "id": "exact_div_signed_overflow",
                    "reference_miri_outcome": "ub@src/lib.rs:4:14",
                    "baseline_anneal_outcome": "ub@src/lib.rs:4:14: 4:33",
                    "baseline_anneal_lean_tag": "MirDiffTag.ub",
                    "probe_rust_source": (
                        "pub fn probe_exact_div_signed_overflow() -> i8 {\n"
                        "    let lhs: i8 = i8::MIN;\n"
                        "    let rhs: i8 = -1i8;\n"
                        "    unsafe { exact_div(lhs, rhs) }\n"
                        "}\n"
                    ),
                },
                "anneal_outcome": "pass:scalar:128:1",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 128 1)",
                "expected_kill_class": "missed_ub",
                "expected_witness_polarity": WITNESS_POLARITY_UNSOUND,
            },
            {
                # `ctlz(0u32) == 32`.
                "label": "nonzero_guard_omitted",
                "probe": {
                    "id": "ctlz_nonzero_zero",
                    "reference_miri_outcome": "ub@src/lib.rs:3:14",
                    "baseline_anneal_outcome": "ub@src/lib.rs:3:14: 3:32",
                    "baseline_anneal_lean_tag": "MirDiffTag.ub",
                    "probe_rust_source": (
                        "pub fn probe_ctlz_nonzero_zero() -> u32 {\n"
                        "    let zero: u32 = 0u32;\n"
                        "    unsafe { ctlz_nonzero(zero) }\n"
                        "}\n"
                    ),
                },
                "anneal_outcome": "pass:scalar:32:4",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 32 4)",
                "expected_kill_class": "missed_ub",
                "expected_witness_polarity": WITNESS_POLARITY_UNSOUND,
            },
        ),
        "probe_rust_source": (
            "pub fn probe_exact_div_rem_omitted() -> u32 {\n"
            "    let lhs: u32 = 7u32;\n"
            "    let rhs: u32 = 2u32;\n"
            "    unsafe { exact_div(lhs, rhs) }\n"
            "}\n"
        ),
    },
    {
        # Two-stage `FnEntry` protector handling in both soundness directions. The
        # probe passes a reborrow of the raw-derived `r0` to `helper_reborrow_mid`,
        # whose `&mut u32` argument Miri retags and protects for the call; the
        # protector is released on return, so the caller's foreign write through
        # `r0` afterwards is valid (Miri returns `20 + 22`). The variant probe passes
        # `&x` as a protected `&u32` argument while the callee writes `x` through an
        # aliasing raw pointer: Miri reports the protector violation at that write
        # (the protected tag would become `Disabled`; with `&x` an unprotected local
        # the same write passes, see `miri_eval.rs`). The live engine agrees at the
        # same write, through its sibling-root retag freeze of `raw` (the capture
        # emits no `Retag(FnEntry)`; `tests/miri-diff/README.md`, Category 9 engine
        # gaps), so the variant models the missed fault of a semantics without that
        # conflict check.
        "id": "protector_release_order",
        "name": "protector_release_order",
        "bug_class": "fn_entry_protector_release_order_and_conflict",
        "target_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Terminators",
        "description": (
            "Release `frame.protectedTags` after `cleanupStackFrame` / `StorageDead` on "
            "return, so the caller's valid post-return write through the protected "
            "reborrow's parent faults (`false_positive_ub`), or omit the `FnEntry` "
            "protector conflict check on a write through a conflicting raw alias during "
            "the protected call (`missed_ub`)"
        ),
        "expected_kill_classes": ("false_positive_ub", "missed_ub"),
        "expected_witness_polarities": (WITNESS_POLARITY_CONSERVATIVE, WITNESS_POLARITY_UNSOUND),
        "reference_miri_outcome": "pass:scalar:42:4",
        "baseline_anneal_outcome": "pass:scalar:42:4",
        "baseline_anneal_lean_tag": "(MirDiffTag.normalScalar 42 4)",
        "mutant_variants": (
            {
                # A protector still active after the return makes the caller's foreign
                # write `*r0 = 20u32` (line 6) fault.
                "label": "release_after_frame_cleanup",
                "anneal_outcome": "ub@src/lib.rs:6:5: 6:16",
                "anneal_lean_tag": "MirDiffTag.ub",
                "expected_kill_class": "false_positive_ub",
                "expected_witness_polarity": WITNESS_POLARITY_CONSERVATIVE,
            },
            {
                # Without the conflict check the write lands: `3 + 8`.
                "label": "protector_conflict_omitted",
                "probe": {
                    "id": "protector_conflict",
                    "reference_miri_outcome": "ub@src/lib.rs:11:9",
                    "baseline_anneal_outcome": "ub@src/lib.rs:11:9: 11:22",
                    "baseline_anneal_lean_tag": "MirDiffTag.ub",
                    "probe_rust_source": (
                        "pub fn probe_protector_conflict() -> u32 {\n"
                        "    let mut x: u32 = 10u32;\n"
                        "    let raw: *mut u32 = &raw mut x;\n"
                        "    let v: u32 = probe_helper_protected_alias_write(&x, raw);\n"
                        "    v + unsafe { *raw }\n"
                        "}\n"
                        "\n"
                        "#[inline(never)]\n"
                        "fn probe_helper_protected_alias_write(_r: &u32, alias: *mut u32)"
                        " -> u32 {\n"
                        "    unsafe {\n"
                        "        *alias = 8u32;\n"
                        "    }\n"
                        "    3u32\n"
                        "}\n"
                    ),
                },
                "anneal_outcome": "pass:scalar:11:4",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 11 4)",
                "expected_kill_class": "missed_ub",
                "expected_witness_polarity": WITNESS_POLARITY_UNSOUND,
            },
        ),
        "probe_rust_source": (
            "pub fn probe_protector_release_order() -> u32 {\n"
            "    let mut x: u32 = 10u32;\n"
            "    let raw: *mut u32 = &raw mut x;\n"
            "    let r0: &mut u32 = unsafe { &mut *raw };\n"
            "    let delta: u32 = helper_reborrow_mid(r0, 7u32);\n"
            "    *r0 = 20u32;\n"
            "    unsafe {\n"
            "        *raw = *r0 + delta;\n"
            "        *raw\n"
            "    }\n"
            "}\n"
        ),
    },
)

# Keys of a probe: a mutant's own probe, or a variant's `probe` override.
SEMANTIC_MUTANT_PROBE_KEYS: tuple[str, ...] = (
    "probe_rust_source",
    "reference_miri_outcome",
    "baseline_anneal_outcome",
    "baseline_anneal_lean_tag",
)


def semantic_mutant_variant_probe(
    mutant: dict[str, Any], variant: dict[str, Any]
) -> dict[str, Any]:
    """The probe a variant runs on: its own `probe` (which must carry an `id` and
    every `SEMANTIC_MUTANT_PROBE_KEYS` entry as non-empty strings), or else its
    mutant's probe (whose id is the mutant id). Raises on a malformed probe or
    override, which the self-check counts as a surviving mutant."""
    override = variant.get("probe")
    if override is None:
        source_map = mutant
        raw_id = mutant.get("id")
    else:
        if not isinstance(override, dict):
            raise ValueError(f"variant {variant.get('label')!r} has a non-object probe")
        source_map = override
        raw_id = override.get("id")
    if not isinstance(raw_id, str) or not raw_id.strip():
        raise ValueError(f"probe has missing or invalid id {raw_id!r}")
    probe: dict[str, Any] = {"id": raw_id.strip()}
    for k in SEMANTIC_MUTANT_PROBE_KEYS:
        val = source_map[k]
        if not isinstance(val, str) or not val.strip():
            raise ValueError(f"probe {probe['id']!r} has missing or empty {k!r}")
        probe[k] = val
    if "fn " not in probe["probe_rust_source"]:
        raise ValueError(
            f"probe {probe['id']!r} probe_rust_source lacks a function definition"
        )
    return probe


def semantic_mutant_probes(
    mutants: tuple[dict[str, Any], ...] | list[dict[str, Any]] = SEEDED_SEMANTIC_MUTANTS,
) -> list[dict[str, Any]]:
    """Every distinct probe of `mutants`, in table order: each mutant's own probe,
    followed by its variants' `probe` overrides. Raises when two probes share an
    `id` but differ, since a probe id names exactly one live-pinned program."""
    probes: list[dict[str, Any]] = []
    by_id: dict[str, dict[str, Any]] = {}
    for mutant in mutants:
        candidates = [semantic_mutant_variant_probe(mutant, {})]
        candidates.extend(
            semantic_mutant_variant_probe(mutant, v)
            for v in mutant.get("mutant_variants", ())
            if v.get("probe") is not None
        )
        for probe in candidates:
            prior = by_id.get(probe["id"])
            if prior is None:
                by_id[probe["id"]] = probe
                probes.append(probe)
            elif prior != probe:
                raise ValueError(
                    f"conflicting definitions of semantic-mutant probe {probe['id']!r}"
                )
    return probes


def _simulate_probe_baseline(probe: dict[str, Any], repro_path: Path) -> dict[str, Any]:
    """Runs a probe's *unmutated* outcome through the campaign pipeline: it is clean
    only when the pipeline exits `EXIT_SUCCESS`, the outcome tags classify as
    `agree`, and they carry no witness polarity."""
    probe_id = str(probe["id"])
    miri_outcome = str(probe["reference_miri_outcome"])
    anneal_outcome = str(probe["baseline_anneal_outcome"])
    summary = build_simulated_miri_summary(
        probe_id,
        miri_outcome,
        anneal_outcome,
        str(probe["baseline_anneal_lean_tag"]),
        repro_path,
    )
    verdict = campaign_verdict_for_miri_summary(summary)
    tag_verdict = classify_oracle_outcome_tags(miri_outcome, anneal_outcome)[0]
    polarity = classify_witness_polarity_from_tags(miri_outcome, anneal_outcome)
    return {
        "probe_id": probe_id,
        "verdict": tag_verdict,
        "exit_code": verdict["exit_code"],
        "witness_polarity": polarity,
        "clean": (
            verdict["exit_code"] == EXIT_SUCCESS
            and tag_verdict == "agree"
            and polarity is None
            and verdict["witness_polarity"] is None
        ),
        "detail": f"{verdict['kill_class']}: {verdict['detail']}",
    }


def _simulate_mutant_through_campaign_pipeline(mutant: dict[str, Any]) -> dict[str, Any]:
    """Differential (baseline vs. mutant) simulation of one seeded semantic mutant.

    Every probe the mutant uses (its own and each variant's `probe` override) is first
    evaluated with the *unmutated* Anneal semantics (`baseline_anneal_outcome`), which
    must agree with the reference Miri outcome, carry no witness polarity, and pass the
    full campaign pipeline with `EXIT_SUCCESS`; otherwise the probe proves nothing and
    the mutant is reported as not killed. Each mutant variant (the Anneal outcome with
    the guard omitted or mutated, on its probe) must then be rejected by the campaign
    pipeline (`EXIT_DIVERGENCE_DETECTED` or `EXIT_HARNESS_FAILED`) with its expected
    kill class and with its `expected_witness_polarity`, which both the pipeline's
    verdict and the exact Rust-tag classifier must report. Verdicts and polarities are
    derived by `classify_oracle_outcome_tags` / `classify_witness_polarity_from_tags`
    and the campaign pipeline, never hard-coded.
    """
    mutant_id = str(mutant["id"])
    expected = tuple(mutant.get("expected_kill_classes", ()))
    expected_polarities = tuple(mutant.get("expected_witness_polarities", ()))
    variants = list(mutant.get("mutant_variants", ()))
    own_probe = semantic_mutant_variant_probe(mutant, {})
    variant_probes = [semantic_mutant_variant_probe(mutant, v) for v in variants]
    with tempfile.TemporaryDirectory(prefix=f"anneal-mutant-{mutant_id}-") as tmp:
        repro_paths: dict[str, Path] = {}
        probes_by_id: dict[str, dict[str, Any]] = {}
        baselines: list[dict[str, Any]] = []
        for probe in [own_probe, *variant_probes]:
            prior = probes_by_id.get(probe["id"])
            if prior is not None:
                # One id, one program: a variant may not reuse a probe id with
                # different outcomes and so skip that program's baseline check.
                if prior != probe:
                    raise ValueError(
                        f"conflicting definitions of semantic-mutant probe {probe['id']!r}"
                    )
                continue
            probes_by_id[probe["id"]] = probe
            repro_path = Path(tmp) / f"{len(repro_paths)}_repro.rs"
            repro_path.write_text(str(probe["probe_rust_source"]), encoding="utf-8")
            repro_paths[probe["id"]] = repro_path
            baselines.append(_simulate_probe_baseline(probe, repro_path))

        own = baselines[0]
        result: dict[str, Any] = {
            "id": mutant_id,
            "baseline_verdict": own["verdict"],
            "baseline_exit_code": own["exit_code"],
            "baseline_witness_polarity": own["witness_polarity"],
            "baselines": baselines,
            "variants": [],
        }
        unclean = [b for b in baselines if not b["clean"]]
        if unclean:
            first = unclean[0]
            result.update(
                killed=False,
                kill_class="baseline_not_clean",
                exit_code=first["exit_code"],
                witness_polarity=first["witness_polarity"],
                detail=(
                    f"unmutated semantics fail probe {first['probe_id']!r} "
                    f"({first['detail']})"
                ),
            )
            return result

        variant_results: list[dict[str, Any]] = []
        observed_classes: set[str] = set()
        observed_polarities: set[str] = set()
        for variant, probe in zip(variants, variant_probes):
            miri_outcome = str(probe["reference_miri_outcome"])
            anneal_outcome = str(variant["anneal_outcome"])
            diagnostics = [dict(d) for d in variant.get("diagnostics", ())]
            summary = build_simulated_miri_summary(
                str(probe["id"]),
                miri_outcome,
                anneal_outcome,
                str(variant["anneal_lean_tag"]),
                repro_paths[probe["id"]],
                diagnostics=diagnostics or None,
            )
            verdict = campaign_verdict_for_miri_summary(summary)
            v_exit, v_class, v_detail = (
                verdict["exit_code"],
                verdict["kill_class"],
                verdict["detail"],
            )
            v_polarity = verdict["witness_polarity"]
            tag_polarity = classify_witness_polarity_from_tags(miri_outcome, anneal_outcome)
            v_expected_cls = variant.get("expected_kill_class")
            v_expected_sub = variant.get("expected_detail_substring")
            v_expected_pol = variant.get("expected_witness_polarity")
            v_killed = (
                v_exit in (EXIT_DIVERGENCE_DETECTED, EXIT_HARNESS_FAILED)
                and bool(expected)
                and v_class in expected
                and isinstance(v_expected_cls, str)
                and (
                    v_expected_cls in VALID_DIVERGENCE_CLASSES
                    or v_expected_cls == HARNESS_ERROR_KILL_CLASS
                )
                and v_class == v_expected_cls
                and (v_expected_sub is None or str(v_expected_sub) in v_detail)
                and v_expected_pol in VALID_WITNESS_POLARITIES
                and v_expected_pol in expected_polarities
                and kill_class_witness_polarity(v_expected_cls) == v_expected_pol
                and v_polarity == tag_polarity == v_expected_pol
            )
            if v_killed:
                observed_classes.add(v_class)
                observed_polarities.add(v_polarity)
            variant_results.append(
                {
                    "label": str(variant.get("label", "")),
                    "probe_id": str(probe["id"]),
                    "verdict": list(classify_oracle_outcome_tags(miri_outcome, anneal_outcome)),
                    "exit_code": v_exit,
                    "kill_class": v_class,
                    "witness_polarity": v_polarity,
                    "tag_witness_polarity": tag_polarity,
                    "expected_witness_polarity": v_expected_pol,
                    "killed": v_killed,
                    "detail": v_detail,
                }
            )
        result["variants"] = variant_results
        missing_classes = [c for c in expected if c not in observed_classes]
        missing_polarities = [p for p in expected_polarities if p not in observed_polarities]
        all_killed = (
            bool(variant_results)
            and bool(expected)
            and bool(expected_polarities)
            and all(v["killed"] for v in variant_results)
            and not missing_classes
            and not missing_polarities
        )
        survivors = [v for v in variant_results if not v["killed"]]
        first = survivors[0] if survivors else variant_results[0] if variant_results else None
        result.update(
            killed=all_killed,
            kill_class=(first["kill_class"] if first else "no_variants"),
            exit_code=(first["exit_code"] if first else EXIT_SUCCESS),
            witness_polarity=(first["witness_polarity"] if first else None),
        )
        if survivors:
            result["survived_variants"] = [v["label"] for v in survivors]
        if missing_classes:
            result["missing_expected_kill_classes"] = missing_classes
        if missing_polarities:
            result["missing_expected_witness_polarities"] = missing_polarities
        return result


def _explicit_or_implied_polarity(raw_res: dict[str, Any], kill_class: str) -> str | None:
    """A dict result's `witness_polarity` when it reports one (which must be a valid
    slug or `None`), else the polarity its kill class implies."""
    if "witness_polarity" in raw_res:
        polarity = raw_res["witness_polarity"]
        if polarity is not None and polarity not in VALID_WITNESS_POLARITIES:
            raise ValueError(f"evaluator returned an invalid witness_polarity {polarity!r}")
        return polarity
    return kill_class_witness_polarity(kill_class)


def _normalize_evaluator_result(
    mutant_id: str, expected_classes: tuple[str, ...], raw_res: Any
) -> dict[str, Any]:
    """Normalizes a custom evaluator's result (bool, exit code, verdict string, or dict)
    into `{"id", "killed", "kill_class", "exit_code", "witness_polarity"}`. The
    polarity is the one a dict result reports explicitly, the campaign verdict's for a
    full `miri-difftest` summary, or else the one its kill class implies
    (`kill_class_witness_polarity`); a survivor carries none."""

    def result(killed: bool, k_class: str, exit_c: int, polarity: str | None) -> dict[str, Any]:
        return {
            "id": mutant_id,
            "killed": killed,
            "kill_class": k_class,
            "exit_code": exit_c,
            "witness_polarity": polarity if killed else None,
        }

    if isinstance(raw_res, bool):
        k_class = expected_classes[0] if (raw_res and expected_classes) else "survived"
        return result(
            raw_res,
            k_class,
            EXIT_DIVERGENCE_DETECTED if raw_res else EXIT_SUCCESS,
            kill_class_witness_polarity(k_class),
        )
    if isinstance(raw_res, int):
        # A bare exit code names only its verdict family: `EXIT_HARNESS_FAILED` is a
        # `harness_error` kill, and `EXIT_DIVERGENCE_DETECTED` is credited to the
        # mutant's first expected divergence class.
        divergence_classes = [c for c in expected_classes if c != HARNESS_ERROR_KILL_CLASS]
        if raw_res == EXIT_HARNESS_FAILED:
            k_class = HARNESS_ERROR_KILL_CLASS
        elif raw_res == EXIT_DIVERGENCE_DETECTED and divergence_classes:
            k_class = divergence_classes[0]
        else:
            k_class = "survived"
        is_killed = k_class != "survived"
        return result(is_killed, k_class, raw_res, kill_class_witness_polarity(k_class))
    if isinstance(raw_res, str):
        clean = raw_res.strip().lower()
        is_killed = clean not in ("agree", "pass", "survived", "ok", "")
        k_class = raw_res.strip() if is_killed else "survived"
        return result(
            is_killed,
            k_class,
            EXIT_DIVERGENCE_DETECTED if is_killed else EXIT_SUCCESS,
            kill_class_witness_polarity(k_class),
        )
    if isinstance(raw_res, dict):
        extra_keys = (
            "variants",
            "baselines",
            "baseline_verdict",
            "baseline_exit_code",
            "baseline_witness_polarity",
            "survived_variants",
            "missing_expected_kill_classes",
            "missing_expected_witness_polarities",
            "detail",
        )
        if "killed" in raw_res:
            raw_exit = raw_res.get(
                "exit_code",
                EXIT_DIVERGENCE_DETECTED if raw_res["killed"] is True else EXIT_SUCCESS,
            )
            if isinstance(raw_exit, bool) or not isinstance(raw_exit, int):
                raise ValueError(f"evaluator returned a non-integer exit_code {raw_exit!r}")
            exit_c = raw_exit
            is_killed = raw_res["killed"] is True and exit_c in (
                EXIT_DIVERGENCE_DETECTED,
                EXIT_HARNESS_FAILED,
            )
            k_class = str(
                raw_res.get(
                    "kill_class",
                    expected_classes[0] if (is_killed and expected_classes) else "survived",
                )
            )
            out = result(
                is_killed, k_class, exit_c, _explicit_or_implied_polarity(raw_res, k_class)
            )
            for extra_key in extra_keys:
                if extra_key in raw_res:
                    out[extra_key] = raw_res[extra_key]
            return out
        if "verdict" in raw_res:
            verdict_str = str(raw_res["verdict"]).strip().lower()
            if verdict_str == "diverge":
                div_cls = raw_res.get("divergence_class", raw_res.get("kill_class"))
                is_killed = isinstance(div_cls, str) and bool(div_cls.strip())
                k_class = div_cls.strip() if is_killed else "survived"
                default_exit = EXIT_DIVERGENCE_DETECTED if is_killed else EXIT_SUCCESS
            elif verdict_str in ("error", HARNESS_ERROR_KILL_CLASS):
                is_killed = True
                k_class = str(
                    raw_res.get(
                        "divergence_class", raw_res.get("kill_class", HARNESS_ERROR_KILL_CLASS)
                    )
                )
                default_exit = EXIT_HARNESS_FAILED
            else:
                is_killed = False
                k_class = "survived"
                default_exit = EXIT_SUCCESS
            raw_exit = raw_res.get("exit_code", default_exit)
            if isinstance(raw_exit, bool) or not isinstance(raw_exit, int):
                raise ValueError(f"evaluator returned a non-integer exit_code {raw_exit!r}")
            exit_c = raw_exit
            if is_killed and exit_c not in (EXIT_DIVERGENCE_DETECTED, EXIT_HARNESS_FAILED):
                is_killed = False
                k_class = "survived"
            out = result(
                is_killed,
                k_class,
                exit_c,
                _explicit_or_implied_polarity(raw_res, k_class) if is_killed else None,
            )
            for extra_key in extra_keys:
                if extra_key in raw_res:
                    out[extra_key] = raw_res[extra_key]
            return out
        if "diverge_count" in raw_res or "miri_verdicts" in raw_res:
            verdict = campaign_verdict_for_miri_summary(raw_res)
            exit_c = verdict["exit_code"]
            is_killed = exit_c in (EXIT_DIVERGENCE_DETECTED, EXIT_HARNESS_FAILED)
            return result(
                is_killed,
                verdict["kill_class"] if is_killed else "survived",
                exit_c,
                verdict["witness_polarity"],
            )
    return result(False, "survived", EXIT_SUCCESS, None)


# Result keys that name a surviving variant or an expected kill class or polarity
# that no killed variant reached (`_reported_variant_problems`).
SEMANTIC_MUTANT_SURVIVAL_KEYS: tuple[str, ...] = (
    "survived_variants",
    "missing_expected_kill_classes",
    "missing_expected_witness_polarities",
)


def _reported_variant_problems(
    mutant: dict[str, Any],
    variants: Any,
    expected_classes: tuple[str, ...],
    expected_polarities: tuple[str, ...],
) -> dict[str, list[str]]:
    """Audits the per-variant results reported for `mutant` (the simulation's, or a
    custom evaluator's `variants`), marking every failing variant dict
    `killed: False`, and returns the `SEMANTIC_MUTANT_SURVIVAL_KEYS` lists (all
    empty exactly when every variant is killed as declared).

    A variant is killed only with `killed is True`, a kill class among the mutant's
    `expected_kill_classes`, a witness polarity among its
    `expected_witness_polarities` that equals the polarity its class implies, and
    (when it reports one) an `exit_code` naming the same verdict
    (`EXIT_HARNESS_FAILED` exactly for `harness_error`, else
    `EXIT_DIVERGENCE_DETECTED`). When the mutant declares `mutant_variants`, the
    report must name each of them exactly once by `label`, killed with that
    variant's own `expected_kill_class` and `expected_witness_polarity`: an
    unlabeled, unknown, duplicated, or omitted variant survives, so no variant can
    be dropped or have its class or polarity swapped with another's. The killed
    variants must reach every expected kill class and polarity.
    """
    survivors: list[str] = []
    obs_classes: set[str] = set()
    obs_polarities: set[str] = set()
    if not isinstance(variants, list) or not variants:
        survivors.append("<no variants reported>")
        variants = []
    declared: dict[str, dict[str, Any]] = {}
    raw_declared = mutant.get("mutant_variants") if isinstance(mutant, dict) else None
    if raw_declared is None:
        raw_declared = ()
    if not isinstance(raw_declared, (list, tuple)):
        survivors.append("<mutant_variants is not a list>")
        raw_declared = ()
    for d_idx, d in enumerate(raw_declared):
        d_label = d.get("label") if isinstance(d, dict) else None
        if not isinstance(d_label, str) or not d_label.strip() or d_label in declared:
            survivors.append(f"<declared variant[{d_idx}] without a unique label>")
            continue
        d_cls = d.get("expected_kill_class")
        d_pol = d.get("expected_witness_polarity")
        if (
            not isinstance(d_cls, str)
            or d_cls not in expected_classes
            or d_pol not in VALID_WITNESS_POLARITIES
            or d_pol not in expected_polarities
            or kill_class_witness_polarity(d_cls) != d_pol
        ):
            survivors.append(f"<declared variant[{d_idx}] ({d_label}) has invalid expectations>")
            continue
        declared[d_label] = d
    reported_labels: set[str] = set()
    for v_idx, v in enumerate(variants):
        if not isinstance(v, dict):
            survivors.append(f"<variant[{v_idx}]>")
            continue
        raw_label = v.get("label")
        label = raw_label if isinstance(raw_label, str) and raw_label.strip() else None
        v_cls = v.get("kill_class")
        v_pol = v.get("witness_polarity")
        v_ok = (
            v.get("killed") is True
            and isinstance(v_cls, str)
            and v_cls in expected_classes
            and v_pol in VALID_WITNESS_POLARITIES
            and v_pol in expected_polarities
            and kill_class_witness_polarity(v_cls) == v_pol
            and ("expected_kill_class" not in v or v.get("expected_kill_class") == v_cls)
            and (
                "expected_witness_polarity" not in v
                or v.get("expected_witness_polarity") == v_pol
            )
            and ("tag_witness_polarity" not in v or v.get("tag_witness_polarity") == v_pol)
        )
        if "verdict" in v:
            # The variant's outcome-tag verdict `[verdict, detail]`: a divergence
            # kill must be exactly `["diverge", kill_class]`, and a harness kill a
            # real divergence or not-compared verdict (never an agreement).
            v_verdict = v.get("verdict")
            verdict_pair = (
                tuple(v_verdict)
                if isinstance(v_verdict, (list, tuple))
                and len(v_verdict) == 2
                and all(isinstance(part, str) for part in v_verdict)
                else None
            )
            v_ok = v_ok and verdict_pair is not None
            if v_ok and verdict_pair is not None:
                if v_cls == HARNESS_ERROR_KILL_CLASS:
                    v_ok = (
                        verdict_pair[0] == "diverge"
                        and verdict_pair[1] in VALID_DIVERGENCE_CLASSES
                    ) or (
                        verdict_pair[0] == "not_compared"
                        and verdict_pair[1] in VALID_NOT_COMPARED_REASONS
                    )
                else:
                    v_ok = verdict_pair == ("diverge", v_cls)
        if "exit_code" in v:
            v_exit = v.get("exit_code")
            v_ok = (
                v_ok
                and isinstance(v_exit, int)
                and not isinstance(v_exit, bool)
                and v_exit
                == (
                    EXIT_HARNESS_FAILED
                    if v_cls == HARNESS_ERROR_KILL_CLASS
                    else EXIT_DIVERGENCE_DETECTED
                )
            )
        if declared:
            spec = declared.get(label) if label is not None else None
            expected_probe_id = None
            expected_sub = None
            if spec is not None:
                raw_probe = spec.get("probe")
                if isinstance(raw_probe, dict) and isinstance(raw_probe.get("id"), str):
                    expected_probe_id = raw_probe["id"].strip()
                elif isinstance(mutant, dict) and isinstance(mutant.get("id"), str):
                    expected_probe_id = mutant["id"].strip()
                expected_sub = spec.get("expected_detail_substring")
            v_ok = (
                v_ok
                and spec is not None
                and label not in reported_labels
                and v_cls == spec.get("expected_kill_class")
                and v_pol == spec.get("expected_witness_polarity")
                and (
                    "probe_id" not in v
                    or expected_probe_id is None
                    or v.get("probe_id") == expected_probe_id
                )
                and (
                    "detail" not in v
                    or expected_sub is None
                    or (isinstance(v.get("detail"), str) and str(expected_sub) in v["detail"])
                )
            )
            if label is not None:
                reported_labels.add(label)
        if v_ok:
            obs_classes.add(v_cls)
            obs_polarities.add(v_pol)
        else:
            v["killed"] = False
            survivors.append(label if label is not None else f"<variant[{v_idx}]>")
    survivors.extend(
        f"{label} (not reported)" for label in declared if label not in reported_labels
    )
    return {
        "survived_variants": survivors,
        "missing_expected_kill_classes": [c for c in expected_classes if c not in obs_classes],
        "missing_expected_witness_polarities": [
            p for p in expected_polarities if p not in obs_polarities
        ],
    }


_JSON_SAFE_MAX_DEPTH = 64


def _safe_repr(value: Any) -> str:
    """`repr(value)`, or a placeholder when that `repr` raises (or is unprintable)."""
    try:
        text = repr(value)
    except Exception:  # noqa: BLE001 - an evaluator object's `__repr__` may raise
        return f"<unrepresentable {type(value).__name__}>"
    return text if isinstance(text, str) else f"<unrepresentable {type(value).__name__}>"


def _safe_str(value: Any) -> str:
    """`str(value)`, falling back to `_safe_repr` when that `str` raises."""
    try:
        text = str(value)
    except Exception:  # noqa: BLE001 - an evaluator exception's `__str__` may raise
        return _safe_repr(value)
    return text if isinstance(text, str) else _safe_repr(value)


def _json_safe(value: Any, _seen: set[int] | None = None, _depth: int = 0) -> Any:
    """A strict-JSON copy of a semantic-mutant result: tuples become lists, keys
    become strings, and anything else that JSON cannot carry (sets, objects,
    non-finite floats, >256-bit integers, cyclic or more than
    `_JSON_SAFE_MAX_DEPTH`-deep containers) becomes a safe string representation, so
    a custom evaluator's passed-through values can never crash the summary JSON,
    Markdown, or JUnit rendering. Total: it never raises, even for a key that
    cannot be stringified or an object whose `__repr__` raises."""
    if value is None or isinstance(value, (bool, str)):
        return value
    if isinstance(value, int):
        return (
            value
            if abs(value) <= (1 << 256)
            else f"<int bit_length={value.bit_length()}>"
        )
    if isinstance(value, float):
        return value if value == value and abs(value) != float("inf") else _safe_repr(value)
    if isinstance(value, (dict, list, tuple)):
        if _depth >= _JSON_SAFE_MAX_DEPTH:
            return f"<{type(value).__name__} nested too deep>"
        seen = set() if _seen is None else _seen
        obj_id = id(value)
        if obj_id in seen:
            return f"<cyclic {type(value).__name__}>"
        next_seen = seen | {obj_id}
        if isinstance(value, dict):
            out: dict[str, Any] = {}
            for k, v in value.items():
                safe_key = k if isinstance(k, str) else _json_safe(k, next_seen, _depth + 1)
                key_text = safe_key if isinstance(safe_key, str) else json.dumps(safe_key)
                out[key_text] = _json_safe(v, next_seen, _depth + 1)
            return out
        return [_json_safe(v, next_seen, _depth + 1) for v in value]
    return _safe_repr(value)


def run_semantic_mutant_self_check(
    evaluator: Any = None,
    mutants: tuple[dict[str, Any], ...] | list[dict[str, Any]] = SEEDED_SEMANTIC_MUTANTS,
) -> dict[str, Any]:
    """Runs the seeded semantic mutant probes (by default the 8 families
    `bool_valid_range`, `storage_dead_tag`, `provenance_frag`, `div_by_zero`,
    `wide_shift`, `move_triggers_tb_write`, `exact_div_rem_omitted`, and
    `protector_release_order`) through the campaign oracle verdict pipeline and fails
    closed (`EXIT_HARNESS_FAILED`) unless every mutant is killed.

    Without `evaluator`, each mutant is checked differentially by
    `_simulate_mutant_through_campaign_pipeline` (unmutated semantics must pass on
    every probe, every mutated variant must be rejected with its expected kill class
    and witness polarity). A custom `evaluator(mutant)` (for example a live run against
    mutated Lean sources) may return a bool, an exit code, a verdict string, a result
    dict, or a full `miri-difftest` summary. Any exception raised while evaluating a
    mutant (by the simulation, a custom evaluator, or while normalizing its result)
    counts as a surviving mutant (`evaluator_error`), never as a kill, and so does a
    kill whose class is not among the mutant's `expected_kill_classes` or whose witness
    polarity is not among its `expected_witness_polarities` (or contradicts the polarity
    its kill class implies). A result that reports `variants` (as the simulation always
    does) is killed only when `_reported_variant_problems` finds every declared variant
    killed exactly once with its own expected class and polarity, and a result naming
    any `SEMANTIC_MUTANT_SURVIVAL_KEYS` entry is never a kill; a custom evaluator that
    reports no `variants` is judged by its mutant-level verdict alone.
    `witness_polarity_counts` tallies the polarities of the killed variants (or of
    killed custom-evaluator mutants).
    """
    killed_mutants: list[str] = []
    survived_mutants: list[str] = []
    per_mutant_results: list[dict[str, Any]] = []
    polarity_counts = empty_witness_polarity_counts()

    for idx, mutant in enumerate(mutants):
        try:
            mutant_id = str(mutant["id"])
            raw_classes = mutant.get("expected_kill_classes", ())
            raw_polarities = mutant.get("expected_witness_polarities", ())
            if not isinstance(raw_classes, (list, tuple)) or not isinstance(
                raw_polarities, (list, tuple)
            ):
                raise TypeError(
                    "expected_kill_classes and expected_witness_polarities must be sequences"
                )
            expected_classes = tuple(raw_classes)
            expected_polarities = tuple(raw_polarities)
        except Exception as e:  # noqa: BLE001 - fail closed on a malformed mutant
            mutant_id = f"<mutant[{idx}]>"
            per_mutant_results.append(
                {
                    "id": mutant_id,
                    "killed": False,
                    "kill_class": "evaluator_error",
                    "exit_code": EXIT_INTERNAL_ERROR,
                    "witness_polarity": None,
                    "detail": f"malformed mutant: {type(e).__name__}: {e}",
                }
            )
            survived_mutants.append(mutant_id)
            continue
        try:
            if evaluator is None:
                outcome = _simulate_mutant_through_campaign_pipeline(mutant)
            else:
                outcome = _normalize_evaluator_result(
                    mutant_id, expected_classes, evaluator(mutant)
                )
            # Every check below runs on a strict-JSON copy, so no evaluator-supplied
            # object (a raising `__eq__` / `__bool__` / `__repr__`, a cycle, a huge
            # int) can crash or sway them.
            outcome = _json_safe(outcome)
            if not isinstance(outcome, dict) or not isinstance(outcome.get("killed"), bool):
                raise ValueError("result is not a JSON object with a boolean 'killed'")
        except Exception as e:  # noqa: BLE001 - fail closed on any evaluation crash
            outcome = {
                "id": mutant_id,
                "killed": False,
                "kill_class": "evaluator_error",
                "exit_code": EXIT_INTERNAL_ERROR,
                "witness_polarity": None,
                "detail": f"{type(e).__name__}: {_safe_str(e)}",
            }

        if outcome["killed"] and (
            not expected_classes or outcome.get("kill_class") not in expected_classes
        ):
            outcome["killed"] = False
            outcome["unexpected_kill_class"] = outcome.get("kill_class")
        # A kill's exit code and class must name the same verdict: the campaign exits
        # `EXIT_HARNESS_FAILED` exactly for a `harness_error` and
        # `EXIT_DIVERGENCE_DETECTED` for a divergence class.
        if outcome["killed"] and (
            (outcome.get("exit_code") == EXIT_HARNESS_FAILED)
            != (outcome.get("kill_class") == HARNESS_ERROR_KILL_CLASS)
        ):
            outcome["killed"] = False
            outcome["inconsistent_exit_code"] = outcome.get("exit_code")
        if outcome["killed"]:
            polarity = outcome.get("witness_polarity")
            implied = kill_class_witness_polarity(outcome.get("kill_class"))
            if (
                not expected_polarities
                or polarity not in VALID_WITNESS_POLARITIES
                or polarity not in expected_polarities
                or implied is None
                or polarity != implied
            ):
                outcome["killed"] = False
                outcome["unexpected_witness_polarity"] = polarity
        if outcome["killed"]:
            if "baseline_verdict" in outcome and outcome.get("baseline_verdict") != "agree":
                outcome["killed"] = False
            if "baseline_exit_code" in outcome and (
                isinstance(outcome.get("baseline_exit_code"), bool)
                or outcome.get("baseline_exit_code") != EXIT_SUCCESS
            ):
                outcome["killed"] = False
            if (
                "baseline_witness_polarity" in outcome
                and outcome.get("baseline_witness_polarity") is not None
            ):
                outcome["killed"] = False
            if "baselines" in outcome:
                baselines = outcome.get("baselines")
                if not isinstance(baselines, list) or not baselines:
                    outcome["killed"] = False
                else:
                    for b in baselines:
                        if not (
                            isinstance(b, dict)
                            and b.get("clean") is True
                            and b.get("verdict") == "agree"
                            and not isinstance(b.get("exit_code"), bool)
                            and b.get("exit_code") == EXIT_SUCCESS
                            and b.get("witness_polarity") is None
                        ):
                            outcome["killed"] = False
                            break
        if outcome["killed"] and "variants" in outcome:
            variants = outcome.get("variants")
            if isinstance(variants, list):
                # Audit copies: never mutate the dicts a custom evaluator returned.
                variants = [dict(v) if isinstance(v, dict) else v for v in variants]
                outcome["variants"] = variants
            try:
                problems = _reported_variant_problems(
                    mutant, variants, expected_classes, expected_polarities
                )
            except Exception as e:  # noqa: BLE001 - fail closed on a malformed report
                problems = {"survived_variants": [f"<variant audit failed: {e!r}>"]}
            if any(problems.values()):
                outcome["killed"] = False
                for key, values in problems.items():
                    if values:
                        outcome[key] = values
        elif outcome["killed"] and isinstance(mutant, dict) and "mutant_variants" in mutant:
            raw_declared = mutant.get("mutant_variants")
            if not isinstance(raw_declared, (list, tuple)) or not raw_declared:
                outcome["killed"] = False
                outcome["survived_variants"] = ["<mutant_variants is empty or not a list>"]
            else:
                seen_decl_labels: set[str] = set()
                decl_classes: set[str] = set()
                decl_polarities: set[str] = set()
                for d_idx, d in enumerate(raw_declared):
                    d_label = d.get("label") if isinstance(d, dict) else None
                    d_cls = d.get("expected_kill_class") if isinstance(d, dict) else None
                    d_pol = d.get("expected_witness_polarity") if isinstance(d, dict) else None
                    if (
                        not isinstance(d_label, str)
                        or not d_label.strip()
                        or d_label in seen_decl_labels
                        or not isinstance(d_cls, str)
                        or d_cls not in expected_classes
                        or d_pol not in VALID_WITNESS_POLARITIES
                        or d_pol not in expected_polarities
                        or kill_class_witness_polarity(d_cls) != d_pol
                    ):
                        outcome["killed"] = False
                        outcome.setdefault("survived_variants", []).append(
                            f"<declared variant[{d_idx}]>"
                        )
                    else:
                        seen_decl_labels.add(d_label)
                        decl_classes.add(d_cls)
                        decl_polarities.add(d_pol)
                if outcome["killed"] and (
                    set(expected_classes) - decl_classes
                    or set(expected_polarities) - decl_polarities
                ):
                    outcome["killed"] = False
        if (
            outcome["killed"]
            and evaluator is not None
            and isinstance(mutant, dict)
            and (
                any(k in mutant for k in SEMANTIC_MUTANT_PROBE_KEYS)
                or any(
                    isinstance(v, dict) and v.get("probe") is not None
                    for v in (mutant.get("mutant_variants") or ())
                    if isinstance(mutant.get("mutant_variants"), (list, tuple))
                )
            )
        ):
            try:
                semantic_mutant_probes([mutant])
            except Exception as e:  # noqa: BLE001 - fail closed on a malformed probe
                outcome["killed"] = False
                outcome.setdefault("survived_variants", []).append(
                    f"<invalid probe: {e}>"
                )
        # A result that itself names a surviving variant or an expected kill class or
        # polarity that no variant reached is never a kill, whatever its `killed`.
        for key in SEMANTIC_MUTANT_SURVIVAL_KEYS:
            if outcome["killed"] and outcome.get(key):
                outcome["killed"] = False

        # The result lands in `LATEST_CAMPAIGN_SUMMARY.json`, the Markdown report, and
        # JUnit: a custom evaluator's passed-through values must not crash them, and
        # a result that cannot even be copied safely is a survivor, never a crash.
        try:
            outcome = _json_safe(outcome)
            if not isinstance(outcome, dict) or not isinstance(outcome.get("killed"), bool):
                raise ValueError("result is not a JSON object with a boolean 'killed'")
        except Exception as e:  # noqa: BLE001 - fail closed on an unserializable result
            outcome = {
                "id": mutant_id,
                "killed": False,
                "kill_class": "evaluator_error",
                "exit_code": EXIT_INTERNAL_ERROR,
                "witness_polarity": None,
                "detail": f"unserializable evaluator result: {type(e).__name__}",
            }
        per_mutant_results.append(outcome)
        if outcome["killed"]:
            killed_mutants.append(mutant_id)
            variants = outcome.get("variants")
            if isinstance(variants, list) and variants:
                for v in variants:
                    if (
                        isinstance(v, dict)
                        and v.get("killed") is True
                        and v.get("witness_polarity") in polarity_counts
                    ):
                        polarity_counts[v["witness_polarity"]] += 1
            elif outcome.get("witness_polarity") in polarity_counts:
                polarity_counts[outcome["witness_polarity"]] += 1
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
        "witness_polarity_counts": polarity_counts,
        "results": per_mutant_results,
        "exit_code": EXIT_SUCCESS if passed else EXIT_HARNESS_FAILED,
    }


def resolve_gate_flags(args: argparse.Namespace, profile: CampaignProfile) -> tuple[bool, bool]:
    """Returns `(self_check_mutants, check_stale_ratchet)`: an explicit
    `--[no-]self-check-mutants` / `--[no-]check-stale-ratchet` wins; otherwise both
    gates follow the profile's `gates_by_default` (on for `nightly` only)."""
    self_check = getattr(args, "self_check_mutants", None)
    ratchet = getattr(args, "check_stale_ratchet", None)
    return (
        profile.gates_by_default if self_check is None else bool(self_check),
        profile.gates_by_default if ratchet is None else bool(ratchet),
    )


def is_standalone_gate_invocation(args: argparse.Namespace) -> bool:
    """True when `--self-check-mutants` and/or `--check-stale-ratchet` are requested
    without anything that selects a harness run: no explicit `--profile`, seeds,
    `--miri-identity`, `--miri-only`, `--compile-only`, remote sync, or
    `--junit-xml`. Such an invocation runs only the gates (`standalone_gate` mode)."""
    return (
        (
            getattr(args, "self_check_mutants", None) is True
            or getattr(args, "check_stale_ratchet", None) is True
        )
        and not getattr(args, "explicit_profile", False)
        and args.miri_seed is None
        and args.itree_seed is None
        and not args.miri_identity
        and not args.miri_only
        and not args.compile_only
        and not args.remote_uri.strip()
        and args.junit_xml is None
    )


def run_campaign_gates(
    self_check_mutants: bool,
    check_stale_ratchet: bool,
    quarantine_file: Path | None,
    manifest_path: Path | None,
    ledger: dict[str, Any],
    evaluated_fingerprints: list[str] | None = None,
    manifest_eval_results: dict[str, Any] | None = None,
    observed_quarantine_keys: set[str] | None = None,
    covered_harnesses: set[str] | None = None,
    manifest_eval_exhaustive: bool = False,
) -> tuple[dict[str, Any] | None, dict[str, Any] | None]:
    """Runs the enabled gates and returns `(mutant_report, ratchet_report)`, each
    `None` when its gate is disabled. Without an evaluated run
    (`evaluated_fingerprints` and `observed_quarantine_keys` both `None`), the
    ratchet audit skips the `unobserved_quarantine_entry` rule."""
    mutant_report = run_semantic_mutant_self_check() if self_check_mutants else None
    ratchet_report = (
        verify_no_stale_quarantine_or_known_bugs(
            quarantine_file=quarantine_file,
            manifest_path=manifest_path,
            ledger=ledger,
            evaluated_fingerprints=evaluated_fingerprints,
            manifest_eval_results=manifest_eval_results,
            observed_quarantine_keys=observed_quarantine_keys,
            covered_harnesses=covered_harnesses,
            manifest_eval_exhaustive=manifest_eval_exhaustive,
        )
        if check_stale_ratchet
        else None
    )
    return mutant_report, ratchet_report


def gates_passed(
    mutant_report: dict[str, Any] | None, ratchet_report: dict[str, Any] | None
) -> bool:
    return (mutant_report is None or mutant_report.get("passed") is True) and (
        ratchet_report is None or ratchet_report.get("passed") is True
    )


def _md_table_cell(value: Any, code: bool = False) -> str:
    """Renders `value` as one Markdown table cell: line breaks become spaces and `|`
    is escaped so that a quarantine path, token, or reason cannot break the row (as
    inline code, backticks become `'`)."""
    text = str(value).replace("\r", " ").replace("\n", " ").replace("|", "\\|")
    if code:
        return "`" + text.replace("`", "'") + "`"
    return text


def render_gate_report_sections(
    mutant_report: dict[str, Any] | None, ratchet_report: dict[str, Any] | None
) -> str:
    """Renders the Markdown sections for the enabled gates (empty when none ran)."""
    lines: list[str] = []
    if mutant_report is not None:
        killed_polarities = mutant_report.get("witness_polarity_counts")
        polarity_line = (
            ", ".join(f"`{p}`={killed_polarities.get(p, 0)}" for p in VALID_WITNESS_POLARITIES)
            if isinstance(killed_polarities, dict)
            else "n/a"
        )
        lines.extend(
            [
                "",
                "## Semantic-Mutant Self-Check (`--self-check-mutants`)",
                "",
                f"- **Passed**: `{mutant_report['passed']}` "
                f"(`{mutant_report['killed_count']}/{mutant_report['total_mutants']}` killed)",
                f"- **Survived mutants**: `{mutant_report['survived_mutants']}`",
                f"- **Killed-variant witness polarities**: {polarity_line}",
                "",
                "| Mutant | Killed | Kill class | Witness polarities | Baseline | "
                "Variants (label: exit, class, polarity) |",
                "| :--- | :--- | :--- | :--- | :--- | :--- |",
            ]
        )
        for res in mutant_report.get("results", []):
            if not isinstance(res, dict):
                continue
            # Only well-formed variant records are rendered (a malformed custom
            # evaluator report is already a survivor, and must not crash the report).
            raw_variants = res.get("variants")
            res_variants = (
                [v for v in raw_variants if isinstance(v, dict)]
                if isinstance(raw_variants, list)
                else []
            )
            variants = "; ".join(
                f"{v.get('label')}: {v.get('exit_code')}, {v.get('kill_class')}, "
                f"{v.get('witness_polarity')}"
                for v in res_variants
            )
            raw_baselines = res.get("baselines")
            probe_count = len(raw_baselines) if isinstance(raw_baselines, list) else 0
            probes_note = f"; {probe_count} probes" if probe_count > 1 else ""
            baseline = (
                f"{_md_table_cell(res.get('baseline_verdict', 'n/a'), code=True)} (exit "
                f"{_md_table_cell(res.get('baseline_exit_code', 'n/a'), code=True)}"
                f"{probes_note})"
            )
            # Every distinct variant polarity, in variant order (a family such as
            # `protector_release_order` kills in both soundness directions).
            variant_polarities = list(
                dict.fromkeys(str(v.get("witness_polarity")) for v in res_variants)
            )
            polarity_cell = (
                ", ".join(variant_polarities)
                if variant_polarities
                else res.get("witness_polarity")
            )
            lines.append(
                f"| {_md_table_cell(res.get('id'), code=True)} "
                f"| {_md_table_cell(res.get('killed'), code=True)} "
                f"| {_md_table_cell(res.get('kill_class'), code=True)} "
                f"| {_md_table_cell(polarity_cell, code=True)} "
                f"| {baseline} | {_md_table_cell(variants or 'n/a')} |"
            )
    if ratchet_report is not None:
        stale = ratchet_report.get("stale_entries", [])
        lines.extend(
            [
                "",
                "## Stale Quarantine & Known-Bug Ratchet Audit (`--check-stale-ratchet`)",
                "",
                f"- **Passed**: `{ratchet_report['passed']}` (`{len(stale)}` stale entries; "
                f"`{ratchet_report['checked_quarantine_count']}` quarantine entries and "
                f"`{ratchet_report['checked_known_bug_count']}` `known_anneal_bug` entries "
                "checked)",
            ]
        )
        if stale:
            lines.extend(["", "| Source | Entry | Reason |", "| :--- | :--- | :--- |"])
            for e in stale:
                lines.append(
                    f"| {_md_table_cell(e.get('source'), code=True)} "
                    f"| {_md_table_cell(e.get('entry'), code=True)} "
                    f"| {_md_table_cell(e.get('reason'))} |"
                )
    return "\n".join(lines) + ("\n" if lines else "")


def gate_junit_cases(
    mutant_report: dict[str, Any] | None, ratchet_report: dict[str, Any] | None
) -> list[tuple[str, tuple[str, str] | None, str | None]]:
    """JUnit test cases `(name, failure, skipped)` for the enabled gates."""
    cases: list[tuple[str, tuple[str, str] | None, str | None]] = []
    if mutant_report is not None:
        survivor_details = [
            f"{r.get('id')}: kill_class={r.get('kill_class')}, "
            f"witness_polarity={r.get('witness_polarity')}"
            + (
                f", survived_variants={r['survived_variants']}"
                if r.get("survived_variants")
                else ""
            )
            + (
                f", unexpected_witness_polarity={r['unexpected_witness_polarity']}"
                if "unexpected_witness_polarity" in r
                else ""
            )
            for r in mutant_report.get("results", [])
            if isinstance(r, dict) and not r.get("killed")
        ]
        failure = (
            None
            if mutant_report.get("passed") is True
            else (
                "semantic mutant survived",
                "\n".join(
                    [
                        f"survived mutants: {mutant_report.get('survived_mutants')}",
                        *survivor_details,
                    ]
                ),
            )
        )
        cases.append(("semantic-mutant-self-check", failure, None))
    if ratchet_report is not None:
        failure = (
            None
            if ratchet_report.get("passed") is True
            else (
                "stale quarantine or known_anneal_bug entries",
                "\n".join(
                    f"{e.get('entry')}: {e.get('reason')}"
                    for e in ratchet_report.get("stale_entries", [])
                ),
            )
        )
        cases.append(("stale-ratchet-audit", failure, None))
    return cases


def write_standalone_gate_reports(
    state_dir: Path,
    profile: CampaignProfile,
    mutant_report: dict[str, Any] | None,
    ratchet_report: dict[str, Any] | None,
    elapsed_sec: float,
) -> tuple[bool, str]:
    """Writes the `standalone_gate` summary and report under `state_dir/reports/`
    (never touching `state/`) and returns `(gate_ok, report_md)`."""
    date_prefix = utc_date_prefix()
    gate_ok = gates_passed(mutant_report, ratchet_report)
    summary = {
        "profile": profile.name,
        "date_utc": date_prefix,
        "mode": "standalone_gate",
        "passed": gate_ok,
        "gates": {
            "passed": gate_ok,
            "self_check_mutants": mutant_report is not None,
            "check_stale_ratchet": ratchet_report is not None,
        },
        "semantic_mutant_self_check": mutant_report,
        "stale_ratchet_audit": ratchet_report,
        # No harness ran, so no `miri-difftest` non-agreement has a polarity; the
        # self-check's killed-variant polarities are in
        # `semantic_mutant_self_check.witness_polarity_counts`.
        "witness_polarity_counts": None,
        "elapsed_sec": round(elapsed_sec, 3),
    }
    reports_dir = state_dir / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)
    summary_text = json.dumps(summary, indent=2) + "\n"
    for path in (
        reports_dir / f"{date_prefix}_standalone_gate_summary.json",
        reports_dir / "LATEST_CAMPAIGN_SUMMARY.json",
    ):
        _atomic_write_text(path, summary_text)
    md_lines = [
        f"# Anneal Differential Testing Gate Report (`standalone_gate` — `{date_prefix}`)",
        "",
        f"> **Gate status: {'PASS' if gate_ok else 'FAIL'}.** Only the requested gates ran: "
        "no harness was invoked, and the campaign ledger and coverage ratchet were left "
        "untouched.",
    ]
    report_md = (
        "\n".join(md_lines) + "\n" + render_gate_report_sections(mutant_report, ratchet_report)
    )
    for path in (
        reports_dir / f"{date_prefix}_standalone_gate_report.md",
        reports_dir / "LATEST_REPORT.md",
    ):
        _atomic_write_text(path, report_md)
    return gate_ok, report_md


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
    extra_cases: list[tuple[str, tuple[str, str] | None, str | None]] | None = None,
) -> None:
    """Writes JUnit XML when neither harness performed an oracle comparison (plus
    `extra_cases`, such as the enabled gates from `gate_junit_cases`)."""
    junit_path.parent.mkdir(parents=True, exist_ok=True)
    extra = list(extra_cases or [])
    suites = ET.Element("testsuites")
    suite = ET.SubElement(
        suites,
        "testsuite",
        attrib={
            "name": f"anneal_diff_test_{profile_name}",
            "tests": str(len(ran_without_oracle) + len(extra)),
            "failures": str(
                len(ran_without_oracle) + sum(1 for _, fail, _ in extra if fail is not None)
            ),
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
    for name, fail, _ in extra:
        case = ET.SubElement(
            suite,
            "testcase",
            attrib={"classname": "anneal_difftest", "name": name},
        )
        if fail is not None:
            msg, text = fail
            failure = ET.SubElement(case, "failure", attrib={"message": msg})
            failure.text = text
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
    extra_cases: list[tuple[str, tuple[str, str] | None, str | None]] | None = None,
) -> None:
    """Writes JUnit XML for a live oracle campaign (plus `extra_cases`, such as the
    enabled gates from `gate_junit_cases`)."""
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
            f"{d.fingerprint} (occurrences={d.occurrences}, "
            f"witness_polarity={d.witness_polarity}, repro={d.primary_repro_path})"
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

    if extra_cases:
        cases.extend(extra_cases)

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
    - Every `miri-difftest` entry a healthy run writes (observed or resolved) records
      the `witness_polarity` of its fingerprint's divergence class; legacy entries
      without one load unchanged and gain it the next time a healthy run touches
      them.
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
    last_run = ledger.get("last_run_utc")
    legacy_seen_date = (
        last_run[:10]
        if isinstance(last_run, str) and len(last_run) >= 10
        else date_prefix
    )

    raw_res_hist = ledger.get("resolved_history", {})
    resolved_history: dict[str, dict[str, Any]] = {}
    migrated_legacy_resolved: set[str] = set()
    if isinstance(raw_res_hist, dict):
        for k, v in raw_res_hist.items():
            if isinstance(k, str) and isinstance(v, dict):
                resolved_history[str(k)] = copy.deepcopy(v)
    elif isinstance(raw_res_hist, list):
        for item in raw_res_hist:
            if isinstance(item, str) and item.strip():
                fp_key = item.strip()
                resolved_history.setdefault(
                    fp_key,
                    {
                        "first_seen_date": legacy_seen_date,
                        "last_seen_date": legacy_seen_date,
                        "campaigns_failing": 1,
                        "resolved_date": legacy_seen_date,
                        "suite": infer_fingerprint_suite(fp_key),
                    },
                )
                migrated_legacy_resolved.add(fp_key)
            elif isinstance(item, dict) and isinstance(item.get("fingerprint"), str):
                fp_key = item["fingerprint"].strip()
                if fp_key:
                    entry_copy = {
                        str(ek): copy.deepcopy(ev)
                        for ek, ev in item.items()
                        if ek != "fingerprint"
                    }
                    entry_copy.setdefault("first_seen_date", legacy_seen_date)
                    entry_copy.setdefault("last_seen_date", legacy_seen_date)
                    entry_copy.setdefault("campaigns_failing", 1)
                    entry_copy.setdefault("resolved_date", legacy_seen_date)
                    entry_copy.setdefault(
                        "suite", infer_fingerprint_suite(fp_key, entry_copy)
                    )
                    resolved_history.setdefault(fp_key, entry_copy)
                    migrated_legacy_resolved.add(fp_key)

    raw_res_fps = ledger.get("resolved_fingerprints")
    if isinstance(raw_res_fps, list):
        for item in raw_res_fps:
            if isinstance(item, str) and item.strip():
                fp_key = item.strip()
                if fp_key not in resolved_history:
                    resolved_history[fp_key] = {
                        "first_seen_date": legacy_seen_date,
                        "last_seen_date": legacy_seen_date,
                        "campaigns_failing": 1,
                        "resolved_date": legacy_seen_date,
                        "suite": infer_fingerprint_suite(fp_key),
                    }
                    migrated_legacy_resolved.add(fp_key)
        ledger.pop("resolved_fingerprints", None)

    def suite_of(fp: str) -> str:
        return infer_fingerprint_suite(fp, fp_history.get(fp) or resolved_history.get(fp))

    def tag_polarity(entry: dict[str, Any], fp: str, suite_name: str) -> dict[str, Any]:
        # The polarity is a function of the fingerprint's divergence class: an entry
        # whose fingerprint has none (an `itree-difftest` or malformed one) must not
        # keep a `witness_polarity` carried over from a migrated legacy record.
        polarity = (
            fingerprint_witness_polarity(fp) if suite_name == "miri-difftest" else None
        )
        if polarity is not None:
            entry["witness_polarity"] = polarity
        else:
            entry.pop("witness_polarity", None)
        return entry

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
            fp_history[fp] = tag_polarity(
                {
                    "first_seen_date": first_seen,
                    "last_seen_date": date_prefix,
                    "campaigns_failing": failing_cnt,
                    "suite": suite_name,
                },
                fp,
                suite_name,
            )
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
            fp_history[fp] = tag_polarity(
                {
                    "first_seen_date": first_seen,
                    "last_seen_date": date_prefix,
                    "campaigns_failing": failing_cnt,
                    "suite": suite_name,
                },
                fp,
                suite_name,
            )
            resolved_history.pop(fp, None)

        to_resolve = (
            (set(prev_suite_active) | set(prev_suite_quar) | prev_suite_hist_keys)
            - obs_unquar
            - obs_quar
        )
        for fp in sorted(to_resolve):
            prev_meta = fp_history.pop(fp, None) or {}
            resolved_history[fp] = tag_polarity(
                {
                    "first_seen_date": str(prev_meta.get("first_seen_date") or legacy_seen_date),
                    "last_seen_date": str(prev_meta.get("last_seen_date") or legacy_seen_date),
                    "campaigns_failing": _safe_nonneg_int(prev_meta.get("campaigns_failing"), 1),
                    "resolved_date": date_prefix,
                    "suite": suite_name,
                },
                fp,
                suite_name,
            )

        for fp in sorted(migrated_legacy_resolved):
            if fp in resolved_history and infer_fingerprint_suite(fp, resolved_history[fp]) == suite_name:
                tag_polarity(resolved_history[fp], fp, suite_name)

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
    gates_failed: bool = False,
) -> str:
    """Renders the full Markdown report for a live oracle campaign.

    `gates_failed` marks a run whose `--self-check-mutants` or
    `--check-stale-ratchet` gate failed (the gate sections themselves are appended
    by `render_gate_report_sections`)."""
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
    if gates_failed and not status.startswith("RED FLAG"):
        status = f"GATE FAILED (campaign verdict: {status})"

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

    unquarantined_polarities = count_dedup_witness_polarities(unquarantined)
    quarantined_polarities = count_dedup_witness_polarities(quarantined)
    if miri_performed and unquarantined_polarities[WITNESS_POLARITY_UNSOUND] > 0:
        banner_lines.append(
            f"> **Soundness alert**: `{unquarantined_polarities[WITNESS_POLARITY_UNSOUND]}` "
            "unquarantined distinct `unsound_missed_fault` divergence(s): Miri faulted and "
            "Anneal did not report the fault."
        )

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

        pol_counts = miri.get("witness_polarity_counts")
        lines.extend(["", "## Witness Polarity Breakdown (`miri-difftest`)", ""])
        if isinstance(pol_counts, dict) and miri_red_flags.checks.get(
            "witness_polarity_accounting", False
        ):
            lines.extend(
                [
                    "Every non-agreement has exactly one soundness direction "
                    f"(`{sum(int(v) for v in pol_counts.values())}` = "
                    f"`{miri['diverge_count']}` diverged + `{miri['not_compared_count']}` "
                    "not compared).",
                    "",
                    "| Witness Polarity | Count | Unquarantined distinct | Quarantined distinct |",
                    "| :--- | ---: | ---: | ---: |",
                ]
            )
            for pol in VALID_WITNESS_POLARITIES:
                lines.append(
                    f"| `{pol}` | {pol_counts.get(pol, 0)} | "
                    f"{unquarantined_polarities[pol]} | {quarantined_polarities[pol]} |"
                )
        else:
            lines.append(
                "The harness's `witness_polarity_counts` failed the accounting audit "
                "(`witness_polarity_accounting` red flag), so no per-polarity counts are "
                "reported."
            )

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
                "| Fingerprint | Class | Occurrences | Polarity | Miri | Anneal | Kernel Confirmed "
                "| Reproducer |",
                "| :--- | :--- | ---: | :--- | :--- | :--- | :--- | :--- |",
            ]
        )
        for d in unquarantined:
            polarity_cell = f"`{d.witness_polarity}`" if d.witness_polarity else "n/a"
            lines.append(
                f"| `{d.fingerprint}` | `{d.divergence_class}` | {d.occurrences} | "
                f"{polarity_cell} | `{d.miri_outcome}` | `{d.anneal_outcome}` | "
                f"`{str(d.kernel_confirmed).lower()}` | `{d.primary_repro_path}` |"
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
                "| Fingerprint | Class | Occurrences | Polarity | Miri | Anneal | Kernel Confirmed "
                "| Reproducer |",
                "| :--- | :--- | ---: | :--- | :--- | :--- | :--- | :--- |",
            ]
        )
        for d in quarantined:
            polarity_cell = f"`{d.witness_polarity}`" if d.witness_polarity else "n/a"
            lines.append(
                f"| `{d.fingerprint}` | `{d.divergence_class}` | {d.occurrences} | "
                f"{polarity_cell} | `{d.miri_outcome}` | `{d.anneal_outcome}` | "
                f"`{str(d.kernel_confirmed).lower()}` | `{d.primary_repro_path}` |"
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
    parser.add_argument(
        "--profile",
        choices=sorted(PROFILES),
        default=None,
        help=(
            "Campaign profile (default: quick). `nightly` also enables "
            "--self-check-mutants and --check-stale-ratchet by default."
        ),
    )
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
    parser.add_argument(
        "--manifest-path",
        type=Path,
        default=None,
        help=(
            "`tests/miri-diff/manifest.toml` whose `known_anneal_bug` entries the "
            "stale-ratchet audit checks (default: the repository manifest)."
        ),
    )
    parser.add_argument(
        "--check-stale-ratchet",
        action=argparse.BooleanOptionalAction,
        default=None,
        help=(
            "Fail closed on stale, expired, malformed, or unobserved --quarantine-file "
            "entries and on stale manifest `known_anneal_bug` entries (default: on for "
            "--profile nightly, off otherwise)."
        ),
    )
    parser.add_argument(
        "--self-check-mutants",
        action=argparse.BooleanOptionalAction,
        default=None,
        help=(
            "Fail unless the campaign verdict pipeline kills all 8 seeded semantic "
            "mutants (`SEEDED_SEMANTIC_MUTANTS`) while passing their unmutated "
            "baselines (default: on for --profile nightly, off otherwise)."
        ),
    )
    ns = parser.parse_args(argv)
    ns.explicit_profile = ns.profile is not None
    if ns.profile is None:
        ns.profile = "quick"
    return ns


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    profile = PROFILES[args.profile]
    self_check_mutants, check_stale_ratchet = resolve_gate_flags(args, profile)
    standalone_gate = is_standalone_gate_invocation(args)
    repo_root = Path(__file__).resolve().parent.parent
    start_time = time.monotonic()

    remote_uri = args.remote_uri.strip()
    baseline_ratchet_uri = args.baseline_ratchet_uri.strip()
    try:
        check_remote_uri(remote_uri)
        check_remote_uri(baseline_ratchet_uri)
        cli_miri_seed = parse_seed_int(args.miri_seed) if args.miri_seed is not None else None
        cli_itree_seed = parse_seed_int(args.itree_seed) if args.itree_seed is not None else None
        try:
            quarantine_rules = load_quarantine_rules(args.quarantine_file)
        except ValueError as e:
            if not check_stale_ratchet:
                raise
            # The stale-ratchet audit reports the unreadable or malformed file and
            # fails the run; meanwhile no quarantine token is applied, so nothing
            # is hidden.
            sys.stderr.write(f"warning: {e}; applying no quarantine rules\n")
            quarantine_rules = set()
        if args.max_oracle_errors < 0 or args.min_oracle_elapsed_ms < 0:
            raise ValueError("thresholds must be non-negative")
    except ValueError as e:
        sys.stderr.write(f"error: {e}\n")
        return EXIT_HARNESS_FAILED

    default_manifest = repo_root / "tests" / "miri-diff" / "manifest.toml"
    manifest_path = args.manifest_path if args.manifest_path is not None else default_manifest

    temp_ctx = (
        tempfile.TemporaryDirectory(prefix="anneal-diff-test-campaign-")
        if args.state_dir is None
        else None
    )
    state_dir = Path(temp_ctx.name) if temp_ctx is not None else args.state_dir.resolve()

    try:
        LAST_HARNESS_DIAGNOSTICS.clear()
        if standalone_gate:
            # Gates only: the ledger is read (for `resolved_history`) but never
            # written, and no harness runs.
            try:
                gate_ledger = load_ledger(state_dir / "state" / "campaign_ledger.json")
            except ValueError as e:
                sys.stderr.write(f"error: {e}\n")
                return EXIT_INTERNAL_ERROR
            mutant_report, ratchet_report = run_campaign_gates(
                self_check_mutants,
                check_stale_ratchet,
                args.quarantine_file,
                manifest_path,
                gate_ledger,
            )
            gate_ok, report_md = write_standalone_gate_reports(
                state_dir,
                profile,
                mutant_report,
                ratchet_report,
                time.monotonic() - start_time,
            )
            print(report_md)
            return EXIT_SUCCESS if gate_ok else EXIT_HARNESS_FAILED

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
        # The stale-ratchet audit judges quarantine entries against the history this
        # run started from, before the per-suite ledger update below rewrites it.
        pre_run_ledger = copy.deepcopy(ledger)

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
            # Requested gates still run (no oracle evaluated anything, so the
            # ratchet audit cannot apply its unobserved-entry rule).
            mutant_report, ratchet_report = run_campaign_gates(
                self_check_mutants,
                check_stale_ratchet,
                args.quarantine_file,
                manifest_path,
                pre_run_ledger,
            )
            report_md += render_gate_report_sections(mutant_report, ratchet_report)
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
                    extra_cases=gate_junit_cases(mutant_report, ratchet_report),
                )

            sync_state_to_remote(
                state_dir,
                remote_uri,
                _filter_written_for_remote(
                    state_dir, remote_uri, written, remote_state_ok
                ),
            )
            print(report_md)
            if harness_failed or not gates_passed(mutant_report, ratchet_report):
                return EXIT_HARNESS_FAILED
            return EXIT_NOT_EVALUATED

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
            mutant_report, ratchet_report = run_campaign_gates(
                self_check_mutants,
                check_stale_ratchet,
                args.quarantine_file,
                manifest_path,
                pre_run_ledger,
            )
            report_md += render_gate_report_sections(mutant_report, ratchet_report)
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
                    extra_cases=gate_junit_cases(mutant_report, ratchet_report),
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

        known_corpus_bug_seeds = load_known_corpus_bug_seeds(repo_root, manifest_path)
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

        # Gates. The ratchet audit only treats a suite as having evaluated (and so
        # able to leave a quarantine entry unobserved) when that suite is healthy,
        # and every finding contributes exactly the keys its dedup matched tokens
        # against. `known_anneal_bug` entries are audited against the healthy Miri
        # run's per-item outcomes (identity runs evaluate every manifest test).
        observed_quarantine_keys: set[str] = set()
        evaluated_fingerprints: list[str] = []
        covered_harnesses: set[str] = set()
        if miri_suite_healthy and miri is not None:
            covered_harnesses.add("miri")
            evaluated_fingerprints.extend(d.fingerprint for d in miri_all_dedup)
            for f in miri["findings"]:
                observed_quarantine_keys |= quarantine_match_keys_for_miri_finding(
                    f, known_corpus_bug_seeds
                )[1]
        if itree_suite_healthy and itree is not None:
            covered_harnesses.add("itree")
            evaluated_fingerprints.extend(d.fingerprint for d in itree_all_dedup)
            for f in itree["findings"]:
                observed_quarantine_keys |= quarantine_match_keys_for_itree_finding(f)[1]
        mutant_report, ratchet_report = run_campaign_gates(
            self_check_mutants,
            check_stale_ratchet,
            args.quarantine_file,
            manifest_path,
            pre_run_ledger,
            evaluated_fingerprints=evaluated_fingerprints,
            manifest_eval_results=(
                extract_manifest_eval_results_from_miri_summary(miri)
                if miri_suite_healthy and miri is not None
                else None
            ),
            observed_quarantine_keys=observed_quarantine_keys,
            covered_harnesses=covered_harnesses,
            manifest_eval_exhaustive=bool(
                miri_suite_healthy
                and miri is not None
                and miri_summary_evaluates_every_manifest_test(miri)
            ),
        )
        gates_ok = gates_passed(mutant_report, ratchet_report)
        harness_or_red_flag_failed = (
            (not miri_suite_healthy) or (not itree_ok) or (not gates_ok)
        )

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
            gates_failed=not gates_ok,
        )
        report_md += render_gate_report_sections(mutant_report, ratchet_report)
        for report_path in [
            state_dir / "reports" / f"{date_prefix}_{profile.name}_campaign_report.md",
            state_dir / "reports" / "LATEST_REPORT.md",
        ]:
            report_path.write_text(report_md, encoding="utf-8")
            written.append(report_path)

        combined_checks = dict(miri_red_flags.checks)
        combined_reasons = list(miri_red_flags.failure_reasons)
        polarity_verified = bool(
            miri_performed
            and miri is not None
            and miri_red_flags.checks.get("witness_polarity_accounting") is True
        )
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
            # Per-candidate `WitnessPolarity` counts of the `miri-difftest` run (every
            # non-agreement has exactly one), reported only once they pass the
            # accounting audit (`witness_polarity_accounting`; the raw harness map
            # stays in `miri_summary`), and the polarities of its distinct
            # unquarantined / quarantined fingerprints; `None` when no valid
            # performed `miri-difftest` summary exists.
            "witness_polarity_accounting_verified": polarity_verified,
            "witness_polarity_counts": (
                {p: int(miri["witness_polarity_counts"][p]) for p in VALID_WITNESS_POLARITIES}
                if polarity_verified and miri is not None
                else None
            ),
            "unquarantined_witness_polarity_counts": (
                count_dedup_witness_polarities(miri_unquarantined)
                if polarity_verified and miri is not None
                else None
            ),
            "quarantined_witness_polarity_counts": (
                count_dedup_witness_polarities(miri_quarantined)
                if polarity_verified and miri is not None
                else None
            ),
            "miri_summary": miri,
            "itree_summary": itree if include_itree else None,
            "deduplicated_findings": [d.to_dict() for d in all_dedup],
            "unquarantined_findings": [d.to_dict() for d in unquarantined],
            "quarantined_findings": [d.to_dict() for d in quarantined],
            "elapsed_sec": round(elapsed_sec, 3),
        }
        if mutant_report is not None or ratchet_report is not None:
            campaign_summary["gates"] = {
                "passed": gates_ok,
                "self_check_mutants": mutant_report is not None,
                "check_stale_ratchet": ratchet_report is not None,
            }
        if mutant_report is not None:
            campaign_summary["semantic_mutant_self_check"] = mutant_report
        if ratchet_report is not None:
            campaign_summary["stale_ratchet_audit"] = ratchet_report
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
                extra_cases=gate_junit_cases(mutant_report, ratchet_report),
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
