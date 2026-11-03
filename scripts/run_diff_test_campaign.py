#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Anneal differential-testing campaign runner.

Runs the candidate generators in `crates/anneal-difftest` (`miri-difftest` and
`itree-difftest`) under a campaign profile, advances their seeds in a
persistent ledger, and writes a Markdown report and, optionally, JUnit XML.

Neither generator runs Miri, Anneal's Lean model, or the programs it
generates. Each one says so in its JSON output
(`"oracle_comparison": "not_performed"`). This runner reports such a campaign
as NOT EVALUATED: it states no agreement rate and no divergence count, marks
each harness as failed in JUnit, and exits with status 3 so that schedulers
and CI never record the campaign as a success.

Exit status:
  1  internal error, such as a ledger that is not a JSON object; no report is
     written;
  2  invalid command line, or a harness failed to run, wrote unreadable
     output, or reported an oracle status other than "not_performed", which
     this runner cannot present;
  3  the harnesses ran, but no oracle comparison was performed.

Apart from `--help`, the runner never exits 0: until it can present real
comparisons, no campaign counts as a success. When a harness fails, the
ledger is left unchanged, so the failed seeds are run again next time.

State: the ledger (`state/campaign_ledger.json`) lives in a local state
directory (`--state-dir`, or a temporary directory). It is synchronized with
x20 through `/usr/bin/fileutil --x20_force_client_creation_at_head` only when
`--x20-uri` names an x20 directory, such as
`/x20/teams/anneal-agent/differential-testing`. Synchronization is off by
default so that a local run cannot overwrite the shared reports; the capsule
launcher stores results on x20 itself.
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
from typing import Any
import xml.etree.ElementTree as ET


FILEUTIL_BIN = "/usr/bin/fileutil"
FILEUTIL_X20_FLAG = "--x20_force_client_creation_at_head"

EXIT_INTERNAL_ERROR = 1
EXIT_HARNESS_FAILED = 2
EXIT_NOT_EVALUATED = 3

# Integer count keys that a harness JSON summary may carry.
HARNESS_INT_KEYS = (
    "batches",
    "batch_size",
    "total_candidates",
    "compiled_candidates",
    "unsafe_token_violations",
    "opt_level_0_compiled",
    "opt_level_2_compiled",
    "opt_level_0_and_2_compiled",
    "instrumented_compiled",
)

# Ledger keys that earlier versions of this runner wrote. They described
# evaluations, coverage, and findings that never happened, so the runner drops
# them whenever it rewrites the ledger.
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
    for subdir in ["state", "reports"]:
        run_fileutil(["mkdir", "-p", f"{base}/{subdir}"])
    for local_file in written:
        rel = local_file.relative_to(state_dir)
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
    res = subprocess.run(cmd, cwd=str(repo_root), text=True, capture_output=True)
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


def harness_ran_without_oracle(name: str, summary: dict[str, Any] | None) -> bool:
    """Reports whether a harness ran and stated that it compared nothing.

    Any other oracle status counts as a failure: this runner has no way to
    present a comparison, so it must not let one pass silently.
    """
    if not isinstance(summary, dict):
        return False
    status = summary.get("oracle_comparison")
    if status != "not_performed":
        sys.stderr.write(
            f"{name} reported oracle_comparison={status!r}; this runner can only "
            'present harnesses that report "not_performed".\n'
        )
        return False
    return True


def compile_summary(name: str, summary: dict[str, Any] | None) -> str:
    """Describes how many candidates a harness generated and compiled."""
    if summary is None:
        return "no candidates"
    key = "compiled_candidates" if name == "miri-difftest" else "opt_level_0_and_2_compiled"
    return (
        f"{summary.get('total_candidates', 'an unknown number of')} candidates, "
        f"{summary.get(key, 'an unknown number')} of which compiled"
    )


def write_junit_xml(
    junit_path: Path,
    profile_name: str,
    summaries: dict[str, dict[str, Any] | None],
    ran_without_oracle: dict[str, bool],
    elapsed_sec: float,
) -> None:
    """Writes JUnit XML in which every harness fails, because none compared."""
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


def render_report(
    profile: CampaignProfile,
    date_prefix: str,
    miri: dict[str, Any] | None,
    itree: dict[str, Any] | None,
    ran_without_oracle: dict[str, bool],
    miri_seed: int,
    itree_seed: int,
    elapsed_sec: float,
) -> str:
    def cell(summary: dict[str, Any] | None, key: str, fmt: str = "{}") -> str:
        if summary is None or key not in summary:
            return "n/a"
        return fmt.format(summary[key])

    def oracle(name: str) -> str:
        return "**not performed**" if ran_without_oracle[name] else "harness failed"

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


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Anneal differential-testing campaign runner. The harnesses it runs "
            "do not yet compare Anneal with any oracle; see the module docstring."
        )
    )
    parser.add_argument("--profile", choices=sorted(PROFILES), default="quick")
    parser.add_argument(
        "--state-dir",
        type=Path,
        default=None,
        help="Local directory for the ledger and reports (default: a temporary directory).",
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
        except ValueError as e:
            sys.stderr.write(f"error: {e}\n")
            return EXIT_INTERNAL_ERROR

        with tempfile.TemporaryDirectory(prefix="anneal-diff-test-run-") as run_tmp:
            run_tmp_path = Path(run_tmp)
            miri = run_harness(
                repo_root,
                "miri-difftest",
                [
                    "--batches",
                    str(profile.miri_batches),
                    "--batch-size",
                    str(profile.miri_batch_size),
                    "--seed",
                    f"0x{miri_seed:08x}",
                ],
                run_tmp_path / "miri_difftest_out.json",
            )
            itree = run_harness(
                repo_root,
                "itree-difftest",
                [
                    "--batches",
                    str(profile.itree_batches),
                    "--batch-size",
                    str(profile.itree_batch_size),
                    "--seed",
                    f"0x{itree_seed:08x}",
                ],
                run_tmp_path / "itree_difftest_out.json",
            )

        summaries = {"miri-difftest": miri, "itree-difftest": itree}
        ran_without_oracle = {
            name: harness_ran_without_oracle(name, summary) for name, summary in summaries.items()
        }
        harness_failed = not all(ran_without_oracle.values())

        written: list[Path] = []
        if not harness_failed:
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
        date_prefix = utc_date_prefix()
        report_md = render_report(
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
            write_junit_xml(
                args.junit_xml.resolve(), profile.name, summaries, ran_without_oracle, elapsed_sec
            )

        sync_state_to_x20(state_dir, x20_uri, written)
        print(report_md)

        return EXIT_HARNESS_FAILED if harness_failed else EXIT_NOT_EVALUATED
    finally:
        if temp_ctx is not None:
            temp_ctx.cleanup()


if __name__ == "__main__":
    raise SystemExit(main())
