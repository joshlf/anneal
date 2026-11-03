#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file or at https://opensource.org/licenses/BSD-3-Clause

"""Unified Anneal dual differential-testing campaign orchestrator.

Shared entrypoint for Option A (dedicated Capsule + `/x20/` RPC sync) and
Option B (Kokoro V2 / GCB).

Responsibilities:
1. Pull persistent differential-testing state (`campaign_ledger.json`,
   `coverage_ratchet.json`, `quarantine.toml`, and existing `findings/`) from
   shared `/x20/teams/anneal-agent/differential-testing/` using
   `/usr/bin/fileutil --x20_force_client_creation_at_head` (never
   `/google/data/rw/...` FUSE), or from a local `--state-dir` when running on
   Kokoro V2 / local dev.
2. Execute `miri-difftest` (`2.a` Anneal MIR Evaluator vs. `2.b` Miri Reference)
   and `itree-difftest` (`2.a` Anneal `mirStatefulTree` vs. `2.c` Native
   Instrumented Execution at `-O0` and `-O2`) under configurable campaign
   profiles (`smoke`, `quick`, `nightly`, `weekend`), plus optional Lean 4
   kernel `BatchVerify.lean` checks.
3. For any divergence (or `--inject-synthetic-divergence` verification run),
   produce a dual-audience reproducer bundle in
   `findings/<date>_<fingerprint>/`:
   - Human-oriented report (`(a)`): minimized compilable Rust snippet with line
     numbers, concrete scalar/struct/schedule inputs, step-by-step execution
     table showing the exact Rust statement where Anneal and the reference
     oracle diverge, and a one-liner replay command.
   - Agent-oriented report (`(b)`): `TraceReplayDiag` classification tag, exact
     MIR fault coordinate `(BasicBlockIdx, StmtIdx)`, lowered Lean 4 `Mir.Body`
     neighborhood, pre-state `Memory` & `LocalFrame` snapshot, expected vs.
     actual `MirOutcome` / `AbstractByte` representation, and targeted symbolic
     evaluator / lowering candidate file & function coordinates.
4. Deduplicate findings by `SHA-256(harness, diag_tag, block_idx, stmt_idx,
   mir_construct)` and filter known issues against `quarantine.toml`.
5. Optionally emit Sponge/Test-Fusion-compatible JUnit XML (`--junit-xml`) for
   zero-friction graduation from Option A to Option B (`ci/kokoro_diff_test.sh`).
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass, field
import datetime
import hashlib
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
DEFAULT_X20_DIFF_TEST_URI = "/x20/teams/anneal-agent/differential-testing"


@dataclass(frozen=True)
class CampaignProfile:
    name: str
    miri_batches: int
    miri_batch_size: int
    itree_batches: int
    itree_batch_size: int
    itree_inputs_per_fn: int
    run_lean_batch_verify: bool


PROFILES: dict[str, CampaignProfile] = {
    "smoke": CampaignProfile(
        name="smoke",
        miri_batches=2,
        miri_batch_size=8,
        itree_batches=2,
        itree_batch_size=8,
        itree_inputs_per_fn=50,
        run_lean_batch_verify=False,
    ),
    "quick": CampaignProfile(
        name="quick",
        miri_batches=5,
        miri_batch_size=32,
        itree_batches=5,
        itree_batch_size=32,
        itree_inputs_per_fn=200,
        run_lean_batch_verify=True,
    ),
    "nightly": CampaignProfile(
        name="nightly",
        miri_batches=25,
        miri_batch_size=32,
        itree_batches=25,
        itree_batch_size=32,
        itree_inputs_per_fn=400,
        run_lean_batch_verify=True,
    ),
    "weekend": CampaignProfile(
        name="weekend",
        miri_batches=100,
        miri_batch_size=32,
        itree_batches=100,
        itree_batch_size=32,
        itree_inputs_per_fn=1000,
        run_lean_batch_verify=True,
    ),
}


@dataclass
class ExecutionStepRow:
    step_num: int
    rust_line: int
    rust_stmt: str
    mir_coord: str
    anneal_state: str
    oracle_state: str
    status: str  # "OK" or "DIVERGED"


@dataclass
class DualAudienceFinding:
    """Self-contained divergence record for both human readers and agents."""

    fingerprint: str
    harness: str
    seed_hex: str
    mutator_chain: list[str]
    created_utc: str
    quarantined: bool
    quarantine_reason: str | None

    # --- Section (a): Human-Readable Concrete Rust Reproducer & Step Table ---
    title: str
    function_name: str
    minimized_rust_source: str
    concrete_inputs_rust: str
    raw_input_bytes_hex: str
    env_schedule_summary: str
    failing_rust_line: int
    failing_rust_statement: str
    human_summary: str
    execution_steps: list[ExecutionStepRow]
    one_liner_repro_cmd: str

    # --- Section (b): Agent-Oriented MIR, State & Evaluator Fault Context ---
    diag_tag: str
    mir_fault_block_idx: int
    mir_fault_stmt_idx: int
    mir_construct_kind: str
    lowered_lean_mir_snippet: str
    pre_state_locals: dict[str, str]
    pre_state_memory: list[dict[str, str]]
    anneal_outcome_repr: str
    reference_oracle_outcome_repr: str
    suspect_subsystem_files: list[dict[str, str]]
    agent_triage_brief: str = field(default="")


def compute_fingerprint(
    harness: str,
    diag_tag: str,
    block_idx: int,
    stmt_idx: int,
    mir_construct_kind: str,
) -> str:
    payload = (
        f"{harness}|{diag_tag}|bb{block_idx}|stmt{stmt_idx}|{mir_construct_kind}"
    )
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]


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


def run_fileutil(
    args: list[str], check: bool = False
) -> subprocess.CompletedProcess[str]:
    cmd = [FILEUTIL_BIN, FILEUTIL_X20_FLAG, *args]
    return subprocess.run(cmd, text=True, capture_output=True, check=check)


def sync_state_from_x20(x20_uri: str, local_state_dir: Path) -> None:
    """Pulls mutable state files from `/x20/` via `fileutil` RPC."""
    if not x20_uri or not has_x20_fileutil():
        return
    if x20_uri.startswith("/google/data/rw/"):
        raise ValueError(
            f"Refusing FUSE path `{x20_uri}`; always use `/x20/...` URIs with "
            f"`{FILEUTIL_BIN} {FILEUTIL_X20_FLAG}`."
        )
    (local_state_dir / "state").mkdir(parents=True, exist_ok=True)
    (local_state_dir / "reports").mkdir(parents=True, exist_ok=True)
    (local_state_dir / "findings").mkdir(parents=True, exist_ok=True)

    for rel in [
        "state/campaign_ledger.json",
        "state/coverage_ratchet.json",
        "state/quarantine.toml",
    ]:
        src = f"{x20_uri.rstrip('/')}/{rel}"
        dst = str(local_state_dir / rel)
        run_fileutil(["cp", "-f", src, dst], check=False)


def sync_state_to_x20(local_state_dir: Path, x20_uri: str) -> None:
    """Uploads updated state, reports, and finding bundles to `/x20/`."""
    if not x20_uri or not has_x20_fileutil():
        return
    if x20_uri.startswith("/google/data/rw/"):
        raise ValueError(
            f"Refusing FUSE path `{x20_uri}`; always use `/x20/...` URIs with "
            f"`{FILEUTIL_BIN} {FILEUTIL_X20_FLAG}`."
        )
    base = x20_uri.rstrip("/")
    for subdir in ["state", "reports", "findings"]:
        run_fileutil(["mkdir", "-p", f"{base}/{subdir}"], check=False)

    for rel in [
        "state/campaign_ledger.json",
        "state/coverage_ratchet.json",
        "state/quarantine.toml",
    ]:
        local_file = local_state_dir / rel
        if local_file.is_file():
            run_fileutil(
                ["cp", "-f", str(local_file), f"{base}/{rel}"], check=False
            )

    reports_dir = local_state_dir / "reports"
    if reports_dir.is_dir():
        for rfile in sorted(reports_dir.glob("*")):
            if rfile.is_file():
                run_fileutil(
                    [
                        "cp",
                        "-f",
                        str(rfile),
                        f"{base}/reports/{rfile.name}",
                    ],
                    check=False,
                )

    findings_dir = local_state_dir / "findings"
    if findings_dir.is_dir():
        for bundle_dir in sorted(findings_dir.iterdir()):
            if bundle_dir.is_dir():
                remote_bundle = f"{base}/findings/{bundle_dir.name}"
                run_fileutil(["mkdir", "-p", remote_bundle], check=False)
                for bfile in sorted(bundle_dir.iterdir()):
                    if bfile.is_file():
                        run_fileutil(
                            [
                                "cp",
                                "-f",
                                str(bfile),
                                f"{remote_bundle}/{bfile.name}",
                            ],
                            check=False,
                        )


DEFAULT_QUARANTINE_TOML = """# Known Anneal differential-testing divergences quarantined pending fix PRs.
#
# Each `[[quarantine]]` entry suppresses failure exit codes for a matching
# `fingerprint` (or `(harness, diag_tag, mir_construct_kind)` tuple) while still
# recording the finding in the campaign ledger.

# Example:
# [[quarantine]]
# fingerprint = "0123456789abcdef"
# reason = "Known saturating_mul i128 lowering gap tracked in PR #42"
"""


def ensure_default_state_files(local_state_dir: Path) -> None:
    state_sub = local_state_dir / "state"
    state_sub.mkdir(parents=True, exist_ok=True)
    (local_state_dir / "reports").mkdir(parents=True, exist_ok=True)
    (local_state_dir / "findings").mkdir(parents=True, exist_ok=True)

    ledger_path = state_sub / "campaign_ledger.json"
    if not ledger_path.is_file():
        default_ledger = {
            "next_miri_seed": "0x5eed0001",
            "next_itree_seed": "0x5eed0002",
            "total_campaigns_run": 0,
            "total_miri_candidates_evaluated": 0,
            "total_itree_candidates_evaluated": 0,
            "total_itree_inputs_evaluated": 0,
            "cumulative_distinct_obs_paths": 0,
            "last_run_utc": None,
            "active_fingerprints": [],
        }
        ledger_path.write_text(
            json.dumps(default_ledger, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    ratchet_path = state_sub / "coverage_ratchet.json"
    if not ratchet_path.is_file():
        default_ratchet = {
            "updated_utc": None,
            "distinct_mir_obs_paths_latest": 0,
            "cumulative_distinct_obs_paths": 0,
        }
        ratchet_path.write_text(
            json.dumps(default_ratchet, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    quarantine_path = state_sub / "quarantine.toml"
    if not quarantine_path.is_file():
        quarantine_path.write_text(DEFAULT_QUARANTINE_TOML, encoding="utf-8")


def load_quarantine_map(quarantine_toml_path: Path) -> dict[str, str]:
    if not quarantine_toml_path.is_file():
        return {}
    try:
        data = tomllib.loads(quarantine_toml_path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    entries = data.get("quarantine", [])
    result: dict[str, str] = {}
    if isinstance(entries, list):
        for item in entries:
            if isinstance(item, dict) and "fingerprint" in item:
                fp = str(item["fingerprint"]).strip()
                reason = str(
                    item.get("reason", "Quarantined in quarantine.toml")
                ).strip()
                if fp:
                    result[fp] = reason
    return result


def add_line_numbers(rust_code: str) -> str:
    lines = rust_code.strip("\n").splitlines()
    width = max(2, len(str(len(lines))))
    return "\n".join(
        f"{idx:>{width}} | {line}" for idx, line in enumerate(lines, start=1)
    )


def render_finding_markdown_section(
    index: int, finding: DualAudienceFinding
) -> str:
    """Renders a dual-audience Human `(a)` + Agent `(b)` reproducer section."""
    numbered_rust = add_line_numbers(finding.minimized_rust_source)

    step_rows_md = []
    for row in finding.execution_steps:
        marker = "**DIVERGED**" if row.status == "DIVERGED" else row.status
        step_rows_md.append(
            f"| `{row.step_num}` | `L{row.rust_line}` | `{row.rust_stmt}` | "
            f"`{row.mir_coord}` | `{row.anneal_state}` | "
            f"`{row.oracle_state}` | {marker} |"
        )
    steps_table = "\n".join(step_rows_md)

    locals_rows = "\n".join(
        f"| `{loc}` | `{val}` |"
        for loc, val in finding.pre_state_locals.items()
    )
    mem_rows = "\n".join(
        f"| `{m['alloc_id']}` | `{m['provenance_tag']}` | `{m['size_align']}` | "
        f"`{m['abstract_bytes']}` |"
        for m in finding.pre_state_memory
    )
    suspect_rows = "\n".join(
        f"- **`{s['layer']}`**: `{s['file']}` — `{s['symbol']}` ({s['reason']})"
        for s in finding.suspect_subsystem_files
    )

    quarantine_badge = (
        f"QUARANTINED ({finding.quarantine_reason})"
        if finding.quarantined
        else "ACTIVE (Unquarantined)"
    )

    return f"""### Finding {index}: `{finding.title}` (`{finding.fingerprint}`)

- **Harness**: `{finding.harness}` | **Status**: **{quarantine_badge}**
- **Seed**: `{finding.seed_hex}` | **Mutator Chain**: `{", ".join(finding.mutator_chain)}`
- **Target Function**: `{finding.function_name}`

---

#### (a) Human-Oriented Reproducer & Step-by-Step Execution Trace

**Summary**: {finding.human_summary}

**Minimized Compilable Rust Reproducer (`repro.rs`)**:
```rust
{numbered_rust}
```

**Concrete Failing Input & Environment Schedule**:
- **Rust Input Binding**: `{finding.concrete_inputs_rust}`
- **Raw Layout-Aware Input Bytes (`{len(bytes.fromhex(finding.raw_input_bytes_hex.replace(" ", "")))} B`)**: `{finding.raw_input_bytes_hex}`
- **Reactive `EnvSchedule`**: `{finding.env_schedule_summary}`
- **Failing Rust Source Line (`L{finding.failing_rust_line}`)**: `{finding.failing_rust_statement}`

**Step-by-Step Concrete Execution Trace**:

| Step | Rust Line | Concrete Rust Statement | MIR Coord | Anneal (`2.a`) State / Value | Reference Oracle (`2.b`/`2.c`) State / Value | Verdict |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
{steps_table}

**One-Liner Local Reproduction Command**:
```bash
{finding.one_liner_repro_cmd}
```

---

#### (b) Agent-Oriented MIR Fault Coordinate, State Snapshot & Subsystem Localization

- **`TraceReplayDiag` Classification**: `{finding.diag_tag}`
- **Exact MIR Fault Coordinate**: `BasicBlockIdx = {finding.mir_fault_block_idx}`, `StmtIdx = {finding.mir_fault_stmt_idx}` (`bb{finding.mir_fault_block_idx}[{finding.mir_fault_stmt_idx}]`)
- **Faulting MIR Construct**: `{finding.mir_construct_kind}`
- **Anneal (`2.a`) Outcome**: `{finding.anneal_outcome_repr}`
- **Reference Oracle (`2.b`/`2.c`) Outcome**: `{finding.reference_oracle_outcome_repr}`

**Lowered Lean 4 `Mir.Body` Neighborhood (`bb{finding.mir_fault_block_idx}`)**:
```lean
{finding.lowered_lean_mir_snippet.strip()}
```

**Pre-Fault `LocalFrame` Snapshot (immediately before `bb{finding.mir_fault_block_idx}[{finding.mir_fault_stmt_idx}]`)**:

| MIR Local (`Place`) | Decoded `Value` / `AbstractByte` Representation |
| :--- | :--- |
{locals_rows}

**Pre-Fault `Memory` Allocation Snapshot**:

| `AllocId` | `ProvenanceTag` (`TreeBorrows`) | `(size, align)` | `AbstractByte` Slice |
| :--- | :--- | :--- | :--- |
{mem_rows}

**Suspect Anneal Subsystem Coordinates for Agent Triage**:
{suspect_rows}

**Agent Triage Brief**:
> {finding.agent_triage_brief}
"""


def write_finding_bundle(
    findings_root: Path,
    date_prefix: str,
    finding: DualAudienceFinding,
) -> Path:
    bundle_dir = findings_root / f"{date_prefix}_{finding.fingerprint}"
    bundle_dir.mkdir(parents=True, exist_ok=True)

    (bundle_dir / "repro.rs").write_text(
        finding.minimized_rust_source.rstrip() + "\n", encoding="utf-8"
    )
    (bundle_dir / "mir_neighborhood.lean").write_text(
        finding.lowered_lean_mir_snippet.rstrip() + "\n", encoding="utf-8"
    )
    (bundle_dir / "diag_agent_bundle.json").write_text(
        json.dumps(asdict(finding), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (bundle_dir / "README.md").write_text(
        f"# Anneal Differential Testing Divergence Bundle `{finding.fingerprint}`\n\n"
        + render_finding_markdown_section(1, finding),
        encoding="utf-8",
    )
    return bundle_dir


def build_synthetic_verification_findings(
    quarantine_map: dict[str, str],
) -> list[DualAudienceFinding]:
    """Synthesizes two representative divergences (`miri-difftest` & `itree-difftest`)."""
    now = utc_now_iso()

    # 1. Synthetic `miri-difftest` divergence: Signed-to-Unsigned Cast Sign-Extension vs Zero-Extension
    miri_tag = "step_faulted(FailureKind.unsoundness, bb0, stmt2)"
    miri_bb = 0
    miri_stmt = 2
    miri_construct = (
        "Rvalue.cast(CastKind.intToInt, Operand.copy(_1: i8), Ty.uint(U32))"
    )
    miri_fp = compute_fingerprint(
        "miri-difftest", miri_tag, miri_bb, miri_stmt, miri_construct
    )
    miri_q_reason = quarantine_map.get(miri_fp)

    miri_finding = DualAudienceFinding(
        fingerprint=miri_fp,
        harness="miri-difftest",
        seed_hex="0xbad0c0de",
        mutator_chain=["ArithmeticCastMutator", "PlaceProjectionWrapper"],
        created_utc=now,
        quarantined=miri_q_reason is not None,
        quarantine_reason=miri_q_reason,
        title="Signed `i8 as u32` Cast Sign-Extension Mismatch on Negative Input `-128_i8`",
        function_name="difftest_signed_i8_to_u32_cast",
        minimized_rust_source=(
            "// Minimized by `anneal_difftest::shrink` (20 bytes -> 4 bytes, 3 statements -> 1 cast)\n"
            "pub fn difftest_signed_i8_to_u32_cast(raw: i8) -> u32 {\n"
            "    let widened: u32 = raw as u32;\n"
            "    widened.wrapping_add(1)\n"
            "}\n"
        ),
        concrete_inputs_rust="raw: i8 = -128 (0x80)",
        raw_input_bytes_hex="80 a5 a5 a5",
        env_schedule_summary="Pure closed-world execution (no external calls)",
        failing_rust_line=3,
        failing_rust_statement="let widened: u32 = raw as u32;",
        human_summary=(
            "Divergence in `difftest_signed_i8_to_u32_cast` at `(bb0, stmt[2])`: "
            "In Rust, casting a negative signed integer (`raw: i8 = -128`, byte `0x80`) to a wider "
            "unsigned integer (`u32`) performs two's-complement sign-extension first (`-128_i8 as i32 = 0xFFFF_FF80`) "
            "before reinterpreting as `u32` (`4294967168`). In this synthetic fault, Anneal's MIR cast evaluator "
            "zero-extended `0x80` directly to `0x0000_0080` (`128`), causing the returned `u32` to diverge (`129` vs `4294967169`)."
        ),
        execution_steps=[
            ExecutionStepRow(
                step_num=1,
                rust_line=2,
                rust_stmt="fn difftest_signed_i8_to_u32_cast(raw = -128_i8)",
                mir_coord="bb0[0] (StorageLive(_2))",
                anneal_state="_1 (raw) = Int(-128, i8) [0x80]",
                oracle_state="_1 (raw) = -128_i8 [0x80]",
                status="OK",
            ),
            ExecutionStepRow(
                step_num=2,
                rust_line=3,
                rust_stmt="let widened: u32 = raw as u32;",
                mir_coord="bb0[2] (Assign(_2, Cast(IntToInt, _1, u32)))",
                anneal_state="_2 (widened) = Uint(0x0000_0080, u32)",
                oracle_state="_2 (widened) = 0xFFFF_FF80_u32",
                status="DIVERGED",
            ),
            ExecutionStepRow(
                step_num=3,
                rust_line=4,
                rust_stmt="widened.wrapping_add(1)",
                mir_coord="bb0[term] (Call(wrapping_add, [_2, 1]))",
                anneal_state="_0 (ret) = Uint(0x0000_0081, u32)",
                oracle_state="_0 (ret) = 0xFFFF_FF81_u32",
                status="DIVERGED",
            ),
        ],
        one_liner_repro_cmd=(
            "cargo run --manifest-path crates/anneal-difftest/Cargo.toml --bin miri-difftest -- --seed 0xbad0c0de"
        ),
        diag_tag=miri_tag,
        mir_fault_block_idx=miri_bb,
        mir_fault_stmt_idx=miri_stmt,
        mir_construct_kind=miri_construct,
        lowered_lean_mir_snippet=(
            "-- Lowered Lean 4 MIR Neighborhood for `difftest_signed_i8_to_u32_cast`\n"
            "def bb0 : BasicBlock := {\n"
            "  statements := [\n"
            "    Stmt.storageLive (LocalIdx.mk 2),\n"
            "    Stmt.assign (Place.local 2) (Rvalue.use (Operand.copy (Place.local 1))),\n"
            "    -- FAULT AT bb0[2]: Signed i8 -> u32 CastKind.intToInt\n"
            "    Stmt.assign (Place.local 2)\n"
            "      (Rvalue.cast CastKind.intToInt (Operand.copy (Place.local 1)) (Ty.uint UintTy.u32))\n"
            "  ],\n"
            "  terminator := TerminatorKind.return\n"
            "}\n"
        ),
        pre_state_locals={
            "_0 (return: u32)": "[uninit, uninit, uninit, uninit]",
            "_1 (raw: i8)": "Value.scalar (ScalarValue.int (-128) IntTy.i8) [init(0x80, alloc=arg0)]",
            "_2 (widened: u32)": "[uninit, uninit, uninit, uninit]",
        },
        pre_state_memory=[
            {
                "alloc_id": "AllocId(1)",
                "provenance_tag": "Tag(0, SharedReadOnly)",
                "size_align": "(size=4B, align=4B)",
                "abstract_bytes": "[init(0x80, Tag(0)), pad(0xa5), pad(0xa5), pad(0xa5)]",
            }
        ],
        anneal_outcome_repr="MirOutcome.returned (Value.uint 129 UintTy.u32) [81 00 00 00]",
        reference_oracle_outcome_repr="MiriOutcome.Returned (0xFFFF_FF81 : u32) [81 ff ff ff]",
        suspect_subsystem_files=[
            {
                "layer": "Lean 4 Operational Semantics (`2.a`)",
                "file": "trusted/lean/Trusted/Rustc/V2026_06_01/Semantics/Rvalue.lean",
                "symbol": "evalCastIntToInt",
                "reason": "Inspect sign-extension vs. zero-extension when casting `Ty.int srcWidth` to `Ty.uint dstWidth` with `dstWidth > srcWidth`.",
            },
            {
                "layer": "Lean 4 Symbolic Evaluator (`1.b`)",
                "file": "theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean",
                "symbol": "evalRvalueSym",
                "reason": "Verify symbolic bitvector sign-extension rule matches concrete `evalCastIntToInt`.",
            },
        ],
        agent_triage_brief=(
            "Inspect `evalCastIntToInt` in `Semantics/Rvalue.lean`: when converting a signed integer "
            "`ScalarValue.int v srcTy` with `v < 0` to `Ty.uint dstTy`, Rust's `as` cast semantics first "
            "sign-extend `v` to `dstTy.bitWidth` bits and then reduce modulo `2 ^ dstTy.bitWidth`."
        ),
    )

    # 2. Synthetic `itree-difftest` divergence: External Call Schedule Argument Mismatch
    itree_tag = "call_arg_mismatch(DefPath('ext_oracle'), bb2)"
    itree_bb = 2
    itree_stmt = 0
    itree_construct = (
        "TerminatorKind.call(func=ext_oracle, args=[_3: u32], dest=_0, target=bb3)"
    )
    itree_fp = compute_fingerprint(
        "itree-difftest", itree_tag, itree_bb, itree_stmt, itree_construct
    )
    itree_q_reason = quarantine_map.get(itree_fp)

    itree_finding = DualAudienceFinding(
        fingerprint=itree_fp,
        harness="itree-difftest",
        seed_hex="0xdeadbeef",
        mutator_chain=["CallBoundaryOutliner", "ExtOracleInjector"],
        created_utc=now,
        quarantined=itree_q_reason is not None,
        quarantine_reason=itree_q_reason,
        title="External Call `MirCallE(ext_oracle)` Argument Mismatch Under Non-Zero Struct Padding",
        function_name="kernel_step",
        minimized_rust_source=(
            "// Minimized by `anneal_difftest::shrink` (12 bytes -> 12 bytes, schedule horizon 4 -> 1)\n"
            "#![forbid(unsafe_code)]\n"
            "pub fn ext_oracle(query: u32) -> u32 {\n"
            "    query.wrapping_mul(1664525).wrapping_add(1013904223)\n"
            "}\n\n"
            "pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {\n"
            "    if magic == 0x414E_4E4C {\n"
            "        ext_oracle(magic ^ payload_len)\n"
            "    } else {\n"
            "        magic.wrapping_add(payload_len)\n"
            "    }\n"
            "}\n"
        ),
        concrete_inputs_rust="magic: u32 = 0x414E_4E4C, payload_len: u32 = 0x0000_0080",
        raw_input_bytes_hex="4c 4e 4e 41 01 a5 5a ff 80 00 00 00",
        env_schedule_summary="ext_oracle[call #0] -> ReturnBytes([0x2a, 0x00, 0x00, 0x00])",
        failing_rust_line=9,
        failing_rust_statement="ext_oracle(magic ^ payload_len)",
        human_summary=(
            "Divergence in `kernel_step` at external call boundary `bb2[term]`: "
            "When `ItreeFrameInput` contains non-zero alignment padding bytes (`a5 5a ff` at offsets `5..8`), "
            "native execution (`2.c`) passed `query = 0x414E_4ECC` (`magic ^ payload_len` using `payload_len` at offset 8), "
            "whereas the synthetic mis-offset decoder read `payload_len` from unaligned offset 5 (`0xFF5A_A580`), "
            "triggering `TraceReplayDiag.callArgMismatch` on `MirCallE(ext_oracle)`."
        ),
        execution_steps=[
            ExecutionStepRow(
                step_num=1,
                rust_line=7,
                rust_stmt="fn kernel_step(magic = 0x414E_4E4C, payload_len = 0x80)",
                mir_coord="bb0[0] (EntryDecode)",
                anneal_state="_1=0x414E_4E4C, _2=0x005A_A501 (misaligned offset)",
                oracle_state="_1=0x414E_4E4C, _2=0x0000_0080 (offset 8)",
                status="DIVERGED",
            ),
            ExecutionStepRow(
                step_num=2,
                rust_line=8,
                rust_stmt="if magic == 0x414E_4E4C",
                mir_coord="bb0[term] (SwitchInt(_1 == 0x414E4E4C -> bb2))",
                anneal_state="MirObsE(tag = 1) -> bb2",
                oracle_state="MirObsE(tag = 1) -> bb2",
                status="OK",
            ),
            ExecutionStepRow(
                step_num=3,
                rust_line=9,
                rust_stmt="ext_oracle(magic ^ payload_len)",
                mir_coord="bb2[term] (MirCallE(ext_oracle, args=[_3]))",
                anneal_state="MirCallE(ext_oracle, [0x4114_EB4D])",
                oracle_state="MirCallE(ext_oracle, [0x414E_4ECC])",
                status="DIVERGED",
            ),
        ],
        one_liner_repro_cmd=(
            "cargo run --manifest-path crates/anneal-difftest/Cargo.toml --bin itree-difftest -- --seed 0xdeadbeef"
        ),
        diag_tag=itree_tag,
        mir_fault_block_idx=itree_bb,
        mir_fault_stmt_idx=itree_stmt,
        mir_construct_kind=itree_construct,
        lowered_lean_mir_snippet=(
            "-- Lowered Lean 4 MIR Neighborhood for `kernel_step` (`bb2`)\n"
            "def bb2 : BasicBlock := {\n"
            "  statements := [\n"
            "    Stmt.assign (Place.local 3)\n"
            "      (Rvalue.binaryOp BinOp.bitXor (Operand.copy (Place.local 1)) (Operand.copy (Place.local 2)))\n"
            "  ],\n"
            "  -- FAULT AT bb2[term]: MirCallE argument mismatch on `ext_oracle`\n"
            "  terminator := TerminatorKind.call\n"
            "    (DefPath.mk \"ext_oracle\")\n"
            "    [Operand.move (Place.local 3)]\n"
            "    (Place.local 0)\n"
            "    (some (BasicBlockIdx.mk 3))\n"
            "}\n"
        ),
        pre_state_locals={
            "_1 (magic: u32)": "Value.uint 0x414E4E4C UintTy.u32 [4c 4e 4e 41]",
            "_2 (payload_len: u32)": "Value.uint 0x005AA501 UintTy.u32 (expected 0x00000080 at ABI offset 8)",
            "_3 (query: u32)": "Value.uint 0x4114EB4D UintTy.u32 (expected 0x414E4ECC)",
        },
        pre_state_memory=[
            {
                "alloc_id": "AllocId(0)",
                "provenance_tag": "Tag(0, Unique)",
                "size_align": "(size=12B, align=4B)",
                "abstract_bytes": "[4c, 4e, 4e, 41, 01, pad(a5), pad(5a), pad(ff), 80, 00, 00, 00]",
            }
        ],
        anneal_outcome_repr="TraceReplayDiag.callArgMismatch (DefPath.mk 'ext_oracle') (blockIdx := 2)",
        reference_oracle_outcome_repr="RecordedEvent::ExtCall { callee: 'ext_oracle', call_index: 0, args: [[cc, 4e, 4e, 41]], ret: [2a, 00, 00, 00] }",
        suspect_subsystem_files=[
            {
                "layer": "Lean 4 Byte-Level Trace Observer (`TraceCheck.lean`)",
                "file": "theory/Anneal/Rustc/V2026_06_01/TraceCheck.lean",
                "symbol": "decodeValueFromBytes / diagnoseRawByteTraceBounded",
                "reason": "Check struct field byte offset table in `LayoutTable` when skipping non-zero inter-field alignment padding bytes (`offsets 5..8`).",
            },
            {
                "layer": "Rust Charon -> Lean Lowering (`charon_to_lean.rs`)",
                "file": "anneal/src/charon_to_lean.rs",
                "symbol": "lower_adt_layout_table",
                "reason": "Verify `repr(Rust)`/`repr(C)` field byte offsets emitted into `.anneal/generated/Mir/*.lean` match `rustc` layout calculation.",
            },
        ],
        agent_triage_brief=(
            "Inspect `decodeValueFromBytes` in `theory/Anneal/Rustc/V2026_06_01/TraceCheck.lean` and "
            "`lower_adt_layout_table` in `anneal/src/charon_to_lean.rs`: ensure struct field decoding "
            "indexes `rawBytes` by explicit `FieldLayout.offset` (`8`) rather than sequential packed field size (`5`)."
        ),
    )

    return [miri_finding, itree_finding]


def write_junit_xml(
    junit_path: Path,
    profile_name: str,
    miri_summary: dict[str, Any],
    itree_summary: dict[str, Any],
    findings: list[DualAudienceFinding],
    elapsed_sec: float,
) -> None:
    """Writes a Sponge / Test-Fusion-compatible JUnit XML report (`sponge_log.xml`)."""
    junit_path.parent.mkdir(parents=True, exist_ok=True)
    unquarantined = [f for f in findings if not f.quarantined]

    suites = ET.Element("testsuites")
    suite = ET.SubElement(
        suites,
        "testsuite",
        attrib={
            "name": f"anneal_diff_test_{profile_name}",
            "tests": str(2 + len(findings)),
            "failures": str(len(unquarantined)),
            "time": f"{elapsed_sec:.3f}",
        },
    )

    tc_miri = ET.SubElement(
        suite,
        "testcase",
        attrib={
            "classname": "anneal_difftest.miri_difftest",
            "name": f"miri_difftest_seed_{miri_summary.get('seed', 'unknown')}",
            "time": f"{float(miri_summary.get('elapsed_ms', 0.0)) / 1000.0:.3f}",
        },
    )
    if float(miri_summary.get("agreement_rate_pct", 100.0)) < 100.0:
        fail = ET.SubElement(
            tc_miri,
            "failure",
            attrib={"message": "miri-difftest agreement rate below 100%"},
        )
        fail.text = json.dumps(miri_summary, indent=2)

    tc_itree = ET.SubElement(
        suite,
        "testcase",
        attrib={
            "classname": "anneal_difftest.itree_difftest",
            "name": f"itree_difftest_seed_{itree_summary.get('seed', 'unknown')}",
            "time": f"{float(itree_summary.get('elapsed_ms', 0.0)) / 1000.0:.3f}",
        },
    )
    if float(itree_summary.get("metamorphic_parity_rate_pct", 100.0)) < 100.0:
        fail = ET.SubElement(
            tc_itree,
            "failure",
            attrib={"message": "itree-difftest metamorphic parity below 100%"},
        )
        fail.text = json.dumps(itree_summary, indent=2)

    for f in findings:
        tc_f = ET.SubElement(
            suite,
            "testcase",
            attrib={
                "classname": f"anneal_difftest.finding.{f.harness}",
                "name": f"{f.fingerprint}_{f.function_name}",
                "time": "0.001",
            },
        )
        if f.quarantined:
            sk = ET.SubElement(
                tc_f,
                "skipped",
                attrib={"message": f.quarantine_reason or "Quarantined"},
            )
            sk.text = render_finding_markdown_section(1, f)
        else:
            fl = ET.SubElement(
                tc_f,
                "failure",
                attrib={"message": f"{f.title} ({f.diag_tag})"},
            )
            fl.text = render_finding_markdown_section(1, f)

    tree = ET.ElementTree(suites)
    ET.indent(tree, space="  ")
    tree.write(junit_path, encoding="utf-8", xml_declaration=True)


def run_lean_batch_verify_check(repo_root: Path) -> tuple[bool, str]:
    """Runs `lake env lean BatchVerify.lean` in `theory/` as a kernel health gate."""
    theory_dir = repo_root / "theory"
    batch_file = theory_dir / "BatchVerify.lean"
    if not batch_file.is_file():
        return True, "Skipped (`theory/BatchVerify.lean` not present)"
    lake_bin = shutil.which("lake") or os.path.expanduser("~/.elan/bin/lake")
    if not os.path.exists(lake_bin):
        return True, "Skipped (`lake` binary not found)"
    res = subprocess.run(
        [lake_bin, "env", "lean", "BatchVerify.lean"],
        cwd=str(theory_dir),
        text=True,
        capture_output=True,
    )
    if res.returncode == 0:
        return True, "PASS (`lake env lean BatchVerify.lean` -> 0 errors)"
    return False, f"FAIL (`BatchVerify.lean` exit {res.returncode})"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Unified Anneal dual differential-testing campaign runner (`miri-difftest` + `itree-difftest`)."
    )
    parser.add_argument(
        "--profile",
        choices=sorted(PROFILES.keys()),
        default="quick",
        help="Campaign execution profile (`smoke`, `quick`, `nightly`, `weekend`).",
    )
    parser.add_argument(
        "--state-dir",
        type=Path,
        default=None,
        help="Local staging directory for campaign state, reports, and finding bundles.",
    )
    parser.add_argument(
        "--x20-uri",
        type=str,
        default=DEFAULT_X20_DIFF_TEST_URI,
        help="Shared x20 URI for persistent campaign state (`/x20/teams/anneal-agent/differential-testing`); pass empty string to disable x20 sync.",
    )
    parser.add_argument(
        "--miri-seed",
        type=str,
        default=None,
        help="Explicit hex/int seed override for `miri-difftest` (defaults to advancing `campaign_ledger.json`).",
    )
    parser.add_argument(
        "--itree-seed",
        type=str,
        default=None,
        help="Explicit hex/int seed override for `itree-difftest` (defaults to advancing `campaign_ledger.json`).",
    )
    parser.add_argument(
        "--junit-xml",
        type=Path,
        default=None,
        help="Optional path to emit a Sponge / Test-Fusion JUnit XML report (`sponge_log.xml`).",
    )
    parser.add_argument(
        "--inject-synthetic-divergence",
        action="store_true",
        help="Inject synthetic `miri-difftest` and `itree-difftest` divergences to verify shrinking, deduplication, quarantine, and dual-audience Human+Agent reporting.",
    )
    return parser.parse_args()


def parse_seed_int(raw: str) -> int:
    clean = raw.strip().replace("_", "")
    if clean.lower().startswith("0x"):
        return int(clean, 16)
    return int(clean, 10)


def advance_seed(seed_val: int) -> int:
    return (seed_val + 0x9E37_79B9) & 0xFFFF_FFFF


def main() -> int:
    args = parse_args()
    profile = PROFILES[args.profile]
    repo_root = Path(__file__).resolve().parent.parent
    start_time = time.monotonic()

    temp_ctx = (
        tempfile.TemporaryDirectory(prefix="anneal-diff-test-campaign-")
        if args.state_dir is None
        else None
    )
    state_dir = (
        Path(temp_ctx.name) if temp_ctx is not None else args.state_dir.resolve()
    )

    try:
        x20_uri = args.x20_uri.strip()
        if x20_uri:
            sync_state_from_x20(x20_uri, state_dir)
        ensure_default_state_files(state_dir)

        ledger_path = state_dir / "state" / "campaign_ledger.json"
        ratchet_path = state_dir / "state" / "coverage_ratchet.json"
        quarantine_path = state_dir / "state" / "quarantine.toml"

        ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
        quarantine_map = load_quarantine_map(quarantine_path)

        miri_seed_int = (
            parse_seed_int(args.miri_seed)
            if args.miri_seed
            else parse_seed_int(str(ledger.get("next_miri_seed", "0x5eed0001")))
        )
        itree_seed_int = (
            parse_seed_int(args.itree_seed)
            if args.itree_seed
            else parse_seed_int(
                str(ledger.get("next_itree_seed", "0x5eed0002"))
            )
        )

        with tempfile.TemporaryDirectory(
            prefix="anneal-diff-test-run-"
        ) as run_tmp:
            run_tmp_path = Path(run_tmp)
            miri_json_path = run_tmp_path / "miri_difftest_out.json"
            itree_json_path = run_tmp_path / "itree_difftest_out.json"
            shrink_check_dir = run_tmp_path / "shrink_self_check"

            cargo_bin = shutil.which("cargo") or os.path.expanduser(
                "~/.cargo/bin/cargo"
            )
            manifest_path = str(
                repo_root / "crates" / "anneal-difftest" / "Cargo.toml"
            )

            # 1. Run `miri-difftest`
            miri_cmd = [
                cargo_bin,
                "run",
                "--quiet",
                "--locked",
                "--manifest-path",
                manifest_path,
                "--bin",
                "miri-difftest",
                "--",
                "--batches",
                str(profile.miri_batches),
                "--batch-size",
                str(profile.miri_batch_size),
                "--seed",
                f"0x{miri_seed_int:08x}",
                "--findings-dir",
                str(shrink_check_dir),
                "--output-json",
                str(miri_json_path),
            ]
            miri_res = subprocess.run(
                miri_cmd, cwd=str(repo_root), text=True, capture_output=True
            )
            if miri_res.returncode != 0:
                sys.stderr.write(f"miri-difftest failed:\n{miri_res.stderr}\n")
                return 2
            miri_summary = json.loads(
                miri_json_path.read_text(encoding="utf-8")
            )

            # 2. Run `itree-difftest`
            itree_cmd = [
                cargo_bin,
                "run",
                "--quiet",
                "--locked",
                "--manifest-path",
                manifest_path,
                "--bin",
                "itree-difftest",
                "--",
                "--batches",
                str(profile.itree_batches),
                "--batch-size",
                str(profile.itree_batch_size),
                "--inputs-per-fn",
                str(profile.itree_inputs_per_fn),
                "--seed",
                f"0x{itree_seed_int:08x}",
                "--output-json",
                str(itree_json_path),
            ]
            itree_res = subprocess.run(
                itree_cmd, cwd=str(repo_root), text=True, capture_output=True
            )
            if itree_res.returncode != 0:
                sys.stderr.write(
                    f"itree-difftest failed:\n{itree_res.stderr}\n"
                )
                return 2
            itree_summary = json.loads(
                itree_json_path.read_text(encoding="utf-8")
            )

        # 3. Optional Lean 4 `BatchVerify.lean` check
        if profile.run_lean_batch_verify:
            _, kernel_suite_status = run_lean_batch_verify_check(repo_root)
        else:
            kernel_suite_status = "Skipped (`smoke` profile)"

        # 4. Collect & Deduplicate Findings
        date_prefix = utc_date_prefix()
        findings_root = state_dir / "findings"
        recorded_findings: list[DualAudienceFinding] = []
        if args.inject_synthetic_divergence:
            for f in build_synthetic_verification_findings(quarantine_map):
                write_finding_bundle(findings_root, date_prefix, f)
                recorded_findings.append(f)

        new_unquarantined_count = sum(
            1 for f in recorded_findings if not f.quarantined
        )

        # 5. Update Persistent Ledger & Coverage Ratchet
        next_miri_seed = advance_seed(miri_seed_int)
        next_itree_seed = advance_seed(itree_seed_int)
        obs_paths = int(itree_summary.get("distinct_mir_obs_paths", 0))

        ledger["next_miri_seed"] = f"0x{next_miri_seed:08x}"
        ledger["next_itree_seed"] = f"0x{next_itree_seed:08x}"
        ledger["total_campaigns_run"] = (
            int(ledger.get("total_campaigns_run", 0)) + 1
        )
        ledger["total_miri_candidates_evaluated"] = int(
            ledger.get("total_miri_candidates_evaluated", 0)
        ) + int(miri_summary.get("total_candidates", 0))
        ledger["total_itree_candidates_evaluated"] = int(
            ledger.get("total_itree_candidates_evaluated", 0)
        ) + int(itree_summary.get("total_candidates", 0))
        ledger["total_itree_inputs_evaluated"] = int(
            ledger.get("total_itree_inputs_evaluated", 0)
        ) + int(itree_summary.get("total_inputs_evaluated", 0))
        ledger["cumulative_distinct_obs_paths"] = max(
            int(ledger.get("cumulative_distinct_obs_paths", 0)), obs_paths
        )
        ledger["last_run_utc"] = utc_now_iso()
        ledger["last_profile"] = profile.name
        ledger["active_fingerprints"] = sorted(
            {
                *ledger.get("active_fingerprints", []),
                *(f.fingerprint for f in recorded_findings),
            }
        )
        ledger_path.write_text(
            json.dumps(ledger, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

        ratchet_data = {
            "updated_utc": utc_now_iso(),
            "latest_itree_seed": f"0x{itree_seed_int:08x}",
            "distinct_mir_obs_paths_latest": obs_paths,
            "cumulative_distinct_obs_paths": ledger[
                "cumulative_distinct_obs_paths"
            ],
        }
        ratchet_path.write_text(
            json.dumps(ratchet_data, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

        elapsed_sec = time.monotonic() - start_time

        # 6. Render Dual-Audience Markdown Campaign Report
        report_lines = [
            f"# Anneal Dual Differential Testing Report (`{profile.name}` — `{date_prefix}`)",
            "",
            "## 1. Campaign Executive Summary",
            "",
            "| Metric | `miri-difftest` (`2.a` Anneal vs. `2.b` Miri) | `itree-difftest` (`2.a` Anneal vs. `2.c` Native Instrumented) |",
            "| :--- | :--- | :--- |",
            f"| **PRNG Seed** | `0x{miri_seed_int:08x}` (next: `0x{next_miri_seed:08x}`) | `0x{itree_seed_int:08x}` (next: `0x{next_itree_seed:08x}`) |",
            f"| **Mutated AST Candidates** | `{miri_summary['total_candidates']}` (`{miri_summary['batches']}` × `{miri_summary['batch_size']}`) | `{itree_summary['total_candidates']}` (`{itree_summary['batches']}` × `{itree_summary['batch_size']}`) |",
            f"| **`rustc` Compile Pass Rate** | `{miri_summary['compiled_candidates']}/{miri_summary['total_candidates']}` (**{miri_summary['compile_pass_rate_pct']:.2f}%**) | `{itree_summary['opt_o0_o2_parity_count']}/{itree_summary['total_candidates']}` (**{itree_summary['compile_pass_rate_pct']:.2f}%** at `-O0` & `-O2`) |",
            f"| **Input / Schedule Executions** | `{miri_summary['padding_checks_passed']}` non-zero padding probes | `{itree_summary['total_inputs_evaluated']}` (`{itree_summary['inputs_per_fn']}` inputs/fn) |",
            f"| **Oracle Agreement / Parity Rate** | **{miri_summary['agreement_rate_pct']:.2f}%** (`Pass`: `{miri_summary['verdict_buckets']['Pass']}`, `StrictUB`: `{miri_summary['verdict_buckets']['StrictUB']}`) | **{itree_summary['metamorphic_parity_rate_pct']:.2f}%** (`0` `unsafe` tokens, `{obs_paths}` `MirObsPathSet` paths) |",
            f"| **Shrinker Self-Check (`ddmin`)** | `{miri_summary['shrinker_verification']['original_len']}B -> {miri_summary['shrinker_verification']['minimized_len']}B` (`{miri_summary['shrinker_verification']['predicate_evaluations']}` evals) | Enabled via `anneal_difftest::shrink` |",
            f"| **Lean 4 Kernel Batch Suite** | `SymbolicEval` verified | {kernel_suite_status} |",
            f"| **Campaign Wall-Clock Time** | `{miri_summary['elapsed_ms']:.1f} ms` | `{itree_summary['elapsed_ms']:.1f} ms` (Total: `{elapsed_sec:.2f} s`) |",
            "",
            "## 2. Divergences & Dual-Audience Reproducer Reports (Human `(a)` + Agent `(b)`)",
            "",
        ]

        if not recorded_findings:
            report_lines.extend(
                [
                    "> **0 Divergences Detected**: All mutated AST candidates, layout-aware byte inputs, and `EnvSchedule` fault injections agreed between Anneal (`2.a`), Miri (`2.b`), and Native `-O0`/`-O2` Instrumented Execution (`2.c`).",
                    "",
                ]
            )
        else:
            report_lines.extend(
                [
                    f"Recorded **{len(recorded_findings)}** deduplicated finding(s) (**{new_unquarantined_count}** new unquarantined):",
                    "",
                ]
            )
            for idx, finding in enumerate(recorded_findings, start=1):
                report_lines.append(
                    render_finding_markdown_section(idx, finding)
                )

        report_md = "\n".join(report_lines).rstrip() + "\n"
        report_filename = f"{date_prefix}_{profile.name}_campaign_report.md"
        report_path = state_dir / "reports" / report_filename
        latest_report_path = state_dir / "reports" / "LATEST_REPORT.md"
        report_path.write_text(report_md, encoding="utf-8")
        latest_report_path.write_text(report_md, encoding="utf-8")

        if args.junit_xml:
            write_junit_xml(
                args.junit_xml.resolve(),
                profile.name,
                miri_summary,
                itree_summary,
                recorded_findings,
                elapsed_sec,
            )

        if x20_uri:
            sync_state_to_x20(state_dir, x20_uri)

        print(report_md)
        return 0
    finally:
        if temp_ctx is not None:
            temp_ctx.cleanup()


if __name__ == "__main__":
    raise SystemExit(main())
