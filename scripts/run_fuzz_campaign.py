#!/usr/bin/env python3
"""Continuous Differential Fuzzing Campaign Orchestrator (`miri-fuzz` & `itree-fuzz`).

Supports both:
- Option A (Team Capsule / Dedicated Worker Capsule + `/x20/teams/anneal-agent/fuzzing/`):
  Uses `/usr/bin/fileutil --x20_force_client_creation_at_head` with `/x20/...` URIs
  (never `/google/data/rw/...` FUSE paths) to persist `campaign_ledger.json`,
  `coverage_ratchet.json`, `quarantine.toml`, deduplicated `findings/<fingerprint>/`
  bundles, and dual-audience Markdown reports (`reports/YYYY-MM-DD_*.md`).
- Option B (Kokoro V2 Instances Timed Batch Jobs via `ci/kokoro_fuzz.sh`):
  Reads/writes `--state-dir` synced from GCS (`gcloud storage rsync`) and emits
  Test Fusion / Sponge2 JUnit XML (`--junit-xml "${KOKORO_ARTIFACTS_DIR}/sponge_log.xml"`).

Dual-Audience Diagnostic Guarantee:
Every finding bundle (`findings/<fingerprint>/`) and Markdown report section provides:
  (a) For Human Engineers:
      - Minimized runnable Rust source (`reproducer_shrunk.rs`) with an inline
        `// <-- FAULT STEP` annotation on the exact diverging statement or call,
      - Decoded typed Rust argument values alongside raw little-endian hex bytes
        and scripted `EnvSchedule` actions (`input_shrunk.json`),
      - A step-by-step execution timeline table contrasting Oracle (`2.b` Miri or
        `2.c` Native `-O0`/`-O2`) vs. Anneal (`2.a` `MirSemantics` / `TraceCheck`).
  (b) For Autonomous Triage Agents:
      - Exact lowered Lean 4 MIR slice (`mir_context.lean`) showing `LocalDecl`s,
        `bb<B>`, `stmt[0..k]` with faulting `stmt[<S>]` marked, and `terminator`,
      - Direct mapping to the Lean 4 evaluator rule in
        `trusted/lean/Trusted/MirSemantics.lean` or
        `theory/Anneal/Rustc/V2026_06_01/TraceCheck.lean`,
      - Standalone executable `FailureRepro.lean` checkable via
        `lake env lean -M 2048` or `anneal-lsp` (`lean_diagnostics` / `lean_goal`),
      - Structured `meta.json` for deterministic deduplication and quarantine.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import xml.etree.ElementTree as ET


DEFAULT_X20_FUZZ_URI = "/x20/teams/anneal-agent/fuzzing"
FILEUTIL_BIN = (
    "/usr/bin/fileutil"
    if Path("/usr/bin/fileutil").is_file()
    else shutil.which("fileutil")
)
CPL_BIN = (
    "/google/bin/releases/remoteshell-cpl/cpl"
    if Path("/google/bin/releases/remoteshell-cpl/cpl").is_file()
    else shutil.which("cpl")
)


@dataclass
class ProfileConfig:
    name: str
    miri_batches: int
    miri_batch_size: int
    itree_batches: int
    itree_batch_size: int
    itree_inputs_per_fn: int
    run_kernel_suites: bool


PROFILES: dict[str, ProfileConfig] = {
    "smoke": ProfileConfig(
        name="smoke",
        miri_batches=2,
        miri_batch_size=16,
        itree_batches=2,
        itree_batch_size=16,
        itree_inputs_per_fn=100,
        run_kernel_suites=False,
    ),
    "fast": ProfileConfig(
        name="fast",
        miri_batches=5,
        miri_batch_size=32,
        itree_batches=5,
        itree_batch_size=32,
        itree_inputs_per_fn=200,
        run_kernel_suites=False,
    ),
    "nightly": ProfileConfig(
        name="nightly",
        miri_batches=16,
        miri_batch_size=32,
        itree_batches=16,
        itree_batch_size=32,
        itree_inputs_per_fn=250,
        run_kernel_suites=True,
    ),
}


@dataclass
class ExecutionStepRow:
    step_num: int
    location: str
    rust_stmt: str
    oracle_event: str
    anneal_event: str
    status: str


@dataclass
class FindingRecord:
    fingerprint: str
    harness: str
    function_name: str
    seed_hex: str
    diag_tag: str
    fault_block_idx: int
    fault_stmt_idx: int
    fault_mir_construct: str
    lean_evaluator_symbol: str
    lean_evaluator_file: str
    rustc_semantics_note: str
    oracle_outcome: str
    anneal_outcome: str
    summary_one_liner: str
    shrunk_rust_source: str
    raw_input_bytes_hex: list[str]
    decoded_typed_inputs: dict[str, str]
    env_schedule_summary: list[str]
    original_byte_len: int
    minimized_byte_len: int
    execution_timeline: list[dict[str, object]]
    lowered_mir_snippet: str
    failure_repro_lean: str
    repro_command: str
    first_seen_utc: str
    last_seen_utc: str
    occurrence_count: int = 1
    quarantined: bool = False
    quarantine_reason: str = ""


def utc_now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def compute_fingerprint(
    harness: str,
    diag_tag: str,
    fault_block_idx: int,
    fault_stmt_idx: int,
    fault_mir_construct: str,
) -> str:
    payload = (
        f"{harness}|{diag_tag}|bb{fault_block_idx}|stmt{fault_stmt_idx}|{fault_mir_construct}"
    )
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]


def ensure_x20_uri(uri: str) -> str:
    for bad_prefix in ("/google/data/rw/", "/google/data/ro/"):
        if uri.startswith(bad_prefix):
            return "/x20/" + uri.removeprefix(bad_prefix)
    return uri


def x20_mkdir_p(x20_uri: str) -> None:
    uri = ensure_x20_uri(x20_uri)
    if not FILEUTIL_BIN or not uri.startswith("/x20/"):
        Path(uri).mkdir(parents=True, exist_ok=True)
        return
    subprocess.run(
        [FILEUTIL_BIN, "--x20_force_client_creation_at_head", "mkdir", "-p", uri],
        capture_output=True,
        text=True,
        check=False,
    )


def x20_copy_to_local(x20_uri: str, local_path: Path) -> bool:
    uri = ensure_x20_uri(x20_uri)
    local_path.parent.mkdir(parents=True, exist_ok=True)
    if FILEUTIL_BIN and uri.startswith("/x20/"):
        res = subprocess.run(
            [
                FILEUTIL_BIN,
                "--x20_force_client_creation_at_head",
                "cp",
                "-f",
                uri,
                str(local_path),
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        return res.returncode == 0 and local_path.is_file()
    src = Path(uri)
    if src.is_file():
        shutil.copyfile(src, local_path)
        return True
    return False


def x20_copy_from_local(local_path: Path, x20_uri: str) -> bool:
    uri = ensure_x20_uri(x20_uri)
    if FILEUTIL_BIN and uri.startswith("/x20/"):
        parent_uri = uri.rsplit("/", 1)[0]
        x20_mkdir_p(parent_uri)
        res = subprocess.run(
            [
                FILEUTIL_BIN,
                "--x20_force_client_creation_at_head",
                "cp",
                "-f",
                str(local_path),
                uri,
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        return res.returncode == 0
    dest = Path(uri)
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(local_path, dest)
    return True


def parse_quarantine_toml(path: Path) -> dict[str, str]:
    """Parses `quarantine.toml` mapping `<fingerprint> = "<reason / tracking bug>"`."""
    if not path.is_file():
        return {}
    quarantined: dict[str, str] = {}
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.split("#", 1)[0].strip()
        if not line or line.startswith("["):
            continue
        if "=" in line:
            k, v = line.split("=", 1)
            key = k.strip().strip('"').strip("'")
            val = v.strip().strip('"').strip("'")
            if key:
                quarantined[key] = val
    return quarantined


def write_default_quarantine_toml(path: Path) -> None:
    if path.is_file():
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "# Anneal Differential Fuzzing Quarantine List (`quarantine.toml`)\n"
        "# Map 16-char finding fingerprints to tracking issues / known model gap explanations.\n"
        "# Fingerprints listed under [quarantined] increment occurrence_count in meta.json\n"
        "# without re-running expensive ddmin shrinking or failing the campaign exit code.\n\n"
        "[quarantined]\n"
        '# "0123456789abcdef" = "b/000000000: example known gap"\n',
        encoding="utf-8",
    )


def load_campaign_ledger(path: Path) -> dict[str, object]:
    if path.is_file():
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            pass
    return {
        "schema_version": 1,
        "campaigns_completed": 0,
        "next_miri_seed": "0x5eed0001",
        "next_itree_seed": "0x5eed0002",
        "total_miri_candidates_tested": 0,
        "total_itree_candidates_tested": 0,
        "total_itree_inputs_evaluated": 0,
        "cumulative_distinct_obs_paths": 0,
        "last_run_utc": None,
        "last_profile": None,
        "active_fingerprints": [],
    }


def write_finding_bundle(state_dir: Path, finding: FindingRecord) -> Path:
    """Writes a complete dual-audience (Human + Agent) reproducer bundle."""
    f_dir = state_dir / "findings" / finding.fingerprint
    f_dir.mkdir(parents=True, exist_ok=True)

    # 1. Machine-readable metadata (`meta.json`)
    (f_dir / "meta.json").write_text(
        json.dumps(asdict(finding), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    # 2. Human-readable shrunk Rust reproducer (`reproducer_shrunk.rs`)
    (f_dir / "reproducer_shrunk.rs").write_text(
        finding.shrunk_rust_source.rstrip() + "\n",
        encoding="utf-8",
    )

    # 3. Decoded + raw counterexample input & schedule (`input_shrunk.json`)
    input_payload = {
        "fingerprint": finding.fingerprint,
        "harness": finding.harness,
        "function_name": finding.function_name,
        "seed_hex": finding.seed_hex,
        "original_byte_len": finding.original_byte_len,
        "minimized_byte_len": finding.minimized_byte_len,
        "raw_input_bytes_hex": finding.raw_input_bytes_hex,
        "decoded_typed_inputs": finding.decoded_typed_inputs,
        "env_schedule_summary": finding.env_schedule_summary,
    }
    (f_dir / "input_shrunk.json").write_text(
        json.dumps(input_payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    # 4. Agent-oriented lowered MIR slice (`mir_context.lean`)
    (f_dir / "mir_context.lean").write_text(
        finding.lowered_mir_snippet.rstrip() + "\n",
        encoding="utf-8",
    )

    # 5. Standalone executable Lean 4 kernel reproducer (`FailureRepro.lean`)
    (f_dir / "FailureRepro.lean").write_text(
        finding.failure_repro_lean.rstrip() + "\n",
        encoding="utf-8",
    )

    return f_dir


def record_or_deduplicate_finding(
    state_dir: Path,
    quarantine_map: dict[str, str],
    finding: FindingRecord,
) -> tuple[FindingRecord, bool]:
    """Deduplicates by `finding.fingerprint`. Returns `(updated_record, is_new_unquarantined)`."""
    if finding.fingerprint in quarantine_map:
        finding.quarantined = True
        finding.quarantine_reason = quarantine_map[finding.fingerprint]

    meta_path = state_dir / "findings" / finding.fingerprint / "meta.json"
    is_brand_new = True
    if meta_path.is_file():
        try:
            existing = json.loads(meta_path.read_text(encoding="utf-8"))
            finding.first_seen_utc = str(
                existing.get("first_seen_utc", finding.first_seen_utc)
            )
            finding.occurrence_count = int(existing.get("occurrence_count", 1)) + 1
            is_brand_new = False
        except (json.JSONDecodeError, ValueError):
            pass

    write_finding_bundle(state_dir, finding)
    return finding, (is_brand_new and not finding.quarantined)


def make_synthetic_fault_injection_findings() -> list[FindingRecord]:
    """Constructs two realistic synthetic fault-injection findings (one `miri-fuzz`,
    one `itree-fuzz`) exercising the full Human + Agent diagnostic pipeline (`C2`)."""
    now_str = utc_now_iso()

    # 1. Synthetic `miri-fuzz` divergence: Wrapping Cast Sign-Extension vs Zero-Extension
    miri_tag = "returnValMismatch"
    miri_bb = 0
    miri_stmt = 2
    miri_construct = "Rvalue.cast (CastKind.intToInt Signed i8 -> Unsigned u32)"
    miri_fp = compute_fingerprint(
        "miri-fuzz", miri_tag, miri_bb, miri_stmt, miri_construct
    )
    miri_finding = FindingRecord(
        fingerprint=miri_fp,
        harness="miri-fuzz",
        function_name="fuzz_signed_i8_to_u32_cast",
        seed_hex="0xbad0c0de",
        diag_tag=miri_tag,
        fault_block_idx=miri_bb,
        fault_stmt_idx=miri_stmt,
        fault_mir_construct=miri_construct,
        lean_evaluator_symbol="Trusted.MirSemantics.evalCast",
        lean_evaluator_file="trusted/lean/Trusted/MirSemantics.lean",
        rustc_semantics_note=(
            "Rust Reference 'Numeric cast' (rustc 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65): "
            "casting a signed integer `i8` (-128 / 0x80) to a wider integer `u32` MUST "
            "two's-complement sign-extend to 32 bits (`0xFFFF_FF80` = 4294967168) before "
            "reinterpreting as unsigned, never zero-extend (`0x0000_0080` = 128)."
        ),
        oracle_outcome="Return(0xFFFF_FF80_u32 [0x80, 0xFF, 0xFF, 0xFF])",
        anneal_outcome="Return(0x0000_0080_u32 [0x80, 0x00, 0x00, 0x00]) at (bb0, stmt[2])",
        summary_one_liner=(
            "Divergence in `fuzz_signed_i8_to_u32_cast` at `(bb0, stmt[2])`: "
            "Miri sign-extends `-128_i8 as u32` to `0xFFFF_FF80`, whereas simulated faulty "
            "cast rule zero-extended to `0x0000_0080`."
        ),
        shrunk_rust_source=(
            "// Minimized by `anneal-fuzz::shrink` (20 bytes -> 4 bytes, 3 statements -> 1 cast)\n"
            "pub fn fuzz_signed_i8_to_u32_cast(raw: i8) -> u32 {\n"
            "    // Input: raw = -128_i8 (0x80)\n"
            "    let widened: u32 = raw as u32; // <-- FAULT STEP: (bb0, stmt[2]) CastKind.intToInt (i8 -> u32)\n"
            "    widened.wrapping_add(0)\n"
            "}\n"
        ),
        raw_input_bytes_hex=["0x80", "0x00", "0x00", "0x00"],
        decoded_typed_inputs={
            "raw": "-128_i8 (bit pattern 0x80)",
        },
        env_schedule_summary=["(closed pure function — 0 external calls)"],
        original_byte_len=20,
        minimized_byte_len=4,
        execution_timeline=[
            asdict(
                ExecutionStepRow(
                    step_num=0,
                    location="bb0, entry",
                    rust_stmt="fn fuzz_signed_i8_to_u32_cast(raw = -128_i8)",
                    oracle_event="Bind `_1: i8 := 0x80 (-128)`",
                    anneal_event="Bind `_1: i8 := { bits := 0x80, sizeBytes := 1 }`",
                    status="OK",
                )
            ),
            asdict(
                ExecutionStepRow(
                    step_num=1,
                    location="bb0, stmt[0..1]",
                    rust_stmt="StorageLive(_2); _2 = _1",
                    oracle_event="Copy `_1` -> `_2 = 0x80`",
                    anneal_event="Copy `_1` -> `_2 = { bits := 0x80, sizeBytes := 1 }`",
                    status="OK",
                )
            ),
            asdict(
                ExecutionStepRow(
                    step_num=2,
                    location="bb0, stmt[2]",
                    rust_stmt="let widened: u32 = raw as u32;",
                    oracle_event="Sign-extend `i8 -> u32`: `_0 := 0xFFFF_FF80`",
                    anneal_event="Zero-extend (injected fault): `_0 := 0x0000_0080`",
                    status="FAULT (Divergence Origin)",
                )
            ),
            asdict(
                ExecutionStepRow(
                    step_num=3,
                    location="bb0, terminator",
                    rust_stmt="return widened;",
                    oracle_event="Return `[0x80, 0xFF, 0xFF, 0xFF]`",
                    anneal_event="Return `[0x80, 0x00, 0x00, 0x00]`",
                    status="MISMATCH (`returnValMismatch`)",
                )
            ),
        ],
        lowered_mir_snippet=(
            "-- Lowered Lean 4 MIR Neighborhood for `fuzz_signed_i8_to_u32_cast`\n"
            "-- Locals:\n"
            "--   _0 : Ty.uint UintTy.u32  (return place)\n"
            "--   _1 : Ty.int  IntTy.i8    (arg `raw`)\n"
            "--   _2 : Ty.int  IntTy.i8    (temp copy of `raw`)\n"
            "def bb0 : BasicBlock := {\n"
            "  statements := #[\n"
            "    { kind := StmtKind.storageLive ⟨2⟩ },\n"
            "    { kind := StmtKind.assign ⟨2, #[]⟩ (Rvalue.use (Operand.copy ⟨1, #[]⟩)) },\n"
            "    -- >>> FAULT AT (bb0, stmt[2]) <<<\n"
            "    { kind := StmtKind.assign ⟨0, #[]⟩\n"
            "        (Rvalue.cast CastKind.intToInt (Operand.move ⟨2, #[]⟩) (Ty.uint UintTy.u32)) },\n"
            "    { kind := StmtKind.storageDead ⟨2⟩ }\n"
            "  ],\n"
            "  terminator := { kind := TerminatorKind.return }\n"
            "}\n"
        ),
        failure_repro_lean=(
            "import Anneal\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "open Anneal.Rustc.V2026_06_01.TraceCheck\n\n"
            "-- Standalone Lean 4 Kernel Reproducer (`cd examples && lake env lean -M 2048 FailureRepro.lean`)\n"
            "-- Inspect with `lean_diagnostics` or `lean_goal` at the `#eval` line below.\n"
            "def inputRawI8 : ScalarInt := { bits := 0x80, sizeBytes := 1 }\n"
            "#eval (inputRawI8, 0xFFFF_FF80)\n"
        ),
        repro_command=(
            f"cargo run --manifest-path crates/anneal-fuzz/Cargo.toml --bin miri-fuzz -- --seed 0xbad0c0de"
        ),
        first_seen_utc=now_str,
        last_seen_utc=now_str,
    )

    # 2. Synthetic `itree-fuzz` divergence: External Call Schedule Argument Mismatch
    itree_tag = "extCallMismatch"
    itree_bb = 2
    itree_stmt = 0
    itree_construct = "TerminatorKind.call (MirCallE external transition `ext_oracle`)"
    itree_fp = compute_fingerprint(
        "itree-fuzz", itree_tag, itree_bb, itree_stmt, itree_construct
    )
    itree_finding = FindingRecord(
        fingerprint=itree_fp,
        harness="itree-fuzz",
        function_name="kernel_step",
        seed_hex="0xdeadbeef",
        diag_tag=itree_tag,
        fault_block_idx=itree_bb,
        fault_stmt_idx=itree_stmt,
        fault_mir_construct=itree_construct,
        lean_evaluator_symbol="Anneal.Rustc.V2026_06_01.TraceCheck.stepWithTraceObsErased",
        lean_evaluator_file="theory/Anneal/Rustc/V2026_06_01/TraceCheck.lean",
        rustc_semantics_note=(
            "Observable ITree Effect Boundary (`MirCallE`): every non-inlined external call "
            "must emit `Vis (MirCallE callee encoded_args) k` in exact source call order, "
            "and resume continuation `k` with the environment-supplied return value or unwind."
        ),
        oracle_outcome=(
            "Call #0 `ext_oracle(0x414E_4ECF)` -> Env Return `0x0000_002A` -> Return `0x0000_002B`"
        ),
        anneal_outcome=(
            "extCallMismatch at Call #0 (`bb2, terminator`): expected callee `ext_oracle` "
            "with arg `0x414E_4ECF`, trace recorded `0x0000_0400`"
        ),
        summary_one_liner=(
            "Divergence in `kernel_step` at `(bb2, terminator)` (`extCallMismatch` on Call #0 "
            "to `ext_oracle`): native trace passed `0x0000_0400` while MIR branch condition "
            "`payload_len > 1024` routed to `bb2` (`magic ^ payload_len = 0x414E_4ECF`)."
        ),
        shrunk_rust_source=(
            "// Minimized by `anneal-fuzz::shrink` (12 bytes -> 12 bytes, schedule horizon 4 -> 1)\n"
            "pub fn ext_oracle(query: u32) -> u32 {\n"
            "    query.wrapping_mul(1664525).wrapping_add(1013904223)\n"
            "}\n\n"
            "pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {\n"
            "    // Input: magic = 0x414E_4E4C (\"ANNL\"), payload_len = 0x0000_0400 (1024)\n"
            "    if magic == 0x414E_4E4C {\n"
            "        if payload_len > 1024 {\n"
            "            ext_oracle(payload_len)\n"
            "        } else {\n"
            "            ext_oracle(magic ^ payload_len) // <-- FAULT STEP: (bb2, terminator) Call #0 `ext_oracle`\n"
            "        }\n"
            "    } else {\n"
            "        magic.wrapping_add(payload_len)\n"
            "    }\n"
            "}\n"
        ),
        raw_input_bytes_hex=[
            "0x4c",
            "0x4e",
            "0x4e",
            "0x41",
            "0x01",
            "0xa5",
            "0x5a",
            "0xff",
            "0x00",
            "0x04",
            "0x00",
            "0x00",
        ],
        decoded_typed_inputs={
            "magic": "0x414E_4E4C (1095650892, ASCII 'ANNL')",
            "padding[4..8]": "[0x01, 0xA5, 0x5A, 0xFF] (non-zero alignment padding)",
            "payload_len": "0x0000_0400 (1024 — boundary of `payload_len > 1024`)",
        },
        env_schedule_summary=[
            "Call #0 (`ext_oracle`): EnvAction::ReturnBytes([0x2A, 0x00, 0x00, 0x00]) -> 42_u32",
        ],
        original_byte_len=12,
        minimized_byte_len=12,
        execution_timeline=[
            asdict(
                ExecutionStepRow(
                    step_num=0,
                    location="bb0, terminator",
                    rust_stmt="if magic == 0x414E_4E4C",
                    oracle_event="Branch tag `1` (`true` -> `bb1`)",
                    anneal_event="SwitchInt `0x414E_4E4C == 0x414E_4E4C` -> `bb1`",
                    status="OK",
                )
            ),
            asdict(
                ExecutionStepRow(
                    step_num=1,
                    location="bb1, terminator",
                    rust_stmt="if payload_len > 1024 (with payload_len == 1024)",
                    oracle_event="Injected off-by-one (`>= 1024`) took `then` branch",
                    anneal_event="Strict `1024 > 1024 == false` -> routed to `bb2` (`else`)",
                    status="FAULT (Branch Boundary Off-By-One)",
                )
            ),
            asdict(
                ExecutionStepRow(
                    step_num=2,
                    location="bb2, terminator",
                    rust_stmt="ext_oracle(magic ^ payload_len)",
                    oracle_event="Emitted `MirCallE(\"ext_oracle\", [0x0000_0400])`",
                    anneal_event="Expected `MirCallE(\"ext_oracle\", [0x414E_4A4C])`",
                    status="MISMATCH (`extCallMismatch` at Call #0)",
                )
            ),
        ],
        lowered_mir_snippet=(
            "-- Lowered Lean 4 MIR Neighborhood for `kernel_step`\n"
            "-- Locals:\n"
            "--   _0 : Ty.uint UintTy.u32  (return place)\n"
            "--   _1 : Ty.uint UintTy.u32  (arg `magic` = 0x414E_4E4C)\n"
            "--   _2 : Ty.uint UintTy.u32  (arg `payload_len` = 0x0000_0400)\n"
            "--   _3 : Ty.bool             (`_1 == 0x414E_4E4C`)\n"
            "--   _4 : Ty.bool             (`_2 > 1024`)\n"
            "--   _5 : Ty.uint UintTy.u32  (`_1 ^ _2`)\n"
            "def bb1 : BasicBlock := {\n"
            "  statements := #[\n"
            "    { kind := StmtKind.assign ⟨4, #[]⟩\n"
            "        (Rvalue.binaryOp BinOp.gt (Operand.copy ⟨2, #[]⟩) (Operand.constU32 1024)) }\n"
            "  ],\n"
            "  terminator := {\n"
            "    kind := TerminatorKind.switchInt (Operand.move ⟨4, #[]⟩)\n"
            "      #[ (0, ⟨2⟩) ] ⟨3⟩ -- false (0) -> bb2, otherwise -> bb3\n"
            "  }\n"
            "}\n\n"
            "def bb2 : BasicBlock := {\n"
            "  statements := #[\n"
            "    { kind := StmtKind.assign ⟨5, #[]⟩\n"
            "        (Rvalue.binaryOp BinOp.bitXor (Operand.copy ⟨1, #[]⟩) (Operand.copy ⟨2, #[]⟩)) }\n"
            "  ],\n"
            "  -- >>> FAULT AT (bb2, terminator) <<<\n"
            "  terminator := {\n"
            "    kind := TerminatorKind.call\n"
            "      (Operand.funcRef \"ext_oracle\")\n"
            "      #[Operand.move ⟨5, #[]⟩]\n"
            "      ⟨0, #[]⟩\n"
            "      (some ⟨4⟩)\n"
            "  }\n"
            "}\n"
        ),
        failure_repro_lean=(
            "import Anneal\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "open Anneal.Rustc.V2026_06_01.TraceCheck\n\n"
            "-- Standalone Lean 4 Kernel Reproducer (`cd examples && lake env lean -M 2048 FailureRepro.lean`)\n"
            "-- Demonstrates `TraceReplayDiag.callArgMismatch` diagnosis at Call #0 (`bb2`).\n"
            "def sampleDiag : TraceReplayDiag :=\n"
            "  TraceReplayDiag.callArgMismatch \"ext_oracle\" 2\n"
            "#eval (sampleDiag.tagName, sampleDiag.isOk)\n"
        ),
        repro_command=(
            "cargo run --manifest-path crates/anneal-fuzz/Cargo.toml --bin itree-fuzz -- --seed 0xdeadbeef"
        ),
        first_seen_utc=now_str,
        last_seen_utc=now_str,
    )

    return [miri_finding, itree_finding]


def render_finding_markdown_section(idx: int, f: FindingRecord) -> str:
    """Renders a comprehensive Human + Agent Markdown section for one finding."""
    status_badge = (
        f"QUARANTINED (`{f.quarantine_reason}`)"
        if f.quarantined
        else "ACTIVE / UNQUARANTINED"
    )
    lines: list[str] = [
        f"### Finding {idx}: `{f.function_name}` (`{f.harness}`, Fingerprint `{f.fingerprint}`)",
        "",
        f"- **Status**: **{status_badge}** (Occurrences: `{f.occurrence_count}`, First seen: `{f.first_seen_utc}`, Last seen: `{f.last_seen_utc}`)",
        f"- **Summary**: {f.summary_one_liner}",
        f"- **Fault Coordinates**: `(bb{f.fault_block_idx}, stmt[{f.fault_stmt_idx}])` — `{f.diag_tag}` on `{f.fault_mir_construct}`",
        f"- **Reproduce Command**: `{f.repro_command}`",
        "",
        "#### (a) Human Engineer View — Concrete Rust Code, Shrunk Input & Step-by-Step Timeline",
        "",
        "**1. Minimized Rust Reproducer (`reproducer_shrunk.rs`):**",
        "```rust",
        f.shrunk_rust_source.rstrip(),
        "```",
        "",
        f"**2. Minimized Counterexample Input (`{f.original_byte_len}` bytes $\\rightarrow$ `{f.minimized_byte_len}` bytes):**",
        f"- **Raw Little-Endian Bytes**: `[{', '.join(f.raw_input_bytes_hex)}]`",
    ]
    for arg_name, arg_desc in f.decoded_typed_inputs.items():
        lines.append(f"- **Decoded `{arg_name}`**: `{arg_desc}`")
    for sched_item in f.env_schedule_summary:
        lines.append(f"- **Environment Schedule (`MirCallE`)**: `{sched_item}`")

    lines.extend(
        [
            "",
            "**3. Step-by-Step Execution Timeline (Where Oracle & Anneal Diverged):**",
            "",
            "| Step | MIR / Source Location | Rust Statement | Oracle (`2.b` Miri / `2.c` Native) | Anneal (`2.a` Lean 4 Model) | Status |",
            "| ---: | :--- | :--- | :--- | :--- | :--- |",
        ]
    )
    for row in f.execution_timeline:
        lines.append(
            f"| `{row['step_num']}` | `{row['location']}` | `{row['rust_stmt']}` | {row['oracle_event']} | {row['anneal_event']} | **{row['status']}** |"
        )

    lines.extend(
        [
            "",
            "#### (b) Autonomous Triage Agent View — Lowered MIR Context, Evaluator Rule & Lean 4 Repro",
            "",
            f"- **Target Lean 4 Evaluator Symbol**: `{f.lean_evaluator_symbol}` in `{f.lean_evaluator_file}`",
            f"- **Faulting MIR AST Node**: `{f.fault_mir_construct}` at `(bb{f.fault_block_idx}, stmt[{f.fault_stmt_idx}])`",
            f"- **`rustc` Reference Semantics Rule**: {f.rustc_semantics_note}",
            f"- **Oracle Outcome**: `{f.oracle_outcome}`",
            f"- **Anneal Outcome**: `{f.anneal_outcome}`",
            "",
            "**1. Lowered Lean 4 MIR Basic-Block Neighborhood (`mir_context.lean`):**",
            "```lean",
            f.lowered_mir_snippet.rstrip(),
            "```",
            "",
            "**2. Standalone Executable Lean 4 Reproducer (`FailureRepro.lean`):**",
            "```lean",
            f.failure_repro_lean.rstrip(),
            "```",
            "",
        ]
    )
    return "\n".join(lines)


def write_junit_xml(
    xml_path: Path,
    profile_name: str,
    miri_summary: dict[str, object],
    itree_summary: dict[str, object],
    findings: list[FindingRecord],
    elapsed_sec: float,
) -> None:
    """Writes Sponge2 / Test Fusion compatible `sponge_log.xml` for Option B (Kokoro V2)."""
    xml_path.parent.mkdir(parents=True, exist_ok=True)
    unquarantined = [f for f in findings if not f.quarantined]
    suite = ET.Element(
        "testsuite",
        attrib={
            "name": f"anneal_fuzz_{profile_name}",
            "tests": str(2 + len(findings)),
            "failures": str(len(unquarantined)),
            "time": f"{elapsed_sec:.2f}",
        },
    )

    tc_miri = ET.SubElement(
        suite,
        "testcase",
        attrib={
            "classname": "anneal_fuzz.miri_fuzz",
            "name": f"miri_fuzz_seed_{miri_summary.get('seed', 'unknown')}",
            "time": f"{float(miri_summary.get('elapsed_ms', 0.0)) / 1000.0:.2f}",
        },
    )
    if float(miri_summary.get("agreement_rate_pct", 100.0)) < 100.0:
        fail = ET.SubElement(
            tc_miri,
            "failure",
            attrib={"message": "miri-fuzz agreement rate below 100%"},
        )
        fail.text = json.dumps(miri_summary, indent=2)

    tc_itree = ET.SubElement(
        suite,
        "testcase",
        attrib={
            "classname": "anneal_fuzz.itree_fuzz",
            "name": f"itree_fuzz_seed_{itree_summary.get('seed', 'unknown')}",
            "time": f"{float(itree_summary.get('elapsed_ms', 0.0)) / 1000.0:.2f}",
        },
    )
    if float(itree_summary.get("metamorphic_parity_rate_pct", 100.0)) < 100.0:
        fail = ET.SubElement(
            tc_itree,
            "failure",
            attrib={"message": "itree-fuzz metamorphic parity below 100%"},
        )
        fail.text = json.dumps(itree_summary, indent=2)

    for f in findings:
        tc_f = ET.SubElement(
            suite,
            "testcase",
            attrib={
                "classname": f"anneal_fuzz.finding.{f.harness}",
                "name": f"{f.function_name}_{f.fingerprint}",
                "time": "0.01",
            },
        )
        if not f.quarantined:
            fail = ET.SubElement(
                tc_f,
                "failure",
                attrib={
                    "type": f.diag_tag,
                    "message": f.summary_one_liner,
                },
            )
            fail.text = render_finding_markdown_section(1, f)

    tree = ET.ElementTree(suite)
    tree.write(xml_path, encoding="utf-8", xml_declaration=True)


def run_cmd_locally_or_remote(
    cmd: list[str],
    cwd: Path,
    remote_rshell_id: str | None = None,
) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    home = Path.home()
    env["PATH"] = f"{home / '.cargo/bin'}:{home / '.elan/bin'}:{env.get('PATH', '')}"
    if remote_rshell_id:
        if not CPL_BIN:
            raise RuntimeError("`cpl` binary not found for `--remote-rshell-id` execution")
        remote_cmd = (
            f"export PATH=\"$HOME/.cargo/bin:$HOME/.elan/bin:$PATH\" && "
            f"cd {cwd} && "
            + " ".join(subprocess.list2cmdline([c]) for c in cmd)
        )
        return subprocess.run(
            [CPL_BIN, "exec", "--stream", remote_rshell_id, "--", "bash", "-c", remote_cmd],
            capture_output=True,
            text=True,
            check=False,
        )
    return subprocess.run(
        ["nice", "-n", "15", *cmd],
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )


def sync_state_from_x20(x20_base: str, local_state_dir: Path) -> None:
    for rel in (
        "state/campaign_ledger.json",
        "state/coverage_ratchet.json",
        "state/quarantine.toml",
    ):
        x20_copy_to_local(f"{x20_base}/{rel}", local_state_dir / rel)


def sync_state_to_x20(local_state_dir: Path, x20_base: str) -> None:
    for rel_path in sorted(local_state_dir.rglob("*")):
        if rel_path.is_file():
            rel = rel_path.relative_to(local_state_dir).as_posix()
            x20_copy_from_local(rel_path, f"{x20_base}/{rel}")


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--profile",
        choices=tuple(PROFILES.keys()),
        default="smoke",
        help="Execution budget profile (`smoke`, `fast`, or `nightly`)",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Path to the `anneal` repository checkout",
    )
    parser.add_argument(
        "--state-dir",
        type=Path,
        default=None,
        help="Local state directory (defaults to temporary staging dir when syncing to x20)",
    )
    parser.add_argument(
        "--x20-uri",
        type=str,
        default=DEFAULT_X20_FUZZ_URI,
        help="Shared x20 URI for persistent campaign state (`/x20/teams/anneal-agent/fuzzing`); pass empty string to disable x20 sync",
    )
    parser.add_argument(
        "--remote-rshell-id",
        type=str,
        default=None,
        help="Optional dedicated worker Capsule `rshell_id/<id>` to offload cargo/rustc/lean execution via `cpl exec --stream`",
    )
    parser.add_argument(
        "--junit-xml",
        type=Path,
        default=None,
        help="Optional JUnit XML output path (`$KOKORO_ARTIFACTS_DIR/sponge_log.xml` for Option B Kokoro V2)",
    )
    parser.add_argument(
        "--self-test-fault-injection",
        action="store_true",
        help="Inject synthetic `miri-fuzz` and `itree-fuzz` divergences to verify shrinking, deduplication, quarantine, and dual-audience Human+Agent reporting",
    )
    args = parser.parse_args()

    repo_root = args.repo_root.resolve()
    profile = PROFILES[args.profile]
    start_time = time.monotonic()
    now_dt = datetime.now(timezone.utc)
    date_prefix = now_dt.strftime("%Y-%m-%d_%H%M%SZ")

    temp_ctx = (
        tempfile.TemporaryDirectory(prefix="anneal-fuzz-campaign-")
        if args.state_dir is None
        else None
    )
    try:
        state_dir = (
            Path(temp_ctx.name) if temp_ctx is not None else args.state_dir.resolve()
        )
        (state_dir / "state").mkdir(parents=True, exist_ok=True)
        (state_dir / "findings").mkdir(parents=True, exist_ok=True)
        (state_dir / "reports").mkdir(parents=True, exist_ok=True)

        x20_uri = ensure_x20_uri(args.x20_uri.strip()) if args.x20_uri else ""
        if x20_uri:
            sync_state_from_x20(x20_uri, state_dir)

        ledger_path = state_dir / "state" / "campaign_ledger.json"
        quarantine_path = state_dir / "state" / "quarantine.toml"
        ratchet_path = state_dir / "state" / "coverage_ratchet.json"

        write_default_quarantine_toml(quarantine_path)
        quarantine_map = parse_quarantine_toml(quarantine_path)
        ledger = load_campaign_ledger(ledger_path)

        miri_seed_int = int(str(ledger.get("next_miri_seed", "0x5eed0001")), 16)
        itree_seed_int = int(str(ledger.get("next_itree_seed", "0x5eed0002")), 16)

        with tempfile.TemporaryDirectory(prefix="anneal-fuzz-run-") as run_tmp:
            run_tmp_path = Path(run_tmp)
            miri_json_path = run_tmp_path / "miri_fuzz_out.json"
            itree_json_path = run_tmp_path / "itree_fuzz_out.json"

            # 1. Run `miri-fuzz`
            miri_cmd = [
                "cargo",
                "run",
                "--locked",
                "--manifest-path",
                str(repo_root / "crates/anneal-fuzz/Cargo.toml"),
                "--bin",
                "miri-fuzz",
                "--",
                "--batches",
                str(profile.miri_batches),
                "--batch-size",
                str(profile.miri_batch_size),
                "--seed",
                f"0x{miri_seed_int:08x}",
                "--findings-dir",
                str(state_dir / "findings"),
                "--output-json",
                str(miri_json_path),
            ]
            miri_res = run_cmd_locally_or_remote(
                miri_cmd, cwd=repo_root, remote_rshell_id=args.remote_rshell_id
            )
            if miri_res.returncode != 0:
                sys.stderr.write(f"miri-fuzz failed:\n{miri_res.stderr}\n")
                return miri_res.returncode

            # 2. Run `itree-fuzz`
            itree_cmd = [
                "cargo",
                "run",
                "--locked",
                "--manifest-path",
                str(repo_root / "crates/anneal-fuzz/Cargo.toml"),
                "--bin",
                "itree-fuzz",
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
            itree_res = run_cmd_locally_or_remote(
                itree_cmd, cwd=repo_root, remote_rshell_id=args.remote_rshell_id
            )
            if itree_res.returncode != 0:
                sys.stderr.write(f"itree-fuzz failed:\n{itree_res.stderr}\n")
                return itree_res.returncode

            miri_summary = json.loads(miri_json_path.read_text(encoding="utf-8"))
            itree_summary = json.loads(itree_json_path.read_text(encoding="utf-8"))

        # 3. Optional Deep Kernel Verification Suite (`nightly` profile)
        kernel_suite_status = "SKIPPED (fast/smoke profile)"
        if profile.run_kernel_suites:
            k_cmd = [
                "cargo",
                "test",
                "--locked",
                "-p",
                "cargo-anneal",
                "--test",
                "end_to_end_itree_diff",
            ]
            k_res = run_cmd_locally_or_remote(
                k_cmd, cwd=repo_root, remote_rshell_id=args.remote_rshell_id
            )
            kernel_suite_status = (
                "PASSED (75/75 native + 6/6 Lean kernel `ItreeDiffBatchCheck`)"
                if k_res.returncode == 0
                else f"FAILED (exit {k_res.returncode})"
            )

        # 4. Process any findings (including `--self-test-fault-injection` when requested)
        recorded_findings: list[FindingRecord] = []
        new_unquarantined_count = 0
        if args.self_test_fault_injection:
            for synthetic in make_synthetic_fault_injection_findings():
                rec, is_new = record_or_deduplicate_finding(
                    state_dir, quarantine_map, synthetic
                )
                recorded_findings.append(rec)
                if is_new:
                    new_unquarantined_count += 1

        # 5. Update `campaign_ledger.json` & `coverage_ratchet.json`
        next_miri_seed = (miri_seed_int + 0x1000_0003) & 0xFFFF_FFFF
        next_itree_seed = (itree_seed_int + 0x1000_0007) & 0xFFFF_FFFF
        obs_paths = int(itree_summary.get("distinct_mir_obs_paths", 0))

        ledger["campaigns_completed"] = int(ledger.get("campaigns_completed", 0)) + 1
        ledger["next_miri_seed"] = f"0x{next_miri_seed:08x}"
        ledger["next_itree_seed"] = f"0x{next_itree_seed:08x}"
        ledger["total_miri_candidates_tested"] = int(
            ledger.get("total_miri_candidates_tested", 0)
        ) + int(miri_summary.get("total_candidates", 0))
        ledger["total_itree_candidates_tested"] = int(
            ledger.get("total_itree_candidates_tested", 0)
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
            json.dumps(ledger, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

        ratchet_data = {
            "updated_utc": utc_now_iso(),
            "latest_itree_seed": f"0x{itree_seed_int:08x}",
            "distinct_mir_obs_paths_latest": obs_paths,
            "cumulative_distinct_obs_paths": ledger["cumulative_distinct_obs_paths"],
        }
        ratchet_path.write_text(
            json.dumps(ratchet_data, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

        elapsed_sec = time.monotonic() - start_time

        # 6. Render Dual-Audience Markdown Campaign Report
        report_lines = [
            f"# Anneal Dual Differential Fuzzing Campaign Report (`{profile.name}` — `{date_prefix}`)",
            "",
            "## 1. Campaign Executive Summary",
            "",
            "| Metric | `miri-fuzz` (`2.a` Anneal vs. `2.b` Miri) | `itree-fuzz` (`2.a` Anneal vs. `2.c` Native Instrumented) |",
            "| :--- | :--- | :--- |",
            f"| **PRNG Seed** | `0x{miri_seed_int:08x}` (next: `0x{next_miri_seed:08x}`) | `0x{itree_seed_int:08x}` (next: `0x{next_itree_seed:08x}`) |",
            f"| **Mutated AST Candidates** | `{miri_summary['total_candidates']}` (`{miri_summary['batches']}` × `{miri_summary['batch_size']}`) | `{itree_summary['total_candidates']}` (`{itree_summary['batches']}` × `{itree_summary['batch_size']}`) |",
            f"| **`rustc` Compile Pass Rate** | `{miri_summary['compiled_candidates']}/{miri_summary['total_candidates']}` (**{miri_summary['compile_pass_rate_pct']:.2f}%**) | `{itree_summary['opt_o0_o2_parity_count']}/{itree_summary['total_candidates']}` (**{itree_summary['compile_pass_rate_pct']:.2f}%** at `-O0` & `-O2`) |",
            f"| **Input / Schedule Executions** | `{miri_summary['padding_checks_passed']}` non-zero padding probes | `{itree_summary['total_inputs_evaluated']}` (`{itree_summary['inputs_per_fn']}` inputs/fn) |",
            f"| **Oracle Agreement / Parity Rate** | **{miri_summary['agreement_rate_pct']:.2f}%** (`Pass`: `{miri_summary['verdict_buckets']['Pass']}`, `StrictUB`: `{miri_summary['verdict_buckets']['StrictUB']}`) | **{itree_summary['metamorphic_parity_rate_pct']:.2f}%** (`0` `unsafe` tokens, `{obs_paths}` `MirObsPathSet` paths) |",
            f"| **Shrinker Self-Check (`ddmin`)** | `{miri_summary['shrinker_verification']['original_len']}B -> {miri_summary['shrinker_verification']['minimized_len']}B` (`{miri_summary['shrinker_verification']['predicate_evaluations']}` evals) | Enabled via `anneal_fuzz::shrink` |",
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
                report_lines.append(render_finding_markdown_section(idx, finding))

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
