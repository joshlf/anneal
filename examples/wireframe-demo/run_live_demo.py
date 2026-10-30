#!/usr/bin/env python3
"""Automated live demonstration driver for `examples/wireframe-demo/`.

Executes all four Anneal human-and-agent user journeys in an isolated temporary
copy of `examples/wireframe-demo` (leaving the git working tree untouched),
records wall-clock latency for each verification step, and runs a `rustc -O`
throughput microbenchmark comparing `checksum_frame_safe` and
`checksum_frame_fast`.
"""

from __future__ import annotations

import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import time


REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
DEMO_CRATE_DIR = REPO_ROOT / "examples" / "wireframe-demo"


def banner(title: str) -> None:
    print(f"\n{'=' * 78}\n{title}\n{'=' * 78}", flush=True)


def run_checked(
    cmd: list[str],
    *,
    cwd: pathlib.Path,
    env: dict[str, str],
    expect_success: bool = True,
    label: str,
) -> tuple[subprocess.CompletedProcess[str], float]:
    t0 = time.monotonic()
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        text=True,
        capture_output=True,
    )
    dt = time.monotonic() - t0
    if expect_success and proc.returncode != 0:
        raise RuntimeError(
            f"[{label}] expected exit 0, got {proc.returncode} ({dt:.2f}s)\n"
            f"--- stdout ---\n{proc.stdout}\n--- stderr ---\n{proc.stderr}"
        )
    if not expect_success and proc.returncode == 0:
        raise RuntimeError(
            f"[{label}] expected non-zero exit, but command succeeded ({dt:.2f}s)\n"
            f"--- stdout ---\n{proc.stdout}"
        )
    status_word = "PASS" if expect_success else "REJECTED AS EXPECTED"
    print(f"  -> {label}: {status_word} ({dt:.2f}s)", flush=True)
    return proc, dt


def ensure_binaries(env: dict[str, str]) -> tuple[pathlib.Path, pathlib.Path]:
    target_dir = pathlib.Path(
        env.get("CARGO_TARGET_DIR", str(REPO_ROOT / "target"))
    )
    cli_bin = target_dir / "debug" / "cargo-anneal"
    wrap_bin = target_dir / "debug" / "anneal-rustc-capture"
    if not (cli_bin.is_file() and wrap_bin.is_file()):
        print("Building cargo-anneal and anneal-rustc-capture...", flush=True)
        subprocess.run(
            [
                "cargo",
                "build",
                "--locked",
                "-p",
                "anneal-rustc-capture",
                "-p",
                "cargo-anneal",
            ],
            cwd=str(REPO_ROOT),
            env=env,
            check=True,
        )
    return cli_bin, wrap_bin


def replace_once(text: str, old: str, new: str, label: str) -> str:
    if old not in text:
        raise RuntimeError(f"Missing expected snippet for {label}:\n{old}")
    return text.replace(old, new, 1)


def run_throughput_benchmark(env: dict[str, str], tmp_root: pathlib.Path) -> None:
    bench_rs = tmp_root / "bench_checksum.rs"
    bench_bin = tmp_root / "bench_checksum"
    bench_rs.write_text(
        """use std::hint::black_box;
use std::time::Instant;

#[inline(never)]
pub fn checksum_frame_safe(frame: &[u8; 8]) -> u32 {
    let mut i: usize = 0;
    let mut acc: u32 = 0;
    while black_box(i) < 4 {
        let hi = frame[i * 2] as u32;
        let lo = frame[i * 2 + 1] as u32;
        acc = acc + ((hi << 8) | lo);
        i = i + 1;
    }
    acc
}

#[inline(never)]
pub fn checksum_frame_fast(frame: &[u8; 8]) -> u32 {
    let words: [u16; 4] = unsafe { core::mem::transmute::<[u8; 8], [u16; 4]>(*frame) };
    let w0 = (((words[0] & 0x00ff) << 8) | (words[0] >> 8)) as u32;
    let w1 = (((words[1] & 0x00ff) << 8) | (words[1] >> 8)) as u32;
    let w2 = (((words[2] & 0x00ff) << 8) | (words[2] >> 8)) as u32;
    let w3 = (((words[3] & 0x00ff) << 8) | (words[3] >> 8)) as u32;
    w0 + w1 + w2 + w3
}

fn main() {
    let iters: u64 = 50_000_000;
    let sample = [0x12u8, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0];
    assert_eq!(checksum_frame_safe(&sample), checksum_frame_fast(&sample));

    let t0 = Instant::now();
    let mut sink_safe: u64 = 0;
    for _ in 0..iters {
        sink_safe = sink_safe.wrapping_add(checksum_frame_safe(black_box(&sample)) as u64);
    }
    let dt_safe = t0.elapsed().as_secs_f64();

    let t1 = Instant::now();
    let mut sink_fast: u64 = 0;
    for _ in 0..iters {
        sink_fast = sink_fast.wrapping_add(checksum_frame_fast(black_box(&sample)) as u64);
    }
    let dt_fast = t1.elapsed().as_secs_f64();

    assert_eq!(sink_safe, sink_fast);
    let speedup = if dt_fast > 0.0 { dt_safe / dt_fast } else { 1.0 };
    println!(
        "  -> Release throughput ({iters} frames): safe={dt_safe:.3}s, fast={dt_fast:.3}s, speedup={speedup:.2}x (checksum sink={sink_fast})"
    );
}
""",
        encoding="utf-8",
    )
    subprocess.run(
        ["rustc", "-C", "opt-level=3", str(bench_rs), "-o", str(bench_bin)],
        env=env,
        check=True,
    )
    out = subprocess.run(
        [str(bench_bin)], env=env, text=True, capture_output=True, check=True
    )
    print(out.stdout.rstrip(), flush=True)


def main() -> int:
    env = os.environ.copy()
    home = pathlib.Path.home()
    extra_paths = [
        str(home / ".elan" / "bin"),
        str(home / ".cargo" / "bin"),
    ]
    cli_bin, wrap_bin = ensure_binaries(env)
    extra_paths.insert(0, str(cli_bin.parent))
    env["PATH"] = os.pathsep.join(extra_paths + [env.get("PATH", "")])
    env["ANNEAL_RUSTC_CAPTURE"] = str(wrap_bin)
    env["ANNEAL_REPO_ROOT"] = str(REPO_ROOT)

    with tempfile.TemporaryDirectory(prefix="anneal-wireframe-live-") as tmp_str:
        tmp_root = pathlib.Path(tmp_str)
        work_crate = tmp_root / "wireframe-demo"
        shutil.copytree(
            DEMO_CRATE_DIR / "src", work_crate / "src"
        )
        shutil.copytree(
            DEMO_CRATE_DIR / "anneal", work_crate / "anneal"
        )
        cargo_toml = (DEMO_CRATE_DIR / "Cargo.toml").read_text(encoding="utf-8")
        cargo_toml = cargo_toml.replace(
            "../../crates/anneal-spec",
            str(REPO_ROOT / "crates" / "anneal-spec"),
        )
        (work_crate / "Cargo.toml").write_text(cargo_toml, encoding="utf-8")
        lib_rs_path = work_crate / "src" / "lib.rs"
        clean_lib_rs = lib_rs_path.read_text(encoding="utf-8")

        # ---------------------------------------------------------------------
        # Journey 1: Bootstrap Verification on Safe Rust (plus warm Lake cache)
        # ---------------------------------------------------------------------
        banner("Journey 1: Bootstrapping Anneal on wireframe_demo")
        proc, _ = run_checked(
            [str(cli_bin), "verify"],
            cwd=work_crate,
            env=env,
            expect_success=True,
            label="Full crate bootstrap verify + CrateVerify TrustedBoundary replay",
        )
        for line in proc.stdout.strip().splitlines():
            print(f"     {line}")

        # ---------------------------------------------------------------------
        # Journey 2: Find an Existing `unsafe` UB Bug & Verify the Repair
        # ---------------------------------------------------------------------
        banner("Journey 2: Catching & Refuting an `unsafe` Transmute Bit-Validity Bug")
        buggy_j2_rs = replace_once(
            clean_lib_rs,
            "    if raw[1] > 1 {\n        return 0;\n    }\n",
            "",
            "Journey 2 remove raw[1] > 1 guard",
        )
        lib_rs_path.write_text(buggy_j2_rs, encoding="utf-8")
        run_checked(
            [str(cli_bin), "verify", "--item", "decode_wire_header"],
            cwd=work_crate,
            env=env,
            expect_success=False,
            label="Reject buggy decode_wire_header (unguarded bool transmute)",
        )

        # Kernel-check an explicit `¬ claim.holds` UB counterexample on the captured buggy MIR!
        decode_proof_path = (
            work_crate
            / "anneal"
            / "proofs"
            / "Proof"
            / "WireframeDemo"
            / "decode_wire_header.lean"
        )
        clean_decode_proof = decode_proof_path.read_text(encoding="utf-8")
        refute_lean = (
            work_crate
            / ".anneal"
            / "generated"
            / "RefuteBuggyDecode.lean"
        )
        refute_lean.write_text(
            """import Trusted
import Anneal
import Obligations.WireframeDemo.decode_wire_header

namespace RefuteBuggyDecode
open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

def badRawArg : List Value :=
  [.aggregate 0 [
    .scalar { bits := 1, sizeBytes := 1 },
    .scalar { bits := 2, sizeBytes := 1 },
    .scalar { bits := 4, sizeBytes := 1 },
    .scalar { bits := 0, sizeBytes := 1 }
  ]]

theorem buggy_decode_wire_header_refuted :
    ¬ Obligations.WireframeDemo.decode_wire_header.claim.holds :=
  refuteClaimByBoundedUB
    Obligations.WireframeDemo.decode_wire_header.claim
    32
    badRawArg
    trivial
    rfl

end RefuteBuggyDecode
""",
            encoding="utf-8",
        )
        run_checked(
            ["lake", "env", "lean", str(refute_lean)],
            cwd=work_crate / ".anneal",
            env=env,
            expect_success=True,
            label="Kernel-checked UB counterexample `¬ claim.holds` at raw=[1, 2, 4, 0]",
        )
        refute_lean.unlink()

        lib_rs_path.write_text(clean_lib_rs, encoding="utf-8")
        decode_proof_path.write_text(clean_decode_proof, encoding="utf-8")
        run_checked(
            [str(cli_bin), "verify", "--item", "decode_wire_header"],
            cwd=work_crate,
            env=env,
            expect_success=True,
            label="Verify repaired decode_wire_header across all 2^32 headers",
        )

        # ---------------------------------------------------------------------
        # Journey 3A & 3B: Keeping the Code Author & Reviewer in Check
        # ---------------------------------------------------------------------
        banner("Journey 3A: Agent Authoring Under Locked Specs (--allow-impl-edit)")
        stub_j3a_rs = replace_once(
            clean_lib_rs,
            """    if requested <= max_window {
        requested
    } else {
        max_window
    }""",
            """    let _ = (
        requested,
        max_window,
    );
    0""",
            "Journey 3A stub clamp_payload_window",
        )
        lib_rs_path.write_text(stub_j3a_rs, encoding="utf-8")
        run_checked(
            [str(cli_bin), "extract"],
            cwd=work_crate,
            env=env,
            expect_success=True,
            label="Extract stubbed clamp_payload_window",
        )
        run_checked(
            [
                str(cli_bin),
                "lock-specs",
                "--from-units",
                "--allow-impl-edit",
                "clamp_payload_window",
            ],
            cwd=work_crate,
            env=env,
            expect_success=True,
            label="Lock specs with --allow-impl-edit clamp_payload_window",
        )

        # Attempt 1: Agent tampers with the `#[anneal_spec::spec]` ensures clause!
        tampered_spec_rs = replace_once(
            clean_lib_rs,
            "    ensures: |ref ret| *ret <= max_window && *ret <= requested && (*ret == requested || *ret == max_window),",
            "    ensures: |ref ret| *ret <= max_window,",
            "Journey 3A tamper spec",
        )
        lib_rs_path.write_text(tampered_spec_rs, encoding="utf-8")
        run_checked(
            [str(cli_bin), "agent-verify", "--item", "clamp_payload_window"],
            cwd=work_crate,
            env=env,
            expect_success=False,
            label="Block agent tampering with locked #[anneal_spec::spec]",
        )

        # Attempt 2: Agent leaves spec intact, but writes buggy implementation (`max_window`).
        buggy_j3a_rs = replace_once(
            clean_lib_rs,
            """    if requested <= max_window {
        requested
    } else {
        max_window
    }""",
            """    let _ = (
        requested,
        max_window,
    );
    max_window""",
            "Journey 3A buggy impl",
        )
        lib_rs_path.write_text(buggy_j3a_rs, encoding="utf-8")
        run_checked(
            [str(cli_bin), "agent-verify", "--item", "clamp_payload_window"],
            cwd=work_crate,
            env=env,
            expect_success=False,
            label="Reject buggy clamp_payload_window implementation under locked spec",
        )

        # Attempt 3: Agent writes valid implementation -> passes locked agent-verify!
        lib_rs_path.write_text(clean_lib_rs, encoding="utf-8")
        run_checked(
            [str(cli_bin), "agent-verify", "--item", "clamp_payload_window"],
            cwd=work_crate,
            env=env,
            expect_success=True,
            label="Accept sound clamp_payload_window implementation under locked spec",
        )

        banner("Journey 3B: Agent Reviewing Human Code via refineSafeSpec & NonVacuousPre")
        human_shortcut_rs = replace_once(
            clean_lib_rs,
            "    (flags_byte & 1) != 0",
            "    unsafe { core::mem::transmute::<u8, bool>(flags_byte) }",
            "Journey 3B human transmute shortcut",
        )
        lib_rs_path.write_text(human_shortcut_rs, encoding="utf-8")
        run_checked(
            [str(cli_bin), "verify", "--item", "parse_compression_flag"],
            cwd=work_crate,
            env=env,
            expect_success=False,
            label="Review agent rejects human `unsafe { transmute }` behind requires (refineSafeSpec)",
        )
        lib_rs_path.write_text(clean_lib_rs, encoding="utf-8")
        run_checked(
            [str(cli_bin), "verify", "--item", "parse_compression_flag"],
            cwd=work_crate,
            env=env,
            expect_success=True,
            label="Review agent verifies safe `(flags_byte & 1) != 0` across all 256 u8 inputs",
        )

        # ---------------------------------------------------------------------
        # Journey 4: Iterative Verified `safe -> unsafe` Optimization
        # ---------------------------------------------------------------------
        banner("Journey 4: Iterative Verified `safe -> unsafe` Checksum Optimization")
        run_checked(
            [str(cli_bin), "extract"],
            cwd=work_crate,
            env=env,
            expect_success=True,
            label="Extract baseline crate with frozen checksum_frame_safe",
        )
        run_checked(
            [
                str(cli_bin),
                "lock-specs",
                "--from-units",
                "--allow-impl-edit",
                "checksum_frame_fast",
            ],
            cwd=work_crate,
            env=env,
            expect_success=True,
            label="Freeze checksum_frame_safe MIR as StatefulEquivItemSpec",
        )

        # Iteration 1: Little-endian word load without lane byte-swap!
        iter1_buggy_fast_rs = replace_once(
            clean_lib_rs,
            """    let w0 = (((words[0] & 0x00ff) << 8) | (words[0] >> 8)) as u32;
    let w1 = (((words[1] & 0x00ff) << 8) | (words[1] >> 8)) as u32;
    let w2 = (((words[2] & 0x00ff) << 8) | (words[2] >> 8)) as u32;
    let w3 = (((words[3] & 0x00ff) << 8) | (words[3] >> 8)) as u32;""",
            """    let w0 = words[0] as u32;
    let w1 = words[1] as u32;
    let w2 = words[2] as u32;
    let w3 = words[3] as u32;""",
            "Journey 4 Iteration 1 little-endian bug",
        )
        lib_rs_path.write_text(iter1_buggy_fast_rs, encoding="utf-8")
        run_checked(
            [str(cli_bin), "agent-verify", "--item", "checksum_frame_fast"],
            cwd=work_crate,
            env=env,
            expect_success=False,
            label="Iteration 1 (`--item checksum_frame_fast`): reject unswapped little-endian lanes",
        )

        # Iteration 2: Byte-swapped word lanes -> behavioral equivalence across all 2^64 frames!
        lib_rs_path.write_text(clean_lib_rs, encoding="utf-8")
        run_checked(
            [str(cli_bin), "agent-verify", "--item", "checksum_frame_fast"],
            cwd=work_crate,
            env=env,
            expect_success=True,
            label="Iteration 2 (`--item checksum_frame_fast`): prove StatefulEquivVerificationResult",
        )
        final_proc, _ = run_checked(
            [str(cli_bin), "agent-verify"],
            cwd=work_crate,
            env=env,
            expect_success=True,
            label="Full-crate locked agent-verify + CrateVerify TrustedBoundary replay",
        )
        for line in final_proc.stdout.strip().splitlines():
            print(f"     {line}")

        run_throughput_benchmark(env, tmp_root)

    print("\nAll four Anneal user journeys completed and verified cleanly.", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
