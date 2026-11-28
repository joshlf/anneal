#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Language-agnostic JSONL differential-oracle runner with IEEE-754 F64Bits and mutant checks."""

from __future__ import annotations

import argparse
import json
import pathlib
import shlex
import subprocess
import sys
import time
from typing import Any

VALID_OUTCOMES: frozenset[str] = frozenset({"returned", "unwound", "aborted", "diverged"})
F64_MASK: int = (1 << 64) - 1
F64_EXP_MASK: int = 0x7FF0000000000000
F64_FRAC_MASK: int = 0x000FFFFFFFFFFFFF
CANONICAL_F64_QNAN: int = 0x7FF8000000000000


def parse_u64_bits(raw: int | str) -> int:
    if isinstance(raw, bool):
        raise ValueError(f"Expected integer or hex string for f64_bits, got bool: {raw!r}")
    if isinstance(raw, int):
        if not (0 <= raw <= F64_MASK):
            raise ValueError(f"f64_bits out of [0, 2^64): {raw}")
        return raw
    if isinstance(raw, str):
        s = raw.strip().lower()
        val = int(s, 16) if s.startswith("0x") else int(s, 10)
        if not (0 <= val <= F64_MASK):
            raise ValueError(f"f64_bits out of [0, 2^64): {raw!r}")
        return val
    raise ValueError(f"Unsupported f64_bits representation: {raw!r}")


def is_f64_nan(bits: int) -> bool:
    return (bits & F64_EXP_MASK) == F64_EXP_MASK and (bits & F64_FRAC_MASK) != 0


def normalize_f64_bits(bits: int, *, exact_nan_bits: bool) -> int:
    if not exact_nan_bits and is_f64_nan(bits):
        return CANONICAL_F64_QNAN
    return bits


def load_jsonl_records(path: pathlib.Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for idx, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw_line.strip()
        if not line:
            continue
        obj = json.loads(line)
        if not isinstance(obj, dict) or "id" not in obj:
            raise ValueError(f"{path}:{idx}: each JSONL record must be an object with an `id` key")
        records.append(obj)
    return records


def invoke_jsonl_producer(cmd_str: str, cases_path: pathlib.Path | None) -> tuple[float, list[dict[str, Any]]]:
    argv = shlex.split(cmd_str)
    if cases_path is not None:
        argv = [str(cases_path) if tok == "{cases}" else tok for tok in argv]
        if "{cases}" not in shlex.split(cmd_str):
            argv.append(str(cases_path))
    t0 = time.monotonic()
    proc = subprocess.run(argv, capture_output=True, text=True, check=False)
    ms = round((time.monotonic() - t0) * 1000.0, 2)
    if proc.returncode != 0:
        raise RuntimeError(
            f"Producer command `{cmd_str}` exited with rc={proc.returncode}: "
            f"{proc.stderr.strip()[:400]}"
        )
    records: list[dict[str, Any]] = []
    for idx, raw_line in enumerate(proc.stdout.splitlines(), start=1):
        line = raw_line.strip()
        if not line:
            continue
        obj = json.loads(line)
        if not isinstance(obj, dict) or "id" not in obj:
            raise ValueError(f"Producer `{cmd_str}` stdout line {idx}: missing `id` key")
        records.append(obj)
    return ms, records


def compare_single_record(
    model_rec: dict[str, Any],
    oracle_rec: dict[str, Any],
    *,
    exact_nan_bits: bool,
) -> list[str]:
    diffs: list[str] = []
    m_out = model_rec.get("outcome")
    o_out = oracle_rec.get("outcome")
    if m_out not in VALID_OUTCOMES:
        diffs.append(f"invalid model outcome: {m_out!r}")
    if o_out not in VALID_OUTCOMES:
        diffs.append(f"invalid oracle outcome: {o_out!r}")
    if m_out != o_out:
        diffs.append(f"outcome mismatch: model={m_out!r} vs oracle={o_out!r}")
        return diffs

    if "f64_bits" in model_rec or "f64_bits" in oracle_rec:
        if "f64_bits" not in model_rec or "f64_bits" not in oracle_rec:
            diffs.append("missing f64_bits on one side")
        else:
            mb = normalize_f64_bits(parse_u64_bits(model_rec["f64_bits"]), exact_nan_bits=exact_nan_bits)
            ob = normalize_f64_bits(parse_u64_bits(oracle_rec["f64_bits"]), exact_nan_bits=exact_nan_bits)
            if mb != ob:
                diffs.append(f"f64_bits mismatch: model=0x{mb:016x} vs oracle=0x{ob:016x}")

    for field in ("int_val", "bool_val", "str_utf16", "bytes_hex", "error_tag"):
        if field in model_rec or field in oracle_rec:
            mv = model_rec.get(field)
            ov = oracle_rec.get(field)
            if mv != ov:
                diffs.append(f"{field} mismatch: model={mv!r} vs oracle={ov!r}")

    return diffs


def compare_record_sets(
    model_records: list[dict[str, Any]],
    oracle_records: list[dict[str, Any]],
    *,
    exact_nan_bits: bool,
) -> dict[str, Any]:
    m_map = {str(r["id"]): r for r in model_records}
    o_map = {str(r["id"]): r for r in oracle_records}
    if len(m_map) != len(model_records):
        raise ValueError("Duplicate case `id` in model output")
    if len(o_map) != len(oracle_records):
        raise ValueError("Duplicate case `id` in oracle output")

    all_ids = sorted(set(m_map) | set(o_map))
    mismatches: list[dict[str, Any]] = []
    outcome_counts: dict[str, int] = {k: 0 for k in sorted(VALID_OUTCOMES)}

    for cid in all_ids:
        if cid not in m_map:
            mismatches.append({"id": cid, "diffs": ["missing from model output"]})
            continue
        if cid not in o_map:
            mismatches.append({"id": cid, "diffs": ["missing from oracle output"]})
            continue
        diffs = compare_single_record(m_map[cid], o_map[cid], exact_nan_bits=exact_nan_bits)
        if diffs:
            mismatches.append({"id": cid, "diffs": diffs})
        else:
            out_tag = str(m_map[cid]["outcome"])
            if out_tag in outcome_counts:
                outcome_counts[out_tag] += 1

    return {
        "total_cases": len(all_ids),
        "matched_cases": len(all_ids) - len(mismatches),
        "mismatch_count": len(mismatches),
        "mismatches": mismatches[:25],
        "outcome_counts": outcome_counts,
    }


def run_differential_suite(
    *,
    cases_jsonl: pathlib.Path | None,
    model_jsonl: pathlib.Path | None,
    oracle_jsonl: pathlib.Path | None,
    model_cmd: str | None,
    oracle_cmd: str | None,
    mutant_model_jsonls: list[pathlib.Path],
    mutant_model_cmds: list[str],
    exact_nan_bits: bool = False,
    min_cases: int = 1,
) -> tuple[int, dict[str, Any]]:
    if (model_jsonl is None) == (model_cmd is None):
        return 2, {
            "passed": False,
            "stage": "arguments",
            "error": "Specify exactly one of `--model-jsonl` or `--model-cmd`.",
        }
    if (oracle_jsonl is None) == (oracle_cmd is None):
        return 2, {
            "passed": False,
            "stage": "arguments",
            "error": "Specify exactly one of `--oracle-jsonl` or `--oracle-cmd`.",
        }

    try:
        model_ms = 0.0
        oracle_ms = 0.0
        if model_jsonl is not None:
            model_records = load_jsonl_records(model_jsonl)
        else:
            assert model_cmd is not None
            model_ms, model_records = invoke_jsonl_producer(model_cmd, cases_jsonl)

        if oracle_jsonl is not None:
            oracle_records = load_jsonl_records(oracle_jsonl)
        else:
            assert oracle_cmd is not None
            oracle_ms, oracle_records = invoke_jsonl_producer(oracle_cmd, cases_jsonl)

        primary = compare_record_sets(
            model_records, oracle_records, exact_nan_bits=exact_nan_bits
        )
    except Exception as exc:  # noqa: BLE001
        return 2, {"passed": False, "stage": "execution", "error": str(exc)}

    if primary["total_cases"] < min_cases:
        return 1, {
            "passed": False,
            "stage": "min_cases",
            "error": f"Expected >= {min_cases} differential cases, ran {primary['total_cases']}.",
            "primary": primary,
        }

    if primary["mismatch_count"] != 0:
        return 1, {
            "passed": False,
            "stage": "differential_parity",
            "model_ms": model_ms,
            "oracle_ms": oracle_ms,
            "primary": primary,
        }

    mutant_reports: list[dict[str, Any]] = []
    for mp in mutant_model_jsonls:
        mut_records = load_jsonl_records(mp)
        cmp_res = compare_record_sets(
            mut_records, oracle_records, exact_nan_bits=exact_nan_bits
        )
        killed = cmp_res["mismatch_count"] > 0
        mutant_reports.append(
            {
                "mutant": mp.name,
                "mismatch_count": cmp_res["mismatch_count"],
                "killed_as_expected": killed,
            }
        )
        if not killed:
            return 1, {
                "passed": False,
                "stage": "mutant_kill_gate",
                "accepted_mutant": str(mp),
                "mutants": mutant_reports,
            }

    for mc in mutant_model_cmds:
        _, mut_records = invoke_jsonl_producer(mc, cases_jsonl)
        cmp_res = compare_record_sets(
            mut_records, oracle_records, exact_nan_bits=exact_nan_bits
        )
        killed = cmp_res["mismatch_count"] > 0
        mutant_reports.append(
            {
                "mutant": mc,
                "mismatch_count": cmp_res["mismatch_count"],
                "killed_as_expected": killed,
            }
        )
        if not killed:
            return 1, {
                "passed": False,
                "stage": "mutant_kill_gate",
                "accepted_mutant": mc,
                "mutants": mutant_reports,
            }

    return 0, {
        "passed": True,
        "model_ms": model_ms,
        "oracle_ms": oracle_ms,
        "primary": primary,
        "mutants": mutant_reports,
    }


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--cases-jsonl", help="Input test-vector JSONL passed to producer commands.")
    ap.add_argument("--model-jsonl", help="Precomputed model output JSONL.")
    ap.add_argument("--oracle-jsonl", help="Precomputed reference-oracle output JSONL.")
    ap.add_argument("--model-cmd", help="Command producing model output JSONL on stdout.")
    ap.add_argument("--oracle-cmd", help="Command producing oracle output JSONL on stdout.")
    ap.add_argument(
        "--mutant-model-jsonl",
        action="append",
        default=[],
        help="Mutated model JSONL that must disagree with the oracle (repeatable).",
    )
    ap.add_argument(
        "--mutant-model-cmd",
        action="append",
        default=[],
        help="Mutated model command whose output must disagree with the oracle (repeatable).",
    )
    ap.add_argument(
        "--exact-nan-bits",
        action="store_true",
        help="Require bit-identical NaN payloads instead of canonical quiet-NaN equivalence.",
    )
    ap.add_argument(
        "--min-cases",
        type=int,
        default=1,
        help="Minimum number of differential test vectors required to pass.",
    )
    ap.add_argument(
        "--out-json",
        "--receipt-out",
        dest="out_json",
        help="Write full JSON differential report to this path.",
    )
    ap.add_argument("--json", action="store_true", help="Print full JSON report to stdout.")
    return ap


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    rc, report = run_differential_suite(
        cases_jsonl=pathlib.Path(args.cases_jsonl) if args.cases_jsonl else None,
        model_jsonl=pathlib.Path(args.model_jsonl) if args.model_jsonl else None,
        oracle_jsonl=pathlib.Path(args.oracle_jsonl) if args.oracle_jsonl else None,
        model_cmd=args.model_cmd,
        oracle_cmd=args.oracle_cmd,
        mutant_model_jsonls=[pathlib.Path(p) for p in args.mutant_model_jsonl],
        mutant_model_cmds=list(args.mutant_model_cmd),
        exact_nan_bits=args.exact_nan_bits,
        min_cases=args.min_cases,
    )
    if args.out_json:
        out_p = pathlib.Path(args.out_json)
        out_p.parent.mkdir(parents=True, exist_ok=True)
        out_p.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    if args.json:
        print(json.dumps(report, indent=2))
    elif report.get("passed"):
        prim = report["primary"]
        print(
            f"[PASS] diff_oracle: cases={prim['total_cases']} "
            f"outcomes={prim['outcome_counts']} "
            f"mutants_killed={len(report['mutants'])}"
        )
    else:
        err = report.get("error") or json.dumps(report, indent=2)
        print(f"[FAIL:{report.get('stage', 'diff_oracle')}] {err}", file=sys.stderr)
    return rc


if __name__ == "__main__":
    sys.exit(main())
