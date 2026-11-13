#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Scaling benchmark for the Track P fuel-free loop / `forcePureEnv` / `TypedAt` prototype.

Three benchmark families compare a *naive* proof strategy against the
prototype's *optimized* strategy on **identical theorem statements** over
universally quantified (symbolic) inputs:

* ``local_slots`` (Pillar 2): ``K`` sequential `List.set` slot updates.
  naive: ``by rfl`` (elaborator `Meta.whnf` with smart unfolding) and a
  ``simp only`` `List.set` rewrite; ablation: end-of-chain `forcePureEnv`
  projection checked by ``rfl``; optimized: step-wise `forcePureEnv` spine
  forcing (``applySlotUpdates_eq_of_forced rfl``).
* ``struct_fields`` (Pillar 3): ``K`` sequential struct-field writes over trusted
  `AbstractByte` memory.  naive: ``rfl`` and byte-list ``simp`` reduction;
  optimized: `TypedAt` field lenses (``applyFieldWrites_spec``).
* ``loop_trip`` (Pillar 1): `countUp(N)` total correctness for trip count
  ``N = K``.  naive: explicit fuel numeral (``3 * N + 3``) evaluated by ``rfl``
  or ``simp``; optimized: ``runCfgToBlock`` + ``forRangeUp_induction``.

Methodology: the prototype module is compiled once into a temporary directory
(module ``FuelFreeProtoBench.Prototype``, byte-identical source); one Lean file
per (family, variant) holds a discarded warm-up instance followed by the ``K``
instances, each wrapped in a ``#measure`` command that records elaboration
wall-clock milliseconds and thread-local heartbeats with ``Elab.async false``.
Files run through ``anneal-lean-run --mode file --concurrency 1 -- lake env lean``
in interleaved, rotating order across repetitions.  A heartbeat budget turns
blow-ups into deterministic timeouts; later (larger) ``K`` of a timed-out
variant are recorded as ``skipped`` (censored).  All scratch files live under a
``tempfile.TemporaryDirectory()``; receipts are written to ``/tmp``.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import pathlib
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from typing import Any

REPO = pathlib.Path(__file__).resolve().parent.parent
PROTO_REL = "theory/Anneal/FuelFreeLoopAndTypedAtLensPrototype.lean"
PROTO = REPO / PROTO_REL
REPORT = REPO / "PROTOTYPE_REPORT.md"
NAMESPACE = "Anneal.FuelFreeLoopAndTypedAtLensPrototype"
BENCH_MODULE = "FuelFreeProtoBench.Prototype"
KS: tuple[int, ...] = (5, 10, 20, 30)
HEARTBEAT_BUDGET = 200000
SCHEMA = "fuel-free-lens-bench/v1"
RECEIPT_DIR = pathlib.Path("/tmp/fuel_free_lens_bench")
BENCH_BEGIN = "<!-- BENCH:BEGIN -->"
BENCH_END = "<!-- BENCH:END -->"
DECISIONS = ("GO", "CONDITIONAL GO", "NO-GO")

FAMILIES: dict[str, tuple[str, ...]] = {
    "local_slots": ("naive_rfl", "naive_simp", "ablation_projection_rfl", "live_two_pass_rfl",
                    "checked_single_pass_rfl", "optimized_forcePureEnv"),
    "struct_fields": ("naive_rfl", "naive_simp", "optimized_typedAt_lens"),
    "loop_trip": ("naive_fuel_rfl", "naive_fuel_simp", "optimized_runCfgToBlock_forRangeUp"),
}

MEASURE_PRELUDE = """open Lean Elab Command in
/-- Elaborate `c`, logging wall-clock ms and thread-local heartbeats; after an
error (e.g. a deterministic heartbeat timeout) later instances are skipped. -/
elab "#measure " lbl:str c:command : command => do
  if (← getOptions).getBool `bench.skipRest false then
    logInfo m!"MEASURE label={lbl.getString} status=skipped ms=0 hb=0"
    return
  let errs0 := (← get).messages.toList.filter (fun m => m.severity matches .error) |>.length
  let h0 ← IO.getNumHeartbeats
  let t0 ← IO.monoNanosNow
  elabCommand c
  let t1 ← IO.monoNanosNow
  let h1 ← IO.getNumHeartbeats
  let errs1 := (← get).messages.toList.filter (fun m => m.severity matches .error) |>.length
  if errs1 > errs0 then
    modifyScope fun sc => { sc with opts := sc.opts.setBool `bench.skipRest true }
  let status := if errs1 > errs0 then "error" else "ok"
  logInfo m!"MEASURE label={lbl.getString} status={status} ms={(t1 - t0) / 1000000} hb={h1 - h0}"
"""

MEASURE_RE = re.compile(
    r"MEASURE label=(?P<label>\S+) status=(?P<status>ok|error|skipped) ms=(?P<ms>\d+) hb=(?P<hb>\d+)"
)
# Public-hygiene patterns (character classes keep this file itself clean).
INTERNAL_PATTERNS = (
    r"\bcp[l]-[a-z0-9]",
    r"googler[s]\.com",
    r"/hom[e]/groupagen[t]",
    r"/x2[0]/",
    r"/googl[e]/",
    r"\bc[l]/\d",
    r"\b[b]/\d",
    r"opu[s]-5\.5",
    r"gemin[i]-",
)


# ---------------------------------------------------------------------------
# Environment and commands


def tool_env(extra: dict[str, str] | None = None) -> dict[str, str]:
    """Subprocess environment with `~/.elan/bin`, `~/.cargo/bin`, `~/.local/bin` prepended."""
    env = dict(os.environ)
    home = pathlib.Path.home()
    prefix = [str(home / ".elan" / "bin"), str(home / ".cargo" / "bin"), str(home / ".local" / "bin")]
    env["PATH"] = os.pathsep.join(prefix + [env.get("PATH", "")])
    if extra:
        env.update(extra)
    return env


def lean_command(lean_args: list[str], timeout_s: int) -> list[str]:
    """Every Lean invocation is wrapped in `anneal-lean-run --mode file --concurrency 1`."""
    return [
        "anneal-lean-run", "--mode", "file", "--concurrency", "1", "--timeout", str(timeout_s),
        "--", "lake", "env", "lean", *lean_args,
    ]


def sha256_file(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# ---------------------------------------------------------------------------
# Benchmark obligations (one statement per (family, K); variants differ only in the proof)


def _slot_obligation(k: int) -> tuple[str, str, dict[str, Any]]:
    n = 8
    init = [f"a{i}" for i in range(n)]
    xs = [f"x{j}" for j in range(1, k + 1)]
    idx = [(3 * j) % n for j in range(1, k + 1)]
    final = list(init)
    for j, i in enumerate(idx):
        final[i] = xs[j]
    ups = "[" + ", ".join(f"({i}, {xs[j]})" for j, i in enumerate(idx)) + "]"
    binders = f"({' '.join(init + xs)} : Nat)"
    stmt = f"applySlotUpdates [{', '.join(init)}] {ups} = [{', '.join(final)}]"
    return binders, stmt, {"slots": n, "updates": k}


def _field_obligation(k: int) -> tuple[str, str, dict[str, Any]]:
    xs = [f"x{j}" for j in range(1, k + 1)]
    writes = []
    last_a, last_b = "a", "b"
    for j, x in enumerate(xs, 1):
        if j % 3 == 0:
            writes.append(f".inr {x}")
            last_b = x
        else:
            writes.append(f".inl {x}")
            last_a = x
    wl = "[" + ", ".join(writes) + "]"
    mem = "[.init a none, .init p none, .init b none]"
    binders = f"(a p b {' '.join(xs)} : UInt8)"
    stmt = (
        f"u8FieldA.readView (applyFieldWrites u8FieldA u8FieldB {wl} {mem}) = {last_a} ∧\n"
        f"      u8FieldB.readView (applyFieldWrites u8FieldA u8FieldB {wl} {mem}) = {last_b}"
    )
    return binders, stmt, {"writes": k, "write_list": wl}


def _loop_obligation(k: int) -> tuple[str, str, dict[str, Any]]:
    binders = "(x junk : Nat)"
    stmt = f"WpConverges (stepCfg countUpCfg) (countUpInit {k} x junk) (fun v => v = x + {k})"
    return binders, stmt, {"trip_count": k}


OBLIGATIONS = {
    "local_slots": _slot_obligation,
    "struct_fields": _field_obligation,
    "loop_trip": _loop_obligation,
}


def obligation(family: str, k: int) -> tuple[str, str]:
    binders, stmt, _ = OBLIGATIONS[family](k)
    return binders, stmt


def proof(family: str, variant: str, k: int) -> str:
    if family == "local_slots":
        if variant == "naive_rfl":
            return "by rfl"
        if variant == "naive_simp":
            return "by simp only [applySlotUpdates, List.foldl, List.set_cons_succ, List.set_cons_zero]"
        if variant == "ablation_projection_rfl":
            return ("eq_of_forcePureEnv (n := 8)\n"
                    "    (by simp only [length_applySlotUpdates, List.length_cons, List.length_nil]) rfl")
        if variant == "live_two_pass_rfl":
            # The live `evalPureStmtNorm` strategy: bounds-checked `Trusted.Sequence.set?`
            # followed by a full spine-forcing pass after every update.
            return "applySlotUpdates_eq_of_twoPass rfl"
        if variant == "checked_single_pass_rfl":
            # Bounds-checked single-pass `setSpineChecked?` (`= Trusted.Sequence.set?` on all inputs).
            return "applySlotUpdates_eq_of_checked rfl"
        if variant == "optimized_forcePureEnv":
            return "applySlotUpdates_eq_of_forced rfl"
    if family == "struct_fields":
        if variant == "naive_rfl":
            return "⟨rfl, rfl⟩"
        if variant == "naive_simp":
            return (
                "by simp [applyFieldWrites, u8FieldA, u8FieldB, fieldLens, writeTyped, readTyped,\n"
                "    Anneal.ByteCodec.FixedByteCodec.u8, Anneal.ByteCodec.FixedByteCodec.ofRoundTrip,\n"
                "    Trusted.Rustc.V2026_06_01.MirSemantics.writeAbstractBytesAt, sliceAbstractBytes_eq]"
            )
        if variant == "optimized_typedAt_lens":
            _, _, meta = _field_obligation(k)
            return (
                "by\n"
                "    obtain ⟨hL₁, hL₂, hI⟩ := u8Fields_lenses\n"
                f"    obtain ⟨_, h₁, h₂⟩ := applyFieldWrites_spec hL₁ hL₂ hI {meta['write_list']} _\n"
                "      (u8FieldsValid_init a p b)\n"
                "    exact ⟨h₁, h₂⟩"
            )
    if family == "loop_trip":
        if variant == "naive_fuel_rfl":
            return f"⟨3 * {k} + 3, x + {k}, rfl, rfl⟩"
        if variant == "naive_fuel_simp":
            return f"⟨3 * {k} + 3, x + {k}, by simp [evalFuel, stepCfg, countUpCfg, countUpInit], rfl⟩"
        if variant == "optimized_runCfgToBlock_forRangeUp":
            return f"""by
    have hfold : forRangeUp 0 {k} x (fun _ _ _ acc => acc + 1) = x + {k} :=
      forRangeUp_induction 0 {k} x (fun _ _ _ acc => acc + 1) (fun i acc => acc = x + i)
        (Nat.zero_le {k}) rfl (fun _ _ _ _ h => by rw [h]; rfl)
    refine StepsTo.bind_wp
      (stepsTo_of_runCfgToBlock_reached (runCfgToBlock_countUp_entry {k} x junk)) (fun s₁ hs₁ => ?_)
    subst hs₁
    refine wpConverges_forRangeUp (stepCfg countUpCfg) 0 {k} x (fun _ _ _ acc => acc + 1)
      (fun i acc s => s = countUpHeader {k} i acc) (countUpHeader {k} 0 x) (fun v => v = x + {k})
      (Nat.zero_le {k}) rfl ?_ ?_
    · intro i _ hlt a s hs
      subst hs
      exact (stepsTo_of_runCfgToBlock_reached (runCfgToBlock_countUp_iter {k} i a hlt)).mono
        (fun _ h => h)
    · intro s_exit hs
      rw [hfold] at hs
      subst hs
      exact wpConverges_of_runCfgToBlock_halted (runCfgToBlock_countUp_exit {k} (x + {k})) rfl"""
    raise ValueError(f"unknown benchmark variant {family}/{variant}")


def theorem_source(family: str, variant: str, k: int, label: str) -> str:
    binders, stmt = obligation(family, k)
    name = f"bench_{family}_{variant}_{label}"
    return f'#measure "{label}" theorem {name} {binders} :\n    {stmt} :=\n  {proof(family, variant, k)}\n'


def bench_file(family: str, variant: str, ks: tuple[int, ...]) -> str:
    parts = [
        "import Lean",
        f"import {BENCH_MODULE}",
        f"open {NAMESPACE}",
        "",
        MEASURE_PRELUDE,
        "set_option Elab.async false",
        f"set_option maxHeartbeats {HEARTBEAT_BUDGET}",
        "set_option maxRecDepth 100000",
        "",
        theorem_source(family, variant, ks[0], "warmup"),
    ]
    parts += [theorem_source(family, variant, k, f"K{k}") for k in ks]
    return "\n".join(parts)


def statement_of(src: str) -> list[str]:
    """Extract each instance's binders+statement (everything between the name and `:=`)."""
    out = []
    for m in re.finditer(r"theorem bench_\S+ (.*?) :=\n", src, re.S):
        out.append(m.group(1))
    return out


def validate_generated(ks: tuple[int, ...] = KS) -> dict[str, Any]:
    """Structural checks shared by `--dry-run` and the unit tests."""
    files = {}
    for family, variants in FAMILIES.items():
        stmts = {}
        for variant in variants:
            src = bench_file(family, variant, ks)
            files[(family, variant)] = src
            stmts[variant] = statement_of(src)
            if len(stmts[variant]) != len(ks) + 1:
                raise AssertionError(f"{family}/{variant}: expected {len(ks) + 1} instances")
            if "sorry" in src or "native_decide" in src or "admit" in src:
                raise AssertionError(f"{family}/{variant}: forbidden token in benchmark source")
        reference = stmts[variants[0]]
        for variant in variants[1:]:
            if stmts[variant] != reference:
                raise AssertionError(f"{family}: statements differ between {variants[0]} and {variant}")
        for k in ks:
            binders, stmt = obligation(family, k)
            names = re.findall(r"\b([a-z]\w*)\b", binders.split(":")[0])
            if not names or not any(re.search(rf"\b{re.escape(n)}\b", stmt) for n in names):
                raise AssertionError(f"{family}/K={k}: statement does not use its symbolic binders")
    return {"files": len(files), "families": len(FAMILIES), "ks": list(ks)}


# ---------------------------------------------------------------------------
# Running Lean


def parse_measure_output(text: str) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for m in MEASURE_RE.finditer(text):
        out[m.group("label")] = {
            "status": m.group("status"),
            "ms": int(m.group("ms")),
            "hb": int(m.group("hb")),
        }
    return out


def build_bench_olean(root: pathlib.Path, timeout_s: int = 600) -> float:
    pkg = root / BENCH_MODULE.split(".")[0]
    pkg.mkdir(parents=True, exist_ok=True)
    src = pkg / "Prototype.lean"
    shutil.copyfile(PROTO, src)
    t0 = time.perf_counter()
    res = subprocess.run(
        lean_command([f"--root={root}", "-o", str(pkg / "Prototype.olean"), str(src)], timeout_s),
        cwd=REPO, env=tool_env(), capture_output=True, text=True,
    )
    elapsed = (time.perf_counter() - t0) * 1000.0
    if res.returncode != 0 or not (pkg / "Prototype.olean").exists():
        raise RuntimeError("failed to compile the prototype module:\n" + res.stdout + res.stderr)
    return elapsed


def run_lean_file(path: pathlib.Path, olean_root: pathlib.Path, timeout_s: int) -> dict[str, Any]:
    t0 = time.perf_counter()
    res = subprocess.run(
        lean_command([str(path)], timeout_s), cwd=REPO,
        env=tool_env({"LEAN_PATH": str(olean_root)}), capture_output=True, text=True,
    )
    wall = (time.perf_counter() - t0) * 1000.0
    text = res.stdout + "\n" + res.stderr
    return {"wall_ms": wall, "measures": parse_measure_output(text), "returncode": res.returncode}


def aggregate(samples: list[dict[str, Any]]) -> dict[str, Any]:
    statuses = [s["status"] for s in samples]
    if all(s == "ok" for s in statuses):
        status = "ok"
    elif any(s == "error" for s in statuses):
        status = "timeout"
    else:
        status = "skipped"
    ok = [s for s in samples if s["status"] == "ok"]
    ms = [s["ms"] for s in ok]
    hb = [s["hb"] for s in ok]
    return {
        "status": status,
        "median_ms": statistics.median(ms) if ms else None,
        "kilo_heartbeats": round(statistics.median(hb) / 1000) if hb else None,
        "ms_samples": ms,
        "hb_samples": hb,
    }


def run_benchmark(reps: int, ks: tuple[int, ...], timeout_s: int) -> dict[str, Any]:
    validate_generated(ks)
    raw: dict[tuple[str, str, int], list[dict[str, Any]]] = {}
    file_walls: dict[tuple[str, str], list[float]] = {}
    with tempfile.TemporaryDirectory(prefix="fuel_free_lens_bench_") as td:
        tdir = pathlib.Path(td)
        olean_root = tdir / "olean"
        build_ms = build_bench_olean(olean_root)
        files = {}
        for family, variants in FAMILIES.items():
            for variant in variants:
                p = tdir / f"Bench_{family}_{variant}.lean"
                p.write_text(bench_file(family, variant, ks))
                files[(family, variant)] = p
        warm = tdir / "Warmup.lean"
        warm.write_text(f"import {BENCH_MODULE}\nexample : 1 + 1 = 2 := rfl\n")
        run_lean_file(warm, olean_root, timeout_s)  # discarded warm-up run
        fams = list(FAMILIES)
        for rep in range(reps):
            order = fams[rep % len(fams):] + fams[: rep % len(fams)]
            for family in order:
                variants = list(FAMILIES[family])
                if rep % 2 == 1:
                    variants.reverse()
                for variant in variants:
                    res = run_lean_file(files[(family, variant)], olean_root, timeout_s)
                    file_walls.setdefault((family, variant), []).append(res["wall_ms"])
                    for k in ks:
                        m = res["measures"].get(f"K{k}", {"status": "error", "ms": 0, "hb": 0})
                        raw.setdefault((family, variant, k), []).append(m)
    results = []
    for family, variants in FAMILIES.items():
        for variant in variants:
            for k in ks:
                agg = aggregate(raw[(family, variant, k)])
                results.append({"family": family, "variant": variant, "k": k, **agg})
    return {
        "schema": SCHEMA,
        "generated_at_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "prototype": PROTO_REL,
        "prototype_sha256": sha256_file(PROTO),
        "lean_toolchain": (REPO / "lean-toolchain").read_text().strip(),
        "cpu_count": os.cpu_count(),
        "ks": list(ks),
        "repetitions": reps,
        "heartbeat_budget": HEARTBEAT_BUDGET,
        "prototype_compile_ms": round(build_ms),
        "file_wall_ms_median": {
            f"{f}/{v}": round(statistics.median(w)) for (f, v), w in sorted(file_walls.items())
        },
        "results": results,
    }


# ---------------------------------------------------------------------------
# Report rendering and verification


def _fmt_cell(r: dict[str, Any]) -> str:
    if r["status"] == "ok":
        return f"{r['median_ms']:.0f} ms / {r['kilo_heartbeats']} k"
    if r["status"] == "timeout":
        return f"timeout (> {HEARTBEAT_BUDGET // 1000} M hb)"
    return "skipped (censored)"


def render_tables(receipt: dict[str, Any]) -> str:
    ks = receipt["ks"]
    by = {(r["family"], r["variant"], r["k"]): r for r in receipt["results"]}
    lines = []
    for family, variants in FAMILIES.items():
        lines.append(f"#### `{family}`")
        lines.append("")
        lines.append("| variant | " + " | ".join(f"K = {k}" for k in ks) + " |")
        lines.append("|---|" + "---|" * len(ks))
        for variant in variants:
            cells = [_fmt_cell(by[(family, variant, k)]) for k in ks]
            lines.append(f"| `{variant}` | " + " | ".join(cells) + " |")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def render_bench_section(receipt: dict[str, Any]) -> str:
    body = [
        BENCH_BEGIN,
        "",
        "Cells: median elaboration wall-clock / median elaboration kilo-heartbeats "
        f"(`#measure`, `Elab.async false`), over {receipt['repetitions']} interleaved repetitions "
        f"after a discarded warm-up; budget `maxHeartbeats {receipt['heartbeat_budget']}`.",
        "",
        render_tables(receipt),
        "<details><summary>Embedded JSON receipt (verified by <code>--verify-report</code>)</summary>",
        "",
        "```json",
        json.dumps(receipt, indent=1, sort_keys=True),
        "```",
        "",
        "</details>",
        "",
        BENCH_END,
    ]
    return "\n".join(body)


def extract_bench_section(report: str) -> str:
    if BENCH_BEGIN not in report or BENCH_END not in report:
        raise ValueError("report is missing the BENCH markers")
    return report.split(BENCH_BEGIN, 1)[1].split(BENCH_END, 1)[0]


def extract_receipt(report: str) -> dict[str, Any]:
    section = extract_bench_section(report)
    m = re.search(r"```json\n(.*?)\n```", section, re.S)
    if not m:
        raise ValueError("report is missing the embedded JSON receipt")
    return json.loads(m.group(1))


def verify_report_text(report: str, proto_sha: str | None = None) -> list[str]:
    """Return a list of problems (empty when the report is consistent)."""
    problems: list[str] = []
    try:
        receipt = extract_receipt(report)
    except (ValueError, json.JSONDecodeError) as e:
        return [str(e)]
    if receipt.get("schema") != SCHEMA:
        problems.append("receipt schema mismatch")
    if proto_sha is not None and receipt.get("prototype_sha256") != proto_sha:
        problems.append("receipt prototype_sha256 does not match the current prototype (re-run benchmarks)")
    expected = {(f, v, k) for f, vs in FAMILIES.items() for v in vs for k in receipt.get("ks", [])}
    got = {(r["family"], r["variant"], r["k"]) for r in receipt.get("results", [])}
    if tuple(receipt.get("ks", [])) != KS:
        problems.append(f"receipt ks {receipt.get('ks')} differ from {list(KS)}")
    if expected != got:
        problems.append("receipt results do not cover every (family, variant, K)")
    else:
        section = extract_bench_section(report)
        if render_tables(receipt) not in section:
            problems.append("benchmark tables drifted from the embedded receipt")
    decisions = re.findall(r"^\*\*Decision:\s*(GO|CONDITIONAL GO|NO-GO)\*\*", report, re.M)
    if len(decisions) != 1:
        problems.append("report must contain exactly one '**Decision: <GO|CONDITIONAL GO|NO-GO>**' line")
    for module in ("PureMirExec.lean", "MirLiftCore.lean", "MirLoops.lean", "SepLogicLenses.lean",
                   "ByteCodec.lean", "MirFuelFree.lean"):
        if module not in report:
            problems.append(f"Track A integration mapping does not mention {module}")
    if "### Round A0" not in report:
        problems.append("adversarial round log is missing the A0 entry")
    for pat in INTERNAL_PATTERNS:
        if re.search(pat, report):
            problems.append(f"report contains an internal string matching {pat!r}")
    if expected == got:
        for claim in derive_claims(receipt):
            if claim not in report:
                problems.append(f"report is missing measured claim: {claim}")
    return problems


def derive_claims(receipt: dict[str, Any]) -> list[str]:
    """Machine-derived one-line claims that the narrative must quote verbatim."""
    by = {(r["family"], r["variant"], r["k"]): r for r in receipt["results"]}
    claims = []
    kmax = receipt["ks"][-1]
    for family, variants in FAMILIES.items():
        opt = variants[-1]
        r = by[(family, opt, kmax)]
        if r["status"] == "ok":
            claims.append(f"`{family}/{opt}` at K = {kmax}: {r['kilo_heartbeats']} k heartbeats")
        else:
            claims.append(f"`{family}/{opt}` at K = {kmax}: {r['status']}")
    return claims


def update_report(receipt: dict[str, Any]) -> None:
    report = REPORT.read_text()
    new_section = render_bench_section(receipt)
    if BENCH_BEGIN in report and BENCH_END in report:
        pre = report.split(BENCH_BEGIN, 1)[0]
        post = report.split(BENCH_END, 1)[1]
        report = pre + new_section + post
    else:
        report = report.rstrip() + "\n\n" + new_section + "\n"
    REPORT.write_text(report)


# ---------------------------------------------------------------------------
# CLI


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dry-run", action="store_true", help="generate and validate benchmark sources only")
    ap.add_argument("--verify-report", action="store_true", help="check PROTOTYPE_REPORT.md against its receipt")
    ap.add_argument("--update-report", action="store_true", help="rewrite the report's BENCH section")
    ap.add_argument("--from-receipt", type=pathlib.Path, default=None,
                    help="with --update-report: render an existing /tmp receipt instead of re-measuring")
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--timeout", type=int, default=300, help="per-file anneal-lean-run timeout (s)")
    ap.add_argument("--ks", type=str, default=",".join(map(str, KS)))
    args = ap.parse_args(argv)
    ks = tuple(int(x) for x in args.ks.split(","))

    if args.dry_run:
        t0 = time.perf_counter()
        info = validate_generated(ks)
        with tempfile.TemporaryDirectory(prefix="fuel_free_lens_dry_") as td:
            for family, variants in FAMILIES.items():
                for variant in variants:
                    (pathlib.Path(td) / f"Bench_{family}_{variant}.lean").write_text(
                        bench_file(family, variant, ks))
            written = len(list(pathlib.Path(td).glob("*.lean")))
        cmd = " ".join(lean_command(["<file>"], args.timeout))
        print(f"dry-run OK: {written} benchmark files ({info['families']} families, K = {list(ks)}) "
              f"validated in {(time.perf_counter() - t0) * 1000:.0f} ms")
        print(f"each file would run as: LEAN_PATH=<tmp olean root> {cmd}")
        return 0

    if args.verify_report:
        problems = verify_report_text(REPORT.read_text(), sha256_file(PROTO))
        if problems:
            for p in problems:
                print(f"verify-report FAIL: {p}")
            return 1
        receipt = extract_receipt(REPORT.read_text())
        print(f"verify-report OK: {len(receipt['results'])} receipt rows match the report tables; "
              f"prototype sha256 {receipt['prototype_sha256'][:12]} matches")
        return 0

    if args.from_receipt is not None:
        if not args.update_report:
            ap.error("--from-receipt requires --update-report")
        receipt = json.loads(args.from_receipt.read_text())
        if receipt.get("prototype_sha256") != sha256_file(PROTO):
            print("warning: receipt was measured on a different prototype revision")
        update_report(receipt)
        print(f"updated {REPORT.name} from {args.from_receipt}")
        return 0

    receipt = run_benchmark(args.reps, ks, args.timeout)
    RECEIPT_DIR.mkdir(parents=True, exist_ok=True)
    out = RECEIPT_DIR / f"receipt-{receipt['generated_at_utc'].replace(':', '')}.json"
    out.write_text(json.dumps(receipt, indent=1, sort_keys=True))
    print(render_tables(receipt))
    print(f"receipt: {out}")
    if args.update_report:
        update_report(receipt)
        print(f"updated {REPORT.name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
