#!/usr/bin/env python3
"""Empirical heartbeat benchmark and `BEq + DecidableEq` repository audit for the
`ws-proto-demand-time-compiler-queries-and-opaque-callee-table` prototype.

Benchmark (`--sizes 4,16,64,128`): for every table size `M`, a probe `.lean` file
staged in a `tempfile.TemporaryDirectory` under `/tmp` imports the prototype module
(compiled once into the same temporary directory with `lean -o`, never into the
worktree) and measures, with Lean's own heartbeat counter (`IO.getNumHeartbeats`)
and monotonic clock around `elabCommand` (with `Elab.async false`, so elaboration
*and* kernel checking are inside the window), three ways of discharging the
call-resolution obligations of the root

    bb0: switchInt(const true) -> [0: bb2, otherwise: bb1]
    bb1: _0 = callee_{M-1}() -> bb3      (live arm)
    bb2: _0 = callee_{M-2}() -> bb3      (dead arm)
    bb3: return

against `M` realistic captured `CapturedMir` callees (`protoLeaf`: real local
decls, basic blocks, `FnAbi`, and `LayoutTable`; crate-qualified `DefPath`s with
long shared prefixes):

* `linear_list`: the unpruned obligation `Q(M)` = the trusted branch step
  (`evalTerminator`, evaluating the literal through the trusted `evalOperand`)
  ∧ the trusted `lookupCallee` resolution of *both* arms over the concrete
  `List CapturedMir`, all closed by `rfl` (the elaborator and kernel unfold the
  `findCallee?` scan);
* `opaque_o1`: *the same proposition* `Q(M)`, with both resolutions discharged
  through the `@[irreducible]` `OpaqueCalleeTable` by
  `opaqueCalleeTable_lookup_eq_trusted` + `lookupCallee_hit_mono` certificates;
* `opaque_pruned`: the pruned obligation `P(M)` = the pruned branch step
  (`stepTerminatorWith_litSwitch`: the literal `switchInt` takes the live arm
  without consulting the dead one) ∧ the live resolution only (certificate).

The one-time certificate generation (`cert_gen_live`, `cert_gen_dead`: one
declaration each, whose `k` trusted-`stringEq` skips are a single
kernel-evaluated Boolean fact; amortized across every later use) is reported
separately.

Lean invocations are wrapped as
`anneal-lean-run --mode file --concurrency 1 -- lake env lean ...` with
`~/.elan/bin` prepended to `PATH`.

Repository audit (`--repo-audit`): `audit_redundant_beq_decidable_eq` is a
comment-, nested-block-comment-, string-, raw-string-, char-, and
guillemet-aware Lean 4 scanner that reports every `deriving` clause and
`deriving instance` command whose class list combines `BEq` with `DecidableEq`
(the `instBEqOfDecidableEq` / `LawfulBEq` shadowing hazard of cl/1022563952).
"""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

import argparse
import json
import math
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import tempfile
import time
from typing import Any, Iterable

REPO_ROOT = Path(__file__).resolve().parent.parent
PROTOTYPE_NAMESPACE = "Anneal.DemandCompilerQueryAndOpaqueCalleePrototype"
BENCH_PACKAGE = "AnnealOpaqueCalleeBench"
BENCH_MODULE = f"{BENCH_PACKAGE}.DemandCompilerQueryAndOpaqueCalleePrototype"
PROTOTYPE_REL = Path("theory/Anneal/DemandCompilerQueryAndOpaqueCalleePrototype.lean")
VARIANTS = ("linear_list", "opaque_o1", "opaque_pruned")
CERT_LABELS = ("cert_gen_live", "cert_gen_dead")
# The naive baseline is allowed to exhaust Lean's kernel resources (recorded as
# data); every opaque-table and certificate measurement must be a checked proof.
BASELINE_LABELS = ("linear_list",)
DEFAULT_SIZES = (4, 16, 64, 128)
DEFAULT_REPS = 3


# ---------------------------------------------------------------------------
# Environment / Lean invocation
# ---------------------------------------------------------------------------


def lean_env(extra_lean_path: Iterable[str] = ()) -> dict[str, str]:
    """Process environment with `~/.elan/bin` (and `~/.cargo/bin`) prepended to
    `PATH` and `extra_lean_path` prepended to `LEAN_PATH`."""
    env = dict(os.environ)
    home = Path.home()
    prefix = [str(home / ".elan" / "bin"), str(home / ".cargo" / "bin"), str(home / ".local" / "bin")]
    env["PATH"] = os.pathsep.join(prefix + [env.get("PATH", "")])
    extra = [p for p in extra_lean_path if p]
    if extra:
        env["LEAN_PATH"] = os.pathsep.join(extra + ([env["LEAN_PATH"]] if env.get("LEAN_PATH") else []))
    env.setdefault("PYTHONDONTWRITEBYTECODE", "1")
    return env


def anneal_lean_run() -> str:
    found = shutil.which("anneal-lean-run", path=lean_env()["PATH"])
    if found is None:
        raise RuntimeError("anneal-lean-run not found on PATH (~/.local/bin/anneal-lean-run)")
    return found


def run_lean(args: list[str], *, extra_lean_path: Iterable[str] = (), timeout: int = 900) -> subprocess.CompletedProcess[str]:
    """Run `anneal-lean-run --mode file --concurrency 1 -- lake env lean <args>` from
    the repository root."""
    cmd = [anneal_lean_run(), "--mode", "file", "--concurrency", "1", "--timeout", str(timeout), "--",
           "lake", "env", "lean", *args]
    return subprocess.run(cmd, cwd=REPO_ROOT, env=lean_env(extra_lean_path), capture_output=True,
                          text=True, timeout=timeout + 60, check=False)


def compile_prototype(tmp: Path) -> tuple[Path, float]:
    """Copy the prototype source into the temporary directory `tmp`, compile it there
    as module `BENCH_MODULE` (a distinct root package, so the workspace's own
    `.lake/build/lib/lean/Anneal` never shadows it), and return the olean search
    root and the wall-clock seconds. Nothing is written into the worktree."""
    src_root = tmp / "src"
    src = src_root / BENCH_PACKAGE / "DemandCompilerQueryAndOpaqueCalleePrototype.lean"
    src.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(REPO_ROOT / PROTOTYPE_REL, src)
    olean_root = tmp / "oleans"
    out = olean_root / BENCH_PACKAGE / "DemandCompilerQueryAndOpaqueCalleePrototype.olean"
    out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.monotonic()
    proc = run_lean(["-R", str(src_root), "-o", str(out), str(src)])
    elapsed = time.monotonic() - t0
    if proc.returncode != 0 or not out.exists():
        raise RuntimeError(f"prototype compilation failed (exit {proc.returncode}):\n{proc.stdout}\n{proc.stderr}")
    return olean_root, elapsed


# ---------------------------------------------------------------------------
# Probe generation
# ---------------------------------------------------------------------------


def callee_path(i: int) -> str:
    return f"bench_crate::module_{i:04d}::callee_{i:04d}"


PROBE_HEADER = f"""import {BENCH_MODULE}
import Lean

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open {PROTOTYPE_NAMESPACE}

open Lean Elab Command in
elab "#bench_hb " label:str cmd:command : command => do
  let h0 ← IO.getNumHeartbeats
  let t0 ← IO.monoNanosNow
  elabCommand cmd
  let t1 ← IO.monoNanosNow
  let h1 ← IO.getNumHeartbeats
  logInfo m!"BENCH {{label.getString}} heartbeats={{h1 - h0}} ns={{t1 - t0}}"
"""


def certificate(label: str, name: str, k: int) -> str:
    """Raw certificate `benchTbl.lookupRaw path(k) = some benchCallee{k}`, emitted
    the way a capture tool would: `lookupRaw_ofList_append_cons_of_skips` with the
    table split as `[benchCallee0, …, benchCallee{k-1}] ++ benchCallee{k} :: benchSuffix{k+1}`,
    the `k` trusted-`stringEq` skips discharged as one Boolean fact by a single
    kernel evaluation (`decide +kernel`), and the hit by `rfl`. Linear in `k`, but
    no elaborator `whnf` of the `findCallee?` scan and no deep kernel term (a
    monolithic `rfl` over the list exhausts Lean's `-M` budget at `M = 128`)."""
    p = callee_path(k)
    pre = "[" + ", ".join(f"benchCallee{j}" for j in range(k)) + "]"
    return (f'#bench_hb "{label}" theorem {name} : benchTbl.lookupRaw "{p}" = some benchCallee{k} := '
            f'lookupRaw_ofList_append_cons_of_skips (pre := {pre}) (post := benchSuffix{k + 1}) '
            f'(by decide +kernel) (rfl : benchCallee{k}.defPath = "{p}")')


PROBE_PARTS = ("opaque", "linear")


def generate_probe(m: int, reps: int, part: str = "opaque") -> str:
    """Probe for table size `m` (`m >= 2`). `part = "opaque"` measures the
    certificates and the opaque variants; `part = "linear"` measures the
    concrete-list baseline in its own Lean process, so a kernel resource blowup of
    the baseline can never contaminate the opaque measurements."""
    if part not in PROBE_PARTS:
        raise ValueError(f"unknown probe part {part!r}")
    if m < 2:
        raise ValueError("table size must be at least 2 (live + dead callee)")
    live, dead = m - 1, m - 2
    lines = [PROBE_HEADER]
    for i in range(m):
        lines.append(f'def benchCallee{i} : CapturedMir := protoLeaf "{callee_path(i)}" {i} 0 []')
    # The table as a cons chain of suffix definitions (`benchSuffix{j} = benchCallee{j} :: benchSuffix{j+1}`).
    lines.append(f"def benchSuffix{m} : List CapturedMir := []")
    for i in range(m - 1, -1, -1):
        lines.append(f"def benchSuffix{i} : List CapturedMir := benchCallee{i} :: benchSuffix{i + 1}")
    lines.append("def benchList : List CapturedMir := benchSuffix0")
    lines.append("def benchTbl : OpaqueCalleeTable := .ofList benchList")
    lines.append(f'def benchRoot : CapturedMir := protoLitIfRoot true "{callee_path(live)}" [] "{callee_path(dead)}"')
    lines.append("def benchInit : MachineState := initMachineState benchRoot []")
    if part == "opaque":
        lines.append(certificate("cert_gen_live", "certLive", live))
        lines.append(certificate("cert_gen_dead", "certDead", dead))
    live_res = f'lookupCallee benchList protoLayouts "{callee_path(live)}" [] [] = some benchCallee{live}'
    dead_res = f'lookupCallee benchList protoLayouts "{callee_path(dead)}" [] [] = some benchCallee{dead}'
    switch_term = "⟨.switchInt (protoBoolConst true) ⟨[(0, 2)], 1⟩, \"root:if\"⟩"
    taken = ("MirStepNode.emitStep (.event 1) { benchInit with frame := "
             "{ blockIdx := 1, stmtIdx := 0, locals := benchInit.frame.locals } }")
    # Unpruned obligation Q(M): the trusted branch step (evaluating the literal operand
    # through the trusted `evalOperand`) and the call resolutions of *both* arms.
    unpruned = (f"evalTerminator benchInit {switch_term} (some benchRoot) = {taken} ∧ "
                f"{live_res} ∧ {dead_res}")
    # Pruned obligation P(M): the pruned branch step and the live call resolution only.
    pruned = (f"stepTerminatorWith true benchTbl.lookup benchInit {switch_term} (some benchRoot) = "
              f"{taken} ∧ {live_res}")
    opaque_live = "(opaqueCalleeTable_lookup_eq_trusted benchList _ _ _ _).symm.trans (lookupCallee_hit_mono certLive rfl)"
    opaque_dead = "(opaqueCalleeTable_lookup_eq_trusted benchList _ _ _ _).symm.trans (lookupCallee_hit_mono certDead rfl)"
    for r in range(reps):
        if part == "linear":
            lines.append(f'#bench_hb "linear_list" theorem benchLinear{r} : {unpruned} := ⟨rfl, rfl, rfl⟩')
        else:
            lines.append(f'#bench_hb "opaque_o1" theorem benchOpaque{r} : {unpruned} := '
                         f"⟨rfl, {opaque_live}, {opaque_dead}⟩")
            lines.append(f'#bench_hb "opaque_pruned" theorem benchPruned{r} : {pruned} := '
                         f"⟨stepTerminatorWith_litSwitch _ _ _ _ _ _ _, {opaque_live}⟩")
    return "\n".join(lines) + "\n"


def parse_bench_messages(stdout: str) -> tuple[dict[str, list[tuple[int, int, str | None]]], list[str]]:
    """Parse `BENCH <label> heartbeats=<n> ns=<t>` messages from `lean --json`
    output, attaching to each sample the first error reported on the same probe
    line (e.g. a kernel resource error of the `linear_list` baseline). Errors on
    lines without a `BENCH` sample are returned separately."""
    samples: list[tuple[int, str, int, int]] = []
    errors: dict[int, str] = {}
    for line in stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        data = msg.get("data", "")
        pos = (msg.get("pos") or {}).get("line", -1)
        if msg.get("severity") == "error":
            errors.setdefault(pos, str(data))
            continue
        if not isinstance(data, str) or not data.startswith("BENCH "):
            continue
        parts = data.split()
        fields = dict(p.split("=", 1) for p in parts[2:])
        samples.append((pos, parts[1], int(fields["heartbeats"]), int(fields["ns"])))
    results: dict[str, list[tuple[int, int, str | None]]] = {}
    sample_lines = set()
    for pos, label, hb, ns in samples:
        sample_lines.add(pos)
        results.setdefault(label, []).append((hb, ns, errors.get(pos)))
    orphan = [f"line {pos}: {err}" for pos, err in sorted(errors.items()) if pos not in sample_lines]
    return results, orphan


# ---------------------------------------------------------------------------
# Statistics
# ---------------------------------------------------------------------------


def linear_slope(xs: list[float], ys: list[float]) -> float:
    """Least-squares slope of `ys` against `xs`."""
    n = len(xs)
    if n < 2:
        return 0.0
    mx, my = sum(xs) / n, sum(ys) / n
    den = sum((x - mx) ** 2 for x in xs)
    return 0.0 if den == 0 else sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / den


def loglog_slope(xs: list[float], ys: list[float]) -> float:
    """Least-squares slope in log-log space (≈1 linear growth, ≈0 flat)."""
    pts = [(math.log(x), math.log(y)) for x, y in zip(xs, ys) if x > 0 and y > 0]
    if len(pts) < 2:
        return 0.0
    return linear_slope([p[0] for p in pts], [p[1] for p in pts])


def summarize(per_size: dict[int, dict[str, dict[str, float]]]) -> dict[str, Any]:
    sizes = sorted(per_size)
    scaling: dict[str, Any] = {}
    for label in VARIANTS + CERT_LABELS:
        hbs = [per_size[m][label]["heartbeats"] for m in sizes]
        mss = [per_size[m][label]["wall_ms"] for m in sizes]
        scaling[label] = {
            "heartbeats_per_callee": linear_slope([float(m) for m in sizes], [float(h) for h in hbs]),
            "heartbeats_loglog_slope": loglog_slope([float(m) for m in sizes], [float(h) for h in hbs]),
            "wall_ms_per_callee": linear_slope([float(m) for m in sizes], mss),
            "heartbeat_growth_first_to_last": (hbs[-1] / hbs[0]) if hbs and hbs[0] else None,
        }
    speedups: dict[str, dict[str, float]] = {}
    for m in sizes:
        lin = per_size[m]["linear_list"]
        speedups[str(m)] = {
            f"{v}_heartbeat_speedup": (lin["heartbeats"] / per_size[m][v]["heartbeats"]) if per_size[m][v]["heartbeats"] else float("inf")
            for v in ("opaque_o1", "opaque_pruned")
        } | {
            f"{v}_wall_speedup": (lin["wall_ms"] / per_size[m][v]["wall_ms"]) if per_size[m][v]["wall_ms"] else float("inf")
            for v in ("opaque_o1", "opaque_pruned")
        }
    return {"scaling": scaling, "speedups": speedups}


def run_benchmark(sizes: list[int], reps: int = DEFAULT_REPS) -> dict[str, Any]:
    """Compile the prototype into a temporary directory and run one probe per size."""
    with tempfile.TemporaryDirectory(prefix="anneal-opaque-callee-bench-", dir="/tmp") as tmp:
        tmp_path = Path(tmp)
        olean_root, compile_s = compile_prototype(tmp_path)
        per_size: dict[int, dict[str, dict[str, float]]] = {}
        raw: dict[str, Any] = {}
        for m in sizes:
            msgs: dict[str, list[tuple[int, int, str | None]]] = {}
            lean_exit: dict[str, int] = {}
            probe_s = 0.0
            for part in PROBE_PARTS:
                probe = tmp_path / f"BenchOpaqueCallee{m}_{part}.lean"
                probe.write_text(generate_probe(m, reps, part), encoding="utf-8")
                t0 = time.monotonic()
                proc = run_lean(["--json", str(probe)], extra_lean_path=[str(olean_root)])
                probe_s += time.monotonic() - t0
                part_msgs, orphan = parse_bench_messages(proc.stdout)
                if orphan:
                    raise RuntimeError(f"probe M={m} ({part}): errors outside measured commands: {orphan}")
                lean_exit[part] = proc.returncode
                for k, v in part_msgs.items():
                    msgs.setdefault(k, []).extend(v)
            row: dict[str, dict[str, Any]] = {}
            for label in VARIANTS + CERT_LABELS:
                samples = msgs.get(label)
                expected = reps if label in VARIANTS else 1
                if not samples or len(samples) != expected:
                    raise RuntimeError(f"probe M={m} (exits {lean_exit}): expected {expected} samples for "
                                       f"{label}, got {samples}")
                errs = sorted({e for _, _, e in samples if e})
                if errs and label not in BASELINE_LABELS:
                    # Every claimed (opaque / certificate) measurement must be a checked proof.
                    raise RuntimeError(f"probe M={m}: {label} failed: {errs}")
                row[label] = {
                    "heartbeats": float(statistics.median(h for h, _, _ in samples)),
                    "kheartbeats": float(statistics.median(h for h, _, _ in samples)) / 1000.0,
                    "wall_ms": float(statistics.median(ns for _, ns, _ in samples)) / 1e6,
                    "samples": len(samples),
                    "status": "ok" if not errs else "lean_error",
                    "errors": errs,
                }
            per_size[m] = row
            raw[str(m)] = {"probe_wall_s": probe_s, "lean_exit": lean_exit,
                           "samples": {k: [[h, ns, e] for h, ns, e in v] for k, v in msgs.items()}}
    result: dict[str, Any] = {
        "sizes": sizes,
        "reps": reps,
        "prototype_compile_s": compile_s,
        "results": {str(m): per_size[m] for m in sizes},
        "raw": raw,
    }
    result.update(summarize(per_size))
    return result


# ---------------------------------------------------------------------------
# Lean 4 lexer-aware `BEq + DecidableEq` audit
# ---------------------------------------------------------------------------


def _is_ident_start(ch: str) -> bool:
    return ch.isalpha() or ch == "_" or ch in "αβγδεζηθικλμνξοπρστυφχψωΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ" or (ord(ch) > 127 and ch.isalpha())


def _is_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'!?" or (ord(ch) > 127 and (ch.isalnum() or ch in "₀₁₂₃₄₅₆₇₈₉ₐₑₒₓₔₕₖₗₘₙₚₛₜᵢᵣᵤᵥⱼ"))


def tokenize_lean(text: str) -> list[tuple[str, str, int]]:
    """Tokenize Lean 4 source into `(kind, value, line)` with kind in
    `ident`, `punct`, skipping whitespace, `--` line comments, nested `/- -/`
    block comments (including doc comments), string literals (with escapes and
    `s!`/`m!`/`f!` interpolation whose `{...}` holes are tokenized recursively),
    raw strings `r"..."` / `r#"..."#`, char literals, and numeric literals.
    Guillemet identifiers `«...»` are single identifier components."""
    toks: list[tuple[str, str, int]] = []
    i, n, line = 0, len(text), 1

    def skip_string(j: int, interpolated: bool) -> int:
        nonlocal line
        # text[j] == '"'
        j += 1
        while j < n:
            c = text[j]
            if c == "\\":
                if j + 1 < n and text[j + 1] == "\n":
                    line += 1
                j += 2
                continue
            if c == "\n":
                line += 1
            if c == '"':
                return j + 1
            if interpolated and c == "{":
                j = skip_code_until_brace(j + 1)
                continue
            j += 1
        return j

    def skip_code_until_brace(j: int) -> int:
        nonlocal line
        depth = 1
        while j < n and depth > 0:
            c = text[j]
            if c == "\n":
                line += 1
                j += 1
            elif c == "{":
                depth += 1
                j += 1
            elif c == "}":
                depth -= 1
                j += 1
            elif c == '"':
                j = skip_string(j, False)
            elif text.startswith("--", j):
                k = text.find("\n", j)
                j = n if k < 0 else k
            elif text.startswith("/-", j):
                j = skip_block_comment(j)
            else:
                j += 1
        return j

    def skip_block_comment(j: int) -> int:
        nonlocal line
        depth = 0
        while j < n:
            if text.startswith("/-", j):
                depth += 1
                j += 2
            elif text.startswith("-/", j):
                depth -= 1
                j += 2
                if depth == 0:
                    return j
            else:
                if text[j] == "\n":
                    line += 1
                j += 1
        return j

    def skip_raw_string(j: int) -> int | None:
        nonlocal line
        # text[j] == 'r'
        k = j + 1
        hashes = 0
        while k < n and text[k] == "#":
            hashes += 1
            k += 1
        if k >= n or text[k] != '"':
            return None
        close = '"' + "#" * hashes
        end = text.find(close, k + 1)
        end = n if end < 0 else end + len(close)
        line += text.count("\n", k, end)
        return end

    while i < n:
        c = text[i]
        if c == "\n":
            line += 1
            i += 1
        elif c.isspace():
            i += 1
        elif text.startswith("--", i):
            k = text.find("\n", i)
            i = n if k < 0 else k
        elif text.startswith("/-", i):
            i = skip_block_comment(i)
        elif c == '"':
            i = skip_string(i, False)
        elif c in "smf" and text.startswith('!"', i + 1) and (i == 0 or not _is_ident_char(text[i - 1])):
            i = skip_string(i + 2, True)
        elif c == "r" and (i == 0 or not _is_ident_char(text[i - 1])) and (
                text.startswith('r"', i) or text.startswith("r#", i)):
            end = skip_raw_string(i)
            if end is None:
                toks.append(("ident", "r", line))
                i += 1
            else:
                i = end
        elif c == "'" and (i == 0 or not _is_ident_char(text[i - 1])):
            # char literal: 'x', '\n', '\x41', '\u{1F600}'
            if text.startswith("'\\", i):
                k = text.find("'", i + 2)
                i = n if k < 0 else k + 1
            elif i + 2 < n and text[i + 2] == "'":
                i += 3
            else:
                toks.append(("punct", "'", line))
                i += 1
        elif c == "«" or _is_ident_start(c):
            start_line = line
            parts: list[str] = []
            j = i
            while True:
                if j < n and text[j] == "«":
                    k = text.find("»", j + 1)
                    k = n if k < 0 else k
                    parts.append(text[j + 1:k])
                    line += text.count("\n", j, k)
                    j = k + 1
                elif j < n and _is_ident_start(text[j]):
                    k = j
                    while k < n and _is_ident_char(text[k]):
                        k += 1
                    parts.append(text[j:k])
                    j = k
                else:
                    break
                if j + 1 < n and text[j] == "." and (text[j + 1] == "«" or _is_ident_start(text[j + 1])):
                    j += 1
                    continue
                break
            toks.append(("ident", ".".join(parts), start_line))
            i = j
        elif c.isdigit():
            k = i
            while k < n and (text[k].isalnum() or text[k] in "_."):
                if text[k] == "." and not (k + 1 < n and text[k + 1].isdigit()):
                    break
                k += 1
            i = k
        else:
            toks.append(("punct", c, line))
            i += 1
    return toks


def _last_component(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def audit_redundant_beq_decidable_eq_text(text: str, path: str = "<text>") -> list[dict[str, Any]]:
    """Every `deriving` clause / `deriving instance` command in `text` whose class
    list contains both `BEq` and `DecidableEq`."""
    toks = tokenize_lean(text)
    findings: list[dict[str, Any]] = []
    i, n = 0, len(toks)
    while i < n:
        kind, val, line = toks[i]
        if kind == "ident" and val == "deriving":
            j = i + 1
            is_instance = j < n and toks[j] == ("ident", "instance", toks[j][2])
            if is_instance:
                j += 1
            classes: list[str] = []
            while j < n and toks[j][0] == "ident" and toks[j][1] not in ("for", "deriving"):
                classes.append(toks[j][1])
                j += 1
                # skip class arguments in parentheses (rare: `deriving Foo (bar)`)
                if j < n and toks[j] == ("punct", ",", toks[j][2]):
                    j += 1
                    continue
                break
            targets: list[str] = []
            if is_instance and j < n and toks[j][1] == "for":
                j += 1
                while j < n and toks[j][0] == "ident":
                    targets.append(toks[j][1])
                    j += 1
                    if j < n and toks[j] == ("punct", ",", toks[j][2]):
                        j += 1
                        continue
                    break
            last = {_last_component(c) for c in classes}
            if "BEq" in last and "DecidableEq" in last:
                findings.append({
                    "path": path,
                    "line": line,
                    "kind": "deriving_instance" if is_instance else "deriving",
                    "classes": classes,
                    "targets": targets,
                })
            i = max(j, i + 1)
        else:
            i += 1
    return findings


_RUST_ESCAPES = {"n": "\n", "t": "\t", "r": "\r", "0": "\0", "\\": "\\", "'": "'", '"': '"'}


def rust_string_literals(text: str) -> list[tuple[int, str]]:
    """Extract `(line, unescaped content)` of every Rust string literal (`"..."`,
    `b"..."`, `r"..."`, `r#"..."#`, `br#"..."#`), skipping `//` line comments,
    nested `/* */` block comments, and char literals (`'"'`), so Lean source
    emitted by Rust code generators can be audited."""
    out: list[tuple[int, str]] = []
    i, n, line = 0, len(text), 1
    while i < n:
        c = text[i]
        if c == "\n":
            line += 1
            i += 1
        elif text.startswith("//", i):
            k = text.find("\n", i)
            i = n if k < 0 else k
        elif text.startswith("/*", i):
            depth = 0
            while i < n:
                if text.startswith("/*", i):
                    depth += 1
                    i += 2
                elif text.startswith("*/", i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    if text[i] == "\n":
                        line += 1
                    i += 1
        elif c in "rb" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            j = i + 1 if c == "r" else (i + 2 if text.startswith("br", i) else i + 1)
            if c == "b" and not text.startswith("br", i):
                # byte string b"..."
                if j < n and text[j] == '"':
                    i = j
                    continue
                i += 1
                continue
            hashes = 0
            while j < n and text[j] == "#":
                hashes += 1
                j += 1
            if j < n and text[j] == '"':
                close = '"' + "#" * hashes
                end = text.find(close, j + 1)
                end = n if end < 0 else end
                out.append((line, text[j + 1:end]))
                line += text.count("\n", j, end)
                i = end + len(close)
            else:
                i += 1
        elif c == '"':
            start_line = line
            j = i + 1
            buf: list[str] = []
            while j < n and text[j] != '"':
                if text[j] == "\\" and j + 1 < n:
                    nxt = text[j + 1]
                    if nxt == "\n":
                        line += 1
                        j += 2
                        while j < n and text[j] in " \t\r\n":
                            if text[j] == "\n":
                                line += 1
                            j += 1
                        continue
                    if nxt == "u" and text.startswith("{", j + 2):
                        k = text.find("}", j + 3)
                        try:
                            buf.append(chr(int(text[j + 3:k], 16)))
                        except ValueError:
                            pass
                        j = k + 1
                        continue
                    if nxt == "x":
                        try:
                            buf.append(chr(int(text[j + 2:j + 4], 16)))
                        except ValueError:
                            pass
                        j += 4
                        continue
                    buf.append(_RUST_ESCAPES.get(nxt, nxt))
                    j += 2
                    continue
                if text[j] == "\n":
                    line += 1
                buf.append(text[j])
                j += 1
            out.append((start_line, "".join(buf)))
            i = j + 1
        elif c == "'":
            # char literal ('x', '\n', '\'', '\u{..}') vs lifetime ('a)
            if text.startswith("'\\", i):
                k = text.find("'", i + 2 if not text.startswith("'\\'", i) else i + 3)
                i = n if k < 0 else k + 1
            elif i + 2 < n and text[i + 2] == "'":
                i += 3
            else:
                i += 1
        else:
            i += 1
    return out


def audit_rust_codegen_text(text: str, path: str = "<rust>") -> list[dict[str, Any]]:
    """`BEq + DecidableEq` derivations inside Lean source emitted by Rust string
    literals (each literal is scanned as Lean text)."""
    findings: list[dict[str, Any]] = []
    for line, content in rust_string_literals(text):
        for f in audit_redundant_beq_decidable_eq_text(content, path):
            f = dict(f)
            f["line"] = line + f["line"] - 1
            f["kind"] = f["kind"] + "_codegen"
            findings.append(f)
    return findings


def _skip(rel_parts: tuple[str, ...]) -> bool:
    return any(part in (".lake", "build", "target", "node_modules") for part in rel_parts)


def audit_redundant_beq_decidable_eq(roots: Iterable[Path] | None = None, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    """Scan every `.lean` file (and the Lean emitted by every `.rs` string literal)
    under `roots` (default `theory/` and `crates/`) for `BEq + DecidableEq`
    derivations."""
    roots = [repo_root / "theory", repo_root / "crates"] if roots is None else [Path(r) for r in roots]
    per_root: dict[str, Any] = {}
    all_findings: list[dict[str, Any]] = []
    lean_total = rust_total = 0
    for root in roots:
        root_findings: list[dict[str, Any]] = []
        lean_count = rust_count = 0
        if root.exists():
            for f in sorted(root.rglob("*")):
                if f.suffix not in (".lean", ".rs") or not f.is_file() or _skip(f.relative_to(root).parts):
                    continue
                try:
                    text = f.read_text(encoding="utf-8")
                except (OSError, UnicodeDecodeError):
                    continue
                rel = str(f.relative_to(repo_root)) if f.is_relative_to(repo_root) else str(f)
                if f.suffix == ".lean":
                    lean_count += 1
                    root_findings.extend(audit_redundant_beq_decidable_eq_text(text, rel))
                else:
                    rust_count += 1
                    root_findings.extend(audit_rust_codegen_text(text, rel))
        lean_total += lean_count
        rust_total += rust_count
        key = str(root.relative_to(repo_root)) if root.is_relative_to(repo_root) else str(root)
        per_root[key] = {"lean_files_scanned": lean_count, "rust_files_scanned": rust_count,
                         "occurrences": len(root_findings),
                         "codegen_occurrences": sum(1 for x in root_findings if x["kind"].endswith("_codegen")),
                         "files_with_occurrences": len({x["path"] for x in root_findings})}
        all_findings.extend(root_findings)
    return {
        "lean_files_scanned": lean_total,
        "rust_files_scanned": rust_total,
        "occurrences": len(all_findings),
        "codegen_occurrences": sum(1 for x in all_findings if x["kind"].endswith("_codegen")),
        "files_with_occurrences": len({x["path"] for x in all_findings}),
        "by_root": per_root,
        "findings": all_findings,
    }


# ---------------------------------------------------------------------------
# Rendering / CLI
# ---------------------------------------------------------------------------


def render_markdown(bench: dict[str, Any] | None, audit: dict[str, Any] | None) -> str:
    out: list[str] = []
    if bench is not None:
        out.append("### Heartbeat / wall-clock benchmark (median of reps)\n")
        out.append("| M | " + " | ".join(f"{v} kHb" for v in VARIANTS) + " | "
                   + " | ".join(f"{v} ms" for v in VARIANTS) + " | cert_gen (live+dead) kHb |")
        out.append("|---" * (2 * len(VARIANTS) + 2) + "|")
        for m in bench["sizes"]:
            row = bench["results"][str(m)]
            cert = row["cert_gen_live"]["kheartbeats"] + row["cert_gen_dead"]["kheartbeats"]
            out.append(f"| {m} | " + " | ".join(f"{row[v]['kheartbeats']:.1f}" for v in VARIANTS) + " | "
                       + " | ".join(f"{row[v]['wall_ms']:.2f}" for v in VARIANTS) + f" | {cert:.1f} |")
        out.append("\n| variant | heartbeats / callee | log-log slope | growth M_first→M_last |")
        out.append("|---|---|---|---|")
        for v in VARIANTS + CERT_LABELS:
            sc = bench["scaling"][v]
            g = sc["heartbeat_growth_first_to_last"]
            out.append(f"| {v} | {sc['heartbeats_per_callee']:.1f} | {sc['heartbeats_loglog_slope']:.3f} | "
                       f"{g:.2f}x |" if g is not None else f"| {v} | {sc['heartbeats_per_callee']:.1f} | "
                       f"{sc['heartbeats_loglog_slope']:.3f} | n/a |")
        out.append("\n| M | opaque_o1 Hb speedup | opaque_pruned Hb speedup | opaque_o1 wall speedup | opaque_pruned wall speedup |")
        out.append("|---|---|---|---|---|")
        for m in bench["sizes"]:
            sp = bench["speedups"][str(m)]
            out.append(f"| {m} | {sp['opaque_o1_heartbeat_speedup']:.1f}x | {sp['opaque_pruned_heartbeat_speedup']:.1f}x | "
                       f"{sp['opaque_o1_wall_speedup']:.1f}x | {sp['opaque_pruned_wall_speedup']:.1f}x |")
    if audit is not None:
        out.append("\n### `BEq + DecidableEq` repository audit\n")
        out.append("| root | .lean files | .rs files (codegen literals) | occurrences | codegen occurrences | files with occurrences |")
        out.append("|---|---|---|---|---|---|")
        for root, st in audit["by_root"].items():
            out.append(f"| `{root}/` | {st['lean_files_scanned']} | {st['rust_files_scanned']} | {st['occurrences']} | "
                       f"{st['codegen_occurrences']} | {st['files_with_occurrences']} |")
        out.append(f"| **total** | {audit['lean_files_scanned']} | {audit['rust_files_scanned']} | {audit['occurrences']} | "
                   f"{audit['codegen_occurrences']} | {audit['files_with_occurrences']} |")
    return "\n".join(out) + "\n"


def parse_sizes(text: str) -> list[int]:
    sizes = [int(x) for x in text.split(",") if x.strip()]
    if not sizes or any(m < 2 for m in sizes):
        raise argparse.ArgumentTypeError("sizes must be comma-separated integers >= 2")
    return sorted(set(sizes))


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--sizes", type=parse_sizes, default=list(DEFAULT_SIZES),
                    help="comma-separated callee-table sizes M (default 4,16,64,128)")
    ap.add_argument("--reps", type=int, default=DEFAULT_REPS, help="repetitions per variant (median reported)")
    ap.add_argument("--json", action="store_true", help="emit structured JSON")
    ap.add_argument("--markdown", action="store_true", help="emit Markdown tables")
    ap.add_argument("--repo-audit", "-repo-audit", dest="repo_audit", action="store_true",
                    help="run the BEq + DecidableEq repository audit (theory/, crates/)")
    ap.add_argument("--audit-only", action="store_true", help="skip the Lean benchmark (audit only)")
    args = ap.parse_args(argv)
    bench = None if args.audit_only else run_benchmark(args.sizes, max(1, args.reps))
    audit = audit_redundant_beq_decidable_eq() if (args.repo_audit or args.audit_only or args.json) else None
    if args.json or not args.markdown:
        payload: dict[str, Any] = {}
        if bench is not None:
            payload["benchmark"] = bench
        if audit is not None:
            payload["repo_audit"] = audit
        print(json.dumps(payload, indent=2, sort_keys=True))
    if args.markdown:
        print(render_markdown(bench, audit))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
