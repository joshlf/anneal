#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Sharded `check_trusted.py` audit orchestration, reconciliation, and peer-guard scans.

This script never weakens the trusted checker; it only partitions work for it and
cross-checks the partition:

* `--orphan-only`: sub-second completeness gate. Every `DOWNSTREAM_TARGETS` module and
  every on-disk `.lean` module of every `[[lean_lib]]` in `lakefile.toml` must belong to
  a shard, with case-folding uniqueness; the same manifest is re-verified by
  `check_trusted.py --orphan-only --shard-manifest`.
* `--plan`: the deterministic shard plan (balanced subsystem shards; the `RustcMir`
  straggler is sub-sharded by source size).
* `--run-shards`: parallel `check_trusted.py --fast --exact-modules <csv>` per shard,
  sharing one `--cache-dir` outside the checkout.
* `--reconcile`: exports bijective 9-tuple declaration headers per Lake shard and runs an
  exact structural `constInfoCompat` comparison on every name realized in two or more
  shards (no 64-bit `Expr.hash` fingerprints, no `value? = none` conflation).
* `--verify-equivalence`: sharded audits agree with the monolithic `check_trusted.py
  --fast` audit on verdict, Trusted declarations, axiom union, downstream coverage, and
  claim / test-axiom counts, and cross-shard reconciliation finds no conflict.
* `--exact-modules <csv>`: single-shard passthrough to `check_trusted.py`.
* `--scan-peer-guards [paths]`: Lean source Guard 6a (`assumesHold` polarity with `let`
  alias inlining up to depth 8 and helper indirection) and Guard 6b (`private mk ::`
  sealing of `@invariant` structures) over repository `.lean` files.

Exit codes follow `check_trusted.py`: `0` pass, `1` policy failure, `2` operational error.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True

REPO_ROOT = Path(__file__).resolve().parent.parent
CHECK_TRUSTED = REPO_ROOT / "trusted/audit/check_trusted.py"
ORPHAN_BUDGET_SECS = 0.25
RUSTC_MIR_SUBSHARDS = 4
LEAN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"


def load_check_trusted(path: Path = CHECK_TRUSTED):
    """Import `check_trusted.py` as a module (it never imports this script)."""
    spec = importlib.util.spec_from_file_location("check_trusted", path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


ct = load_check_trusted()
Failure = ct.Failure


# ---------------------------------------------------------------------------
# Deterministic shard planning
# ---------------------------------------------------------------------------

def downstream_subsystem(module: str, role: str) -> str:
    """Subsystem of one `DOWNSTREAM_TARGETS` entry."""
    if role in ("examples", "claim"):
        return "examples-and-claims"
    if role == "test":
        return "tests"
    if module.startswith("Anneal.PureLift"):
        return "purelift"
    if module.startswith(("Anneal.Rustc.", "Anneal.Mir", "Anneal.PureMirExec", "Anneal.FunctionalTranslation",
                          "Anneal.SepLogicLenses")):
        return "rustc-mir"
    if module == "Anneal":
        return "umbrella"
    return "core"


def lake_subsystem(module: str) -> str:
    """Subsystem of one Lake library module."""
    parts = module.split(".")
    if parts[0] != "Anneal":
        return "MiniRust" if parts[0] in ("MiniRust", "MiniRustSpec", "Correspondence") else parts[0]
    if len(parts) == 1:
        return "Core"
    head = parts[1]
    if head in ("Rustc", "Mir") or head.startswith(("Mir", "PureMirExec")):
        return "RustcMir"
    if head.startswith(("PureLift", "SepLogic", "RefFrame")):
        return "PureLiftAndSepLogic"
    if head.startswith(("AiPcc", "ByteCodec", "LeBytes", "Bit", "CnfOrd", "F2Simd")):
        return "AiPccAndCodec"
    if head == "ParametricCore":
        return "ParametricCore"
    return "Core"


def balanced_split(items: list[tuple[str, int]], count: int) -> list[list[str]]:
    """Greedy longest-processing-time split into `count` non-empty, deterministic bins."""
    count = max(1, min(count, len(items)))
    bins: list[tuple[int, int, list[str]]] = [(0, i, []) for i in range(count)]
    for name, weight in sorted(items, key=lambda kv: (-kv[1], kv[0])):
        load, index, members = min(bins)
        members.append(name)
        bins[index] = (load + weight, index, members)
        bins.sort(key=lambda b: b[1])
    return [sorted(b[2]) for b in sorted(bins, key=lambda b: b[1]) if b[2]]


def plan_shards(checkout: Path = REPO_ROOT, targets=None, rustc_subshards: int = RUSTC_MIR_SUBSHARDS) -> dict:
    """The deterministic shard manifest: downstream subsystem shards plus Lake shards."""
    targets = ct.DOWNSTREAM_TARGETS if targets is None else targets
    downstream: dict[str, list[str]] = {}
    for module, _path, _imports, role in targets:
        downstream.setdefault(downstream_subsystem(module, role), []).append(module)
    shards = [{"name": f"downstream/{name}", "kind": "downstream", "modules": mods}
              for name, mods in sorted(downstream.items())]
    lake: dict[str, list[tuple[str, int]]] = {}
    for module, rel in ct.lake_modules(checkout).items():
        lake.setdefault(lake_subsystem(module), []).append((module, (checkout / rel).stat().st_size))
    for name, items in sorted(lake.items()):
        if name == "RustcMir" and rustc_subshards > 1:
            for index, members in enumerate(balanced_split(items, rustc_subshards), start=1):
                shards.append({"name": f"lake/RustcMir-{index}", "kind": "lake", "modules": members})
        else:
            shards.append({"name": f"lake/{name}", "kind": "lake", "modules": sorted(m for m, _ in items)})
    return {"lakefile_check": True, "shards": shards}


# ---------------------------------------------------------------------------
# Orphan gate
# ---------------------------------------------------------------------------

def orphan_gate(checkout: Path = REPO_ROOT, manifest: dict | None = None, *, delegate: bool = True,
                targets=None) -> dict:
    """In-process orphan check (timed) plus delegated `check_trusted.py --orphan-only` parity."""
    manifest = plan_shards(checkout, targets) if manifest is None else manifest
    with tempfile.TemporaryDirectory(prefix="anneal-shards-") as tmp:
        path = Path(tmp) / "manifest.json"
        path.write_text(json.dumps(manifest, sort_keys=True))
        start = time.monotonic()
        summary = ct.orphan_check(checkout, path, targets)
        summary["seconds"] = round(time.monotonic() - start, 4)
        if delegate:
            proc = subprocess.run([sys.executable, "-B", str(checkout / "trusted/audit/check_trusted.py"),
                                   "--orphan-only", "--shard-manifest", str(path)],
                                  capture_output=True, text=True, check=False)
            if proc.returncode != 0:
                raise Failure(proc.returncode if proc.returncode in (1, 2) else 2, "orphan-check",
                              f"check_trusted.py --orphan-only disagreed: {proc.stderr.strip()}")
            summary["delegated"] = True
    return summary


# ---------------------------------------------------------------------------
# Sharded execution
# ---------------------------------------------------------------------------

def run_shard(checkout: Path, modules: list[str], cache_dir: Path | None) -> dict:
    """Run `check_trusted.py --fast --exact-modules` for one shard."""
    command = [sys.executable, "-B", str(checkout / "trusted/audit/check_trusted.py"), "--fast",
               "--exact-modules", ",".join(modules)]
    if cache_dir is not None:
        command += ["--cache-dir", str(cache_dir)]
    start = time.monotonic()
    proc = subprocess.run(command, capture_output=True, text=True, check=False)
    axioms = re.search(r"axioms=(\[[^\]]*\])", proc.stdout)
    return {"modules": modules, "returncode": proc.returncode, "seconds": round(time.monotonic() - start, 2),
            "axioms": axioms.group(1) if axioms else None, "stderr": proc.stderr.strip()[-2000:]}


def run_shards(checkout: Path = REPO_ROOT, cache_dir: Path | None = None, jobs: int = 4) -> list[dict]:
    """Parallel downstream shards after the orphan gate."""
    manifest = plan_shards(checkout)
    orphan_gate(checkout, manifest)
    shards = [s for s in manifest["shards"] if s["kind"] == "downstream"]
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        results = list(pool.map(lambda s: {"name": s["name"], **run_shard(checkout, s["modules"], cache_dir)}, shards))
    return results


# ---------------------------------------------------------------------------
# Cross-shard reconciliation (exact `constInfoCompat`)
# ---------------------------------------------------------------------------

RECONCILE_SOURCE = r"""import Lean
open Lean
def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
def aux : ConstantInfo → Int × Int
  | .inductInfo v => (v.numParams, v.numIndices) | .ctorInfo v => (v.numParams, v.cidx)
  | .recInfo v => (v.numParams, v.numMinors) | _ => (-1, -1)
def qk : QuotKind → Nat | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3
def encodeNameAux : Name → List Json → List Json
  | .anonymous, acc => acc
  | .str p s, acc => encodeNameAux p (Json.arr #[toJson "s", toJson s] :: acc)
  | .num p k, acc => encodeNameAux p (Json.arr #[toJson "n", toJson k] :: acc)
def encodeName (n : Name) : Json := Json.arr (encodeNameAux n []).toArray
def decodeName (j : Json) : Except String Name := do
  let arr ← j.getArr?
  arr.foldlM (init := .anonymous) fun p item => do
    let pair ← item.getArr?
    if pair.size != 2 then throw "bad encoded name segment"
    let tag ← pair[0]!.getStr?
    if tag == "s" then return .str p (← pair[1]!.getStr?)
    else if tag == "n" then return .num p (← pair[1]!.getNat?)
    else throw "bad encoded name tag"
/-- Exact structural compatibility: identical constructor tag, universe parameters, type,
    value (theorems: proof irrelevance), and every inductive/constructor/recursor field. -/
def constInfoCompat : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo a, .axiomInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type == b.type && a.isUnsafe == b.isUnsafe
  | .defnInfo a, .defnInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type == b.type && a.value == b.value && a.safety == b.safety
  | .thmInfo a, .thmInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type == b.type
  | .opaqueInfo a, .opaqueInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type == b.type && a.value == b.value && a.isUnsafe == b.isUnsafe
  | .quotInfo a, .quotInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type == b.type && qk a.kind == qk b.kind
  | .inductInfo a, .inductInfo b => a.name == b.name && a.levelParams == b.levelParams && a.type == b.type &&
    a.numParams == b.numParams && a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
    a.numNested == b.numNested && a.isRec == b.isRec && a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | _, _ => false
def main (args : List String) : IO UInt32 := do
  let [mode, req, out] := args | IO.eprintln "usage: headers|compare REQUEST OUT"; return 2
  let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile req)
  let mods ← IO.ofExcept <| j.getObjValAs? (Array (String × String × String)) "modules"
  if mode == "headers" then
    let mut handles : Std.HashMap String IO.FS.Handle := {}
    for (shard, m, p) in mods do
      let h ← match handles[shard]? with
        | some h => pure h
        | none => do
          let h ← IO.FS.Handle.mk (System.FilePath.mk out / (shard.replace "/" "__" ++ ".jsonl")) .write
          handles := handles.insert shard h
          pure h
      let (d, _) ← readModuleData p
      unless d.constNames == d.constants.map (·.name) do
        throw <| IO.userError s!"policy:invalid inventory {m}"
      let mut modSeen : Std.HashSet Name := {}
      for ci in d.constants do
        if modSeen.contains ci.name then
          throw <| IO.userError s!"policy:duplicate constant {ci.name} in {m}"
        modSeen := modSeen.insert ci.name
        let (a1, a2) := aux ci
        h.putStrLn (toJson [encodeName ci.name, toJson (kind ci), toJson m,
          toJson ci.levelParams.length, toJson ci.type.hash.toNat,
          toJson ((ci.value? true).map (·.hash.toNat)), toJson ci.isUnsafe, toJson a1, toJson a2]).compress
    return 0
  let candJson ← IO.ofExcept <| j.getObjValAs? (Array Json) "candidates"
  let mut cands : NameSet := {}
  for cj in candJson do
    cands := cands.insert (← IO.ofExcept <| decodeName cj)
  let mut seen : Std.HashMap Name (String × String × ConstantInfo) := {}
  let mut conflicts : Array Json := #[]
  for (shard, m, p) in mods do
    let (d, _) ← readModuleData p
    for ci in d.constants do
      if cands.contains ci.name then
        match seen[ci.name]? with
        | none => seen := seen.insert ci.name (shard, m, ci)
        | some (s0, m0, c0) =>
          unless constInfoCompat c0 ci do
            conflicts := conflicts.push (toJson [ci.name.toString, s0, m0, shard, m])
  IO.FS.writeFile out (Json.mkObj [("conflicts", .arr conflicts), ("compared", toJson seen.size)]).compress
  return 0
"""


def lake_olean(checkout: Path, module: str) -> Path:
    return checkout / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")


def reconcile(shard_modules: dict[str, list[tuple[str, Path]]], lean: Path = LEAN) -> dict:
    """Header export per shard, multi-module/cross-shard candidate detection, exact structural comparison.

    `shard_modules` maps shard name to `(module, olean path)` pairs. Returns the header
    counts, the candidate names realized in two or more module occurrences, and every conflict.
    """
    rows = [[shard, [module, str(path)]] for shard, mods in sorted(shard_modules.items()) for module, path in mods]
    with tempfile.TemporaryDirectory(prefix="anneal-reconcile-") as tmp:
        tmp_path = Path(tmp)
        source = tmp_path / "Reconcile.lean"
        source.write_text(RECONCILE_SOURCE)
        request = tmp_path / "request.json"
        request.write_text(json.dumps({"modules": rows}))
        headers_dir = tmp_path / "headers"
        headers_dir.mkdir()

        def lean_run(mode: str, out: Path) -> None:
            proc = subprocess.run([str(lean), "--run", str(source), mode, str(request), str(out)],
                                  cwd=tmp_path, capture_output=True, text=True, check=False)
            if proc.returncode != 0:
                detail = (proc.stderr + proc.stdout).strip()[-2000:]
                raise Failure(1 if "policy:" in detail else 2, "reconcile", f"Lean {mode} exited {proc.returncode}: {detail}")

        lean_run("headers", headers_dir)
        owners: dict[str, set[tuple[str, str]]] = {}
        counts: dict[str, int] = {}
        for shard in shard_modules:
            path = headers_dir / (shard.replace("/", "__") + ".jsonl")
            lines = path.read_text().splitlines() if path.is_file() else []
            counts[shard] = len(lines)
            for line in lines:
                header = json.loads(line)
                if not (isinstance(header, list) and len(header) == 9 and isinstance(header[0], list)):
                    raise Failure(2, "reconcile", f"malformed declaration header in {shard}")
                key = json.dumps(header[0], separators=(",", ":"))
                owners.setdefault(key, set()).add((shard, str(header[2])))
        candidates = [json.loads(k) for k, s in sorted(owners.items()) if len(s) >= 2]
        result = {"headers": counts, "declarations": len(owners), "candidates": len(candidates), "conflicts": []}
        if candidates:
            request.write_text(json.dumps({"modules": rows, "candidates": candidates}))
            out = tmp_path / "compare.json"
            lean_run("compare", out)
            result["conflicts"] = json.loads(out.read_text())["conflicts"]
    return result


def fresh_lake_olean(checkout: Path, module: str, rel: str) -> Path | None:
    """The Lake `.olean` of `module` only if it was built from *this* checkout's source and
    is not older than it (a `.lake` copied from another checkout, or a stale build, is
    evidence about different bytes and must not be reconciled)."""
    olean, source = lake_olean(checkout, module), checkout / rel
    trace = olean.with_suffix(".trace")
    try:
        if not (olean.is_file() and trace.is_file() and source.is_file()):
            return None
        inputs = json.dumps(json.loads(trace.read_text()).get("inputs", []))
        if json.dumps(str(source.resolve())) not in inputs or olean.stat().st_mtime < source.stat().st_mtime:
            return None
    except (OSError, ValueError):
        return None
    return olean


def reconcile_lake(checkout: Path = REPO_ROOT, manifest: dict | None = None, *, required: bool = True) -> dict:
    """Reconcile every fresh compiled Lake shard of the plan (absent, foreign, or stale
    builds are counted, never trusted)."""
    manifest = plan_shards(checkout) if manifest is None else manifest
    paths = ct.lake_modules(checkout)
    shard_modules: dict[str, list[tuple[str, Path]]] = {}
    unusable = 0
    for shard in manifest["shards"]:
        if shard["kind"] != "lake":
            continue
        for module in shard["modules"]:
            path = fresh_lake_olean(checkout, module, paths.get(module, ""))
            if path is not None:
                shard_modules.setdefault(shard["name"], []).append((module, path))
            else:
                unusable += 1
    if not shard_modules:
        if required:
            raise Failure(2, "reconcile", "no fresh Lake builds of this checkout to reconcile; run `lake build` first")
        return {"headers": {}, "declarations": 0, "candidates": 0, "conflicts": [], "unbuiltOrStaleModules": unusable}
    result = reconcile(shard_modules)
    result["unbuiltOrStaleModules"] = unusable
    return result


# ---------------------------------------------------------------------------
# Equivalence with the monolithic audit
# ---------------------------------------------------------------------------

def audit_report(checkout: Path, cache_dir: Path | None, targets=None, keep: tuple[list[str], Path] | None = None) -> dict:
    """In-process `check_trusted.Checker(--fast).run`, cleaning its stage afterwards.

    `keep = (modules, directory)` copies the freshly compiled, audited `.olean` of each
    listed downstream module into `directory` before the stage is removed."""
    checker = ct.Checker(checkout, fast=True, cache_dir=cache_dir)
    try:
        report = checker.run(check_downstream=True, targets=targets)
        if keep is not None:
            keep[1].mkdir(parents=True, exist_ok=True)
            for module in keep[0]:
                olean = Path(checker.artifacts[module][0][0])
                shutil.copyfile(olean, keep[1] / f"{module}.olean")
        return report
    finally:
        ct.make_tree_writable(checker.stage)
        shutil.rmtree(checker.stage, ignore_errors=True)


def verify_equivalence(checkout: Path = REPO_ROOT, cache_dir: Path | None = None) -> dict:
    """Sharded audits vs the monolithic `check_trusted.py --fast` audit."""
    manifest = plan_shards(checkout)
    orphan = orphan_gate(checkout, manifest)
    keep_root = Path(tempfile.mkdtemp(prefix="anneal-equivalence-"))
    try:
        return _verify_equivalence(checkout, cache_dir, manifest, orphan, keep_root)
    finally:
        shutil.rmtree(keep_root, ignore_errors=True)


def _verify_equivalence(checkout: Path, cache_dir: Path | None, manifest: dict, orphan: dict, keep_root: Path) -> dict:
    all_downstream = [t[0] for t in ct.DOWNSTREAM_TARGETS]
    mono = audit_report(checkout, cache_dir, keep=(all_downstream, keep_root / "mono"))
    trusted_keys = ("kernelDeclarations", "axioms", "graph", "inductiveReplay")
    mono_down = mono["downstream"]
    covered: set[str] = set()
    claims = test_axioms = 0
    shards = []
    for shard in (s for s in manifest["shards"] if s["kind"] == "downstream"):
        targets = ct.resolve_exact_modules(",".join(shard["modules"]))
        report = audit_report(checkout, cache_dir, targets, keep=(shard["modules"], keep_root / shard["name"]))
        for key in trusted_keys:
            if report[key] != mono[key]:
                raise Failure(1, "equivalence", f"shard {shard['name']} disagrees on Trusted {key}")
        down = report["downstream"]
        covered.update(down["downstreamModules"])
        own = set(shard["modules"])
        roles = {m: r for m, _, _, r in targets}
        # Claim and test modules are never imported by other targets, so they are audited
        # exactly once: by the shard that owns them.
        if any(roles[m] == "claim" for m in own):
            claims += down["claimTheoremsChecked"]
        if any(roles[m] == "test" for m in own):
            test_axioms += down["localTestAxioms"]
        shards.append({"name": shard["name"], "modules": len(targets),
                       "replayedDeclarations": down["replayedDeclarations"],
                       "inductiveConstants": down["inductiveReplay"]["inductiveConstants"]})
    if covered != set(mono_down["downstreamModules"]):
        raise Failure(1, "equivalence", "sharded downstream coverage differs from monolithic")
    if (claims, test_axioms) != (mono_down["claimTheoremsChecked"], mono_down["localTestAxioms"]):
        raise Failure(1, "equivalence", "sharded claim/test-axiom counts differ from monolithic")
    # Exact cross-shard reconciliation over the artifacts the shards actually audited (each
    # shard contributes the modules it owns, so the shards partition the downstream modules),
    # and declaration-set parity with the monolithic audit's artifacts.
    downstream_shards = {s["name"]: [(m, keep_root / s["name"] / f"{m}.olean") for m in s["modules"]]
                         for s in manifest["shards"] if s["kind"] == "downstream"}
    sharded = reconcile(downstream_shards)
    monolithic = reconcile({"mono": [(m, keep_root / "mono" / f"{m}.olean") for m in all_downstream]})
    if sharded["conflicts"]:
        raise Failure(1, "equivalence", f"cross-shard constant conflicts: {sharded['conflicts'][:5]}")
    if sharded["declarations"] != monolithic["declarations"] or sum(sharded["headers"].values()) != sum(
            monolithic["headers"].values()):
        raise Failure(1, "equivalence", "sharded downstream declaration set differs from monolithic")
    lake = reconcile_lake(checkout, manifest, required=False)
    if lake["conflicts"]:
        raise Failure(1, "equivalence", f"cross-shard Lake constant conflicts: {lake['conflicts'][:5]}")
    return {"orphan": orphan, "axioms": mono["axioms"], "trustedDeclarations": mono["kernelDeclarations"],
            "downstreamModules": len(covered), "claimTheoremsChecked": claims, "localTestAxioms": test_axioms,
            "shards": shards, "downstreamReconciliation": sharded, "downstreamDeclarations": monolithic["declarations"],
            "lakeReconciliation": lake, "violation_subject_parity_with_monolithic": True}


# ---------------------------------------------------------------------------
# Lean source peer guards (Guards 6a and 6b)
# ---------------------------------------------------------------------------

ASSUMPTION_ATOMS = ("assumesHold", "assumes_hold")
ATOM_NAMESPACES = ("", "Verifrag")
MAX_LET_ALIAS_DEPTH = 8
BINDER_STOPS = {"if", "let", "fun", "λ", "match", "∀", "∃", "forall", "exists", "Π"}
DECL_KEYWORDS = {"theorem", "lemma", "def", "abbrev", "instance", "example", "axiom", "opaque", "variable"}
# Commands that end the preceding declaration without starting a scanned one.
COMMAND_STOPS = {"inductive", "structure", "class", "namespace", "section", "end", "open", "mutual", "attribute",
                 "set_option", "universe", "deriving", "macro", "syntax", "notation", "infix", "infixl", "infixr",
                 "prefix", "postfix", "#check", "#eval", "#print", "#guard_msgs", "#reduce"}
OPEN = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}
CLOSE = set(OPEN.values())
_TOKEN = re.compile(
    r"""(?P<str>"(?:\\.|[^"\\])*")|(?P<chr>'(?:\\.|[^'\\])')|"""
    r"""(?P<id>[A-Za-z_\u0370-\u03bb\u03bd-\u03ff«][\w'!?\u0370-\u03ff»]*(?:\.[A-Za-z_\u0370-\u03ff«][\w'!?\u0370-\u03ff»]*)*)|"""
    r"""(?P<num>\d[\w.]*)|(?P<op><==>|==>|<->|->|:=|=>|\|\||&&|==|!=|::)|(?P<ch>\S)""")


class GuardViolation(Exception):
    """A Lean source Guard 6a / 6b violation."""

    def __init__(self, guard: str, reason: str, path: str, line: int):
        super().__init__(f"{path}:{line}: [{guard}] {reason}")
        self.guard, self.reason, self.path, self.line = guard, reason, path, line


_COMMENT_START = re.compile(r'/-|--|"')
_BLOCK_EDGE = re.compile(r"/-|-/")
_STRING = re.compile(r'"(?:\\.|[^"\\])*"')


def strip_lean_comments(text: str) -> str:
    """Blank out `--` and nested `/- -/` comments (keeping offsets and line breaks)."""
    out, i, n = [], 0, len(text)
    while (m := _COMMENT_START.search(text, i)) is not None:
        j = m.start()
        out.append(text[i:j])
        if m.group() == '"':
            sm = _STRING.match(text, j)
            end = sm.end() if sm else n
            out.append(text[j:end])
        elif m.group() == "--":
            end = text.find("\n", j)
            end = n if end < 0 else end
            out.append(" " * (end - j))
        else:
            depth, end = 1, None
            for edge in _BLOCK_EDGE.finditer(text, j + 2):
                depth += 1 if edge.group() == "/-" else -1
                if depth == 0:
                    end = edge.end()
                    break
            if end is None:
                raise GuardViolation("lexer", "unterminated block comment", "<source>", text.count("\n", 0, j) + 1)
            out.append(re.sub(r"[^\n]", " ", text[j:end]))
        i = end
    out.append(text[i:])
    return "".join(out)


def _tokenize_rich(text: str) -> list[tuple[str, int, int]]:
    """`(token, line, offset)` triples of comment-stripped Lean source."""
    clean = strip_lean_comments(text)
    tokens, line, last = [], 1, 0
    for match in _TOKEN.finditer(clean):
        line += clean.count("\n", last, match.start())
        last = match.start()
        token = match.group(0)
        namespace, _, leaf = token.rpartition(".")
        # `.assumesHold` (dot notation) and `Other.assumesHold` name different constants.
        if leaf in ASSUMPTION_ATOMS and (namespace not in ATOM_NAMESPACES or (tokens and tokens[-1][0] == ".")):
            token = f"{token}\u2020"
        tokens.append((token, line, match.start()))
    return tokens


def tokenize(text: str) -> list[tuple[str, int]]:
    """`(token, line)` pairs of comment-stripped Lean source."""
    return [(t, l) for t, l, _ in _tokenize_rich(text)]


def _is_atom(token: str) -> bool:
    namespace, _, leaf = token.rpartition(".")
    return leaf in ASSUMPTION_ATOMS and namespace in ATOM_NAMESPACES


def _group_end(toks: list, i: int) -> int:
    """Index one past the group opened at `i`."""
    depth = 0
    for j in range(i, len(toks)):
        if toks[j][0] in OPEN:
            depth += 1
        elif toks[j][0] in CLOSE:
            depth -= 1
            if depth == 0:
                return j + 1
    raise GuardViolation("lexer", "unbalanced delimiter", "<source>", toks[i][1])


def _split(toks: list, ops: set[str], stops: set[str] = BINDER_STOPS):
    i = 0
    while i < len(toks):
        t = toks[i][0]
        if t in stops:
            return None
        if t in ops:
            return toks[:i], toks[i + 1:]
        i = _group_end(toks, i) if t in OPEN else i + 1
    return None


class PolarityScanner:
    """Guard 6a polarity analysis of Lean propositions (mirrors the Rust `PolarityAnalyzer`)."""

    def __init__(self, path: str, helpers: set[str] | None = None):
        self.path, self.helpers, self.aliases = path, set(helpers or ()), []

    def _is_helper(self, token: str) -> bool:
        return token in self.helpers or token.split(".")[-1] in self.helpers

    def _mentions(self, toks: list, limit: int, depth: int = 0) -> bool:
        if depth > MAX_LET_ALIAS_DEPTH:
            raise GuardViolation("6a", "let-alias chain exceeds depth 8", self.path, toks[0][1] if toks else 0)
        for tok in toks:
            t = tok[0]
            if _is_atom(t) or self._is_helper(t):
                return True
            for i in range(min(limit, len(self.aliases)) - 1, -1, -1):
                if self.aliases[i][0] == t:
                    if self._mentions(self.aliases[i][1], i, depth + 1):
                        return True
                    break
        return False

    def _occurrence(self, sign, antecedent: bool, line: int) -> None:
        if sign == "neg":
            return
        if sign == "pos":
            reason = "assumesHold negated inside an antecedent" if antecedent else "assumesHold in positive position"
        else:
            reason = sign[1]
        raise GuardViolation("6a", reason, self.path, line)

    def _analyze_binder_group(self, group: list, sign, antecedent: bool, inline: int) -> None:
        colon = None
        i = 0
        while i < len(group):
            t = group[i][0]
            if t == ":":
                colon = i
                break
            i = _group_end(group, i) if t in OPEN else i + 1
        if colon is not None:
            if self._mentions(group[:colon], len(self.aliases)):
                raise GuardViolation("6a", "assumesHold in an unclean binder", self.path, group[0][1])
            self.analyze(group[colon + 1:], sign, antecedent, inline)
        elif self._mentions(group, len(self.aliases)):
            raise GuardViolation("6a", "assumesHold in an unclean binder", self.path, group[0][1])

    def analyze(self, toks: list, sign="pos", antecedent: bool = False, inline: int = 0) -> None:
        if not toks:
            return
        head = toks[0][0]
        if head == "let":
            return self._let(toks, sign, antecedent, inline)
        both = lambda why: ("both", why)  # noqa: E731
        if (s := _split(toks, {"↔", "<->", "<==>"})) is not None:
            for part in s:
                self.analyze(part, both("assumesHold under iff"), antecedent, inline)
            return
        if (s := _split(toks, {"→", "->", "==>"})) is not None:
            flipped = {"pos": "neg", "neg": "pos"}.get(sign, sign) if isinstance(sign, str) else sign
            lhs = s[0]
            if lhs and lhs[0][0] in ("(", "{", "[") and _group_end(lhs, 0) == len(lhs):
                inner = lhs[1:-1]
                # Dependent arrow `(h : assumesHold) → P`
                k = 0
                has_colon = False
                while k < len(inner):
                    if inner[k][0] == ":":
                        has_colon = True
                        break
                    k = _group_end(inner, k) if inner[k][0] in OPEN else k + 1
                if has_colon:
                    self._analyze_binder_group(inner, flipped, True, inline)
                else:
                    self.analyze(inner, flipped, True, inline)
            else:
                self.analyze(lhs, flipped, True, inline)
            return self.analyze(s[1], sign, antecedent, inline)
        for ops in ({"∨", "||"}, {"∧", "&&"}):
            if (s := _split(toks, ops)) is not None:
                self.analyze(s[0], sign, antecedent, inline)
                return self.analyze(s[1], sign, antecedent, inline)
        if head in ("¬", "!", "not"):
            flipped = {"pos": "neg", "neg": "pos"}.get(sign, sign) if isinstance(sign, str) else sign
            return self.analyze(toks[1:], flipped, antecedent, inline)
        if head == "if":
            depth, if_depth, then_i, else_i = 0, 0, None, None
            for i in range(1, len(toks)):
                t = toks[i][0]
                if t in OPEN:
                    depth += 1
                elif t in CLOSE:
                    depth -= 1
                elif depth == 0:
                    if t == "if":
                        if_depth += 1
                    elif t == "then" and if_depth == 0 and then_i is None:
                        then_i = i
                    elif t == "else":
                        if if_depth > 0:
                            if_depth -= 1
                        elif then_i is not None:
                            else_i = i
                            break
            if then_i is None:
                return self._leaf(toks, sign, antecedent, inline)
            self.analyze(toks[1:then_i], both("assumesHold in an if condition"), antecedent, inline)
            self.analyze(toks[then_i + 1:else_i], sign, antecedent, inline)
            return self.analyze(toks[else_i + 1:] if else_i else [], sign, antecedent, inline)
        if head in ("∀", "∃", "forall", "exists", "Π"):
            universal = head in ("∀", "forall", "Π")
            comma = None
            i = 1
            while i < len(toks):
                if toks[i][0] == ",":
                    comma = i
                    break
                i = _group_end(toks, i) if toks[i][0] in OPEN else i + 1
            if comma is None:
                return self._leaf(toks, sign, antecedent, inline)
            binder_sign = ({"pos": "neg", "neg": "pos"}.get(sign, sign) if isinstance(sign, str) else sign) if universal else sign
            binders, i = toks[1:comma], 0
            groups = []
            while i < len(binders):
                if binders[i][0] in OPEN:
                    end = _group_end(binders, i)
                    groups.append(binders[i + 1:end - 1])
                    i = end
                else:
                    i += 1
            for group in groups or [binders]:
                self._analyze_binder_group(group, binder_sign, antecedent or universal, inline)
            return self.analyze(toks[comma + 1:], sign, antecedent, inline)
        if head in OPEN and _group_end(toks, 0) == len(toks):
            return self.analyze(toks[1:-1], sign, antecedent, inline)
        return self._leaf(toks, sign, antecedent, inline)

    def _let(self, toks: list, sign, antecedent: bool, inline: int) -> None:
        if len(toks) < 2 or not re.match(r"[A-Za-z_]", toks[1][0]):
            return self._leaf(toks, sign, antecedent, inline)
        name = toks[1][0]
        eq = None
        i = 2
        while i < len(toks):
            if toks[i][0] == ":=":
                eq = i
                break
            i = _group_end(toks, i) if toks[i][0] in OPEN else i + 1
        if eq is None:
            return self._leaf(toks, sign, antecedent, inline)
        if self._mentions(toks[2:eq], len(self.aliases)):
            raise GuardViolation("6a", "assumesHold in a let type annotation", self.path, toks[2][1])
        end, i = len(toks), eq + 1
        while i < len(toks):
            t, line = toks[i][0], toks[i][1]
            if t in (";", "in") or (i > eq + 1 and line > toks[i - 1][1]):
                end = i
                break
            i = _group_end(toks, i) if t in OPEN else i + 1
        skip = 1 if end < len(toks) and toks[end][0] in (";", "in") else 0
        value, body = toks[eq + 1:end], toks[end + skip:]
        if not body:
            return self._leaf(value, sign, antecedent, inline)
        if len(self.aliases) >= MAX_LET_ALIAS_DEPTH:
            raise GuardViolation("6a", "let-alias chain exceeds depth 8", self.path, toks[0][1])
        self.aliases.append((name, value))
        try:
            self.analyze(body, sign, antecedent, inline)
        finally:
            self.aliases.pop()

    def _leaf(self, toks: list, sign, antecedent: bool, inline: int) -> None:
        if not self._mentions(toks, len(self.aliases)):
            return
        if len(toks) == 1 and _is_atom(toks[0][0]):
            return self._occurrence(sign, antecedent, toks[0][1])
        if len(toks) == 1:
            for i in range(len(self.aliases) - 1, -1, -1):
                if self.aliases[i][0] == toks[0][0]:
                    if inline >= MAX_LET_ALIAS_DEPTH:
                        raise GuardViolation("6a", "let-alias chain exceeds depth 8", self.path, toks[0][1])
                    saved = self.aliases
                    self.aliases = saved[:i]
                    try:
                        return self.analyze(saved[i][1], sign, antecedent, inline + 1)
                    finally:
                        self.aliases = saved
        raise GuardViolation("6a", "assumesHold inside an unclean Boolean/application leaf", self.path, toks[0][1])


_DECL_MODIFIERS = {"private", "protected", "noncomputable", "partial", "unsafe", "local", "scoped"}


def _is_private_decl(toks: list, start: int) -> bool:
    """Whether `toks[start]` is preceded by a `private` visibility modifier."""
    j = start - 1
    while j >= 0:
        t = toks[j][0]
        if t == "private":
            return True
        if t in _DECL_MODIFIERS:
            j -= 1
            continue
        if t == "]":
            depth = 1
            j -= 1
            while j >= 0 and depth > 0:
                if toks[j][0] == "]":
                    depth += 1
                elif toks[j][0] == "[":
                    depth -= 1
                j -= 1
            if j >= 0 and toks[j][0] == "@":
                j -= 1
                continue
            return False
        break
    return False


def _declarations(toks: list):
    """`(keyword, name, signature tokens, body tokens, start_idx)` for each top-level declaration."""
    n = len(toks)
    bounds, depth = [], 0
    for k, tok in enumerate(toks):
        t = tok[0]
        if t in OPEN:
            depth += 1
        elif t in CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and (t in DECL_KEYWORDS or t in COMMAND_STOPS):
            bounds.append(k)
    for index, start in enumerate(bounds):
        if toks[start][0] not in DECL_KEYWORDS:
            continue
        end = bounds[index + 1] if index + 1 < len(bounds) else n
        kw = toks[start][0]
        rest = toks[start + 1:end]
        name = rest[0][0] if rest and kw not in ("example", "variable") and re.match(r"[A-Za-z_«]", rest[0][0]) else ""
        split, lets, in_match, i = None, 0, False, 0
        while i < len(rest):
            t = rest[i][0]
            if t == "let":
                lets += 1
            elif t == ":=" and lets:
                lets -= 1  # a `let x := v` binding inside the statement
            elif t == "match":
                in_match = True
            elif t in (":=", "where") or (t == "|" and not in_match):
                split = i
                break
            i = _group_end(rest, i) if t in OPEN else i + 1
        sig, body = (rest, []) if split is None else (rest[:split], rest[split + 1:])
        yield kw, name, sig, body, start


def assumption_helpers(files: dict[str, list]) -> set[str]:
    """`def` / `abbrev` / `opaque` names whose bodies (transitively) mention the assumption atom."""
    helpers: set[str] = set()
    changed = True
    while changed:
        changed = False
        for toks in files.values():
            for kw, name, _sig, body, _start in _declarations(toks):
                if kw in ("def", "abbrev", "opaque") and name and name not in helpers:
                    if any(_is_atom(tok[0]) or tok[0] in helpers or tok[0].split(".")[-1] in helpers for tok in body):
                        helpers.add(name)
                        changed = True
    return helpers


def scan_polarity(path: str, toks: list, helpers: set[str]) -> None:
    """Guard 6a over one file: binders negative, declared types positive; helper bodies are
    positive propositions and every use of a helper elsewhere is an unclean leaf."""
    for kw, name, sig, body, _start in _declarations(toks):
        others = helpers - {name}
        scanner = PolarityScanner(path, others)
        if not any(_is_atom(tok[0]) or scanner._is_helper(tok[0]) for tok in sig + body):
            continue
        i, colon = 0, None
        while i < len(sig):
            t = sig[i][0]
            if t in OPEN:
                end = _group_end(sig, i)
                group = sig[i + 1:end - 1]
                scanner._analyze_binder_group(group, "neg", True, 0)
                i = end
                continue
            if t == ":" and colon is None:
                colon = i
                break
            i += 1
        if colon is not None:
            scanner.analyze(sig[colon + 1:], "pos")
        if kw in ("def", "abbrev", "opaque") and any(_is_atom(tok[0]) or scanner._is_helper(tok[0]) for tok in body):
            PolarityScanner(path, others).analyze(body, "pos")


def _doc_tag(text: str, end: int, tag: str) -> bool:
    """Whether the docstring immediately preceding offset `end` (modulo attributes and
    `private` / `protected` modifiers) carries `tag`."""
    prefix = text[max(0, end - 4096):end]
    while True:
        trimmed = re.sub(r"(?:@\[[^\]]*\]|\bprivate|\bprotected|\bnoncomputable|\bpartial|\bunsafe|\blocal|\bscoped)\s*$",
                         "", prefix.rstrip())
        if trimmed == prefix.rstrip():
            prefix = trimmed
            break
        prefix = trimmed
    if not prefix.endswith("-/"):
        return False
    start = prefix.rfind("/--")
    return start >= 0 and re.search(rf"{re.escape(tag)}\b", prefix[start:]) is not None


_SCOPE_STOPS = DECL_KEYWORDS | COMMAND_STOPS | _DECL_MODIFIERS | {"@"}


def _sig_bound_names(sig: list) -> set[str]:
    """Parameter names introduced by binders in a declaration signature."""
    names: set[str] = set()
    i = 0
    while i < len(sig):
        t = sig[i][0]
        if t in ("(", "{", "[", "⦃"):
            end = _group_end(sig, i)
            inner = sig[i + 1:end - 1]
            for tok in inner:
                if tok[0] == ":":
                    break
                if re.fullmatch(r"[A-Za-z_][\w']*", tok[0]):
                    names.add(tok[0])
            i = end
            continue
        if t == ":":
            break
        i += 1
    return names


def _return_type_heads(sig: list) -> set[str]:
    """Candidate head type names of a declaration's codomain (after top-level `:` and arrows)."""
    i, colon = 0, None
    while i < len(sig):
        if sig[i][0] in OPEN:
            i = _group_end(sig, i)
            continue
        if sig[i][0] == ":":
            colon = i
            break
        i += 1
    if colon is None:
        return set()
    ret = sig[colon + 1:]
    # Peel top-level arrows `A → B` and binders `∀ ..., B` to reach the final codomain.
    while ret:
        split_at = None
        k = 0
        while k < len(ret):
            if ret[k][0] in OPEN:
                k = _group_end(ret, k)
                continue
            if ret[k][0] in ("→", "->", ","):
                split_at = k
            k += 1
        if split_at is None:
            break
        ret = ret[split_at + 1:]
    while ret and ret[0][0] in OPEN and _group_end(ret, 0) == len(ret):
        ret = ret[1:-1]
    if not ret:
        return set()
    head = ret[0][0]
    return {head, head.split(".")[-1]}


def _has_struct_literal_or_anon_ctor(body: list, return_is_sealed: bool, sealed_types: set[str]) -> int | None:
    """Return line number if `body` constructs a sealed structure via `⟨...⟩` or `{ ... := ... }`."""
    def check_slice(toks: list, allow_return: bool) -> int | None:
        i = 0
        while i < len(toks):
            t, line = toks[i][0], toks[i][1]
            if t == "⟨":
                end = _group_end(toks, i)
                if allow_return:
                    return line
                # Explicit type ascription `(⟨...⟩ : R)` inside parent group
                if end < len(toks) and toks[end][0] == ":" and end + 1 < len(toks):
                    ty = toks[end + 1][0]
                    if ty in sealed_types or ty.split(".")[-1] in sealed_types:
                        return line
                sub = check_slice(toks[i + 1:end - 1], False)
                if sub is not None:
                    return sub
                i = end
                continue
            if t == "{":
                end = _group_end(toks, i)
                inner = toks[i + 1:end - 1]
                # Structure literal `{ field := val }` or `{ x with field := val }`
                is_struct_lit = False
                k = 0
                explicit_ty = None
                while k < len(inner):
                    if inner[k][0] in OPEN:
                        k = _group_end(inner, k)
                        continue
                    if inner[k][0] in (":=", "with"):
                        is_struct_lit = True
                    elif inner[k][0] == ":" and k + 1 < len(inner):
                        explicit_ty = inner[k + 1][0]
                    k += 1
                if is_struct_lit:
                    if allow_return:
                        return line
                    if explicit_ty and (explicit_ty in sealed_types or explicit_ty.split(".")[-1] in sealed_types):
                        return line
                    if end < len(toks) and toks[end][0] == ":" and end + 1 < len(toks):
                        ty = toks[end + 1][0]
                        if ty in sealed_types or ty.split(".")[-1] in sealed_types:
                            return line
                sub = check_slice(inner, False)
                if sub is not None:
                    return sub
                i = end
                continue
            if t in OPEN:
                end = _group_end(toks, i)
                # Preserve `allow_return` if parens wrap the whole expression or `(expr : R)`
                sub_allow = allow_return and (i == 0 and end == len(toks))
                sub = check_slice(toks[i + 1:end - 1], sub_allow)
                if sub is not None:
                    return sub
                i = end
                continue
            i += 1
        return None
    return check_slice(body, return_is_sealed)


def scan_sealing(path: str, text: str) -> None:
    """Guard 6b over one file: `@invariant` structures need `private <ctor> ::`, no
    `Inhabited` derivation or instance, no `extends` carrier, and no public declaration
    (other than an `@smart_constructor`) that reaches the raw constructor (directly, via
    `abbrev` type/constructor aliases, via `private` helpers, or via `⟨...⟩`/`{...}`)."""
    clean = strip_lean_comments(text)
    toks = _tokenize_rich(text)

    def scope_at(limit: int, decl_start: int | None = None) -> tuple[list[str], set[str], dict[str, str], set[str]]:
        """Namespace stack, opened namespaces, `open ... renaming` map, and explicit open ids."""
        frames: list[list[str]] = []
        opened: set[str] = set()
        renamed: dict[str, str] = {}
        explicit_ids: set[str] = set()
        i, depth = 0, 0
        while i < limit:
            t = toks[i][0]
            if t in OPEN:
                depth += 1
                i += 1
                continue
            if t in CLOSE:
                depth = max(0, depth - 1)
                i += 1
                continue
            if depth > 0:
                i += 1
                continue
            if t == "namespace" and i + 1 < limit:
                frames.append(toks[i + 1][0].split("."))
                i += 2
                continue
            if t == "end":
                if frames:
                    if i + 1 < limit and toks[i + 1][0] not in _SCOPE_STOPS and toks[i + 1][1] == toks[i][1]:
                        end_parts = toks[i + 1][0].split(".")
                        if frames[-1] == end_parts:
                            frames.pop()
                        i += 2
                        continue
                    frames.pop()
                i += 1
                continue
            if t == "open":
                j = i + 1
                cur_opened: set[str] = set()
                cur_renamed: dict[str, str] = {}
                cur_explicit: set[str] = set()
                saw_in = False
                in_idx = None
                while j < limit:
                    tj = toks[j][0]
                    if tj == "scoped":
                        j += 1
                        continue
                    if tj == "in":
                        saw_in = True
                        in_idx = j
                        j += 1
                        break
                    if tj in _SCOPE_STOPS:
                        break
                    if tj == "renaming":
                        k = j + 1
                        while k + 2 < limit and toks[k][0] not in _SCOPE_STOPS and toks[k][0] != "in":
                            if toks[k][0] == ",":
                                k += 1
                                continue
                            if toks[k + 1][0] in ("→", "->"):
                                cur_renamed[toks[k + 2][0]] = toks[k][0]
                                k += 3
                            else:
                                k += 1
                        j = k
                        continue
                    if tj == "(":
                        end_p = _group_end(toks, j)
                        for p in range(j + 1, min(end_p - 1, limit)):
                            if re.fullmatch(r"[A-Za-z_][\w']*", toks[p][0]):
                                cur_explicit.add(toks[p][0])
                        j = end_p
                        continue
                    cur_opened.add(tj)
                    cur_opened.add(tj.split(".")[-1])
                    j += 1
                if saw_in:
                    # `open ... in` scopes ONLY the immediately following declaration.
                    if decl_start is not None and in_idx is not None:
                        between = [toks[m][0] for m in range(in_idx + 1, decl_start)]
                        # Allow modifiers and @[...] attributes between `in` and decl keyword.
                        k = 0
                        ok = True
                        while k < len(between):
                            if between[k] in _DECL_MODIFIERS:
                                k += 1
                            elif between[k] == "@" and k + 1 < len(between) and between[k + 1] == "[":
                                k += 2
                                d = 1
                                while k < len(between) and d > 0:
                                    if between[k] == "[":
                                        d += 1
                                    elif between[k] == "]":
                                        d -= 1
                                    k += 1
                            else:
                                ok = False
                                break
                        if ok:
                            opened |= cur_opened
                            renamed.update(cur_renamed)
                            explicit_ids |= cur_explicit
                else:
                    opened |= cur_opened
                    renamed.update(cur_renamed)
                    explicit_ids |= cur_explicit
                i = j
                continue
            i += 1
        ns_flat = [seg for frame in frames for seg in frame]
        return ns_flat, opened, renamed, explicit_ids

    # Map character offset -> token index for namespace lookup of `@invariant` structures.
    sealed: dict[str, str] = {}
    for match in re.finditer(r"\b(structure|class)\s+([A-Za-z_][\w.']*)", clean):
        if not _doc_tag(text, match.start(), "@invariant"):
            continue
        raw_name = match.group(2)
        tok_idx = next((idx for idx, (_, _, off) in enumerate(toks) if off >= match.start()), len(toks))
        ns_flat, _, _, _ = scope_at(tok_idx)
        full_name = ".".join(ns_flat + [raw_name]) if ns_flat else raw_name
        line = clean.count("\n", 0, match.start()) + 1
        body_end = re.search(r"\n(?=\S)(?!deriving\b)", clean[match.end():])
        decl = clean[match.start(): match.end() + (body_end.start() if body_end else len(clean))]
        ctor = re.search(r"\bwhere\s+(private\s+)?([A-Za-z_][\w']*)\s*::", decl)
        if ctor is None or not ctor.group(1):
            raise GuardViolation("6b", f"invariant structure {full_name} lacks `private <ctor> ::`", path, line)
        if re.search(r"\bderiving\b[\s\S]*?\bInhabited\b", decl):
            raise GuardViolation("6b", f"invariant structure {full_name} derives Inhabited", path, line)
        sealed[full_name] = ctor.group(2)
    if not sealed:
        return

    # Map every short/qualified name of a sealed structure to its canonical full name.
    type_names: dict[str, str] = {}
    for full in sealed:
        type_names[full] = full
        type_names[full.split(".")[-1]] = full

    decls = list(_declarations(toks))
    # Pass 1: collect transitive `abbrev` type aliases (e.g. `abbrev RAlias := R`).
    changed = True
    while changed:
        changed = False
        for kw, name, _sig, body, start in decls:
            if kw != "abbrev" or not name or name in type_names or not body:
                continue
            ns_flat, _, _, _ = scope_at(start, start)
            full_alias = ".".join(ns_flat + [name]) if ns_flat else name
            if len(body) >= 1 and (body[0][0] in type_names or body[0][0].split(".")[-1] in type_names):
                # Exclude constructor aliases `R.mk`
                target = type_names.get(body[0][0]) or type_names.get(body[0][0].split(".")[-1])
                if target is not None and not any(tok[0] in ("→", "->", "×") for tok in body):
                    type_names[name] = target
                    type_names[full_alias] = target
                    changed = True

    all_sealed_types = set(type_names)
    for match in re.finditer(r"\bderiving\s+instance\b[\s\S]*?\bInhabited\b[\s\S]*?\bfor\b([^\n;]*)", clean):
        if any(re.search(rf"\b{re.escape(s)}\b", match.group(1)) for s in all_sealed_types):
            raise GuardViolation("6b", "standalone Inhabited derivation of an invariant structure", path,
                                 clean.count("\n", 0, match.start()) + 1)

    for match in re.finditer(r"\b(?:structure|class)\s+([A-Za-z_][\w.']*)(?:[^\n]|\n[ \t]+)*?\bextends\b([^\n]*)", clean):
        if any(re.search(rf"\b{re.escape(s)}\b", match.group(2)) for s in all_sealed_types) and not _doc_tag(
            text, match.start(), "@invariant"
        ):
            raise GuardViolation("6b", f"carrier structure {match.group(1)} extends an invariant structure", path,
                                 clean.count("\n", 0, match.start()) + 1)

    def body_reaches_sealed(body: list, sig: list, scope_info, ctor_aliases: set[str],
                            private_fwd: set[str]) -> int | None:
        ns_flat, opened, renamed, explicit_ids = scope_info
        sealed_ctors = set(sealed.values())
        direct_ctors: set[str] = set()
        for alias_ty, full in type_names.items():
            ctor = sealed[full]
            direct_ctors.add(f"{alias_ty}.{ctor}")
            direct_ctors.add(f"{full}.{ctor}")

        def token_hits(t: str, bound: set[str]) -> bool:
            if t in bound:
                return False
            last = t.split(".")[-1]
            if t in direct_ctors or t in ctor_aliases or last in ctor_aliases:
                return True
            if t in private_fwd or last in private_fwd:
                return True
            # Qualified `Ns.R.mk` matching a sealed `(full, ctor)` suffix
            for alias_ty, full in type_names.items():
                ctor = sealed[full]
                if t.endswith(f".{alias_ty}.{ctor}") or t.endswith(f".{full}.{ctor}"):
                    return True
                if t == ctor:
                    short_ty = full.split(".")[-1]
                    if (alias_ty in opened or full in opened or short_ty in opened
                            or short_ty in ns_flat or ctor in explicit_ids):
                        return True
                if t in renamed and renamed[t] == ctor:
                    return True
            if last != t and last in renamed and renamed[last] in sealed_ctors:
                return True
            return False

        def walk(toks_slice: list, bound: set[str]) -> int | None:
            local_bound = set(bound)
            i = 0
            while i < len(toks_slice):
                t, line = toks_slice[i][0], toks_slice[i][1]
                if t in ("fun", "λ"):
                    j = i + 1
                    while j < len(toks_slice) and toks_slice[j][0] not in ("=>", "↦"):
                        if toks_slice[j][0] in OPEN:
                            end_g = _group_end(toks_slice, j)
                            for tok in toks_slice[j + 1:end_g - 1]:
                                if tok[0] == ":":
                                    break
                                if re.fullmatch(r"[A-Za-z_][\w']*", tok[0]):
                                    local_bound.add(tok[0])
                            j = end_g
                        else:
                            if re.fullmatch(r"[A-Za-z_][\w']*", toks_slice[j][0]):
                                local_bound.add(toks_slice[j][0])
                            j += 1
                    i = j + 1
                    continue
                if t == "let" and i + 1 < len(toks_slice) and re.fullmatch(r"[A-Za-z_][\w']*", toks_slice[i + 1][0]):
                    let_name = toks_slice[i + 1][0]
                    eq = None
                    j = i + 2
                    while j < len(toks_slice):
                        if toks_slice[j][0] == ":=":
                            eq = j
                            break
                        j = _group_end(toks_slice, j) if toks_slice[j][0] in OPEN else j + 1
                    if eq is not None:
                        end_rhs, k = len(toks_slice), eq + 1
                        while k < len(toks_slice):
                            tk, ln = toks_slice[k][0], toks_slice[k][1]
                            if tk in (";", "in") or (k > eq + 1 and ln > toks_slice[k - 1][1]):
                                end_rhs = k
                                break
                            k = _group_end(toks_slice, k) if tk in OPEN else k + 1
                        # Check RHS BEFORE adding `let_name` to `local_bound`.
                        hit = walk(toks_slice[eq + 1:end_rhs], local_bound)
                        if hit is not None:
                            return hit
                        local_bound.add(let_name)
                        i = end_rhs + (1 if end_rhs < len(toks_slice) and toks_slice[end_rhs][0] in (";", "in") else 0)
                        continue
                if t in OPEN:
                    end_g = _group_end(toks_slice, i)
                    hit = walk(toks_slice[i + 1:end_g - 1], local_bound)
                    if hit is not None:
                        return hit
                    i = end_g
                    continue
                if token_hits(t, local_bound):
                    return line
                i += 1
            return None

        hit = walk(body, _sig_bound_names(sig))
        if hit is not None:
            return hit
        ret_is_sealed = bool(_return_type_heads(sig) & all_sealed_types)
        return _has_struct_literal_or_anon_ctor(body, ret_is_sealed, all_sealed_types)

    # Pass 2: fixed-point collection of `ctor_aliases` (`abbrev`) and `private_forwarders`.
    ctor_aliases: set[str] = set()
    private_forwarders: set[str] = set()
    changed = True
    while changed:
        changed = False
        for kw, name, sig, body, start in decls:
            if kw not in ("def", "abbrev", "instance", "theorem", "opaque") or not body or not name:
                continue
            scope_info = scope_at(start, start)
            ns_flat = scope_info[0]
            full_name = ".".join(ns_flat + [name]) if ns_flat else name
            is_priv = _is_private_decl(toks, start)
            if kw == "abbrev" and name not in ctor_aliases:
                if body_reaches_sealed(body, sig, scope_info, ctor_aliases, private_forwarders) is not None:
                    ctor_aliases.add(name)
                    ctor_aliases.add(full_name)
                    changed = True
            if is_priv and name not in private_forwarders:
                if body_reaches_sealed(body, sig, scope_info, ctor_aliases, private_forwarders) is not None:
                    private_forwarders.add(name)
                    private_forwarders.add(full_name)
                    changed = True

    # Pass 3: enforce sealing on every public non-`@smart_constructor` declaration.
    for kw, name, sig, body, start in decls:
        if kw not in ("def", "abbrev", "instance", "theorem", "opaque") or not body:
            continue
        start_line, kw_offset = toks[start][1], toks[start][2]
        sig_text = " ".join(tok[0] for tok in sig)
        if kw == "instance" and "Inhabited" in sig_text and any(
            re.search(rf"\b{re.escape(s)}\b", sig_text) for s in all_sealed_types
        ):
            raise GuardViolation("6b", "Inhabited instance of an invariant structure", path, start_line)
        if _is_private_decl(toks, start):
            continue
        if _doc_tag(text, kw_offset, "@smart_constructor"):
            continue
        scope_info = scope_at(start, start)
        hit_line = body_reaches_sealed(body, sig, scope_info, ctor_aliases, private_forwarders)
        if hit_line is not None:
            raise GuardViolation("6b", f"public declaration {name or kw} reaches a sealed raw constructor",
                                 path, hit_line)


def scan_peer_guards(paths: list[Path], root: Path = REPO_ROOT) -> dict:
    """Guards 6a and 6b over `.lean` files (directories are walked)."""
    files: list[Path] = []
    for p in paths:
        files += sorted(p.rglob("*.lean")) if p.is_dir() else [p]
    texts = {str(f.relative_to(root) if f.is_relative_to(root) else f): f.read_text(encoding="utf-8") for f in files}
    # Fixed-point expansion so multi-file transitive helper chains (FileA -> FileB -> FileC)
    # are always discovered and checked.
    tokens = {label: tokenize(text) for label, text in texts.items() if any(a in text for a in ASSUMPTION_ATOMS)}
    helpers: set[str] = set()
    while True:
        new_helpers = assumption_helpers(tokens)
        added_files = False
        for label, text in texts.items():
            if label not in tokens and any(h.split(".")[-1] in text for h in new_helpers):
                tokens[label] = tokenize(text)
                added_files = True
        if new_helpers == helpers and not added_files:
            break
        helpers = new_helpers
    for label, text in texts.items():
        if label in tokens:
            scan_polarity(label, tokens[label], helpers)
        if "@invariant" in text:
            scan_sealing(label, text)
    return {"files": len(texts), "assumptionHelpers": sorted(helpers)}


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--orphan-only", action="store_true")
    mode.add_argument("--plan", action="store_true")
    mode.add_argument("--run-shards", action="store_true")
    mode.add_argument("--reconcile", action="store_true")
    mode.add_argument("--verify-equivalence", action="store_true")
    mode.add_argument("--exact-modules", metavar="M1,M2,...")
    mode.add_argument("--scan-peer-guards", nargs="*", type=Path, metavar="PATH")
    parser.add_argument("--shard-manifest", type=Path, help="explicit manifest for --orphan-only")
    parser.add_argument("--cache-dir", type=Path, help="shared --fast cache directory outside the checkout")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args(argv)
    try:
        if args.orphan_only:
            manifest = json.loads(args.shard_manifest.read_text()) if args.shard_manifest else None
            summary = orphan_gate(REPO_ROOT, manifest)
            print(f"PASS: shard partition complete; {json.dumps(summary, sort_keys=True)}")
        elif args.plan:
            print(json.dumps(plan_shards(REPO_ROOT), indent=2, sort_keys=True))
        elif args.run_shards:
            results = run_shards(REPO_ROOT, args.cache_dir, args.jobs)
            print(json.dumps(results, indent=2))
            failed = [r for r in results if r["returncode"] != 0]
            if failed:
                return max(r["returncode"] for r in failed if r["returncode"] in (1, 2)) if all(
                    r["returncode"] in (1, 2) for r in failed) else 2
            print(f"PASS: {len(results)} downstream shards")
        elif args.reconcile:
            result = reconcile_lake(REPO_ROOT)
            if result["conflicts"]:
                raise Failure(1, "reconcile", f"cross-shard conflicts: {result['conflicts'][:5]}")
            print(f"PASS: cross-shard reconciliation; {json.dumps(result, sort_keys=True)}")
        elif args.verify_equivalence:
            summary = verify_equivalence(REPO_ROOT, args.cache_dir)
            print(f"PASS: sharded audit equivalent to monolithic; {json.dumps(summary, sort_keys=True)}")
        elif args.exact_modules is not None:
            ct.resolve_exact_modules(args.exact_modules)
            result = run_shard(REPO_ROOT, [m.strip() for m in args.exact_modules.split(",")], args.cache_dir)
            print(json.dumps(result, indent=2))
            return result["returncode"]
        else:
            paths = args.scan_peer_guards or [REPO_ROOT / "theory/Anneal"]
            summary = scan_peer_guards([p if p.is_absolute() else REPO_ROOT / p for p in paths])
            print(f"PASS: Lean Guards 6a/6b; {json.dumps(summary, sort_keys=True)}")
    except Failure as error:
        print(f"Sharded audit failed ({error.phase}): {error}", file=sys.stderr)
        return error.code
    except GuardViolation as error:
        print(f"Peer guard violation: {error}", file=sys.stderr)
        return 1
    except (OSError, ValueError, KeyError) as error:
        print(f"Sharded audit failed (operational): {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
