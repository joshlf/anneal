#!/usr/bin/env python3
"""Isolated Track P prototype: lean4#16717 inductive replay, grmf sharded audit, and peer-verifier spec guards.

Zero-TCB Python 3.11+ stdlib-only implementation with 1-for-1 wire-schema parity
against `Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto`.
"""

from __future__ import annotations

import argparse
import concurrent.futures
from dataclasses import dataclass
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
from typing import Any

sys.dont_write_bytecode = True

# ---------------------------------------------------------------------------
# 1. Cross-Language Frozen Wire Schema (1-for-1 Parity with Lean)
# ---------------------------------------------------------------------------

SCHEMA_VERSION = 1

# Frozen baseline ranks 0..2 from `Anneal.SpecBoundaryGuards.SpecBoundaryGuardClass`
# (read-only reference for disjointness checks; never duplicated as candidate ranks).
SPEC_BOUNDARY_GUARDS: tuple[dict[str, Any], ...] = (
    {
        "rank": 0,
        "guard_id": "entry_point_requires",
        "canonical_name": "EntryPointPrecondition",
        "vacuity_class": "DeadPrecondition",
        "source_ref": "verus#3606",
    },
    {
        "rank": 1,
        "guard_id": "fixed_width_ghost_length",
        "canonical_name": "FixedWidthGhostLength",
        "vacuity_class": "SpecViolation",
        "source_ref": "Slate#121",
    },
    {
        "rank": 2,
        "guard_id": "error_branch_wildcard",
        "canonical_name": "ErrorBranchWildcard",
        "vacuity_class": "SurvivedAllMutants",
        "source_ref": "awsm2",
    },
)

# Candidate ranks 3..6 matching `PeerSpecGuardClass.wire_table`.
PEER_SPEC_GUARDS: tuple[dict[str, Any], ...] = (
    {
        "rank": 3,
        "guard_id": "unsatisfiable_extern_ensures",
        "canonical_name": "UnsatisfiableExternEnsures",
        "vacuity_class": "SpecViolation",
        "source_ref": "creusot#2388",
    },
    {
        "rank": 4,
        "guard_id": "fndef_ghost_token_coercion",
        "canonical_name": "FnDefGhostTokenCoercion",
        "vacuity_class": "SpecViolation",
        "source_ref": "creusot#2389",
    },
    {
        "rank": 5,
        "guard_id": "external_type_drop_omission",
        "canonical_name": "ExternalTypeDropOmission",
        "vacuity_class": "SpecViolation",
        "source_ref": "verus#3514",
    },
    {
        "rank": 6,
        "guard_id": "assumption_polarity_and_struct_sealing",
        "canonical_name": "AssumptionPolarityAndStructSealing",
        "vacuity_class": "TrivialPostcondition",
        "source_ref": "Verifrag cl/1029131309 + Samite cl/1029680381",
    },
)

PEER_GUARD_BY_ID: dict[str, dict[str, Any]] = {g["guard_id"]: g for g in PEER_SPEC_GUARDS}

INDUCTIVE_REPLAY_VIOLATION_CODES: tuple[str, ...] = (
    "key_mismatch",
    "self_not_in_all",
    "duplicate_in_all",
    "non_induct_in_all",
    "mutual_metadata_mismatch",
    "duplicate_in_ctors",
    "non_ctor_in_ctors",
    "ctor_induct_mismatch",
    "ctor_cidx_mismatch",
    "dangling_ctor_not_listed_in_induct",
    "indices_mismatch",
    "is_rec_mismatch",
)

SHARD_AUDIT_VIOLATION_CODES: tuple[str, ...] = (
    "empty_shard_list",
    "empty_shard",
    "duplicate_module_in_shard",
    "overlapping_shards",
    "unregistered_module_in_shard",
    "uncovered_registered_module",
    "unregistered_on_disk_orphan",
    "disallowed_transitive_axiom",
    "missing_dependency_decl",
)

PEER_GUARD_VIOLATION_CODES: tuple[str, ...] = (
    "unsatisfiable_extern_ensures",
    "fndef_ghost_token_coercion",
    "external_type_drop_omission",
    "external_type_body_with_drop",
    "assumption_positive_polarity",
    "unsealed_invariant_struct",
)

PEER_VIOLATION_TO_GUARD_ID: dict[str, str] = {
    "unsatisfiable_extern_ensures": "unsatisfiable_extern_ensures",
    "fndef_ghost_token_coercion": "fndef_ghost_token_coercion",
    "external_type_drop_omission": "external_type_drop_omission",
    "external_type_body_with_drop": "external_type_drop_omission",
    "assumption_positive_polarity": "assumption_polarity_and_struct_sealing",
    "unsealed_invariant_struct": "assumption_polarity_and_struct_sealing",
}

PERMITTED_FOUNDATIONAL_AXIOMS: frozenset[str] = frozenset(
    {"propext", "Classical.choice", "Quot.sound"}
)

SUBSYSTEM_SHARD_NAMES: tuple[str, ...] = (
    "Trusted",
    "Anneal.Core",
    "Anneal.RustcMir",
    "Anneal.PureLiftAndSepLogic",
    "Anneal.ParametricCore",
    "Anneal.AiPccAndCodec",
    "Examples",
    "Tests",
)


def wire_schema_dict() -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "baseline_spec_boundary_guards": list(SPEC_BOUNDARY_GUARDS),
        "peer_spec_guards": list(PEER_SPEC_GUARDS),
        "inductive_replay_violation_codes": list(INDUCTIVE_REPLAY_VIOLATION_CODES),
        "shard_audit_violation_codes": list(SHARD_AUDIT_VIOLATION_CODES),
        "peer_guard_violation_codes": list(PEER_GUARD_VIOLATION_CODES),
        "subsystem_shards": list(SUBSYSTEM_SHARD_NAMES),
    }


# ---------------------------------------------------------------------------
# 2. Pillar 1: lean4#16717 Forged-Inductive Replay Integrity + Live .olean Check
# ---------------------------------------------------------------------------


def _has_dups(items: list[str]) -> bool:
    return len(set(items)) != len(items)


def check_inductive_replay_integrity(
    constants: dict[str, dict[str, Any]],
    kernel_inductives: dict[str, dict[str, Any]] | None = None,
    kernel_ctors: dict[str, dict[str, Any]] | None = None,
) -> list[dict[str, str]]:
    """Verify all 12 `lean4#16717` structural and post-replay inductive invariants."""
    violations: list[dict[str, str]] = []

    for key in sorted(constants):
        entry = constants[key]
        name = entry.get("name")
        kind = entry.get("kind")
        if name != key:
            violations.append(
                {
                    "code": "key_mismatch",
                    "subject": key,
                    "detail": str(name),
                }
            )
        if kind == "inductive":
            all_list = list(entry.get("all", []))
            ctors = list(entry.get("ctors", []))
            if name not in all_list:
                violations.append(
                    {
                        "code": "self_not_in_all",
                        "subject": str(name),
                        "detail": "missing_self",
                    }
                )
            if _has_dups(all_list):
                violations.append(
                    {
                        "code": "duplicate_in_all",
                        "subject": str(name),
                        "detail": "duplicate_all",
                    }
                )
            for peer_name in all_list:
                peer = constants.get(peer_name)
                if peer is None or peer.get("kind") != "inductive":
                    violations.append(
                        {
                            "code": "non_induct_in_all",
                            "subject": str(name),
                            "detail": str(peer_name),
                        }
                    )
                else:
                    if (
                        list(peer.get("all", [])) != all_list
                        or list(peer.get("level_params", []))
                        != list(entry.get("level_params", []))
                        or peer.get("num_params") != entry.get("num_params")
                        or peer.get("is_reflexive") != entry.get("is_reflexive")
                        or peer.get("is_rec") != entry.get("is_rec")
                    ):
                        violations.append(
                            {
                                "code": "mutual_metadata_mismatch",
                                "subject": str(name),
                                "detail": str(peer_name),
                            }
                        )
            if _has_dups(ctors):
                violations.append(
                    {
                        "code": "duplicate_in_ctors",
                        "subject": str(name),
                        "detail": "duplicate_ctors",
                    }
                )
            for idx, ctor_name in enumerate(ctors):
                ctor = constants.get(ctor_name)
                if ctor is None or ctor.get("kind") != "constructor":
                    violations.append(
                        {
                            "code": "non_ctor_in_ctors",
                            "subject": str(name),
                            "detail": str(ctor_name),
                        }
                    )
                else:
                    if (
                        ctor.get("induct") != name
                        or ctor.get("num_params") != entry.get("num_params")
                        or list(ctor.get("level_params", []))
                        != list(entry.get("level_params", []))
                    ):
                        violations.append(
                            {
                                "code": "ctor_induct_mismatch",
                                "subject": str(name),
                                "detail": str(ctor_name),
                            }
                        )
                    if ctor.get("cidx") != idx:
                        violations.append(
                            {
                                "code": "ctor_cidx_mismatch",
                                "subject": str(name),
                                "detail": str(ctor_name),
                            }
                        )
        elif kind == "constructor":
            parent_name = entry.get("induct")
            parent = constants.get(parent_name) if isinstance(parent_name, str) else None
            if (
                parent is None
                or parent.get("kind") != "inductive"
                or name not in list(parent.get("ctors", []))
            ):
                violations.append(
                    {
                        "code": "dangling_ctor_not_listed_in_induct",
                        "subject": str(name),
                        "detail": str(parent_name),
                    }
                )

    if kernel_inductives is not None:
        for key in sorted(constants):
            entry = constants[key]
            if entry.get("kind") != "inductive":
                continue
            name = str(entry.get("name"))
            k_info = kernel_inductives.get(name)
            if k_info is None:
                violations.append(
                    {
                        "code": "self_not_in_all",
                        "subject": name,
                        "detail": "not_replayed_in_kernel",
                    }
                )
                continue
            if k_info.get("num_indices") != entry.get("num_indices"):
                violations.append(
                    {
                        "code": "indices_mismatch",
                        "subject": name,
                        "detail": f"kernel={k_info.get('num_indices')} stored={entry.get('num_indices')}",
                    }
                )
            if k_info.get("is_rec") != entry.get("is_rec"):
                violations.append(
                    {
                        "code": "is_rec_mismatch",
                        "subject": name,
                        "detail": f"kernel={k_info.get('is_rec')} stored={entry.get('is_rec')}",
                    }
                )
            for field in (
                "name",
                "level_params",
                "type",
                "num_params",
                "all",
                "ctors",
                "is_reflexive",
                "is_unsafe",
            ):
                if field in k_info and field in entry and k_info[field] != entry[field]:
                    violations.append(
                        {
                            "code": "mutual_metadata_mismatch",
                            "subject": name,
                            "detail": f"post_replay_diff:{field}",
                        }
                    )
                    break

    if kernel_ctors is not None:
        for key in sorted(constants):
            entry = constants[key]
            if entry.get("kind") != "constructor":
                continue
            name = str(entry.get("name"))
            k_ctor = kernel_ctors.get(name)
            if k_ctor is None:
                violations.append(
                    {
                        "code": "dangling_ctor_not_listed_in_induct",
                        "subject": name,
                        "detail": "ctor_not_in_kernel",
                    }
                )
            elif k_ctor.get("cidx") != entry.get("cidx"):
                violations.append(
                    {
                        "code": "ctor_cidx_mismatch",
                        "subject": name,
                        "detail": "post_replay_cidx",
                    }
                )
            elif any(
                field in k_ctor and field in entry and k_ctor[field] != entry[field]
                for field in ("induct", "num_params", "num_fields", "level_params", "type")
            ):
                violations.append(
                    {
                        "code": "ctor_induct_mismatch",
                        "subject": name,
                        "detail": "post_replay_ctor_diff",
                    }
                )

    return violations


def simulate_vulnerable_replay(
    constants: dict[str, dict[str, Any]],
    kernel_inductives: dict[str, dict[str, Any]],
    kernel_ctors: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    """Model Lean 4.34.1 `Replay.lean` lines 102-190 (pre-`lean4#16717`).

    Replays `info.all` blindly without checking `info.name in info.all`, checks
    `postponedConstructors` at the end, and omits `checkPostponedInductives`.
    """
    replayed_inducts: dict[str, dict[str, Any]] = {}
    replayed_ctors: dict[str, dict[str, Any]] = {}
    postponed_ctors: list[str] = []
    remaining = set(constants.keys())

    for key in list(constants.keys()):
        if key not in remaining:
            continue
        remaining.discard(key)
        entry = constants[key]
        kind = entry.get("kind")
        if kind == "inductive":
            all_names = list(entry.get("all", []))
            for peer_name in all_names:
                remaining.discard(peer_name)
                if peer_name in kernel_inductives:
                    replayed_inducts[peer_name] = kernel_inductives[peer_name]
                    for ctor_name in kernel_inductives[peer_name].get("ctors", []):
                        if ctor_name in kernel_ctors:
                            replayed_ctors[ctor_name] = kernel_ctors[ctor_name]
        elif kind == "constructor":
            postponed_ctors.append(entry["name"])

    ctor_errors: list[str] = []
    for ctor_name in postponed_ctors:
        if ctor_name not in replayed_ctors or replayed_ctors[ctor_name] != constants.get(ctor_name):
            ctor_errors.append(ctor_name)

    return {
        "accepted": len(ctor_errors) == 0,
        "ctor_errors": ctor_errors,
        "replayed_inductives": sorted(replayed_inducts.keys()),
        "replayed_ctors": sorted(replayed_ctors.keys()),
    }


_LIVE_OLEAN_INSPECTOR_LEAN = r'''
import Lean

open Lean

def isStdlibMod (m : Name) : Bool :=
  let s := m.toString
  m == `Init || s.startsWith "Init." || m == `Std || s.startsWith "Std." ||
  m == `Lean || s.startsWith "Lean."

def expressionEdges (e : Expr) : NameSet :=
  let base := e.getUsedConstantsAsSet
  let base := if (e.find? fun | .lit (.natVal _) => true | _ => false).isSome then base.insert `Nat else base
  let base := if (e.find? fun | .lit (.strVal _) => true | _ => false).isSome then base.insert `String else base
  base

def declarationEdges (ci : ConstantInfo) : NameSet :=
  let r0 := expressionEdges ci.type
  let r1 := match ci.value? (allowOpaque := true) with
    | some v => r0 ++ expressionEdges v
    | none => r0
  match ci with
  | .defnInfo v => r1 ++ .ofList v.all
  | .thmInfo v => r1 ++ .ofList v.all
  | .opaqueInfo v => r1 ++ .ofList v.all
  | .inductInfo v => r1 ++ .ofList (v.all ++ v.ctors)
  | .ctorInfo v => r1.insert v.induct
  | .recInfo v =>
    v.rules.foldl (fun acc rule => (acc.insert rule.ctor) ++ expressionEdges rule.rhs) (r1 ++ .ofList v.all)
  | _ => r1

def hasDupNames (xs : List Name) : Bool :=
  let rec go (seen : NameSet) : List Name → Bool
    | [] => false
    | x :: rest => if seen.contains x then true else go (seen.insert x) rest
  go {} xs

def mkViol (code subject detail : String) : Json :=
  Json.mkObj [("code", toJson code), ("subject", toJson subject), ("detail", toJson detail)]

def main (args : List String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let mut reqPath : Option String := none
  for arg in args do
    reqPath := some arg
  let some path := reqPath | do
    IO.eprintln "usage: inspect_oleans.lean <request.json>"
    return 2
  let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  let importMods ← IO.ofExcept <| j.getObjValAs? (Array String) "import_modules"
  let exactMods ← IO.ofExcept <| j.getObjValAs? (Array String) "exact_modules"
  let allowedAxioms ← IO.ofExcept <| j.getObjValAs? (Array String) "permitted_axioms"
  let sysroot ← Lean.findSysroot
  let leanPathStr := (← IO.getEnv "LEAN_PATH").getD ""
  let sp := System.SearchPath.parse leanPathStr
  initSearchPath sysroot sp
  let baseEnv ← importModules #[{ module := `Init }, { module := `Std }, { module := `Lean }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let baseEnv := baseEnv.setExporting false
  let exactSet : NameSet := exactMods.foldl (fun s m => s.insert m.toName) {}
  let allowedAxSet : NameSet := allowedAxioms.foldl (fun s a => s.insert a.toName) {}
  -- Load all requested non-stdlib `.olean` files and their transitive non-stdlib imports
  -- directly via `Lean.readModuleData` so sibling `.eq_k` realizations never abort loading.
  let mut queue : List Name := (importMods.map String.toName).toList
  let mut loadedMods : NameSet := {}
  let mut modDatas : Array (Name × ModuleData) := #[]
  let mut constMap : Std.HashMap Name ConstantInfo := {}
  let mut viols : Array Json := #[]
  let mut siblingEqDedup : Nat := 0
  while !queue.isEmpty do
    let m := queue.head!
    queue := queue.tail!
    if !loadedMods.contains m && !isStdlibMod m then
      loadedMods := loadedMods.insert m
      let oleanPath ← Lean.findOLean m
      let mut partPaths : Array System.FilePath := #[oleanPath]
      let serverPath := System.FilePath.mk (oleanPath.toString ++ ".server")
      if ← serverPath.pathExists then
        partPaths := partPaths.push serverPath
      let privPath := System.FilePath.mk (oleanPath.toString ++ ".private")
      if ← privPath.pathExists then
        partPaths := partPaths.push privPath
      let parts ← Lean.readModuleDataParts partPaths
      for (mdata, _region) in parts do
        modDatas := modDatas.push (m, mdata)
        if mdata.constNames.size != mdata.constants.size then
          viols := viols.push (mkViol "key_mismatch" m.toString "constNames_size_mismatch")
        for idx in [:mdata.constants.size] do
          let ci := mdata.constants[idx]!
          match constMap[ci.name]? with
          | none => constMap := constMap.insert ci.name ci
          | some existing =>
            siblingEqDedup := siblingEqDedup + 1
            -- Mirror Lean 4.34.1 `Replay.lean` lines 90-95: reserved/duplicate theorems
            -- must agree on type & levelParams (proof bodies are proof-irrelevant or
            -- split between exported `.olean` stubs and `.olean.private`).
            let compat :=
              existing.levelParams == ci.levelParams &&
              (match existing, ci with
               | .thmInfo _, .thmInfo _ => existing.type.eqv ci.type
               | _, _ =>
                 existing.type == ci.type &&
                 (existing.value? true == ci.value? true || existing.value? true == none || ci.value? true == none))
            if !compat then
              let vCode := match ci with
                | .inductInfo _ => "mutual_metadata_mismatch"
                | _ => "stale_sibling_duplicate"
              viols := viols.push (mkViol vCode ci.name.toString "sibling_duplicate_diff")
            -- Prefer the entry carrying a body if one came from an exported stub.
            if (existing.value? true).isNone && (ci.value? true).isSome then
              constMap := constMap.insert ci.name ci
        for imp in mdata.imports do
          if !loadedMods.contains imp.module && !isStdlibMod imp.module then
            queue := imp.module :: queue
  let lookupConst (n : Name) : Option ConstantInfo :=
    match constMap[n]? with
    | some ci => some ci
    | none => baseEnv.find? n
  let mut checkedModSet : NameSet := {}
  let mut declsChecked : Nat := 0
  let mut inductsChecked : Nat := 0
  let mut ctorsChecked : Nat := 0
  let mut roots : Array Name := #[]
  for (modName, data) in modDatas do
    let isTarget := if exactMods.isEmpty then true else exactSet.contains modName
    if isTarget then
      checkedModSet := checkedModSet.insert modName
      for idx in [:data.constants.size] do
        let ci := data.constants[idx]!
        let kName := data.constNames[idx]!
        declsChecked := declsChecked + 1
        roots := roots.push ci.name
        if kName != ci.name then
          viols := viols.push (mkViol "key_mismatch" kName.toString ci.name.toString)
        match ci with
        | .inductInfo ind =>
          inductsChecked := inductsChecked + 1
          if !ind.all.contains ind.name then
            viols := viols.push (mkViol "self_not_in_all" ind.name.toString "missing_self")
          if hasDupNames ind.all then
            viols := viols.push (mkViol "duplicate_in_all" ind.name.toString "duplicate_all")
          for peerName in ind.all do
            match lookupConst peerName with
            | some (.inductInfo peer) =>
              if peer.all != ind.all || peer.levelParams != ind.levelParams ||
                  peer.numParams != ind.numParams || peer.isReflexive != ind.isReflexive ||
                  peer.isRec != ind.isRec then
                viols := viols.push (mkViol "mutual_metadata_mismatch" ind.name.toString peerName.toString)
            | _ =>
              viols := viols.push (mkViol "non_induct_in_all" ind.name.toString peerName.toString)
          if hasDupNames ind.ctors then
            viols := viols.push (mkViol "duplicate_in_ctors" ind.name.toString "duplicate_ctors")
          let mut cidxExpected : Nat := 0
          for cName in ind.ctors do
            match lookupConst cName with
            | some (.ctorInfo cVal) =>
              if cVal.induct != ind.name || cVal.numParams != ind.numParams ||
                  cVal.levelParams != ind.levelParams then
                viols := viols.push (mkViol "ctor_induct_mismatch" ind.name.toString cName.toString)
              if cVal.cidx != cidxExpected then
                viols := viols.push (mkViol "ctor_cidx_mismatch" ind.name.toString cName.toString)
            | _ =>
              viols := viols.push (mkViol "non_ctor_in_ctors" ind.name.toString cName.toString)
            cidxExpected := cidxExpected + 1
          match lookupConst ind.name with
          | some (.inductInfo stored) =>
            if stored.numIndices != ind.numIndices then
              viols := viols.push (mkViol "indices_mismatch" ind.name.toString "env_diff")
            if stored.isRec != ind.isRec then
              viols := viols.push (mkViol "is_rec_mismatch" ind.name.toString "env_diff")
            if stored.all != ind.all || stored.ctors != ind.ctors ||
                stored.numParams != ind.numParams || stored.levelParams != ind.levelParams ||
                stored.isReflexive != ind.isReflexive || stored.type != ind.type then
              viols := viols.push (mkViol "mutual_metadata_mismatch" ind.name.toString "env_diff")
          | _ =>
            viols := viols.push (mkViol "self_not_in_all" ind.name.toString "missing_in_env")
        | .ctorInfo cVal =>
          ctorsChecked := ctorsChecked + 1
          match lookupConst cVal.induct with
          | some (.inductInfo parent) =>
            if !parent.ctors.contains cVal.name then
              viols := viols.push (mkViol "dangling_ctor_not_listed_in_induct" cVal.name.toString cVal.induct.toString)
          | _ =>
            viols := viols.push (mkViol "dangling_ctor_not_listed_in_induct" cVal.name.toString cVal.induct.toString)
        | _ => pure ()
  -- Full transitive constant-graph walk across all loaded + stdlib imports for `--exact-modules`.
  let mut pending : List Name := roots.toList
  let mut visited : NameSet := {}
  let mut axiomsReached : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !visited.contains n then
      visited := visited.insert n
      match lookupConst n with
      | none =>
        viols := viols.push (mkViol "missing_dependency_decl" n.toString "not_found")
      | some ci =>
        if ci.isAxiom then
          axiomsReached := axiomsReached.insert n
          if !allowedAxSet.contains n then
            viols := viols.push (mkViol "disallowed_transitive_axiom" n.toString "unapproved")
        let edges := declarationEdges ci
        for e in edges do
          if !visited.contains e then
            pending := e :: pending
  let t1 ← IO.monoMsNow
  let sortedAxioms := (axiomsReached.toArray.qsort Name.lt).map Name.toString
  let out := Json.mkObj [
    ("modules_checked", toJson checkedModSet.size),
    ("loaded_olean_count", toJson loadedMods.size),
    ("sibling_eq_dedup_count", toJson siblingEqDedup),
    ("declarations_checked", toJson declsChecked),
    ("inductives_checked", toJson inductsChecked),
    ("ctors_checked", toJson ctorsChecked),
    ("transitive_visited", toJson visited.size),
    ("axioms_reached", toJson sortedAxioms),
    ("violations", .arr viols),
    ("lean_elapsed_ms", toJson (t1 - t0))
  ]
  IO.println out.compress
  return 0
'''


def _find_anneal_lean_run(repo_root: Path) -> str:
    on_path = shutil.which("anneal-lean-run")
    if on_path:
        return on_path
    local = repo_root / "scripts" / "anneal-lean-run"
    if local.is_file():
        return str(local)
    raise FileNotFoundError("anneal-lean-run executable not found on PATH or scripts/")


def inspect_live_oleans(
    repo_root: Path,
    import_modules: list[str],
    exact_modules: list[str] | None = None,
    permitted_axioms: list[str] | None = None,
    timeout_sec: int = 300,
) -> dict[str, Any]:
    """Run live read-only `.olean` inspection under `anneal-lean-run --mode file`."""
    runner = _find_anneal_lean_run(repo_root)
    t0 = time.perf_counter()
    with tempfile.TemporaryDirectory(prefix="anneal-olean-insp-") as tmp_str:
        tmp = Path(tmp_str)
        lean_script = tmp / "inspect_oleans.lean"
        req_json = tmp / "req.json"
        lean_script.write_text(_LIVE_OLEAN_INSPECTOR_LEAN, encoding="utf-8")
        req_payload = {
            "import_modules": list(import_modules),
            "exact_modules": list(exact_modules) if exact_modules is not None else [],
            "permitted_axioms": (
                list(permitted_axioms)
                if permitted_axioms is not None
                else sorted(PERMITTED_FOUNDATIONAL_AXIOMS)
            ),
        }
        req_json.write_text(json.dumps(req_payload, sort_keys=True), encoding="utf-8")
        cmd = [
            runner,
            "--mode",
            "file",
            "--",
            "lake",
            "env",
            "lean",
            "--run",
            str(lean_script),
            str(req_json),
        ]
        proc = subprocess.run(
            cmd,
            cwd=str(repo_root),
            capture_output=True,
            text=True,
            timeout=timeout_sec,
            check=False,
        )
        wall_sec = round(time.perf_counter() - t0, 4)
        if proc.returncode != 0:
            raise RuntimeError(
                f"live .olean inspector failed (rc={proc.returncode}): "
                f"stderr={proc.stderr.strip()} stdout={proc.stdout.strip()}"
            )
        lines = [ln.strip() for ln in proc.stdout.splitlines() if ln.strip()]
        if not lines:
            raise RuntimeError("live .olean inspector emitted empty stdout")
        result = json.loads(lines[-1])
        result["axioms_reached"] = sorted(result.get("axioms_reached", []))
        result["wall_sec"] = wall_sec
        return result


def run_trusted_boundary_inspect_source(
    repo_root: Path,
    module_name: str,
    lean_file: Path,
    timeout_sec: int = 180,
) -> dict[str, Any]:
    """Invoke `TrustedBoundary.inspectSource` read-only on a single Lean source file."""
    runner = _find_anneal_lean_run(repo_root)
    tb_path = repo_root / "trusted" / "audit" / "TrustedBoundary.lean"
    wrapper_code = f"""
import Lean
open Lean
"""
    # Use `TrustedBoundary.lean` directly via a tiny driver that imports nothing external
    # and runs `TrustedBoundary.inspectSource` on the exact parserEnv (`Init`, `Std`).
    driver_lean = r'''
import Lean.Elab.Import
import Lean.Parser.Tactic
''' + "\n" + tb_path.read_text(encoding="utf-8")
    # Strip the `main` function from our temporary copy and add a minimal `inspectSource` driver
    # so we exercise the exact `TrustedBoundary.inspectSource` code verbatim without mutating `trusted/`.
    marker = "\ndef main (args : List String) : IO UInt32 := do"
    idx = driver_lean.find(marker)
    if idx == -1:
        raise RuntimeError("Could not locate main in TrustedBoundary.lean")
    tb_body = driver_lean[:idx]
    driver = (
        tb_body
        + r'''

def main (args : List String) : IO UInt32 := do
  match args with
  | [modStr, filePath] =>
    try
      let sysroot ← Lean.findSysroot
      let leanPathStr := (← IO.getEnv "LEAN_PATH").getD ""
      let sp := System.SearchPath.parse leanPathStr
      initSearchPath sysroot sp
      unsafe enableInitializersExecution
      let parserEnv ← importModules #[{ module := `Init }, { module := `Std }] {}
        (trustLevel := 0) (plugins := #[]) (loadExts := true) (level := .private)
      let res ← TrustedBoundary.inspectSource parserEnv modStr.toName filePath #[] false
      IO.println (Json.mkObj [("ok", toJson true), ("result", res)]).compress
      return 0
    catch err =>
      IO.println (Json.mkObj [("ok", toJson false), ("error", toJson err.toString)]).compress
      return 1
  | _ =>
    IO.eprintln "usage: <module_name> <file_path>"
    return 2
'''
    )
    with tempfile.TemporaryDirectory(prefix="anneal-tb-src-") as tmp_str:
        tmp_driver = Path(tmp_str) / "tb_inspect_source.lean"
        tmp_driver.write_text(driver, encoding="utf-8")
        cmd = [
            runner,
            "--mode",
            "file",
            "--",
            "lake",
            "env",
            "lean",
            "--run",
            str(tmp_driver),
            module_name,
            str(lean_file.resolve()),
        ]
        proc = subprocess.run(
            cmd,
            cwd=str(repo_root),
            capture_output=True,
            text=True,
            timeout=timeout_sec,
            check=False,
        )
        lines = [ln.strip() for ln in proc.stdout.splitlines() if ln.strip()]
        if not lines:
            return {
                "ok": False,
                "returncode": proc.returncode,
                "error": proc.stderr.strip(),
            }
        data = json.loads(lines[-1])
        data["returncode"] = proc.returncode
        return data


# ---------------------------------------------------------------------------
# 3. Pillar 2: grmf cl/1029226310 Sharded Audit, 8-Shard Planner, --orphan-only
# ---------------------------------------------------------------------------


def _lean_path_to_module(rel_under_root: Path) -> str:
    return ".".join(rel_under_root.with_suffix("").parts)


def discover_repo_modules(repo_root: Path) -> dict[str, dict[str, Any]]:
    """Fast (< 0.05s) discovery of all Lean modules across Trusted, theory/, examples/, tests/."""
    modules: dict[str, dict[str, Any]] = {}
    olean_root = repo_root / ".lake" / "build" / "lib" / "lean"

    def add_mod(mod_name: str, abs_path: Path, root_group: str) -> None:
        rel_posix = abs_path.relative_to(repo_root).as_posix()
        olean_path = olean_root / (mod_name.replace(".", "/") + ".olean")
        modules[mod_name] = {
            "module": mod_name,
            "rel_path": rel_posix,
            "root_group": root_group,
            "has_olean": olean_path.is_file(),
        }

    # 1. trusted/lean -> Trusted.*
    trusted_dir = repo_root / "trusted" / "lean"
    if trusted_dir.is_dir():
        for dirpath, dirnames, filenames in os.walk(trusted_dir):
            dirnames.sort()
            for fn in sorted(filenames):
                if fn.endswith(".lean"):
                    p = Path(dirpath) / fn
                    mod = _lean_path_to_module(p.relative_to(trusted_dir))
                    add_mod(mod, p, "trusted")

    # 2. theory/ -> Anneal.*, Correspondence.*, MiniRust.*
    theory_dir = repo_root / "theory"
    if theory_dir.is_dir():
        for dirpath, dirnames, filenames in os.walk(theory_dir):
            dirnames.sort()
            for fn in sorted(filenames):
                if fn.endswith(".lean"):
                    p = Path(dirpath) / fn
                    mod = _lean_path_to_module(p.relative_to(theory_dir))
                    add_mod(mod, p, "theory")

    # 3. Root standalone examples/ Lean modules (excluding Cargo subproject examples)
    examples_dir = repo_root / "examples"
    if examples_dir.is_dir():
        for sub in ("", "mir", "pass", "refinement", "step-result"):
            d = examples_dir / sub if sub else examples_dir
            if d.is_dir():
                for fn in sorted(os.listdir(d)):
                    if fn.endswith(".lean"):
                        p = d / fn
                        if p.is_file():
                            mod = p.stem
                            if mod in modules:
                                mod = f"Examples.{mod}"
                            add_mod(mod, p, "examples")

    # 4. Root tests/ Lean modules (excluding trusted-boundary/positive.lean harness fixture)
    tests_dir = repo_root / "tests"
    if tests_dir.is_dir():
        for sub in ("", "mir", "pass", "refinement", "step-result"):
            d = tests_dir / sub if sub else tests_dir
            if d.is_dir():
                for fn in sorted(os.listdir(d)):
                    if fn.endswith(".lean"):
                        p = d / fn
                        if p.is_file():
                            stem = p.stem
                            mod = "SmokeTest" if (sub == "" and stem == "Smoke") else stem
                            if mod in modules:
                                mod = f"Tests.{mod}"
                            add_mod(mod, p, "tests")

    return dict(sorted(modules.items()))


def classify_subsystem_shard(module_name: str, rel_path: str) -> str:
    """Deterministic total classifier assigning every discovered module to 1 of 8 shards."""
    if rel_path.startswith("trusted/lean/") or module_name == "Trusted" or module_name.startswith("Trusted."):
        return "Trusted"
    if rel_path.startswith("examples/"):
        return "Examples"
    if rel_path.startswith("tests/"):
        return "Tests"
    if module_name.startswith("Anneal.ParametricCore"):
        return "Anneal.ParametricCore"
    if (
        module_name == "Anneal.PureLift"
        or module_name.startswith("Anneal.PureLift.")
        or module_name.startswith("Anneal.SepLogic")
        or module_name.startswith("Anneal.RefFrame")
        or module_name in {"Anneal.Memory", "Anneal.UnsafeObligations", "Anneal.AtomicHistInv"}
    ):
        return "Anneal.PureLiftAndSepLogic"
    if (
        module_name.startswith("Anneal.AiPcc")
        or module_name == "Anneal.F2Simd"
        or module_name.startswith("Anneal.F2Simd.")
        or module_name.startswith("Anneal.CnfOrd")
        or module_name.startswith("Anneal.Bit")
        or module_name
        in {
            "Anneal.ByteCodec",
            "Anneal.LeBytes",
            "Anneal.ListChunks",
            "Anneal.NatBitwise",
            "Anneal.LinearArith",
            "Anneal.PTree",
            "Anneal.Scalars",
        }
    ):
        return "Anneal.AiPccAndCodec"
    if (
        module_name.startswith("Anneal.Rustc.")
        or module_name.startswith("Anneal.Mir.")
        or module_name.startswith("Anneal.Mir")
        or module_name
        in {
            "Anneal.PureMirExec",
            "Anneal.FunctionalTranslation",
            "Anneal.DualCorrespondenceBundle",
            "Anneal.TreeBorrowsPruningAndFrameWp",
            "Anneal.PanicContracts",
            "Anneal.DiffTestShrinker",
        }
        or module_name == "Correspondence"
        or module_name.startswith("Correspondence.")
        or module_name == "MiniRust"
        or module_name.startswith("MiniRust.")
    ):
        return "Anneal.RustcMir"
    return "Anneal.Core"


def plan_subsystem_shards(repo_root: Path) -> dict[str, Any]:
    """Build the deterministic 8-shard subsystem partition covering all discovered modules."""
    discovered = discover_repo_modules(repo_root)
    shards: dict[str, list[str]] = {name: [] for name in SUBSYSTEM_SHARD_NAMES}
    compiled_shards: dict[str, list[str]] = {name: [] for name in SUBSYSTEM_SHARD_NAMES}
    for mod_name, info in discovered.items():
        shard = classify_subsystem_shard(mod_name, info["rel_path"])
        shards[shard].append(mod_name)
        if info["has_olean"]:
            compiled_shards[shard].append(mod_name)
    return {
        "schema_version": SCHEMA_VERSION,
        "shard_names": list(SUBSYSTEM_SHARD_NAMES),
        "total_discovered_modules": len(discovered),
        "total_compiled_oleans": sum(len(v) for v in compiled_shards.values()),
        "shards": shards,
        "compiled_olean_shards": {k: v for k, v in compiled_shards.items() if v},
    }


def check_shard_partition(
    registered_modules: list[str],
    on_disk_modules: list[str],
    shards: list[list[str]],
) -> list[dict[str, str]]:
    """Exact 1-for-1 Python implementation of Lean's `checkShardPartition`."""
    violations: list[dict[str, str]] = []
    reg_set = set(registered_modules)

    if not shards:
        violations.append({"code": "empty_shard_list", "subject": "<shards>"})

    seen_global: set[str] = set()
    overlaps_reported: set[str] = set()
    for shard in shards:
        if not shard:
            violations.append({"code": "empty_shard", "subject": "<shard>"})
        if _has_dups(shard):
            violations.append({"code": "duplicate_module_in_shard", "subject": "<shard>"})
        for mod in shard:
            if mod not in reg_set:
                violations.append({"code": "unregistered_module_in_shard", "subject": mod})
            if mod in seen_global and mod not in overlaps_reported:
                overlaps_reported.add(mod)
                violations.append({"code": "overlapping_shards", "subject": mod})
        seen_global.update(shard)

    for mod in registered_modules:
        if mod not in seen_global:
            violations.append({"code": "uncovered_registered_module", "subject": mod})

    for mod in on_disk_modules:
        if mod not in reg_set:
            violations.append({"code": "unregistered_on_disk_orphan", "subject": mod})

    return violations


def run_orphan_only_gate(
    repo_root: Path,
    registered_modules: list[str] | None = None,
    shards: list[list[str]] | None = None,
) -> dict[str, Any]:
    """Run `< 0.25s` `--orphan-only` completeness and exact-partition gate."""
    t0 = time.perf_counter()
    discovered = discover_repo_modules(repo_root)
    on_disk = sorted(discovered.keys())
    if registered_modules is None and shards is None:
        plan = plan_subsystem_shards(repo_root)
        registered = on_disk
        shard_lists = [plan["shards"][name] for name in SUBSYSTEM_SHARD_NAMES]
    elif registered_modules is not None and shards is None:
        registered = list(registered_modules)
        shard_lists = [registered] if registered else []
    elif registered_modules is None and shards is not None:
        registered = on_disk
        shard_lists = shards
    else:
        registered = list(registered_modules)
        shard_lists = shards

    violations = check_shard_partition(registered, on_disk, shard_lists)
    elapsed_sec = round(time.perf_counter() - t0, 5)
    return {
        "ok": len(violations) == 0,
        "elapsed_sec": elapsed_sec,
        "under_250ms": elapsed_sec < 0.25,
        "on_disk_count": len(on_disk),
        "registered_count": len(registered),
        "shard_count": len(shard_lists),
        "violations": violations,
    }


def audit_repo_graph_exact_modules(
    env: dict[str, Any],
    shard: list[str],
) -> dict[str, Any]:
    """Pure-Python reference evaluator for `--exact-modules` full transitive graph audit.

    Handles arbitrary multi-hop cross-shard chains, diamonds, and cycles cleanly.
    """
    decls_by_name: dict[str, dict[str, Any]] = {
        d["name"]: d for d in env.get("decls", [])
    }
    permitted = set(env.get("permitted_axioms", sorted(PERMITTED_FOUNDATIONAL_AXIOMS)))
    shard_set = set(shard)
    violations: list[dict[str, str]] = []
    reached_axioms: set[str] = set()
    visited: set[str] = set()

    roots = [d["name"] for d in env.get("decls", []) if d.get("origin_mod") in shard_set]
    stack = list(roots)
    while stack:
        cur = stack.pop()
        if cur in visited:
            continue
        visited.add(cur)
        rec = decls_by_name.get(cur)
        if rec is None:
            violations.append({"code": "missing_dependency_decl", "subject": cur})
            continue
        if rec.get("is_unsafe_or_partial"):
            violations.append({"code": "disallowed_transitive_axiom", "subject": f"unsafe:{cur}"})
        if rec.get("is_axiom"):
            reached_axioms.add(cur)
            if cur not in permitted:
                violations.append({"code": "disallowed_transitive_axiom", "subject": cur})
        for dep in rec.get("direct_deps", []):
            if dep not in visited:
                stack.append(dep)

    return {
        "ok": len(violations) == 0,
        "shard": sorted(shard_set),
        "roots_checked": len(roots),
        "transitive_visited": len(visited),
        "axioms_reached": sorted(reached_axioms),
        "violations": violations,
    }


def run_live_benchmark(
    repo_root: Path,
    max_workers: int | None = None,
) -> dict[str, Any]:
    """Benchmark `--orphan-only`, monolithic live `.olean` audit, and parallel sharded audit."""
    orphan_res = run_orphan_only_gate(repo_root)
    plan = plan_subsystem_shards(repo_root)
    compiled_shards: dict[str, list[str]] = plan["compiled_olean_shards"]
    all_compiled: list[str] = sorted(
        m for mods in compiled_shards.values() for m in mods
    )

    # 1. Monolithic live `.olean` audit (all compiled modules in one Lean invocation)
    mono_res = inspect_live_oleans(
        repo_root=repo_root,
        import_modules=all_compiled,
        exact_modules=all_compiled,
    )

    # 2. Parallel `--exact-modules` sharded live `.olean` audit
    workers = max_workers if max_workers is not None else min(len(compiled_shards), 6)
    workers = max(1, workers)
    t0 = time.perf_counter()
    per_shard: dict[str, dict[str, Any]] = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        future_map = {
            pool.submit(inspect_live_oleans, repo_root, mods, mods): shard_name
            for shard_name, mods in sorted(compiled_shards.items())
        }
        for fut in concurrent.futures.as_completed(future_map):
            shard_name = future_map[fut]
            per_shard[shard_name] = fut.result()
    sharded_wall_sec = round(time.perf_counter() - t0, 4)

    union_axioms = sorted(
        {a for res in per_shard.values() for a in res.get("axioms_reached", [])}
    )
    sharded_violations = [
        {"shard": name, **v}
        for name in sorted(per_shard)
        for v in per_shard[name].get("violations", [])
    ]
    sharded_decls = sum(r["declarations_checked"] for r in per_shard.values())
    sharded_inducts = sum(r["inductives_checked"] for r in per_shard.values())
    sharded_ctors = sum(r["ctors_checked"] for r in per_shard.values())
    mono_wall = mono_res["wall_sec"]
    speedup = round(mono_wall / sharded_wall_sec, 3) if sharded_wall_sec > 0 else 0.0

    ind_code_set = set(INDUCTIVE_REPLAY_VIOLATION_CODES)
    mono_ind_viols = [v for v in mono_res["violations"] if v.get("code") in ind_code_set]
    sharded_ind_viols = [v for v in sharded_violations if v.get("code") in ind_code_set]
    mono_dep_viols = [v for v in mono_res["violations"] if v.get("code") not in ind_code_set]
    sharded_dep_viols = [v for v in sharded_violations if v.get("code") not in ind_code_set]

    return {
        "schema_version": SCHEMA_VERSION,
        "orphan_only": orphan_res,
        "compiled_shard_count": len(compiled_shards),
        "compiled_module_count": len(all_compiled),
        "max_workers": workers,
        "monolithic": {
            "wall_sec": mono_wall,
            "lean_elapsed_ms": mono_res["lean_elapsed_ms"],
            "modules_checked": mono_res["modules_checked"],
            "declarations_checked": mono_res["declarations_checked"],
            "inductives_checked": mono_res["inductives_checked"],
            "ctors_checked": mono_res["ctors_checked"],
            "transitive_visited": mono_res["transitive_visited"],
            "axioms_reached": mono_res["axioms_reached"],
            "violation_count": len(mono_res["violations"]),
            "inductive_violation_count": len(mono_ind_viols),
            "dependency_violation_count": len(mono_dep_viols),
        },
        "sharded": {
            "wall_sec": sharded_wall_sec,
            "modules_checked": sum(r["modules_checked"] for r in per_shard.values()),
            "declarations_checked": sharded_decls,
            "inductives_checked": sharded_inducts,
            "ctors_checked": sharded_ctors,
            "union_axioms": union_axioms,
            "violation_count": len(sharded_violations),
            "inductive_violation_count": len(sharded_ind_viols),
            "dependency_violation_count": len(sharded_dep_viols),
            "per_shard": {k: per_shard[k] for k in sorted(per_shard)},
        },
        "parity": {
            "axiom_union_matches_monolithic": union_axioms == mono_res["axioms_reached"],
            "declaration_count_matches_monolithic": sharded_decls == mono_res["declarations_checked"],
            "inductive_count_matches_monolithic": sharded_inducts == mono_res["inductives_checked"],
            "ctor_count_matches_monolithic": sharded_ctors == mono_res["ctors_checked"],
            "zero_inductive_violations": len(mono_ind_viols) == 0 and len(sharded_ind_viols) == 0,
            "zero_violations": len(mono_res["violations"]) == 0 and len(sharded_violations) == 0,
            "speedup_vs_monolithic": speedup,
        },
    }


# ---------------------------------------------------------------------------
# 4. Pillar 3: Comment/String/Char/Attr-Aware Rust & Lean Scanners (Guards 3-6)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Token:
    kind: str  # IDENT, NUMBER, STRING, CHAR, LIFETIME, OP, PUNCT
    text: str
    start: int
    end: int
    line: int


@dataclass(frozen=True)
class CommentSpan:
    kind: str  # line, doc_line, block, doc_block, mod_doc
    text: str
    start: int
    end: int
    line: int


def _is_ident_start(ch: str) -> bool:
    return ch.isalpha() or ch == "_"


def _is_ident_continue(ch: str) -> bool:
    return ch.isalnum() or ch == "_"


def _match_rust_raw_str(text: str, pos: int, n: int) -> int | None:
    i = pos
    if i < n and text[i] in ("b", "c"):
        i += 1
    if i >= n or text[i] != "r":
        return None
    i += 1
    hashes = 0
    while i < n and text[i] == "#":
        hashes += 1
        i += 1
    if i >= n or text[i] != '"':
        return None
    i += 1
    close = '"' + ("#" * hashes)
    end = text.find(close, i)
    return n if end == -1 else end + len(close)


def _match_rust_char(text: str, pos: int, n: int) -> int | None:
    """Match a Rust char/byte-char literal starting at `'` (distinguishing lifetimes `'a`)."""
    if pos >= n or text[pos] != "'":
        return None
    if pos + 1 >= n:
        return None
    if text[pos + 1] == "\\":
        i = pos + 2
        if i >= n:
            return None
        esc = text[i]
        if esc in ("n", "r", "t", "\\", "0", "'", '"'):
            i += 1
        elif esc == "x":
            i += 3
        elif esc == "u" and i + 1 < n and text[i + 1] == "{":
            close_b = text.find("}", i + 2)
            if close_b == -1:
                return None
            i = close_b + 1
        else:
            return None
        if i < n and text[i] == "'":
            return i + 1
        return None
    if text[pos + 1] != "'" and text[pos + 1] != "\n" and pos + 2 < n and text[pos + 2] == "'":
        return pos + 3
    return None


def lex_rust_tokens(text: str) -> list[Token]:
    """Comment-, string-, raw-string-, and char-literal-aware Rust lexer."""
    tokens: list[Token] = []
    n = len(text)
    i = 0
    line = 1
    two_char_ops = {"::", "->", "=>", "&&", "||", "==", "!=", "<=", ">=", "..", "+=", "-=", "*=", "/="}

    while i < n:
        ch = text[i]
        if ch in " \t\r":
            i += 1
            continue
        if ch == "\n":
            line += 1
            i += 1
            continue

        # Line comment //
        if ch == "/" and i + 1 < n and text[i + 1] == "/":
            nl = text.find("\n", i + 2)
            i = n if nl == -1 else nl
            continue

        # Nested block comment /* ... */
        if ch == "/" and i + 1 < n and text[i + 1] == "*":
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text[i] == "\n":
                    line += 1
                    i += 1
                elif text[i] == "/" and i + 1 < n and text[i + 1] == "*":
                    depth += 1
                    i += 2
                elif text[i] == "*" and i + 1 < n and text[i + 1] == "/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue

        # Raw strings: r"...", r#"..."#, br#"..."#, cr#"..."#
        raw_end = _match_rust_raw_str(text, i, n)
        if raw_end is not None:
            seg = text[i:raw_end]
            tokens.append(Token("STRING", seg, i, raw_end, line))
            line += seg.count("\n")
            i = raw_end
            continue

        # Byte/C quoted string: b"...", c"..."
        if ch in ("b", "c") and i + 1 < n and text[i + 1] == '"':
            start_line = line
            j = i + 2
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == "\n":
                    line += 1
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            tokens.append(Token("STRING", text[i:j], i, j, start_line))
            i = j
            continue

        # Byte char literal: b'x'
        if ch == "b" and i + 1 < n and text[i + 1] == "'":
            c_end = _match_rust_char(text, i + 1, n)
            if c_end is not None:
                tokens.append(Token("CHAR", text[i:c_end], i, c_end, line))
                i = c_end
                continue

        # Quoted string "..."
        if ch == '"':
            start_line = line
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == "\n":
                    line += 1
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            tokens.append(Token("STRING", text[i:j], i, j, start_line))
            i = j
            continue

        # Char literal vs lifetime
        if ch == "'":
            c_end = _match_rust_char(text, i, n)
            if c_end is not None:
                tokens.append(Token("CHAR", text[i:c_end], i, c_end, line))
                i = c_end
                continue
            j = i + 1
            while j < n and _is_ident_continue(text[j]):
                j += 1
            tokens.append(Token("LIFETIME", text[i:j], i, j, line))
            i = j
            continue

        # Raw identifier r#ident
        if ch == "r" and i + 2 < n and text[i + 1] == "#" and _is_ident_start(text[i + 2]):
            j = i + 2
            while j < n and _is_ident_continue(text[j]):
                j += 1
            tokens.append(Token("IDENT", text[i:j], i, j, line))
            i = j
            continue

        # Identifiers / keywords
        if _is_ident_start(ch):
            j = i + 1
            while j < n and _is_ident_continue(text[j]):
                j += 1
            tokens.append(Token("IDENT", text[i:j], i, j, line))
            i = j
            continue

        # Numbers
        if ch.isdigit():
            j = i + 1
            while j < n and (text[j].isalnum() or text[j] == "_"):
                j += 1
            tokens.append(Token("NUMBER", text[i:j], i, j, line))
            i = j
            continue

        # Three-char op ..=
        if text[i : i + 3] == "..=":
            tokens.append(Token("OP", "..=", i, i + 3, line))
            i += 3
            continue

        # Two-char ops
        if i + 1 < n and text[i : i + 2] in two_char_ops:
            tokens.append(Token("OP", text[i : i + 2], i, i + 2, line))
            i += 2
            continue

        tokens.append(Token("PUNCT", ch, i, i + 1, line))
        i += 1

    return tokens


def _find_matching_delim(tokens: list[Token], open_idx: int, open_ch: str, close_ch: str) -> int:
    depth = 0
    for idx in range(open_idx, len(tokens)):
        t = tokens[idx].text
        if t == open_ch:
            depth += 1
        elif t == close_ch:
            depth -= 1
            if depth == 0:
                return idx
    return len(tokens) - 1


def _collect_rust_outer_attrs(tokens: list[Token], pos: int) -> tuple[list[tuple[list[Token], int]], int]:
    """Collect contiguous outer attributes `#[...]` starting at `pos`."""
    attrs: list[tuple[list[Token], int]] = []
    i = pos
    n = len(tokens)
    while i + 1 < n and tokens[i].text == "#" and tokens[i + 1].text == "[":
        close_idx = _find_matching_delim(tokens, i + 1, "[", "]")
        attrs.append((tokens[i + 2 : close_idx], tokens[i].line))
        i = close_idx + 1
    return attrs, i


def _attr_path_and_args(attr_toks: list[Token]) -> tuple[str, list[Token]]:
    """Split `foo::bar(args...)` or `foo::bar` into path string and inner arg tokens."""
    i = 0
    parts: list[str] = []
    n = len(attr_toks)
    if i < n and attr_toks[i].text == "::":
        i += 1
    while i < n and attr_toks[i].kind == "IDENT":
        parts.append(attr_toks[i].text)
        i += 1
        if i < n and attr_toks[i].text == "::":
            i += 1
        else:
            break
    path = "::".join(parts)
    if i < n and attr_toks[i].text == "(":
        close_idx = _find_matching_delim(attr_toks, i, "(", ")")
        return path, attr_toks[i + 1 : close_idx]
    return path, attr_toks[i:]


def _split_top_level_tokens(toks: list[Token], sep: str) -> list[list[Token]]:
    parts: list[list[Token]] = []
    cur: list[Token] = []
    depth = 0
    for t in toks:
        if t.text in ("(", "[", "{"):
            depth += 1
        elif t.text in (")", "]", "}"):
            depth = max(0, depth - 1)
        if depth == 0 and t.text == sep:
            parts.append(cur)
            cur = []
        else:
            cur.append(t)
    parts.append(cur)
    return parts


def _strip_outer_parens(toks: list[Token]) -> list[Token]:
    while len(toks) >= 2 and toks[0].text == "(" and _find_matching_delim(toks, 0, "(", ")") == len(toks) - 1:
        toks = toks[1:-1]
    return toks


def _strip_closure_header(toks: list[Token]) -> list[Token]:
    toks = _strip_outer_parens(toks)
    if toks and toks[0].text == "move":
        toks = toks[1:]
    if toks and toks[0].text == "|":
        for j in range(1, len(toks)):
            if toks[j].text == "|":
                return _strip_outer_parens(toks[j + 1 :])
    elif toks and toks[0].text == "||":
        return _strip_outer_parens(toks[1:])
    return toks


def _norm_tok_expr(toks: list[Token]) -> str:
    return " ".join(t.text for t in _strip_outer_parens(toks))


def _rust_expr_is_unsatisfiable(toks: list[Token]) -> bool:
    """Sound syntactic unsatisfiability detector for Rust contract clauses."""
    toks = _strip_closure_header(toks)
    toks = _strip_outer_parens(toks)
    if not toks:
        return False

    # Array conjunction `[e1, e2, ...]`
    if toks[0].text == "[" and _find_matching_delim(toks, 0, "[", "]") == len(toks) - 1:
        elems = [e for e in _split_top_level_tokens(toks[1:-1], ",") if e]
        if any(_rust_expr_is_unsatisfiable(e) for e in elems):
            return True
        return _rust_conjuncts_contradict(elems)

    # Constant `false` or `!true`
    if len(toks) == 1 and toks[0].text == "false":
        return True
    if len(toks) == 2 and toks[0].text == "!" and toks[1].text == "true":
        return True

    # `if cond { then_branch } else { else_branch }`
    if toks[0].text == "if":
        brace_idx = -1
        depth = 0
        for idx in range(1, len(toks)):
            t = toks[idx].text
            if t in ("(", "["):
                depth += 1
            elif t in (")", "]"):
                depth = max(0, depth - 1)
            elif depth == 0 and t == "{":
                brace_idx = idx
                break
        if brace_idx != -1:
            cond = _strip_outer_parens(toks[1:brace_idx])
            then_end = _find_matching_delim(toks, brace_idx, "{", "}")
            then_toks = toks[brace_idx + 1 : then_end]
            if then_end + 2 < len(toks) and toks[then_end + 1].text == "else":
                if toks[then_end + 2].text == "{":
                    else_end = _find_matching_delim(toks, then_end + 2, "{", "}")
                    else_toks = toks[then_end + 3 : else_end]
                else:
                    else_toks = toks[then_end + 2 :]
                if len(cond) == 1 and cond[0].text == "true":
                    return _rust_expr_is_unsatisfiable(then_toks)
                if len(cond) == 1 and cond[0].text == "false":
                    return _rust_expr_is_unsatisfiable(else_toks)
                return _rust_expr_is_unsatisfiable(then_toks) and _rust_expr_is_unsatisfiable(else_toks)

    # Top-level disjunction `a || b`: unsatisfiable iff every disjunct is unsatisfiable.
    disjuncts = _split_top_level_tokens(toks, "||")
    if len(disjuncts) > 1:
        return all(_rust_expr_is_unsatisfiable(d) for d in disjuncts)

    # Top-level conjunction `a && b`: unsatisfiable if any conjunct is unsatisfiable or contradictory pair.
    conjuncts = _split_top_level_tokens(toks, "&&")
    if len(conjuncts) > 1:
        if any(_rust_expr_is_unsatisfiable(c) for c in conjuncts):
            return True
        return _rust_conjuncts_contradict(conjuncts)

    # Irreflexive binary comparison on identical operands: `x != x`, `x < x`, `x > x`
    for op in ("!=", "<", ">"):
        parts = _split_top_level_tokens(toks, op)
        if len(parts) == 2 and parts[0] and parts[1]:
            if _norm_tok_expr(parts[0]) == _norm_tok_expr(parts[1]):
                return True
    return False


def _rust_conjuncts_contradict(conjuncts: list[list[Token]]) -> bool:
    pos_atoms: set[str] = set()
    neg_atoms: set[str] = set()
    eq_pairs: set[tuple[str, str]] = set()
    neq_pairs: set[tuple[str, str]] = set()
    for raw in conjuncts:
        c = _strip_outer_parens(raw)
        if not c:
            continue
        if c[0].text == "!":
            neg_atoms.add(_norm_tok_expr(c[1:]))
        else:
            pos_atoms.add(_norm_tok_expr(c))
        eq_p = _split_top_level_tokens(c, "==")
        if len(eq_p) == 2 and eq_p[0] and eq_p[1]:
            a, b = _norm_tok_expr(eq_p[0]), _norm_tok_expr(eq_p[1])
            eq_pairs.add((a, b))
            eq_pairs.add((b, a))
        neq_p = _split_top_level_tokens(c, "!=")
        if len(neq_p) == 2 and neq_p[0] and neq_p[1]:
            a, b = _norm_tok_expr(neq_p[0]), _norm_tok_expr(neq_p[1])
            neq_pairs.add((a, b))
            neq_pairs.add((b, a))
    return bool((pos_atoms & neg_atoms) or (eq_pairs & neq_pairs))


def _extract_contract_clauses(attr_args: list[Token]) -> tuple[list[list[Token]], list[list[Token]]]:
    """Extract `requires` and `ensures` clauses from Anneal or Creusot/Verus attribute args."""
    req_clauses: list[list[Token]] = []
    ens_clauses: list[list[Token]] = []
    for item in _split_top_level_tokens(attr_args, ","):
        if not item:
            continue
        if item[0].text == "requires":
            if len(item) >= 2 and item[1].text == ":":
                req_clauses.append(item[2:])
            elif len(item) >= 2 and item[1].text == "(":
                end = _find_matching_delim(item, 1, "(", ")")
                req_clauses.append(item[2:end])
        elif item[0].text == "ensures":
            if len(item) >= 2 and item[1].text == ":":
                ens_clauses.append(item[2:])
            elif len(item) >= 2 and item[1].text == "(":
                end = _find_matching_delim(item, 1, "(", ")")
                ens_clauses.append(item[2:end])
    return req_clauses, ens_clauses


def _parse_rust_fn_sig(tokens: list[Token], pos: int) -> tuple[str, bool, bool, int] | None:
    """Parse Rust `fn` signature starting at `pos`.

    Returns `(fn_name, is_extern_fn, is_diverging, next_pos)` or `None`.
    """
    i = pos
    n = len(tokens)
    is_extern_fn = False
    while i < n:
        t = tokens[i].text
        if t == "pub":
            i += 1
            if i < n and tokens[i].text == "(":
                i = _find_matching_delim(tokens, i, "(", ")") + 1
        elif t in ("unsafe", "const", "async", "default"):
            i += 1
        elif t == "extern":
            is_extern_fn = True
            i += 1
            if i < n and tokens[i].kind == "STRING":
                i += 1
        else:
            break
    if i >= n or tokens[i].text != "fn":
        return None
    i += 1
    if i >= n or tokens[i].kind != "IDENT":
        return None
    fn_name = tokens[i].text
    i += 1
    # Skip optional generics `<...>`
    if i < n and tokens[i].text == "<":
        depth = 1
        i += 1
        while i < n and depth > 0:
            if tokens[i].text == "<":
                depth += 1
            elif tokens[i].text == ">":
                depth -= 1
            i += 1
    # Skip parameter list `(...)`
    if i >= n or tokens[i].text != "(":
        return None
    i = _find_matching_delim(tokens, i, "(", ")") + 1
    is_diverging = False
    if i < n and tokens[i].text == "->":
        i += 1
        ret_start = i
        depth = 0
        while i < n:
            t = tokens[i].text
            if t in ("(", "[", "<"):
                depth += 1
            elif t in (")", "]", ">"):
                depth = max(0, depth - 1)
            elif depth == 0 and t in ("{", ";", "where"):
                break
            i += 1
        ret_toks = tokens[ret_start:i]
        if len(ret_toks) == 1 and ret_toks[0].text == "!":
            is_diverging = True
    return fn_name, is_extern_fn, is_diverging, i


def _make_peer_finding(
    code: str,
    subject: str,
    line: int,
    detail: str,
    file_path: str | None = None,
) -> dict[str, Any]:
    guard_id = PEER_VIOLATION_TO_GUARD_ID[code]
    guard_meta = PEER_GUARD_BY_ID[guard_id]
    finding: dict[str, Any] = {
        "code": code,
        "guard_id": guard_id,
        "canonical_name": guard_meta["canonical_name"],
        "rank": guard_meta["rank"],
        "vacuity_class": guard_meta["vacuity_class"],
        "subject": subject,
        "line": line,
        "detail": detail,
    }
    if file_path is not None:
        finding["file"] = file_path
    return finding


def scan_rust_unsatisfiable_extern_ensures(
    text: str,
    *,
    file_path: str | None = None,
) -> list[dict[str, Any]]:
    """Guard 3 (`creusot#2388`): reject unsatisfiable `ensures` on non-diverging extern specs."""
    tokens = lex_rust_tokens(text)
    findings: list[dict[str, Any]] = []
    n = len(tokens)
    in_extern_block_brace_depths: list[int] = []
    brace_depth = 0
    i = 0
    while i < n:
        if tokens[i].text == "{":
            brace_depth += 1
            i += 1
            continue
        if tokens[i].text == "}":
            if in_extern_block_brace_depths and brace_depth == in_extern_block_brace_depths[-1]:
                in_extern_block_brace_depths.pop()
            brace_depth = max(0, brace_depth - 1)
            i += 1
            continue

        # Detect `extern "C" {` blocks (optionally preceded by `unsafe`)
        if tokens[i].text == "extern":
            j = i + 1
            if j < n and tokens[j].kind == "STRING":
                j += 1
            if j < n and tokens[j].text == "{":
                brace_depth += 1
                in_extern_block_brace_depths.append(brace_depth)
                i = j + 1
                continue

        if tokens[i].text == "#" and i + 1 < n and tokens[i + 1].text == "[":
            attrs, after_attrs = _collect_rust_outer_attrs(tokens, i)
            is_external_spec_attr = False
            is_spec_attr = False
            req_clauses: list[list[Token]] = []
            ens_clauses: list[list[Token]] = []
            attr_line = tokens[i].line
            for attr_toks, ln in attrs:
                path, args = _attr_path_and_args(attr_toks)
                leaf = path.split("::")[-1] if path else ""
                if leaf == "external_spec":
                    is_external_spec_attr = True
                    attr_line = ln
                    rq, en = _extract_contract_clauses(args)
                    req_clauses.extend(rq)
                    ens_clauses.extend(en)
                elif leaf in ("ensures", "requires"):
                    is_spec_attr = True
                    if leaf == "ensures":
                        ens_clauses.append(args)
                    else:
                        req_clauses.append(args)
                elif leaf in ("spec", "embed_spec", "trusted"):
                    is_spec_attr = True
                    rq, en = _extract_contract_clauses(args)
                    req_clauses.extend(rq)
                    ens_clauses.extend(en)

            fn_info = _parse_rust_fn_sig(tokens, after_attrs)
            if fn_info is not None:
                fn_name, is_extern_fn, is_diverging, next_pos = fn_info
                is_extern_target = (
                    is_external_spec_attr
                    or (is_spec_attr and (is_extern_fn or bool(in_extern_block_brace_depths)))
                )
                if is_extern_target and ens_clauses and not is_diverging:
                    req_unsat = any(_rust_expr_is_unsatisfiable(r) for r in req_clauses)
                    if not req_unsat:
                        ens_unsat = any(_rust_expr_is_unsatisfiable(e) for e in ens_clauses) or _rust_conjuncts_contradict(
                            [_strip_closure_header(e) for e in ens_clauses]
                        )
                        if ens_unsat:
                            findings.append(
                                _make_peer_finding(
                                    "unsatisfiable_extern_ensures",
                                    fn_name,
                                    attr_line,
                                    "non-diverging extern/external_spec carries unsatisfiable ensures",
                                    file_path=file_path,
                                )
                            )
                i = next_pos
                continue
            i = after_attrs
            continue
        i += 1
    return findings


def _parse_rust_path_at(tokens: list[Token], pos: int) -> tuple[list[str], int, bool]:
    """Parse a Rust path `a::b::c` (with optional turbofish `::<...>`) starting at `pos`.

    Returns `(segments, next_index, had_turbofish)`.
    """
    i = pos
    n = len(tokens)
    segs: list[str] = []
    had_turbofish = False
    if i < n and tokens[i].text == "::":
        i += 1
    if i >= n or tokens[i].kind != "IDENT":
        return [], pos, False
    segs.append(tokens[i].text)
    i += 1
    while i < n and tokens[i].text == "::":
        if i + 1 < n and tokens[i + 1].text == "<":
            # Turbofish `::<...>`
            had_turbofish = True
            j = i + 2
            depth = 1
            while j < n and depth > 0:
                if tokens[j].text == "<":
                    depth += 1
                elif tokens[j].text == ">":
                    depth -= 1
                j += 1
            i = j
            break
        elif i + 1 < n and tokens[i + 1].kind == "IDENT":
            segs.append(tokens[i + 1].text)
            i += 2
        else:
            break
    return segs, i, had_turbofish


def scan_rust_fndef_ghost_token_coercion(
    text: str,
    *,
    file_path: str | None = None,
    extra_token_ctors: set[str] | None = None,
) -> list[dict[str, Any]]:
    """Guard 4 (`creusot#2389`): ban non-call `FnDef` / closure / `fn()` coercions on ghost-token ctors."""
    tokens = lex_rust_tokens(text)
    n = len(tokens)
    findings: list[dict[str, Any]] = []

    # Pass 1: discover `#[ghost_token_ctor]` functions/methods and `use ... as Alias` aliases.
    ctor_suffixes: set[tuple[str, ...]] = {("Tokens", "new")}
    if extra_token_ctors:
        for c in extra_token_ctors:
            ctor_suffixes.add(tuple(seg for seg in c.split("::") if seg))
    type_aliases: dict[str, tuple[str, ...]] = {}
    fn_aliases: set[str] = set()
    fn_header_spans: list[tuple[int, int]] = []
    use_spans: list[tuple[int, int]] = []

    current_impl_type: str | None = None
    impl_brace_depth: int | None = None
    brace_depth = 0
    i = 0
    while i < n:
        if tokens[i].text == "{":
            brace_depth += 1
            i += 1
            continue
        if tokens[i].text == "}":
            if impl_brace_depth is not None and brace_depth == impl_brace_depth:
                current_impl_type = None
                impl_brace_depth = None
            brace_depth = max(0, brace_depth - 1)
            i += 1
            continue

        # Track `impl [Trait for] TypeName {`
        if tokens[i].text == "impl":
            j = i + 1
            if j < n and tokens[j].text == "<":
                d = 1
                j += 1
                while j < n and d > 0:
                    if tokens[j].text == "<":
                        d += 1
                    elif tokens[j].text == ">":
                        d -= 1
                    j += 1
            last_ident = None
            while j < n and tokens[j].text != "{":
                if tokens[j].text == "where":
                    while j < n and tokens[j].text != "{":
                        j += 1
                    break
                if tokens[j].kind == "IDENT" and tokens[j].text != "for":
                    last_ident = tokens[j].text
                j += 1
            if j < n and tokens[j].text == "{":
                brace_depth += 1
                current_impl_type = last_ident
                impl_brace_depth = brace_depth
                i = j + 1
                continue

        # Track `use ...;`
        if tokens[i].text == "use":
            u_start = i
            j = i + 1
            while j < n and tokens[j].text != ";":
                j += 1
            use_toks = tokens[u_start + 1 : j]
            use_spans.append((u_start, j))
            # Handle `use foo::Tokens as T;` and `use foo::Tokens::new as mk;`
            as_idx = next((k for k, t in enumerate(use_toks) if t.text == "as"), -1)
            if as_idx != -1 and as_idx + 1 < len(use_toks):
                lhs_segs = [t.text for t in use_toks[:as_idx] if t.kind == "IDENT"]
                alias = use_toks[as_idx + 1].text
                if lhs_segs:
                    if lhs_segs[-1] == "Tokens":
                        type_aliases[alias] = ("Tokens",)
                    elif tuple(lhs_segs[-2:]) in ctor_suffixes or (lhs_segs[-1],) in ctor_suffixes:
                        fn_aliases.add(alias)
            i = j + 1
            continue

        if tokens[i].text == "#" and i + 1 < n and tokens[i + 1].text == "[":
            attrs, after_attrs = _collect_rust_outer_attrs(tokens, i)
            has_ctor_attr = any(
                _attr_path_and_args(at)[0].split("::")[-1] == "ghost_token_ctor"
                for at, _ in attrs
            )
            fn_info = _parse_rust_fn_sig(tokens, after_attrs)
            if fn_info is not None:
                fn_name, _, _, sig_end = fn_info
                fn_header_spans.append((after_attrs, sig_end))
                if has_ctor_attr:
                    if current_impl_type:
                        ctor_suffixes.add((current_impl_type, fn_name))
                    else:
                        ctor_suffixes.add((fn_name,))
                i = sig_end
                continue
            i = after_attrs
            continue

        if tokens[i].text == "fn":
            fn_info = _parse_rust_fn_sig(tokens, i)
            if fn_info is not None:
                fn_header_spans.append((i, fn_info[3]))
                i = fn_info[3]
                continue
        i += 1

    # Expand aliases
    expanded_suffixes = set(ctor_suffixes)
    for alias in type_aliases:
        expanded_suffixes.add((alias, "new"))
    for alias in fn_aliases:
        expanded_suffixes.add((alias,))

    ignored = [False] * n
    for s, e in fn_header_spans:
        for k in range(max(0, s), min(n, e)):
            ignored[k] = True
    for s, e in use_spans:
        for k in range(max(0, s), min(n, e + 1)):
            ignored[k] = True

    def matches_ctor(segs: list[str]) -> bool:
        if not segs:
            return False
        t_segs = tuple(segs)
        for suf in expanded_suffixes:
            if len(t_segs) >= len(suf) and t_segs[-len(suf) :] == suf:
                return True
        return False

    # Pass 2: scan token occurrences, tracking closure scopes (`|...|` / `||`).
    closure_end_stack: list[int] = []
    i = 0
    while i < n:
        while closure_end_stack and i >= closure_end_stack[-1]:
            closure_end_stack.pop()

        if tokens[i].text == "#" and i + 1 < n and tokens[i + 1].text == "[":
            _, i = _collect_rust_outer_attrs(tokens, i)
            continue

        if ignored[i]:
            i += 1
            continue

        # Detect closure start: `|| expr` or `|params| expr` when preceded by expr-start token
        prev_txt = tokens[i - 1].text if i > 0 else ""
        can_start_closure = i == 0 or prev_txt in (
            "=", "(", ",", "{", ";", "return", "move", "=>", ":", "[", "&&", "||",
        )
        if can_start_closure and tokens[i].text in ("||", "|"):
            body_start = -1
            if tokens[i].text == "||":
                body_start = i + 1
            else:
                # Find closing `|` of closure params before `;`/`{`/`}`
                j = i + 1
                pdepth = 0
                while j < n:
                    if tokens[j].text in ("(", "[", "<"):
                        pdepth += 1
                    elif tokens[j].text in (")", "]", ">"):
                        pdepth = max(0, pdepth - 1)
                    elif pdepth == 0 and tokens[j].text == "|":
                        body_start = j + 1
                        break
                    elif pdepth == 0 and tokens[j].text in (";", "{", "}"):
                        break
                    j += 1
            if body_start != -1 and body_start < n:
                # Skip optional `-> RetType`
                k = body_start
                if k < n and tokens[k].text == "->":
                    k += 1
                    while k < n and tokens[k].text != "{":
                        k += 1
                if k < n and tokens[k].text == "{":
                    c_end = _find_matching_delim(tokens, k, "{", "}") + 1
                else:
                    # Single-expression closure ends at depth-0 `,`, `)`, `]`, `;`, `}`
                    c_end = k
                    ed = 0
                    while c_end < n:
                        et = tokens[c_end].text
                        if et in ("(", "[", "{"):
                            ed += 1
                        elif et in (")", "]", "}"):
                            if ed == 0:
                                break
                            ed -= 1
                        elif ed == 0 and et in (",", ";"):
                            break
                        c_end += 1
                closure_end_stack.append(c_end)
                i = body_start
                continue

        if tokens[i].kind == "IDENT" or (
            tokens[i].text == "::" and i + 1 < n and tokens[i + 1].kind == "IDENT"
        ):
            segs, next_i, _ = _parse_rust_path_at(tokens, i)
            if matches_ctor(segs):
                is_direct_call = next_i < n and tokens[next_i].text == "("
                path_str = "::".join(segs)
                if not is_direct_call:
                    findings.append(
                        _make_peer_finding(
                            "fndef_ghost_token_coercion",
                            path_str,
                            tokens[i].line,
                            "non-call FnDef value reference or fn() coercion on one-shot ghost-token constructor",
                            file_path=file_path,
                        )
                    )
                elif closure_end_stack:
                    findings.append(
                        _make_peer_finding(
                            "fndef_ghost_token_coercion",
                            path_str,
                            tokens[i].line,
                            "closure capture/invocation of one-shot ghost-token constructor allows multi-call duplication",
                            file_path=file_path,
                        )
                    )
                i = next_i
                continue
            i = max(i + 1, next_i)
            continue
        i += 1
    return findings


_STD_DROP_GLUE_TYPES: frozenset[str] = frozenset(
    {
        "Box",
        "Vec",
        "String",
        "File",
        "MutexGuard",
        "RwLockReadGuard",
        "RwLockWriteGuard",
        "Ref",
        "RefMut",
        "Arc",
        "Rc",
        "BTreeMap",
        "BTreeSet",
        "HashMap",
        "HashSet",
        "VecDeque",
        "LinkedList",
        "CString",
        "OsString",
        "PathBuf",
        "BufReader",
        "BufWriter",
        "TcpStream",
        "UdpSocket",
        "Child",
        "JoinHandle",
    }
)

_NO_DROP_WRAPPER_TYPES: frozenset[str] = frozenset({"PhantomData", "ManuallyDrop", "NonNull"})


def _extract_owned_type_names(type_toks: list[Token]) -> set[str]:
    """Extract owned nominal type names from a Rust field type (excluding `&T`, `*const T`, `ManuallyDrop<T>`, `PhantomData<T>`)."""
    out: set[str] = set()
    i = 0
    n = len(type_toks)
    # Leading reference `&...` or raw pointer `*const`/`*mut` or `fn(...)` has no drop glue
    if n > 0 and type_toks[0].text in ("&", "*", "fn"):
        return out
    while i < n:
        t = type_toks[i]
        if t.text in ("&", "*"):
            # Skip inner borrowed/raw-pointer type until matching delimiter or comma
            i += 1
            if i < n and type_toks[i].kind == "LIFETIME":
                i += 1
            if i < n and type_toks[i].text in ("mut", "const"):
                i += 1
            # Skip the referenced type token group
            if i < n and type_toks[i].kind == "IDENT":
                i += 1
                if i < n and type_toks[i].text == "<":
                    d = 1
                    i += 1
                    while i < n and d > 0:
                        if type_toks[i].text == "<":
                            d += 1
                        elif type_toks[i].text == ">":
                            d -= 1
                        i += 1
            continue
        if t.kind == "IDENT":
            # Take leaf of path `std::vec::Vec` -> `Vec`
            leaf = t.text
            j = i + 1
            while j + 1 < n and type_toks[j].text == "::" and type_toks[j + 1].kind == "IDENT":
                leaf = type_toks[j + 1].text
                j += 2
            if leaf in _NO_DROP_WRAPPER_TYPES:
                # Skip its generic args completely (no drop glue!)
                i = j
                if i < n and type_toks[i].text == "<":
                    d = 1
                    i += 1
                    while i < n and d > 0:
                        if type_toks[i].text == "<":
                            d += 1
                        elif type_toks[i].text == ">":
                            d -= 1
                        i += 1
                continue
            out.add(leaf)
            i = j
            continue
        i += 1
    return out


def scan_rust_external_type_drop_omission(
    text: str,
    *,
    file_path: str | None = None,
    known_drop_types: set[str] | None = None,
) -> list[dict[str, Any]]:
    """Guard 5 (`verus#3514`): reject `#[external_type_specification]` omitting `Drop` / drop glue."""
    tokens = lex_rust_tokens(text)
    n = len(tokens)

    # Pass 1: gather `impl ... Drop for TypeName` and struct/enum field type dependencies.
    direct_drop: set[str] = set(_STD_DROP_GLUE_TYPES)
    if known_drop_types:
        direct_drop.update(known_drop_types)
    type_fields: dict[str, set[str]] = {}
    ext_type_items: list[dict[str, Any]] = []

    i = 0
    while i < n:
        # Collect `impl [<...>] [path::]Drop for TypeName`
        if tokens[i].text == "impl":
            j = i + 1
            if j < n and tokens[j].text == "<":
                d = 1
                j += 1
                while j < n and d > 0:
                    if tokens[j].text == "<":
                        d += 1
                    elif tokens[j].text == ">":
                        d -= 1
                    j += 1
            # Scan trait path up to `for` or `{`
            trait_segs: list[str] = []
            found_for = False
            while j < n and tokens[j].text != "{":
                if tokens[j].text == "for":
                    found_for = True
                    j += 1
                    break
                if tokens[j].kind == "IDENT":
                    trait_segs.append(tokens[j].text)
                j += 1
            if found_for and trait_segs and trait_segs[-1] == "Drop":
                # Parse target type name after `for`
                target_segs, _, _ = _parse_rust_path_at(tokens, j)
                if target_segs:
                    direct_drop.add(target_segs[-1])
            i += 1
            continue

        attrs: list[tuple[list[Token], int]] = []
        item_start = i
        if tokens[i].text == "#" and i + 1 < n and tokens[i + 1].text == "[":
            attrs, i = _collect_rust_outer_attrs(tokens, i)

        # Skip visibility
        j = i
        if j < n and tokens[j].text == "pub":
            j += 1
            if j < n and tokens[j].text == "(":
                j = _find_matching_delim(tokens, j, "(", ")") + 1

        if j < n and tokens[j].text in ("struct", "enum"):
            kind_kw = tokens[j].text
            j += 1
            if j < n and tokens[j].kind == "IDENT":
                type_name = tokens[j].text
                type_line = tokens[j].line
                j += 1
                # Skip generics `<...>`
                if j < n and tokens[j].text == "<":
                    d = 1
                    j += 1
                    while j < n and d > 0:
                        if tokens[j].text == "<":
                            d += 1
                        elif tokens[j].text == ">":
                            d -= 1
                        j += 1
                # Skip `where ...`
                if j < n and tokens[j].text == "where":
                    while j < n and tokens[j].text not in ("{", "(", ";"):
                        j += 1
                owned_deps: set[str] = set()
                tuple_wrapped: list[str] = []
                if j < n and tokens[j].text == "(":
                    close_p = _find_matching_delim(tokens, j, "(", ")")
                    for field_toks in _split_top_level_tokens(tokens[j + 1 : close_p], ","):
                        # Strip field visibility/attrs
                        ft = [t for t in field_toks if t.text != "pub"]
                        deps = _extract_owned_type_names(ft)
                        owned_deps.update(deps)
                        if len(deps) == 1:
                            tuple_wrapped.extend(deps)
                    j = close_p + 1
                elif j < n and tokens[j].text == "{":
                    close_b = _find_matching_delim(tokens, j, "{", "}")
                    body = tokens[j + 1 : close_b]
                    if kind_kw == "struct":
                        for field_toks in _split_top_level_tokens(body, ","):
                            colon = next((k for k, t in enumerate(field_toks) if t.text == ":"), -1)
                            if colon != -1:
                                owned_deps.update(_extract_owned_type_names(field_toks[colon + 1 :]))
                    else:
                        # Enum variants
                        for var_toks in _split_top_level_tokens(body, ","):
                            if "(" in [t.text for t in var_toks]:
                                lp = next(k for k, t in enumerate(var_toks) if t.text == "(")
                                rp = _find_matching_delim(var_toks, lp, "(", ")")
                                for ft in _split_top_level_tokens(var_toks[lp + 1 : rp], ","):
                                    owned_deps.update(_extract_owned_type_names(ft))
                            elif "{" in [t.text for t in var_toks]:
                                lb = next(k for k, t in enumerate(var_toks) if t.text == "{")
                                rb = _find_matching_delim(var_toks, lb, "{", "}")
                                for ft in _split_top_level_tokens(var_toks[lb + 1 : rb], ","):
                                    colon = next((k for k, t in enumerate(ft) if t.text == ":"), -1)
                                    if colon != -1:
                                        owned_deps.update(_extract_owned_type_names(ft[colon + 1 :]))
                    j = close_b + 1

                type_fields.setdefault(type_name, set()).update(owned_deps)

                # Inspect attributes for `external_type_specification`
                has_ext_type = False
                has_ext_body = False
                drop_modeled = False
                explicit_drop = False
                explicit_for_targets: set[str] = set()
                attr_line = type_line
                for attr_toks, ln in attrs:
                    path, args = _attr_path_and_args(attr_toks)
                    leaf = path.split("::")[-1] if path else ""
                    if leaf == "external_type_specification":
                        has_ext_type = True
                        attr_line = ln
                        for item in _split_top_level_tokens(args, ","):
                            if len(item) >= 3 and item[0].text == "for" and item[1].text == "=":
                                segs, _, _ = _parse_rust_path_at(item, 2)
                                if segs:
                                    explicit_for_targets.add(segs[-1])
                            if any(t.text in ("models_drop", "drop_modeled") for t in item):
                                drop_modeled = True
                            if any(t.text == "external_body" for t in item):
                                has_ext_body = True
                    elif leaf == "external_body":
                        has_ext_body = True
                    elif leaf in ("drop_spec", "models_drop", "anneal_drop_modeled"):
                        drop_modeled = True
                    elif leaf in ("has_drop_glue", "implements_drop"):
                        explicit_drop = True

                if has_ext_type:
                    targets = set(explicit_for_targets) | set(tuple_wrapped) | {type_name}
                    ext_type_items.append(
                        {
                            "name": type_name,
                            "line": attr_line,
                            "targets": targets,
                            "has_external_body": has_ext_body,
                            "drop_modeled": drop_modeled,
                            "explicit_drop": explicit_drop,
                        }
                    )
                i = max(j, item_start + 1)
                continue

        i = max(i + 1, item_start + 1)

    # Pass 2: transitive drop-glue fixed point
    has_drop_glue: set[str] = set(direct_drop)
    changed = True
    while changed:
        changed = False
        for tname, deps in type_fields.items():
            if tname not in has_drop_glue and (deps & has_drop_glue):
                has_drop_glue.add(tname)
                changed = True

    # Pass 3: emit findings for `#[external_type_specification]` items
    findings: list[dict[str, Any]] = []
    for item in ext_type_items:
        drop_hits = sorted(t for t in item["targets"] if t in has_drop_glue)
        if item["explicit_drop"] or drop_hits:
            if item["has_external_body"]:
                findings.append(
                    _make_peer_finding(
                        "external_type_body_with_drop",
                        item["name"],
                        item["line"],
                        f"external_type_specification combined with external_body on Drop/drop-glue type ({', '.join(drop_hits) or item['name']})",
                        file_path=file_path,
                    )
                )
            elif not item["drop_modeled"]:
                findings.append(
                    _make_peer_finding(
                        "external_type_drop_omission",
                        item["name"],
                        item["line"],
                        f"external_type_specification omits modeled Drop / transitive drop glue ({', '.join(drop_hits) or item['name']})",
                        file_path=file_path,
                    )
                )
    return findings


# ---------------------------------------------------------------------------
# Lean 4 Lexer & Guards 6a (Verifrag) + 6b (Samite)
# ---------------------------------------------------------------------------


def _match_lean_interp_string(text: str, pos: int, n: int) -> int:
    """Scan a Lean interpolated string `s!"... { expr } ..."` starting at the opening `"`."""
    i = pos + 1
    while i < n:
        ch = text[i]
        if ch == "\\":
            i += 2
            continue
        if ch == '"':
            return i + 1
        if ch == "{":
            # Balanced interpolation expression (may contain nested strings/braces/comments)
            depth = 1
            i += 1
            while i < n and depth > 0:
                c = text[i]
                if c == '"':
                    i += 1
                    while i < n:
                        if text[i] == "\\":
                            i += 2
                            continue
                        if text[i] == '"':
                            i += 1
                            break
                        i += 1
                elif c == "{":
                    depth += 1
                    i += 1
                elif c == "}":
                    depth -= 1
                    i += 1
                else:
                    i += 1
            continue
        i += 1
    return n


def _is_lean_ident_start(ch: str) -> bool:
    return ch.isalpha() or ch == "_"


def _is_lean_ident_continue(ch: str) -> bool:
    return ch.isalnum() or ch in ("_", "'", "?", "!")


def _match_lean_char(text: str, pos: int, n: int) -> int | None:
    if pos >= n or text[pos] != "'" or pos + 1 >= n:
        return None
    if text[pos + 1] == "\\":
        i = pos + 2
        if i >= n:
            return None
        esc = text[i]
        if esc in ("n", "r", "t", "\\", "0", "'", '"'):
            i += 1
        elif esc == "x":
            i += 3
        elif esc == "u":
            i += 5
        else:
            return None
        return i + 1 if (i < n and text[i] == "'") else None
    if text[pos + 1] != "'" and text[pos + 1] != "\n" and pos + 2 < n and text[pos + 2] == "'":
        return pos + 3
    return None


def lex_lean_tokens(text: str) -> tuple[list[Token], list[CommentSpan]]:
    """Nested-comment, interpolated-string, char-literal, and guillemet-aware Lean 4 lexer."""
    tokens: list[Token] = []
    comments: list[CommentSpan] = []
    n = len(text)
    i = 0
    line = 1
    two_char_ops = {"::", ":=", "->", "/\\", "\\/", "!=", "<=", ">=", "&&", "||", "@["}
    unicode_ops = {"→", "↔", "∧", "∨", "¬", "∀", "∃", "≠", "≤", "≥"}

    while i < n:
        ch = text[i]
        if ch in " \t\r":
            i += 1
            continue
        if ch == "\n":
            line += 1
            i += 1
            continue

        # Line comment `-- ...`
        if ch == "-" and i + 1 < n and text[i + 1] == "-":
            nl = text.find("\n", i + 2)
            end = n if nl == -1 else nl
            comments.append(CommentSpan("line", text[i:end], i, end, line))
            i = end
            continue

        # Nested block comment `/- ... -/` (incl. `/--` docstring and `/-!` module doc)
        if ch == "/" and i + 1 < n and text[i + 1] == "-":
            start = i
            start_line = line
            ckind = "block"
            if i + 2 < n and text[i + 2] == "-":
                ckind = "doc_block"
            elif i + 2 < n and text[i + 2] == "!":
                ckind = "mod_doc"
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text[i] == "\n":
                    line += 1
                    i += 1
                elif text[i] == "/" and i + 1 < n and text[i + 1] == "-":
                    depth += 1
                    i += 2
                elif text[i] == "-" and i + 1 < n and text[i + 1] == "/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            comments.append(CommentSpan(ckind, text[start:i], start, i, start_line))
            continue

        # Interpolated string `s!"..."`, `m!"..."`, `f!"..."`
        if ch in ("s", "m", "f") and i + 2 < n and text[i + 1] == "!" and text[i + 2] == '"':
            start_line = line
            end = _match_lean_interp_string(text, i + 2, n)
            seg = text[i:end]
            tokens.append(Token("STRING", seg, i, end, start_line))
            line += seg.count("\n")
            i = end
            continue

        # Standard string literal `"..."`
        if ch == '"':
            start_line = line
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == "\n":
                    line += 1
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            tokens.append(Token("STRING", text[i:j], i, j, start_line))
            i = j
            continue

        # Char literal `'x'` (only when not trailing an identifier)
        if ch == "'":
            c_end = _match_lean_char(text, i, n)
            if c_end is not None:
                tokens.append(Token("CHAR", text[i:c_end], i, c_end, line))
                i = c_end
                continue

        # Escaped identifier `«...»`
        if ch == "«":
            close = text.find("»", i + 1)
            end = n if close == -1 else close + 1
            seg = text[i:end]
            tokens.append(Token("IDENT", seg, i, end, line))
            line += seg.count("\n")
            i = end
            continue

        # 3-char op `<->`
        if text[i : i + 3] == "<->":
            tokens.append(Token("OP", "<->", i, i + 3, line))
            i += 3
            continue

        # 2-char ops (note `@[` is emitted as a single OP token)
        if i + 1 < n and text[i : i + 2] in two_char_ops:
            tokens.append(Token("OP", text[i : i + 2], i, i + 2, line))
            i += 2
            continue

        if ch in unicode_ops:
            tokens.append(Token("OP", ch, i, i + 1, line))
            i += 1
            continue

        # Identifiers (keep `.` separated as PUNCT or compound? Keep dotted names intact only if no spaces!)
        if _is_lean_ident_start(ch):
            j = i + 1
            while j < n and _is_lean_ident_continue(text[j]):
                j += 1
            # Attach dotted projection/namespace suffixes `a.b.c` cleanly
            while j + 1 < n and text[j] == "." and _is_lean_ident_start(text[j + 1]):
                j += 2
                while j < n and _is_lean_ident_continue(text[j]):
                    j += 1
            tokens.append(Token("IDENT", text[i:j], i, j, line))
            i = j
            continue

        if ch.isdigit():
            j = i + 1
            while j < n and (text[j].isalnum() or text[j] == "_"):
                j += 1
            tokens.append(Token("NUMBER", text[i:j], i, j, line))
            i = j
            continue

        tokens.append(Token("PUNCT", ch, i, i + 1, line))
        i += 1

    return tokens, comments


def _skip_lean_attr_block(tokens: list[Token], pos: int) -> int:
    """If `tokens[pos]` is `@[`, advance past the matching `]`."""
    n = len(tokens)
    if pos >= n or tokens[pos].text != "@[":
        return pos
    depth = 1
    i = pos + 1
    while i < n and depth > 0:
        if tokens[i].text in ("[", "@["):
            depth += 1
        elif tokens[i].text == "]":
            depth -= 1
        i += 1
    return i


def _skip_lean_attrs_and_mods(tokens: list[Token], pos: int) -> int:
    i = pos
    n = len(tokens)
    mods = {"private", "protected", "noncomputable", "unsafe", "partial", "local", "scoped"}
    while i < n:
        if tokens[i].text == "@[":
            i = _skip_lean_attr_block(tokens, i)
        elif tokens[i].kind == "IDENT" and tokens[i].text in mods:
            i += 1
        else:
            break
    return i


_ASSUMES_IDENT_LEAVES: frozenset[str] = frozenset(
    {"assumesHold", "implAssumes", "specAssumes", "envAssumes"}
)


def _is_assumes_token(tok: Token) -> bool:
    if tok.kind != "IDENT":
        return False
    leaf = tok.text.split(".")[-1]
    return leaf in _ASSUMES_IDENT_LEAVES


def _flip_pol(pol: str) -> str:
    return "neg" if pol == "pos" else "pos"


def _check_lean_prop_polarity(toks: list[Token], pol: str = "pos") -> list[Token]:
    """Recursive-descent Lean propositional polarity checker returning any positive-polarity assumes tokens."""
    # Strip outer parens
    while (
        len(toks) >= 2
        and toks[0].text == "("
        and _find_matching_delim(toks, 0, "(", ")") == len(toks) - 1
    ):
        toks = toks[1:-1]
    if not toks:
        return []

    # Strip leading `∀ ... ,` or `∃ ... ,` quantifiers at depth 0
    if toks[0].text in ("∀", "∃", "forall", "exists"):
        depth = 0
        for idx in range(1, len(toks)):
            t = toks[idx].text
            if t in ("(", "[", "{"):
                depth += 1
            elif t in (")", "]", "}"):
                depth = max(0, depth - 1)
            elif depth == 0 and t == ",":
                return _check_lean_prop_polarity(toks[idx + 1 :], pol)

    # Lowest precedence: `↔` / `<->` (both polarities!)
    for op in ("↔", "<->"):
        parts = _split_top_level_tokens(toks, op)
        if len(parts) > 1:
            bad: list[Token] = []
            for p in parts:
                bad.extend(_check_lean_prop_polarity(p, "pos"))
                bad.extend(_check_lean_prop_polarity(p, "neg"))
            return bad

    # Next: `→` / `->` (right-associative! Find FIRST depth-0 arrow)
    depth = 0
    arrow_idx = -1
    for idx, tok in enumerate(toks):
        if tok.text in ("(", "[", "{"):
            depth += 1
        elif tok.text in (")", "]", "}"):
            depth = max(0, depth - 1)
        elif depth == 0 and tok.text in ("→", "->"):
            arrow_idx = idx
            break
    if arrow_idx != -1:
        lhs = toks[:arrow_idx]
        rhs = toks[arrow_idx + 1 :]
        # Dependent binder `(h : T) → rhs` -> strip binder name `h :` inside parens
        lhs_s = _strip_outer_parens(lhs)
        if len(lhs_s) >= 3 and lhs_s[0].kind == "IDENT" and lhs_s[1].text == ":":
            lhs = lhs_s[2:]
        return _check_lean_prop_polarity(lhs, _flip_pol(pol)) + _check_lean_prop_polarity(rhs, pol)

    # Next: `∨` / `\/`
    for op in ("∨", "\\/"):
        parts = _split_top_level_tokens(toks, op)
        if len(parts) > 1:
            bad = []
            for p in parts:
                bad.extend(_check_lean_prop_polarity(p, pol))
            return bad

    # Next: `∧` / `/\`
    for op in ("∧", "/\\"):
        parts = _split_top_level_tokens(toks, op)
        if len(parts) > 1:
            bad = []
            for p in parts:
                bad.extend(_check_lean_prop_polarity(p, pol))
            return bad

    # Next: unary negation `¬` / `Not`
    if toks[0].text in ("¬", "Not"):
        return _check_lean_prop_polarity(toks[1:], _flip_pol(pol))

    # Leaf / atomic expression: check sub-parenthesized expressions and direct assumes tokens
    bad = []
    i = 0
    while i < len(toks):
        if toks[i].text == "(":
            close = _find_matching_delim(toks, i, "(", ")")
            bad.extend(_check_lean_prop_polarity(toks[i + 1 : close], pol))
            i = close + 1
            continue
        if _is_assumes_token(toks[i]) and pol == "pos":
            bad.append(toks[i])
        i += 1
    return bad


_LEAN_TOP_COMMANDS: frozenset[str] = frozenset(
    {
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "structure",
        "inductive",
        "class",
        "instance",
        "axiom",
        "opaque",
        "namespace",
        "section",
        "end",
        "open",
        "variable",
        "universe",
        "import",
        "set_option",
        "attribute",
        "deriving",
        "mutual",
    }
)


def scan_lean_assumption_polarity(
    text: str,
    *,
    file_path: str | None = None,
) -> list[dict[str, Any]]:
    """Guard 6a (`Verifrag` cl/1029131309): audit Lean equivalence obligations for positive-polarity assumptions."""
    tokens, _ = lex_lean_tokens(text)
    findings: list[dict[str, Any]] = []
    n = len(tokens)
    i = 0
    while i < n:
        # Advance past leading attrs/modifiers to check for `theorem`/`lemma`/`def`/`abbrev`
        start_i = i
        j = _skip_lean_attrs_and_mods(tokens, i)
        if j >= n:
            break
        kw = tokens[j].text
        if kw in ("theorem", "lemma", "def", "abbrev") and j + 1 < n and tokens[j + 1].kind == "IDENT":
            decl_name = tokens[j + 1].text
            decl_line = tokens[j].line
            # Find depth-0 `:` (signature start) and `:=` / `where` (body start)
            k = j + 2
            depth = 0
            colon_idx = -1
            assign_idx = -1
            while k < n:
                t = tokens[k].text
                if t in ("(", "[", "{", "@["):
                    depth += 1
                elif t in (")", "]", "}"):
                    depth = max(0, depth - 1)
                elif depth == 0:
                    if t == ":" and colon_idx == -1:
                        colon_idx = k
                    elif t in (":=", "where"):
                        assign_idx = k
                        break
                    elif t in _LEAN_TOP_COMMANDS and k > j + 2:
                        break
                k += 1

            # Also find end of declaration (next top-level command at depth 0)
            body_end = assign_idx + 1 if assign_idx != -1 else k
            depth = 0
            while body_end < n:
                t = tokens[body_end].text
                if t in ("(", "[", "{", "@["):
                    depth += 1
                elif t in (")", "]", "}"):
                    depth = max(0, depth - 1)
                elif depth == 0 and (
                    t in _LEAN_TOP_COMMANDS or t == "@["
                ):
                    break
                body_end += 1

            # Inspect statement (for theorem/lemma) or Prop body (for `: Prop :=` def/abbrev)
            target_slices: list[list[Token]] = []
            if kw in ("theorem", "lemma") and colon_idx != -1:
                stmt_end = assign_idx if assign_idx != -1 else k
                target_slices.append(tokens[colon_idx + 1 : stmt_end])
            elif kw in ("def", "abbrev") and colon_idx != -1 and assign_idx != -1:
                ret_slice = tokens[colon_idx + 1 : assign_idx]
                if any(t.text == "Prop" for t in ret_slice):
                    target_slices.append(tokens[assign_idx + 1 : body_end])

            for sl in target_slices:
                if any(_is_assumes_token(t) for t in sl):
                    bad_toks = _check_lean_prop_polarity(sl, pol="pos")
                    if bad_toks:
                        findings.append(
                            _make_peer_finding(
                                "assumption_positive_polarity",
                                decl_name,
                                bad_toks[0].line or decl_line,
                                f"assumption `{bad_toks[0].text}` appears in positive polarity",
                                file_path=file_path,
                            )
                        )
                        break

            i = max(body_end, start_i + 1)
            continue
        i = max(j + 1, start_i + 1)
    return findings


def _comments_immediately_before(
    comments: list[CommentSpan],
    prev_tok_end: int,
    decl_start: int,
) -> list[CommentSpan]:
    return [c for c in comments if prev_tok_end <= c.start and c.end <= decl_start]


def scan_lean_invariant_struct_sealing(
    text: str,
    *,
    target_structs: set[str] | None = None,
    file_path: str | None = None,
) -> list[dict[str, Any]]:
    """Guard 6b (`Samite` cl/1029680381): verify invariant-bearing Lean `structure`s start with `private mk ::`."""
    tokens, comments = lex_lean_tokens(text)
    findings: list[dict[str, Any]] = []
    n = len(tokens)
    ns_stack: list[str] = []
    scope_kinds: list[tuple[str, str | None]] = []  # ("namespace"|"section", name)

    i = 0
    while i < n:
        prev_end = tokens[i - 1].end if i > 0 else 0
        start_i = i
        j = _skip_lean_attrs_and_mods(tokens, i)
        if j >= n:
            break

        # Track namespace / section / end for qualified struct names
        if tokens[j].text == "namespace" and j + 1 < n and tokens[j + 1].kind == "IDENT":
            ns_name = tokens[j + 1].text
            ns_stack.append(ns_name)
            scope_kinds.append(("namespace", ns_name))
            i = j + 2
            continue
        if tokens[j].text == "section":
            sec_name = (
                tokens[j + 1].text
                if (j + 1 < n and tokens[j + 1].kind == "IDENT" and tokens[j + 1].text not in _LEAN_TOP_COMMANDS)
                else None
            )
            scope_kinds.append(("section", sec_name))
            i = j + (2 if sec_name else 1)
            continue
        if tokens[j].text == "end":
            end_name = (
                tokens[j + 1].text
                if (j + 1 < n and tokens[j + 1].kind == "IDENT" and tokens[j + 1].text not in _LEAN_TOP_COMMANDS)
                else None
            )
            if scope_kinds:
                kind, nm = scope_kinds.pop()
                if kind == "namespace" and ns_stack:
                    ns_stack.pop()
            i = j + (2 if end_name else 1)
            continue

        if tokens[j].text == "structure" and j + 1 < n and tokens[j + 1].kind == "IDENT":
            raw_name = tokens[j + 1].text
            struct_line = tokens[j].line
            qual_name = ".".join(ns_stack + [raw_name]) if ns_stack else raw_name
            short_leaf = raw_name.split(".")[-1]

            # Check whether this structure is an invariant-bearing target
            leading_comments = _comments_immediately_before(comments, prev_end, tokens[start_i].start)
            has_marker_comment = any(
                "@sealed_invariant" in c.text or "sealed_invariant" in c.text
                for c in leading_comments
            )
            has_marker_attr = any(
                tokens[k].text == "sealed_invariant" for k in range(start_i, j)
            )

            is_target = False
            if target_structs is not None:
                is_target = bool({raw_name, qual_name, short_leaf} & target_structs)
            else:
                is_target = has_marker_comment or has_marker_attr

            # Scan strictly within this structure's header at depth 0 for `where`
            k = j + 2
            depth = 0
            where_idx = -1
            while k < n:
                t = tokens[k].text
                if t == "@[":
                    k = _skip_lean_attr_block(tokens, k)
                    continue
                if t in ("(", "[", "{"):
                    depth += 1
                elif t in (")", "]", "}"):
                    depth = max(0, depth - 1)
                elif depth == 0:
                    if t == "where":
                        where_idx = k
                        break
                    if t in _LEAN_TOP_COMMANDS or t == "deriving":
                        break
                k += 1

            if is_target:
                sealed_ok = False
                reason = "missing `where` clause and `private mk ::` constructor"
                if where_idx != -1:
                    # Skip ONLY `@[...]` attribute blocks immediately after `where`
                    b = where_idx + 1
                    while b < n and tokens[b].text == "@[":
                        b = _skip_lean_attr_block(tokens, b)
                    if (
                        b + 2 < n
                        and tokens[b].kind == "IDENT"
                        and tokens[b].text == "private"
                        and tokens[b + 1].kind == "IDENT"
                        and tokens[b + 1].text == "mk"
                        and tokens[b + 2].text == "::"
                    ):
                        sealed_ok = True
                    else:
                        preview = " ".join(t.text for t in tokens[b : min(b + 4, n)])
                        reason = f"`where` body does not begin with `private mk ::` (found `{preview}`)"
                if not sealed_ok:
                    findings.append(
                        _make_peer_finding(
                            "unsealed_invariant_struct",
                            qual_name,
                            struct_line,
                            reason,
                            file_path=file_path,
                        )
                    )

            i = max((where_idx + 1 if where_idx != -1 else k), j + 2)
            continue

        i = max(j + 1, start_i + 1)
    return findings


def scan_rust_all_peer_guards(
    text: str,
    *,
    file_path: str | None = None,
    extra_token_ctors: set[str] | None = None,
    known_drop_types: set[str] | None = None,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    findings.extend(scan_rust_unsatisfiable_extern_ensures(text, file_path=file_path))
    findings.extend(
        scan_rust_fndef_ghost_token_coercion(
            text, file_path=file_path, extra_token_ctors=extra_token_ctors
        )
    )
    findings.extend(
        scan_rust_external_type_drop_omission(
            text, file_path=file_path, known_drop_types=known_drop_types
        )
    )
    findings.sort(key=lambda f: (f.get("file", ""), f["line"], f["rank"], f["code"], f["subject"]))
    return findings


def scan_lean_all_peer_guards(
    text: str,
    *,
    target_structs: set[str] | None = None,
    file_path: str | None = None,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    findings.extend(scan_lean_assumption_polarity(text, file_path=file_path))
    findings.extend(
        scan_lean_invariant_struct_sealing(
            text, target_structs=target_structs, file_path=file_path
        )
    )
    findings.sort(key=lambda f: (f.get("file", ""), f["line"], f["rank"], f["code"], f["subject"]))
    return findings


def scan_live_repo_peer_guards(repo_root: Path) -> dict[str, Any]:
    """Run all 4 peer-verifier guards across live `theory/Anneal/` and `crates/anneal-spec/`."""
    t0 = time.perf_counter()
    lean_files = sorted((repo_root / "theory" / "Anneal").rglob("*.lean"))
    rust_files = sorted((repo_root / "crates" / "anneal-spec").rglob("*.rs"))
    findings: list[dict[str, Any]] = []
    for lf in lean_files:
        rel = lf.relative_to(repo_root).as_posix()
        txt = lf.read_text(encoding="utf-8", errors="replace")
        findings.extend(scan_lean_all_peer_guards(txt, file_path=rel))
    for rf in rust_files:
        rel = rf.relative_to(repo_root).as_posix()
        txt = rf.read_text(encoding="utf-8", errors="replace")
        findings.extend(scan_rust_all_peer_guards(txt, file_path=rel))
    elapsed_sec = round(time.perf_counter() - t0, 4)
    return {
        "ok": len(findings) == 0,
        "elapsed_sec": elapsed_sec,
        "lean_files_scanned": len(lean_files),
        "rust_files_scanned": len(rust_files),
        "finding_count": len(findings),
        "findings": findings,
    }


# ---------------------------------------------------------------------------
# 5. CLI Entry Point
# ---------------------------------------------------------------------------


def _load_module_list_file(path: Path) -> list[str]:
    raw = path.read_text(encoding="utf-8").strip()
    if raw.startswith("[") or raw.startswith("{"):
        parsed = json.loads(raw)
        if isinstance(parsed, list):
            return [str(x) for x in parsed]
        if isinstance(parsed, dict) and "modules" in parsed:
            return [str(x) for x in parsed["modules"]]
    return [ln.strip() for ln in raw.splitlines() if ln.strip() and not ln.strip().startswith("#")]


def _load_shards_file(path: Path) -> list[list[str]]:
    parsed = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(parsed, dict) and "shards" in parsed:
        sh = parsed["shards"]
        if isinstance(sh, dict):
            return [list(v) for v in sh.values()]
        if isinstance(sh, list):
            return [list(v) for v in sh]
    if isinstance(parsed, list):
        return [list(v) for v in parsed]
    raise ValueError(f"Unsupported shard-modules-file format in {path}")


def build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Prototype CLI: lean4#16717 inductive replay, grmf sharded audit, and peer-verifier spec guards."
    )
    p.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Anneal repository root",
    )
    p.add_argument("--wire-schema", action="store_true", help="Emit frozen cross-language wire schema JSON")
    p.add_argument("--plan-shards", action="store_true", help="Emit deterministic 8-shard subsystem plan")
    p.add_argument("--orphan-only", action="store_true", help="Run <0.25s orphan & exact-partition completeness gate")
    p.add_argument("--exact-modules", type=str, default=None, help="Comma-separated exact module list for live .olean audit")
    p.add_argument("--modules-file", type=Path, default=None, help="File listing registered or exact modules (JSON or newline-delimited)")
    p.add_argument("--shard-modules-file", type=Path, default=None, help="JSON file defining shard partition")
    p.add_argument("--check-live-oleans", action="store_true", help="Run lean4#16717 + axiom check on compiled Trusted & Anneal .oleans")
    p.add_argument("--benchmark-live", action="store_true", help="Run full live sharding vs monolithic benchmark telemetry")
    p.add_argument("--max-workers", type=int, default=None, help="Max parallel shard workers for --benchmark-live")
    p.add_argument("--scan-guards", action="store_true", help="Sweep live theory/Anneal/ and crates/anneal-spec/ with Guards 3-6")
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_arg_parser().parse_args(argv)
    repo_root = args.repo_root.resolve()

    if args.wire_schema:
        print(json.dumps(wire_schema_dict(), indent=2, sort_keys=True))
        return 0

    if args.plan_shards:
        print(json.dumps(plan_subsystem_shards(repo_root), indent=2, sort_keys=True))
        return 0

    if args.orphan_only:
        reg = _load_module_list_file(args.modules_file) if args.modules_file else None
        sh = _load_shards_file(args.shard_modules_file) if args.shard_modules_file else None
        res = run_orphan_only_gate(repo_root, registered_modules=reg, shards=sh)
        print(json.dumps(res, indent=2, sort_keys=True))
        return 0 if res["ok"] else 1

    if args.exact_modules or (args.modules_file and not args.orphan_only):
        mods: list[str] = []
        if args.exact_modules:
            mods.extend(m.strip() for m in args.exact_modules.split(",") if m.strip())
        if args.modules_file:
            mods.extend(_load_module_list_file(args.modules_file))
        res = inspect_live_oleans(repo_root, import_modules=mods, exact_modules=mods)
        print(json.dumps(res, indent=2, sort_keys=True))
        return 0 if len(res["violations"]) == 0 else 1

    if args.check_live_oleans:
        plan = plan_subsystem_shards(repo_root)
        compiled = sorted(
            m for mods in plan["compiled_olean_shards"].values() for m in mods
        )
        res = inspect_live_oleans(repo_root, import_modules=compiled, exact_modules=compiled)
        print(json.dumps(res, indent=2, sort_keys=True))
        return 0 if len(res["violations"]) == 0 else 1

    if args.benchmark_live:
        res = run_live_benchmark(repo_root, max_workers=args.max_workers)
        print(json.dumps(res, indent=2, sort_keys=True))
        return 0 if res["parity"]["zero_violations"] and res["parity"]["axiom_union_matches_monolithic"] else 1

    if args.scan_guards:
        res = scan_live_repo_peer_guards(repo_root)
        print(json.dumps(res, indent=2, sort_keys=True))
        return 0 if res["ok"] else 1

    build_arg_parser().print_help()
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
