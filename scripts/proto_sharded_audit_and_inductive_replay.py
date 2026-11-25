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
import functools
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
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
    "recursor_mismatch",
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
    "module_name_collision",
    "cross_shard_duplicate_conflict",
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


_MISSING = object()

_KERNEL_INDUCT_META_FIELDS: tuple[str, ...] = (
    "name",
    "level_params",
    "type",
    "num_params",
    "all",
    "ctors",
    "num_nested",
    "is_reflexive",
    "is_unsafe",
)

_KERNEL_CTOR_FIELDS: tuple[str, ...] = (
    "name",
    "induct",
    "num_params",
    "num_fields",
    "level_params",
    "type",
    "is_unsafe",
)


def _stored_differs(kernel_rec: dict[str, Any], stored: dict[str, Any], field: str) -> bool:
    """A field the kernel generated must be present AND equal in the stored entry.

    Omitting a field from the stored `.olean`/JSON entry is itself a mismatch (fail closed):
    a forged entry must never pass merely by leaving out the field it lies about.
    """
    if field not in kernel_rec:
        return False
    return stored.get(field, _MISSING) != kernel_rec[field]


def check_inductive_replay_integrity(
    constants: dict[str, dict[str, Any]],
    kernel_inductives: dict[str, dict[str, Any]] | None = None,
    kernel_ctors: dict[str, dict[str, Any]] | None = None,
    kernel_recursors: dict[str, dict[str, Any]] | None = None,
) -> list[dict[str, str]]:
    """Verify all 13 `lean4#16717` structural and post-replay inductive invariants.

    Mirrors Lean `checkInductiveReplayIntegrity` = static ++ postponed inductives ++
    postponed constructors ++ postponed recursors.
    """
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
            if entry.get("num_indices", _MISSING) != k_info.get("num_indices", _MISSING):
                violations.append(
                    {
                        "code": "indices_mismatch",
                        "subject": name,
                        "detail": f"kernel={k_info.get('num_indices')} stored={entry.get('num_indices')}",
                    }
                )
            if entry.get("is_rec", _MISSING) != k_info.get("is_rec", _MISSING):
                violations.append(
                    {
                        "code": "is_rec_mismatch",
                        "subject": name,
                        "detail": f"kernel={k_info.get('is_rec')} stored={entry.get('is_rec')}",
                    }
                )
            for field in _KERNEL_INDUCT_META_FIELDS:
                if _stored_differs(k_info, entry, field):
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
            elif entry.get("cidx", _MISSING) != k_ctor.get("cidx", _MISSING):
                violations.append(
                    {
                        "code": "ctor_cidx_mismatch",
                        "subject": name,
                        "detail": "post_replay_cidx",
                    }
                )
            elif any(_stored_differs(k_ctor, entry, field) for field in _KERNEL_CTOR_FIELDS):
                violations.append(
                    {
                        "code": "ctor_induct_mismatch",
                        "subject": name,
                        "detail": "post_replay_ctor_diff",
                    }
                )

    if kernel_recursors is not None:
        for key in sorted(constants):
            entry = constants[key]
            if entry.get("kind") != "recursor":
                continue
            name = str(entry.get("name"))
            k_rec = kernel_recursors.get(name)
            if k_rec is None:
                violations.append(
                    {
                        "code": "recursor_mismatch",
                        "subject": name,
                        "detail": "rec_not_in_kernel",
                    }
                )
            elif {f: v for f, v in entry.items() if f != "kind"} != {
                f: v for f, v in k_rec.items() if f != "kind"
            }:
                violations.append(
                    {
                        "code": "recursor_mismatch",
                        "subject": name,
                        "detail": "post_replay_rec_diff",
                    }
                )

    return violations


def simulate_vulnerable_replay(
    constants: dict[str, dict[str, Any]],
    kernel_inductives: dict[str, dict[str, Any]],
    kernel_ctors: dict[str, dict[str, Any]],
    kernel_recursors: dict[str, dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Faithful model of Lean 4.34.1 `Replay.lean` (pre-`lean4#16717`), mirroring Lean `replayLoop`.

    - Iterates keys in the given order; a key is processed only while still in `remaining`.
    - `.inductInfo`: erases every `n in info.all` from `remaining`, replays ONLY `info.all`
      (never `info.name`), and the kernel rejects already-declared types.
    - Checks postponed constructors AND postponed recursors at the end (both exist in
      4.34.1) but has no `checkPostponedInductives`.
    """
    k_recs = kernel_recursors if kernel_recursors is not None else {}
    replayed_inducts: dict[str, dict[str, Any]] = {}
    replayed_ctors: dict[str, dict[str, Any]] = {}
    replayed_recs: dict[str, dict[str, Any]] = {}
    keys = list(constants.keys())
    remaining = list(keys)

    def _result(accepted: bool, error: str | None, ctor_errors: list[str], rec_errors: list[str]) -> dict[str, Any]:
        return {
            "accepted": accepted,
            "error": error,
            "ctor_errors": ctor_errors,
            "rec_errors": rec_errors,
            "replayed_inductives": sorted(replayed_inducts.keys()),
            "replayed_ctors": sorted(replayed_ctors.keys()),
            "replayed_recursors": sorted(replayed_recs.keys()),
        }

    for key in keys:
        if key not in remaining:
            continue
        remaining = [k for k in remaining if k != key]
        entry = constants[key]
        if entry.get("kind") != "inductive":
            continue
        all_names = list(entry.get("all", []))
        remaining = [k for k in remaining if k not in all_names]
        for peer_name in all_names:
            peer = constants.get(peer_name)
            if peer is None or peer.get("kind") != "inductive":
                return _result(False, f"malformed induct req for {key}", [], [])
            for ctor_name in peer.get("ctors", []):
                c = constants.get(ctor_name)
                if c is None or c.get("kind") != "constructor":
                    return _result(False, f"malformed induct req for {key}", [], [])
        if any(peer_name in replayed_inducts for peer_name in all_names):
            return _result(False, f"kernel: already declared while replaying {key}", [], [])
        if any(peer_name not in kernel_inductives for peer_name in all_names):
            return _result(False, f"kernel rejected induct req for {key}", [], [])
        for peer_name in all_names:
            k_ind = kernel_inductives[peer_name]
            replayed_inducts[peer_name] = k_ind
            for ctor_name in k_ind.get("ctors", []):
                if ctor_name in kernel_ctors:
                    replayed_ctors[ctor_name] = kernel_ctors[ctor_name]
            for rec_name, k_rec in k_recs.items():
                if list(k_rec.get("all", [])) == list(k_ind.get("all", [])):
                    replayed_recs[rec_name] = k_rec

    ctor_errors: list[str] = []
    rec_errors: list[str] = []
    for key in keys:
        entry = constants[key]
        if entry.get("kind") == "constructor":
            if key not in replayed_ctors or replayed_ctors[key] != entry:
                ctor_errors.append(key)
        elif entry.get("kind") == "recursor":
            if key not in replayed_recs or replayed_recs[key] != entry:
                rec_errors.append(key)
    if ctor_errors:
        return _result(False, "postponed constructor mismatch", ctor_errors, rec_errors)
    if rec_errors:
        return _result(False, "postponed recursor mismatch", ctor_errors, rec_errors)
    return _result(True, None, ctor_errors, rec_errors)


_LIVE_OLEAN_INSPECTOR_LEAN = r'''
import Lean

open Lean

def exprHasOpenTerm (e : Expr) : Bool :=
  e.hasFVar || e.hasMVar || e.hasLooseBVars

def constantHasOpenExpr (ci : ConstantInfo) : Bool :=
  exprHasOpenTerm ci.type ||
  (match ci.value? (allowOpaque := true) with
   | some v => exprHasOpenTerm v
   | none => false) ||
  (match ci with
   | .recInfo v => v.rules.any (fun r => exprHasOpenTerm r.rhs)
   | _ => false)

def ciKindStr : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "defn"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def ciMetaTag : ConstantInfo → String
  | .inductInfo v =>
    let allS := String.intercalate "," (v.all.map Name.toString)
    let ctorS := String.intercalate "," (v.ctors.map Name.toString)
    s!"ind:{v.numParams}:{v.numIndices}:{v.numNested}:{v.isRec}:{v.isReflexive}:{v.isUnsafe}:{allS}:{ctorS}"
  | .ctorInfo v =>
    s!"ctor:{v.induct}:{v.cidx}:{v.numParams}:{v.numFields}:{v.isUnsafe}"
  | .recInfo v =>
    let allS := String.intercalate "," (v.all.map Name.toString)
    s!"rec:{v.numParams}:{v.numIndices}:{v.numMotives}:{v.numMinors}:{v.k}:{v.isUnsafe}:{allS}:{v.rules.length}"
  | _ => ""

def isCodegenUnsafeRec (lookup : Name → Option ConstantInfo) (n : Name) (ci : ConstantInfo) : Bool :=
  if ci.isUnsafe || !ci.isPartial then false
  else match n with
    | .str parent "_unsafe_rec" =>
      match lookup parent with
      | some parentCi => !parentCi.isUnsafe && !parentCi.isPartial
      | none => false
    | _ => false

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

/-- Unchecked kernel declaration for a non-inductive-block constant (dependency context only). -/
def declOfNonBlock? : ConstantInfo → Option Declaration
  | .defnInfo v => some (.defnDecl v)
  | .thmInfo v => some (.thmDecl v)
  | .axiomInfo v => some (.axiomDecl v)
  | .opaqueInfo v => some (.opaqueDecl v)
  | _ => none

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
  let kernelReplay := (j.getObjValAs? Bool "kernel_replay_inductives").toOption.getD true
  let rejectUnsafePartial := (j.getObjValAs? Bool "reject_unsafe_partial").toOption.getD false
  let fingerprintOutPath? := (j.getObjValAs? String "fingerprint_out_path").toOption
  -- Optional `[[module, path]]` overrides used ONLY by red-team tests to feed synthetic
  -- forged `.olean` fixtures through the exact same audit pipeline.
  let overridePairs := (j.getObjValAs? (Array (Array String)) "olean_overrides").toOption.getD #[]
  let overrides : Std.HashMap Name String := overridePairs.foldl (fun acc pr =>
    if pr.size == 2 then acc.insert pr[0]!.toName pr[1]! else acc) {}
  let sysroot ← Lean.findSysroot
  let leanPathStr := (← IO.getEnv "LEAN_PATH").getD ""
  let sp := System.SearchPath.parse leanPathStr
  initSearchPath sysroot sp
  -- Toolchain-owned modules are identified by their `.olean` living under the toolchain
  -- sysroot (never by name prefix: a repo module named `Lean.Evil` must still be audited).
  let sysLibPrefix := (sysroot / "lib" / "lean").toString ++ "/"
  let baseEnv ← importModules #[{ module := `Init }, { module := `Std }, { module := `Lean }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let baseEnv := baseEnv.setExporting false
  let exactSet : NameSet := exactMods.foldl (fun s m => s.insert m.toName) {}
  let allowedAxSet : NameSet := allowedAxioms.foldl (fun s a => s.insert a.toName) {}
  let mut queue : List Name := (importMods.map String.toName).toList
  let mut visitedMods : NameSet := {}
  let mut loadedMods : NameSet := {}
  let mut stdlibSkipped : Nat := 0
  let mut modDatas : Array (Name × ModuleData) := #[]
  let mut constMap : Std.HashMap Name ConstantInfo := {}
  let mut constOrigin : Std.HashMap Name Name := {}
  let mut viols : Array Json := #[]
  let mut siblingEqDedup : Nat := 0
  while !queue.isEmpty do
    let m := queue.head!
    queue := queue.tail!
    if !visitedMods.contains m then
      visitedMods := visitedMods.insert m
      let overridePath? := overrides[m]?
      let oleanPath ← match overridePath? with
        | some op => pure (System.FilePath.mk op)
        | none => Lean.findOLean m
      if overridePath?.isNone && oleanPath.toString.startsWith sysLibPrefix then
        stdlibSkipped := stdlibSkipped + 1
      else
        loadedMods := loadedMods.insert m
        let mut partPaths : Array System.FilePath := #[oleanPath]
        if overridePath?.isNone then
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
            | none =>
              constMap := constMap.insert ci.name ci
              constOrigin := constOrigin.insert ci.name m
            | some existing =>
              siblingEqDedup := siblingEqDedup + 1
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
              if (existing.value? true).isNone && (ci.value? true).isSome then
                constMap := constMap.insert ci.name ci
          for imp in mdata.imports do
            if !visitedMods.contains imp.module then
              queue := imp.module :: queue
  let lookupConst (n : Name) : Option ConstantInfo :=
    match constMap[n]? with
    | some ci => some ci
    | none => baseEnv.find? n
  let isTargetMod (modName : Name) : Bool :=
    if exactMods.isEmpty then true else exactSet.contains modName
  let mut checkedModSet : NameSet := {}
  let mut declsChecked : Nat := 0
  let mut inductsChecked : Nat := 0
  let mut ctorsChecked : Nat := 0
  let mut recsChecked : Nat := 0
  let mut roots : Array Name := #[]
  let fpHandle? : Option IO.FS.Handle ← match fingerprintOutPath? with
    | some p => pure (some (← IO.FS.Handle.mk (System.FilePath.mk p) .write))
    | none => pure none
  for (modName, data) in modDatas do
    if isTargetMod modName then
      checkedModSet := checkedModSet.insert modName
      for idx in [:data.constants.size] do
        let ci := data.constants[idx]!
        let kName := data.constNames[idx]!
        declsChecked := declsChecked + 1
        roots := roots.push ci.name
        if let some fh := fpHandle? then
          let lvlStr := String.intercalate "," (ci.levelParams.map Name.toString)
          let (hasVal, valHash) := match ci.value? (allowOpaque := true) with
            | some v => ("1", toString v.hash)
            | none => ("0", "0")
          fh.putStrLn s!"{modName}\t{ci.name}\t{ciKindStr ci}\t{lvlStr}\t{ci.type.hash}\t{hasVal}\t{valHash}\t{ciMetaTag ci}"
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
        | .ctorInfo cVal =>
          ctorsChecked := ctorsChecked + 1
          match lookupConst cVal.induct with
          | some (.inductInfo parent) =>
            if !parent.ctors.contains cVal.name then
              viols := viols.push (mkViol "dangling_ctor_not_listed_in_induct" cVal.name.toString cVal.induct.toString)
          | _ =>
            viols := viols.push (mkViol "dangling_ctor_not_listed_in_induct" cVal.name.toString cVal.induct.toString)
        | .recInfo rVal =>
          recsChecked := recsChecked + 1
          if rVal.all.isEmpty then
            viols := viols.push (mkViol "recursor_mismatch" rVal.name.toString "empty_rec_all")
          for peerName in rVal.all do
            match lookupConst peerName with
            | some (.inductInfo parent) =>
              if parent.all != rVal.all || parent.numParams != rVal.numParams then
                viols := viols.push (mkViol "recursor_mismatch" rVal.name.toString peerName.toString)
            | _ =>
              viols := viols.push (mkViol "recursor_mismatch" rVal.name.toString peerName.toString)
        | _ => pure ()
  if let some fh := fpHandle? then
    fh.flush
  -- Every requested exact module must actually have been loaded and audited.
  for m in exactMods do
    if !checkedModSet.contains m.toName then
      viols := viols.push (mkViol "uncovered_registered_module" m "exact_module_not_audited")
  -- lean4#16717 `checkPostponedInductives` + `checkPostponedConstructors` + `checkPostponedRecursors`:
  -- re-send every non-stdlib inductive block to the REAL kernel (dependencies added unchecked as
  -- context), then sweep EVERY `.inductInfo`, `.ctorInfo`, and `.recInfo` in target modules
  -- directly against `kenv.find?` (catching cross-module forged `all`, mutual recursors `rec_1`,
  -- and dangling recursors).
  let tk0 ← IO.monoMsNow
  let mut kBlocksChecked : Nat := 0
  let mut kBlocksUnresolved : Nat := 0
  let mut kUncheckedAdded : Nat := 0
  if kernelReplay then
    let mut kenv := baseEnv.toKernelEnv
    for (_, ci) in constMap.toList do
      match declOfNonBlock? ci with
      | some d =>
        match kenv.addDeclWithoutChecking d with
        | .ok e => kenv := e; kUncheckedAdded := kUncheckedAdded + 1
        | .error _ => viols := viols.push (mkViol "missing_dependency_decl" ci.name.toString "kernel_context_add_failed")
      | none => pure ()
    -- Group inductives into blocks keyed by the head of their (stored) `all` list.
    let mut blockHeads : NameSet := {}
    let mut blocks : Array (Name × InductiveVal) := #[]
    for (_, ci) in constMap.toList do
      match ci with
      | .inductInfo ind =>
        let head := ind.all.headD ind.name
        if !blockHeads.contains head then
          blockHeads := blockHeads.insert head
          blocks := blocks.push (head, ind)
      | _ => pure ()
    let mut pending := blocks.toList
    let mut progress := true
    while progress && !pending.isEmpty do
      progress := false
      let mut deferred : List (Name × InductiveVal) := []
      for (head, ind) in pending do
        let mut types : List InductiveType := []
        let mut wellFormed := true
        for n in ind.all do
          match constMap[n]? with
          | some (.inductInfo peer) =>
            let mut ctors : List Constructor := []
            for c in peer.ctors do
              match constMap[c]? with
              | some (.ctorInfo cv) => ctors := ctors ++ [{ name := c, type := cv.type }]
              | _ => wellFormed := false
            types := types ++ [{ name := n, type := peer.type, ctors := ctors }]
          | _ => wellFormed := false
        if !wellFormed then
          progress := true
          continue
        let decl := Declaration.inductDecl ind.levelParams ind.numParams types ind.isUnsafe
        match kenv.addDeclCore 0 0 decl (cancelTk? := none) with
        | .error (.unknownConstant _ _) =>
          deferred := (head, ind) :: deferred
        | .error ex =>
          progress := true
          let anyPeerTgt := ind.all.any fun p =>
            match constOrigin[p]? with | some om => isTargetMod om | none => false
          if anyPeerTgt then
            let msg := (← (ex.toMessageData {}).toString)
            viols := viols.push (mkViol "mutual_metadata_mismatch" head.toString s!"kernel_rejected_stored_block: {msg.take 200}")
        | .ok e =>
          progress := true
          kenv := e
          kBlocksChecked := kBlocksChecked + 1
      pending := deferred
    for (head, ind) in pending do
      kBlocksUnresolved := kBlocksUnresolved + 1
      let anyPeerTgt := ind.all.any fun p =>
        match constOrigin[p]? with | some om => isTargetMod om | none => false
      if anyPeerTgt then
        viols := viols.push (mkViol "missing_dependency_decl" head.toString "kernel_replay_unresolved_dependency")
    -- Unconditional post-replay sweep over EVERY target inductive, constructor, and recursor!
    for (modName, data) in modDatas do
      if isTargetMod modName then
        for ci in data.constants do
          match ci with
          | .inductInfo st =>
            match kenv.find? st.name with
            | some (.inductInfo k) =>
              if k.numIndices != st.numIndices then
                viols := viols.push (mkViol "indices_mismatch" st.name.toString s!"kernel={k.numIndices} stored={st.numIndices}")
              if k.isRec != st.isRec then
                viols := viols.push (mkViol "is_rec_mismatch" st.name.toString s!"kernel={k.isRec} stored={st.isRec}")
              if k.all != st.all || k.ctors != st.ctors || k.numParams != st.numParams ||
                  k.levelParams != st.levelParams || k.isReflexive != st.isReflexive ||
                  k.type != st.type || k.numNested != st.numNested || k.isUnsafe != st.isUnsafe then
                viols := viols.push (mkViol "mutual_metadata_mismatch" st.name.toString "kernel_post_replay_diff")
            | _ =>
              let code := if !st.all.contains st.name then "self_not_in_all" else "mutual_metadata_mismatch"
              viols := viols.push (mkViol code st.name.toString "not_replayed_in_kernel")
          | .ctorInfo sc =>
            match kenv.find? sc.name with
            | some (.ctorInfo kc) =>
              if kc.cidx != sc.cidx then
                viols := viols.push (mkViol "ctor_cidx_mismatch" sc.name.toString "kernel_post_replay_cidx")
              else if !(kc == sc) then
                viols := viols.push (mkViol "ctor_induct_mismatch" sc.name.toString "kernel_post_replay_ctor_diff")
            | _ =>
              viols := viols.push (mkViol "dangling_ctor_not_listed_in_induct" sc.name.toString "ctor_not_in_kernel")
          | .recInfo sr =>
            match kenv.find? sr.name with
            | some (.recInfo kr) =>
              if !(kr == sr) then
                viols := viols.push (mkViol "recursor_mismatch" sr.name.toString "kernel_post_replay_rec_diff")
            | _ =>
              viols := viols.push (mkViol "recursor_mismatch" sr.name.toString "rec_not_in_kernel")
          | _ => pure ()
  let tk1 ← IO.monoMsNow
  -- Full transitive constant-graph walk across all loaded + stdlib imports for `--exact-modules`.
  let mut pendingNames : List Name := roots.toList
  let mut visited : NameSet := {}
  let mut axiomsReached : NameSet := {}
  let mut unsafePartialReached : NameSet := {}
  while !pendingNames.isEmpty do
    let n := pendingNames.head!
    pendingNames := pendingNames.tail!
    if !visited.contains n then
      visited := visited.insert n
      match lookupConst n with
      | none =>
        viols := viols.push (mkViol "missing_dependency_decl" n.toString "not_found")
      | some ci =>
        if constantHasOpenExpr ci then
          viols := viols.push (mkViol "disallowed_transitive_axiom" n.toString "open_expr_in_constant")
        if (ci.isUnsafe || ci.isPartial) && !isCodegenUnsafeRec lookupConst n ci then
          unsafePartialReached := unsafePartialReached.insert n
          if rejectUnsafePartial then
            viols := viols.push (mkViol "disallowed_transitive_axiom" n.toString "unsafe_or_partial_decl")
        if ci.isAxiom then
          axiomsReached := axiomsReached.insert n
          if !allowedAxSet.contains n then
            viols := viols.push (mkViol "disallowed_transitive_axiom" n.toString "unapproved")
        let edges := declarationEdges ci
        for e in edges do
          if !visited.contains e then
            pendingNames := e :: pendingNames
  let t1 ← IO.monoMsNow
  let sortedAxioms := (axiomsReached.toArray.qsort Name.lt).map Name.toString
  let sortedUnsafe := (unsafePartialReached.toArray.qsort Name.lt).map Name.toString
  let out := Json.mkObj [
    ("modules_checked", toJson checkedModSet.size),
    ("loaded_olean_count", toJson loadedMods.size),
    ("stdlib_modules_skipped", toJson stdlibSkipped),
    ("sibling_eq_dedup_count", toJson siblingEqDedup),
    ("declarations_checked", toJson declsChecked),
    ("inductives_checked", toJson inductsChecked),
    ("ctors_checked", toJson ctorsChecked),
    ("recursors_checked", toJson recsChecked),
    ("kernel_replay_enabled", toJson kernelReplay),
    ("kernel_blocks_checked", toJson kBlocksChecked),
    ("kernel_blocks_unresolved", toJson kBlocksUnresolved),
    ("kernel_context_decls_added_unchecked", toJson kUncheckedAdded),
    ("kernel_replay_elapsed_ms", toJson (tk1 - tk0)),
    ("transitive_visited", toJson visited.size),
    ("axioms_reached", toJson sortedAxioms),
    ("unsafe_partial_reached_count", toJson sortedUnsafe.size),
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
    timeout_sec: int = 600,
    kernel_replay_inductives: bool = True,
    olean_overrides: dict[str, str] | None = None,
    reject_unsafe_partial: bool = False,
    export_fingerprints: bool = False,
) -> dict[str, Any]:
    """Run live read-only `.olean` inspection under `anneal-lean-run --mode file`.

    With `kernel_replay_inductives` (default), every non-stdlib inductive block is re-sent
    to the real Lean kernel and EVERY target inductive/constructor/recursor is checked
    against `kenv.find?` (`lean4#16717`). With `export_fingerprints=True`, emits per-target
    declaration fingerprints for cross-shard duplicate consistency reconciliation.
    """
    runner = _find_anneal_lean_run(repo_root)
    t0 = time.perf_counter()
    with tempfile.TemporaryDirectory(prefix="anneal-olean-insp-") as tmp_str:
        tmp = Path(tmp_str)
        lean_script = tmp / "inspect_oleans.lean"
        req_json = tmp / "req.json"
        fp_path = tmp / "fingerprints.tsv"
        lean_script.write_text(_LIVE_OLEAN_INSPECTOR_LEAN, encoding="utf-8")
        req_payload: dict[str, Any] = {
            "import_modules": list(import_modules),
            "exact_modules": list(exact_modules) if exact_modules is not None else [],
            "permitted_axioms": (
                list(permitted_axioms)
                if permitted_axioms is not None
                else sorted(PERMITTED_FOUNDATIONAL_AXIOMS)
            ),
            "kernel_replay_inductives": bool(kernel_replay_inductives),
            "reject_unsafe_partial": bool(reject_unsafe_partial),
            "olean_overrides": [
                [mod, str(path)] for mod, path in sorted((olean_overrides or {}).items())
            ],
        }
        if export_fingerprints:
            req_payload["fingerprint_out_path"] = str(fp_path)
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
        if export_fingerprints and fp_path.is_file():
            fps: list[tuple[str, str, str, str, str, bool, str, str]] = []
            with fp_path.open("r", encoding="utf-8") as fh:
                for raw in fh:
                    raw = raw.rstrip("\n")
                    if not raw:
                        continue
                    parts = raw.split("\t")
                    if len(parts) == 8:
                        fps.append(
                            (
                                parts[0],
                                parts[1],
                                parts[2],
                                parts[3],
                                parts[4],
                                parts[5] == "1",
                                parts[6],
                                parts[7],
                            )
                        )
            result["declaration_fingerprints"] = fps
        return result


def reconcile_cross_shard_fingerprints(
    shard_fingerprints: dict[str, list[tuple[str, str, str, str, str, bool, str, str]]],
) -> dict[str, Any]:
    """Global cross-shard duplicate consistency reconciliation (closes Pillar 2 §3.2).

    Each fingerprint tuple is:
    `(mod_name, decl_name, kind, level_params, type_hash, has_val, val_hash, meta_tag)`.
    Compares declarations of the same `decl_name` across ALL shards using the exact same
    compatibility predicate as monolithic `.olean` loading (`levelParams`, `type`, `value?`,
    and inductive/ctor/recursor metadata).
    """
    by_decl: dict[str, list[tuple[str, tuple[str, str, str, str, str, bool, str, str]]]] = {}
    total_records = 0
    for shard_name, recs in shard_fingerprints.items():
        for rec in recs:
            total_records += 1
            by_decl.setdefault(rec[1], []).append((shard_name, rec))

    def _compatible(
        a: tuple[str, str, str, str, str, bool, str, str],
        b: tuple[str, str, str, str, str, bool, str, str],
    ) -> bool:
        # (mod, name, kind, lvls, type_h, has_val, val_h, meta_tag)
        if a[3] != b[3]:  # levelParams
            return False
        if a[2] == "thm" and b[2] == "thm":
            return a[4] == b[4]  # alpha-equivalent type hash
        if a[2] != b[2] or a[4] != b[4] or a[7] != b[7]:
            return False
        return (a[6] == b[6]) or (not a[5]) or (not b[5])

    violations: list[dict[str, str]] = []
    cross_shard_only: list[dict[str, str]] = []
    conflicting_subjects: set[str] = set()
    duplicate_decl_count = 0
    for decl_name, entries in sorted(by_decl.items()):
        if len(entries) < 2:
            continue
        duplicate_decl_count += 1
        # Check compatibility against canonical first entry (and all valued entries).
        first_shard, first_rec = entries[0]
        canonical_val_rec = first_rec if first_rec[5] else None
        canonical_val_shard = first_shard if first_rec[5] else None
        for shard_name, rec in entries[1:]:
            ref_rec = canonical_val_rec if (canonical_val_rec is not None and rec[5]) else first_rec
            ref_shard = canonical_val_shard if (canonical_val_rec is not None and rec[5]) else first_shard
            if not _compatible(ref_rec, rec):
                conflicting_subjects.add(decl_name)
                viol = {
                    "code": "cross_shard_duplicate_conflict",
                    "subject": decl_name,
                    "detail": f"conflict:{ref_shard}:{ref_rec[0]}!={shard_name}:{rec[0]}",
                }
                violations.append(viol)
                if ref_shard != shard_name:
                    cross_shard_only.append(viol)
            if canonical_val_rec is None and rec[5]:
                canonical_val_rec = rec
                canonical_val_shard = shard_name

    return {
        "ok": len(violations) == 0,
        "total_fingerprint_records": total_records,
        "unique_declarations": len(by_decl),
        "duplicate_declarations_seen": duplicate_decl_count,
        "conflicting_subjects": sorted(conflicting_subjects),
        "violations": violations,
        "cross_shard_only_violations": cross_shard_only,
    }


_OLEAN_FORGER_LEAN = r'''
import Lean

open Lean

/-- Red-team fixture generator: rewrite or append a stored `ConstantInfo` inside a copy of
    a real compiled `.olean`, emulating a malicious/buggy `.olean` producer (`lean4#16717`). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [inPath, outPath, modStr, targetStr, mutation] =>
    let parts ← readModuleDataParts #[System.FilePath.mk inPath]
    let some (data, _) := parts[0]? | return 3
    let target := targetStr.toName
    let mut hit := false
    let mut constNames : Array Name := data.constNames
    let mut consts : Array ConstantInfo := #[]
    let mut extraRec : Option (Name × ConstantInfo) := none
    for ci in data.constants do
      let mut ci' := ci
      match ci with
      | .inductInfo v =>
        if v.name == target then
          match mutation with
          | "flip_is_rec" => ci' := .inductInfo { v with isRec := !v.isRec }; hit := true
          | "bump_num_indices" => ci' := .inductInfo { v with numIndices := v.numIndices + 1 }; hit := true
          | "drop_self_from_all" =>
            ci' := .inductInfo { v with all := v.all.filter (· != v.name) ++ [`Nat] }; hit := true
          | "cross_mod_all_hijack" =>
            ci' := .inductInfo { v with all := [`Anneal.SpecBoundaryGuards.SpecBoundaryGuardClass, v.name] }; hit := true
          | "flip_is_reflexive" => ci' := .inductInfo { v with isReflexive := !v.isReflexive }; hit := true
          | "forge_open_expr" => ci' := .inductInfo { v with type := .bvar 0 }; hit := true
          | _ => pure ()
      | .recInfo v =>
        if v.name == target ++ `rec then
          match mutation with
          | "flip_rec_k" => ci' := .recInfo { v with k := !v.k }; hit := true
          | "append_dangling_rec" =>
            let forgedName := target ++ `rec_forged_1
            extraRec := some (forgedName, .recInfo { v with name := forgedName, all := [`Ghost.NonExistent] })
            hit := true
          | _ => pure ()
      | .ctorInfo v =>
        if v.induct == target && v.cidx == 0 && mutation == "bump_ctor_fields" then
          ci' := .ctorInfo { v with numFields := v.numFields + 1 }; hit := true
      | .defnInfo v =>
        if v.name == target && mutation == "forge_open_expr" then
          ci' := .defnInfo { v with value := .bvar 0 }; hit := true
      | .thmInfo v =>
        if v.name == target && mutation == "forge_open_expr" then
          ci' := .thmInfo { v with value := .bvar 0 }; hit := true
      | _ => pure ()
      consts := consts.push ci'
    if let some (fn, fci) := extraRec then
      constNames := constNames.push fn
      consts := consts.push fci
    if !hit then
      IO.eprintln s!"forger: no constant matched {targetStr} / {mutation}"
      return 4
    saveModuleData (System.FilePath.mk outPath) modStr.toName { data with constNames := constNames, constants := consts }
    return 0
  | _ =>
    IO.eprintln "usage: forge <in.olean> <out.olean> <module> <inductive> <mutation>"
    return 2
'''

FORGE_MUTATIONS: tuple[str, ...] = (
    "flip_is_rec",
    "bump_num_indices",
    "drop_self_from_all",
    "cross_mod_all_hijack",
    "flip_is_reflexive",
    "flip_rec_k",
    "append_dangling_rec",
    "bump_ctor_fields",
    "forge_open_expr",
)


def forge_olean_fixture(
    repo_root: Path,
    module: str,
    inductive: str,
    mutation: str,
    out_path: Path,
    timeout_sec: int = 300,
) -> None:
    """Write a synthetic forged copy of `module`'s compiled `.olean` to `out_path`."""
    if mutation not in FORGE_MUTATIONS:
        raise ValueError(f"unknown forge mutation {mutation!r}")
    runner = _find_anneal_lean_run(repo_root)
    src_olean = repo_root / ".lake" / "build" / "lib" / "lean" / (module.replace(".", "/") + ".olean")
    if not src_olean.is_file():
        raise FileNotFoundError(f"compiled .olean not found for {module}: {src_olean}")
    with tempfile.TemporaryDirectory(prefix="anneal-olean-forge-") as tmp_str:
        script = Path(tmp_str) / "forge_olean.lean"
        script.write_text(_OLEAN_FORGER_LEAN, encoding="utf-8")
        proc = subprocess.run(
            [runner, "--mode", "file", "--", "lake", "env", "lean", "--run", str(script),
             str(src_olean), str(out_path), module, inductive, mutation],
            cwd=str(repo_root),
            capture_output=True,
            text=True,
            timeout=timeout_sec,
            check=False,
        )
        if proc.returncode != 0:
            raise RuntimeError(
                f"olean forger failed (rc={proc.returncode}): {proc.stderr.strip()} {proc.stdout.strip()}"
            )


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


def load_lake_lean_libs(repo_root: Path) -> list[dict[str, Any]]:
    """Parse `[[lean_lib]]` declarations (name, srcDir, roots, globs) from `lakefile.toml`."""
    lakefile = repo_root / "lakefile.toml"
    if not lakefile.is_file():
        return []
    data = tomllib.loads(lakefile.read_text(encoding="utf-8"))
    libs: list[dict[str, Any]] = []
    for lib in data.get("lean_lib", []):
        name = str(lib["name"])
        roots = [str(r) for r in lib.get("roots", [name])]
        globs = [str(g) for g in lib.get("globs", roots)]
        libs.append(
            {
                "name": name,
                "src_dir": str(lib.get("srcDir", ".")).strip("/") or ".",
                "roots": roots,
                "globs": globs,
            }
        )
    return libs


def _name_is_prefix(prefix: str, mod: str) -> bool:
    return mod == prefix or mod.startswith(prefix + ".")


def _lake_glob_matches(glob: str, mod: str) -> bool:
    """Lake `Glob` semantics: `M` (one), `M.*` (strict submodules), `M.+` (M and submodules)."""
    if glob.endswith(".*"):
        base = glob[:-2]
        return mod.startswith(base + ".")
    if glob.endswith(".+"):
        return _name_is_prefix(glob[:-2], mod)
    return mod == glob


def lake_is_buildable_module(lib: dict[str, Any], mod: str) -> bool:
    """Mirror Lake `LeanLibConfig.isBuildableModule` (Lake/Config/LeanLibConfig.lean)."""
    globs = lib["globs"]
    if any(_lake_glob_matches(g, mod) for g in globs):
        return True
    return any(
        _name_is_prefix(root, mod) and any(_lake_glob_matches(g, root) for g in globs)
        for root in lib["roots"]
    )


def _walk_lean_files(base: Path) -> list[Path]:
    out: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(base):
        dirnames[:] = sorted(d for d in dirnames if not d.startswith(".") and d != "build")
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                out.append(Path(dirpath) / fn)
    return out


def _parse_lean_header_imports(path: Path) -> list[str]:
    """Fast header-only `import` parser.

    Nesting-aware for `/- ... -/` block comments and `--` line comments; stops at the first
    token that is not part of the Lean module header (`module`, `prelude`, `import`
    [`public`|`meta`|`all`] `Mod`).
    """
    imports: list[str] = []
    depth = 0
    expecting_mod = False
    try:
        fh = path.open(encoding="utf-8", errors="replace")
    except OSError:
        return imports
    with fh:
        for raw in fh:
            chars: list[str] = []
            i = 0
            n = len(raw)
            while i < n:
                if depth:
                    if raw.startswith("/-", i):
                        depth += 1
                        i += 2
                    elif raw.startswith("-/", i):
                        depth -= 1
                        i += 2
                    else:
                        i += 1
                elif raw.startswith("/-", i):
                    depth = 1
                    i += 2
                elif raw.startswith("--", i):
                    break
                else:
                    chars.append(raw[i])
                    i += 1
            for word in "".join(chars).split():
                if expecting_mod:
                    if word in ("public", "meta", "all", "private"):
                        continue
                    imports.append(word.strip("«»"))
                    expecting_mod = False
                elif word in ("module", "prelude"):
                    continue
                elif word == "import":
                    expecting_mod = True
                else:
                    return imports
    return imports


def discover_lake_sources(repo_root: Path) -> dict[str, Any]:
    """Discover every on-disk `.lean` file under each `lean_lib` `srcDir` and its Lake owner.

    Returns `{"modules": {mod: [entries...]}, "libs": [...]}` where every entry records
    the file path, srcDir, and the list of libs for which the module is buildable.
    """
    libs = load_lake_lean_libs(repo_root)
    by_src: dict[str, list[dict[str, Any]]] = {}
    for lib in libs:
        by_src.setdefault(lib["src_dir"], []).append(lib)
    modules: dict[str, list[dict[str, Any]]] = {}
    for src_dir in sorted(by_src):
        base = repo_root / src_dir
        if not base.is_dir():
            continue
        for fp in _walk_lean_files(base):
            mod = _lean_path_to_module(fp.relative_to(base))
            owners = sorted(lib["name"] for lib in by_src[src_dir] if lake_is_buildable_module(lib, mod))
            modules.setdefault(mod, []).append(
                {
                    "rel_path": fp.relative_to(repo_root).as_posix(),
                    "src_dir": src_dir,
                    "owners": owners,
                }
            )
    return {"modules": modules, "libs": libs}


def lake_default_import_closure(repo_root: Path, lake: dict[str, Any] | None = None) -> set[str]:
    """Modules reachable by `import` from every `lean_lib` root (what `lake build <lib>` builds)."""
    lake = lake if lake is not None else discover_lake_sources(repo_root)
    path_of: dict[str, Path] = {}
    for mod, entries in lake["modules"].items():
        owned = [e for e in entries if e["owners"]]
        if owned:
            path_of[mod] = repo_root / owned[0]["rel_path"]
    seen: set[str] = set()
    stack = [root for lib in lake["libs"] for root in lib["roots"]]
    while stack:
        mod = stack.pop()
        if mod in seen or mod not in path_of:
            continue
        seen.add(mod)
        stack.extend(_parse_lean_header_imports(path_of[mod]))
    return seen


def discover_repo_modules(repo_root: Path) -> dict[str, dict[str, Any]]:
    """Fast discovery of all Lean modules: every `lean_lib` srcDir (Lake-owned or orphaned) plus
    the standalone `examples/` and `tests/` harness files."""
    modules: dict[str, dict[str, Any]] = {}
    olean_root = repo_root / ".lake" / "build" / "lib" / "lean"

    def add_mod(mod_name: str, rel_posix: str, root_group: str, lake_owners: list[str] | None) -> None:
        olean_path = olean_root / (mod_name.replace(".", "/") + ".olean")
        modules[mod_name] = {
            "module": mod_name,
            "rel_path": rel_posix,
            "root_group": root_group,
            "has_olean": olean_path.is_file(),
            "lake_owners": lake_owners,
        }

    lake = discover_lake_sources(repo_root)
    for mod, entries in sorted(lake["modules"].items()):
        e = entries[0]
        group = "trusted" if e["src_dir"].startswith("trusted") else (
            "minirust" if e["src_dir"].startswith("minirust") else "theory"
        )
        add_mod(mod, e["rel_path"], group, sorted({o for x in entries for o in x["owners"]}))

    # Standalone examples/ and tests/ harness files (compiled per-file via `lake env lean`).
    for top, group in (("examples", "examples"), ("tests", "tests")):
        top_dir = repo_root / top
        if not top_dir.is_dir():
            continue
        for sub in ("", "mir", "pass", "refinement", "step-result"):
            d = top_dir / sub if sub else top_dir
            if not d.is_dir():
                continue
            for fn in sorted(os.listdir(d)):
                if not fn.endswith(".lean") or not (d / fn).is_file():
                    continue
                stem = fn[: -len(".lean")]
                mod = stem
                if group == "tests" and sub == "" and stem == "Smoke":
                    mod = "SmokeTest"
                if mod in modules:
                    mod = f"{'Examples' if group == 'examples' else 'Tests'}.{mod}"
                add_mod(mod, (d / fn).relative_to(repo_root).as_posix(), group, None)

    return dict(sorted(modules.items()))


def find_module_name_collisions(names: list[str]) -> list[dict[str, str]]:
    """Case-folding collisions (`Anneal.Foo` vs `Anneal.foo`) that alias one path on
    case-insensitive filesystems (Python `casefold` is a superset of Lean's ASCII fold)."""
    groups: dict[str, set[str]] = {}
    for nm in names:
        groups.setdefault(nm.casefold(), set()).add(nm)
    out: list[dict[str, str]] = []
    for key in sorted(groups):
        if len(groups[key]) > 1:
            for nm in sorted(groups[key]):
                out.append({"code": "module_name_collision", "subject": nm})
    return out


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
        or module_name == "MiniRustSpec"
        or module_name.startswith("MiniRustSpec.")
    ):
        return "Anneal.RustcMir"
    return "Anneal.Core"


def plan_subsystem_shards(
    repo_root: Path,
    discovered: dict[str, dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Build the deterministic 8-shard subsystem partition covering all discovered modules."""
    discovered = discovered if discovered is not None else discover_repo_modules(repo_root)
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

    violations.extend(
        find_module_name_collisions(sorted(set(registered_modules) | set(on_disk_modules)))
    )
    return violations


def run_orphan_only_gate(
    repo_root: Path,
    registered_modules: list[str] | None = None,
    shards: list[list[str]] | None = None,
) -> dict[str, Any]:
    """Run the `< 0.25s` `--orphan-only` completeness and exact-partition gate.

    `registered` defaults to the modules Lake can actually build (`isBuildableModule` of
    some `[[lean_lib]]` in `lakefile.toml`, plus the standalone examples/tests harness files);
    `on_disk` is EVERY `.lean` file under every `lean_lib` srcDir, so a `.lean` file that no
    library owns (e.g. `theory/Rogue.lean`) is reported as `unregistered_on_disk_orphan`.
    Modules that Lake owns but that are NOT in the default import closure of any library
    root are reported as advisory telemetry (`outside_lib_root_import_closure`).
    """
    t0 = time.perf_counter()
    lake = discover_lake_sources(repo_root)
    discovered = discover_repo_modules(repo_root)
    on_disk = sorted(discovered.keys())
    lake_registered = sorted(
        m for m, info in discovered.items()
        if info["lake_owners"] is None or len(info["lake_owners"]) > 0
    )
    duplicate_paths = sorted(m for m, entries in lake["modules"].items() if len(entries) > 1)
    if registered_modules is None and shards is None:
        plan = plan_subsystem_shards(repo_root, discovered=discovered)
        registered = lake_registered
        shard_lists = [plan["shards"][name] for name in SUBSYSTEM_SHARD_NAMES]
    elif registered_modules is not None and shards is None:
        registered = list(registered_modules)
        shard_lists = [registered] if registered else []
    elif registered_modules is None and shards is not None:
        registered = lake_registered
        shard_lists = shards
    else:
        registered = list(registered_modules)
        shard_lists = shards

    violations = check_shard_partition(registered, on_disk, shard_lists)
    for mod in duplicate_paths:
        violations.append({"code": "module_name_collision", "subject": mod})
    closure = lake_default_import_closure(repo_root, lake)
    outside_closure = sorted(
        m for m, info in discovered.items() if info["lake_owners"] and m not in closure
    )
    elapsed_sec = round(time.perf_counter() - t0, 5)
    return {
        "ok": len(violations) == 0,
        "elapsed_sec": elapsed_sec,
        "under_250ms": elapsed_sec < 0.25,
        "on_disk_count": len(on_disk),
        "registered_count": len(registered),
        "lake_lib_count": len(lake["libs"]),
        "shard_count": len(shard_lists),
        "violations": violations,
        "outside_lib_root_import_closure": outside_closure,
        "outside_lib_root_import_closure_count": len(outside_closure),
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
    discovered = discover_repo_modules(repo_root)
    plan = plan_subsystem_shards(repo_root, discovered=discovered)
    compiled_shards: dict[str, list[str]] = plan["compiled_olean_shards"]
    # Benchmark honesty: Lake-owned modules with NO compiled `.olean` are NOT audited by
    # either the monolithic or the sharded run; surface them instead of silently dropping.
    uncompiled = sorted(
        m for m, info in discovered.items() if info["lake_owners"] and not info["has_olean"]
    )
    all_compiled: list[str] = sorted(
        m for mods in compiled_shards.values() for m in mods
    )

    # 1. Monolithic live `.olean` audit (all compiled modules in one Lean invocation)
    mono_res = inspect_live_oleans(
        repo_root=repo_root,
        import_modules=all_compiled,
        exact_modules=all_compiled,
    )

    # 2. Parallel `--exact-modules` sharded live `.olean` audit with fingerprint export
    workers = max_workers if max_workers is not None else min(len(compiled_shards), 6)
    workers = max(1, workers)
    t0 = time.perf_counter()
    per_shard: dict[str, dict[str, Any]] = {}
    shard_fps: dict[str, list[tuple[str, str, str, str, str, bool, str, str]]] = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        future_map = {
            pool.submit(
                inspect_live_oleans,
                repo_root,
                mods,
                mods,
                export_fingerprints=True,
            ): shard_name
            for shard_name, mods in sorted(compiled_shards.items())
        }
        for fut in concurrent.futures.as_completed(future_map):
            shard_name = future_map[fut]
            res = fut.result()
            shard_fps[shard_name] = res.pop("declaration_fingerprints", [])
            per_shard[shard_name] = res
    recon = reconcile_cross_shard_fingerprints(shard_fps)
    sharded_wall_sec = round(time.perf_counter() - t0, 4)

    union_axioms = sorted(
        {a for res in per_shard.values() for a in res.get("axioms_reached", [])}
    )
    sharded_violations = [
        {"shard": name, **v}
        for name in sorted(per_shard)
        for v in per_shard[name].get("violations", [])
    ]
    sharded_reconciled_violations = sharded_violations + [
        {"shard": "_reconciliation", **v} for v in recon["cross_shard_only_violations"]
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
    sharded_dep_viols = [v for v in sharded_reconciled_violations if v.get("code") not in ind_code_set]

    dup_codes = {"stale_sibling_duplicate", "cross_shard_duplicate_conflict"}
    mono_dup_subjects = sorted({v.get("subject", "") for v in mono_res["violations"] if v.get("code") in dup_codes})
    sharded_dup_subjects = sorted(
        {v.get("subject", "") for v in sharded_reconciled_violations if v.get("code") in dup_codes}
        | set(recon["conflicting_subjects"])
    )
    mono_missing_subjects = sorted({v.get("subject", "") for v in mono_res["violations"] if v.get("code") == "missing_dependency_decl"})
    sharded_missing_subjects = sorted({v.get("subject", "") for v in sharded_reconciled_violations if v.get("code") == "missing_dependency_decl"})

    return {
        "schema_version": SCHEMA_VERSION,
        "orphan_only": orphan_res,
        "compiled_shard_count": len(compiled_shards),
        "compiled_module_count": len(all_compiled),
        "unaudited_uncompiled_lake_modules": uncompiled,
        "max_workers": workers,
        "monolithic": {
            "wall_sec": mono_wall,
            "lean_elapsed_ms": mono_res["lean_elapsed_ms"],
            "modules_checked": mono_res["modules_checked"],
            "declarations_checked": mono_res["declarations_checked"],
            "inductives_checked": mono_res["inductives_checked"],
            "ctors_checked": mono_res["ctors_checked"],
            "recursors_checked": mono_res.get("recursors_checked", 0),
            "transitive_visited": mono_res["transitive_visited"],
            "kernel_blocks_checked": mono_res.get("kernel_blocks_checked"),
            "kernel_replay_elapsed_ms": mono_res.get("kernel_replay_elapsed_ms"),
            "axioms_reached": mono_res["axioms_reached"],
            "violation_count": len(mono_res["violations"]),
            "inductive_violation_count": len(mono_ind_viols),
            "dependency_violation_count": len(mono_dep_viols),
            "duplicate_conflict_subject_count": len(mono_dup_subjects),
        },
        "sharded": {
            "wall_sec": sharded_wall_sec,
            "modules_checked": sum(r["modules_checked"] for r in per_shard.values()),
            "declarations_checked": sharded_decls,
            "inductives_checked": sharded_inducts,
            "ctors_checked": sharded_ctors,
            "recursors_checked": sum(r.get("recursors_checked", 0) for r in per_shard.values()),
            "union_axioms": union_axioms,
            "violation_count": len(sharded_reconciled_violations),
            "raw_per_shard_violation_count": len(sharded_violations),
            "cross_shard_reconciliation": {
                "total_fingerprint_records": recon["total_fingerprint_records"],
                "unique_declarations": recon["unique_declarations"],
                "duplicate_declarations_seen": recon["duplicate_declarations_seen"],
                "conflicting_subject_count": len(recon["conflicting_subjects"]),
                "cross_shard_only_conflict_count": len(recon["cross_shard_only_violations"]),
            },
            "inductive_violation_count": len(sharded_ind_viols),
            "dependency_violation_count": len(sharded_dep_viols),
            "duplicate_conflict_subject_count": len(sharded_dup_subjects),
            "per_shard": {k: per_shard[k] for k in sorted(per_shard)},
        },
        "parity": {
            "axiom_union_matches_monolithic": union_axioms == mono_res["axioms_reached"],
            "declaration_count_matches_monolithic": sharded_decls == mono_res["declarations_checked"],
            "inductive_count_matches_monolithic": sharded_inducts == mono_res["inductives_checked"],
            "ctor_count_matches_monolithic": sharded_ctors == mono_res["ctors_checked"],
            "zero_inductive_violations": len(mono_ind_viols) == 0 and len(sharded_ind_viols) == 0,
            "zero_violations": len(mono_res["violations"]) == 0 and len(sharded_reconciled_violations) == 0,
            "duplicate_conflict_subjects_match_monolithic": mono_dup_subjects == sharded_dup_subjects,
            "missing_dependency_subjects_match_monolithic": mono_missing_subjects == sharded_missing_subjects,
            "violation_subject_parity_with_monolithic": (
                mono_dup_subjects == sharded_dup_subjects
                and mono_missing_subjects == sharded_missing_subjects
                and sorted((v.get("code", ""), v.get("subject", "")) for v in mono_ind_viols)
                == sorted((v.get("code", ""), v.get("subject", "")) for v in sharded_ind_viols)
            ),
            "all_lake_modules_compiled_and_audited": not uncompiled,
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


def _expand_cfg_attr(attr_toks: list[Token], line: int, depth: int = 0) -> list[tuple[list[Token], int]]:
    """Expand `cfg_attr(pred, a1, a2, ...)` into `[a1, a2, ...]` (recursively).

    A contract hidden behind `#[cfg_attr(creusot, ensures(false))]` is active whenever the
    verifier's cfg is set, so every guard must see it (fail closed on any predicate).
    """
    if depth > 8:
        return [(attr_toks, line)]
    path, args = _attr_path_and_args(attr_toks)
    if path.split("::")[-1] != "cfg_attr":
        return [(attr_toks, line)]
    out: list[tuple[list[Token], int]] = []
    for part in _split_top_level_tokens(args, ",")[1:]:
        if part:
            out.extend(_expand_cfg_attr(part, line, depth + 1))
    return out


def _collect_rust_outer_attrs(tokens: list[Token], pos: int) -> tuple[list[tuple[list[Token], int]], int]:
    """Collect contiguous outer attributes `#[...]` starting at `pos` (with `cfg_attr` expanded)."""
    attrs: list[tuple[list[Token], int]] = []
    i = pos
    n = len(tokens)
    while i + 1 < n and tokens[i].text == "#" and tokens[i + 1].text == "[":
        close_idx = _find_matching_delim(tokens, i + 1, "[", "]")
        attrs.extend(_expand_cfg_attr(tokens[i + 2 : close_idx], tokens[i].line))
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
        if t.text in ("(", "[", "{", "⦃"):
            depth += 1
        elif t.text in (")", "]", "}", "⦄"):
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


def _strip_outer_rust_wrappers(toks: list[Token]) -> list[Token]:
    """Strip outer matching `(...)` and single-expression `{ ... }` blocks (no top-level `;`)."""
    changed = True
    while changed and len(toks) >= 2:
        changed = False
        if toks[0].text == "(" and _find_matching_delim(toks, 0, "(", ")") == len(toks) - 1:
            toks = toks[1:-1]
            changed = True
        elif toks[0].text == "{" and _find_matching_delim(toks, 0, "{", "}") == len(toks) - 1:
            inner = toks[1:-1]
            if len(_split_top_level_tokens(inner, ";")) == 1:
                toks = inner
                changed = True
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


def _rust_literal_value(tok: Token) -> int | bool | None:
    """Integer/boolean value of a single literal token (`1_000u32`, `0xFF`, `true`), else `None`."""
    if tok.text in ("true", "false"):
        return tok.text == "true"
    if tok.kind != "NUMBER":
        return None
    txt = tok.text.replace("_", "").lower()
    for suf in ("u128", "i128", "usize", "isize", "u64", "i64", "u32", "i32", "u16", "i16", "u8", "i8"):
        if txt.endswith(suf) and len(txt) > len(suf):
            txt = txt[: -len(suf)]
            break
    try:
        if txt.startswith("0x"):
            return int(txt[2:], 16)
        if txt.startswith("0o"):
            return int(txt[2:], 8)
        if txt.startswith("0b"):
            return int(txt[2:], 2)
        return int(txt, 10)
    except ValueError:
        return None


_LITERAL_CMP_OPS: dict[str, Any] = {
    "==": lambda a, b: a == b,
    "!=": lambda a, b: a != b,
    "<=": lambda a, b: a <= b,
    ">=": lambda a, b: a >= b,
    "<": lambda a, b: a < b,
    ">": lambda a, b: a > b,
}


def _rust_literal_comparison(toks: list[Token]) -> bool | None:
    """Evaluate `lit OP lit` (e.g. `1 == 2`, `0u8 > 1`) to a constant truth value, else `None`."""
    toks = _strip_outer_parens(toks)
    if len(toks) == 1:
        v = _rust_literal_value(toks[0])
        return v if isinstance(v, bool) else None
    if len(toks) != 3 or toks[1].text not in _LITERAL_CMP_OPS:
        return None
    a = _rust_literal_value(toks[0])
    b = _rust_literal_value(toks[2])
    if a is None or b is None or isinstance(a, bool) != isinstance(b, bool):
        return None
    if isinstance(a, bool) and toks[1].text not in ("==", "!="):
        return None
    return bool(_LITERAL_CMP_OPS[toks[1].text](a, b))


def _parse_rust_match_arm_bodies(body_toks: list[Token]) -> list[list[Token]]:
    """Extract RHS expressions of top-level `pat => expr` arms inside a Rust `match { ... }` body."""
    arms: list[list[Token]] = []
    i = 0
    n = len(body_toks)
    while i < n:
        # Find depth-0 `=>`
        depth = 0
        arrow = -1
        j = i
        while j < n:
            t = body_toks[j].text
            if t in ("(", "[", "{"):
                depth += 1
            elif t in (")", "]", "}"):
                depth = max(0, depth - 1)
            elif depth == 0 and t == "=>":
                arrow = j
                break
            j += 1
        if arrow == -1:
            break
        rhs_start = arrow + 1
        if rhs_start >= n:
            break
        if body_toks[rhs_start].text == "{":
            close = _find_matching_delim(body_toks, rhs_start, "{", "}")
            arms.append(body_toks[rhs_start : close + 1])
            i = close + 1
            if i < n and body_toks[i].text == ",":
                i += 1
        else:
            k = rhs_start
            d2 = 0
            while k < n:
                t = body_toks[k].text
                if t in ("(", "[", "{"):
                    d2 += 1
                elif t in (")", "]", "}"):
                    d2 = max(0, d2 - 1)
                elif d2 == 0 and t == ",":
                    break
                k += 1
            arms.append(body_toks[rhs_start:k])
            i = k + 1
    return arms


def _rust_expr_is_tautology(toks: list[Token]) -> bool:
    """Sound syntactic tautology detector paired with `_rust_expr_is_unsatisfiable`."""
    toks = _strip_outer_rust_wrappers(toks)
    if not toks:
        return False
    if len(toks) == 1 and toks[0].text == "true":
        return True
    if _rust_literal_comparison(toks) is True:
        return True
    if toks[0].text == "!" and len(toks) > 1:
        return _rust_expr_is_unsatisfiable(toks[1:])
    disjuncts = _split_top_level_tokens(toks, "||")
    if len(disjuncts) > 1:
        if any(_rust_expr_is_tautology(d) for d in disjuncts):
            return True
        pos: set[str] = set()
        neg: set[str] = set()
        for d in disjuncts:
            ds = _strip_outer_rust_wrappers(d)
            if ds and ds[0].text == "!":
                neg.add(_norm_tok_expr(ds[1:]))
            elif ds:
                pos.add(_norm_tok_expr(ds))
        if pos & neg:
            return True
    conjuncts = _split_top_level_tokens(toks, "&&")
    if len(conjuncts) > 1:
        return all(_rust_expr_is_tautology(c) for c in conjuncts)
    for op in ("==", "<=", ">="):
        parts = _split_top_level_tokens(toks, op)
        if len(parts) == 2 and parts[0] and parts[1]:
            if _norm_tok_expr(parts[0]) == _norm_tok_expr(parts[1]):
                return True
    return False


def _rust_expr_is_unsatisfiable(toks: list[Token]) -> bool:
    """Sound syntactic unsatisfiability detector for Rust contract clauses."""
    toks = _strip_closure_header(toks)
    toks = _strip_outer_rust_wrappers(toks)
    if not toks:
        return False

    # Constant-foldable literal comparison (`1 == 2`, `0 > 1`, `true == false`)
    if _rust_literal_comparison(toks) is False:
        return True

    # Negation: double negation `!!e` and negated tautologies `!(x == x)`, `!(1 == 1)`, `!(true || p)`
    if toks[0].text == "!" and len(toks) > 1:
        inner = _strip_outer_rust_wrappers(toks[1:])
        if inner and inner[0].text == "!" and len(inner) > 1:
            return _rust_expr_is_unsatisfiable(inner[1:])
        if _rust_expr_is_tautology(inner):
            return True

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
            cond = _strip_outer_rust_wrappers(toks[1:brace_idx])
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

    # `match scrut { pat => arm1, pat2 => arm2 }`: unsatisfiable iff every arm is unsatisfiable.
    if toks[0].text == "match":
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
            close_idx = _find_matching_delim(toks, brace_idx, "{", "}")
            arms = _parse_rust_match_arm_bodies(toks[brace_idx + 1 : close_idx])
            if arms and all(_rust_expr_is_unsatisfiable(arm) for arm in arms):
                return True

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
    # Flatten nested `&&` across conjuncts so `[x == 1 && y == 2, x == 2]` is caught too.
    flat: list[list[Token]] = []
    for raw in conjuncts:
        s = _strip_outer_rust_wrappers(raw)
        if not s:
            continue
        sub = _split_top_level_tokens(s, "&&")
        if len(sub) > 1:
            flat.extend(sub)
        else:
            flat.append(s)

    pos_atoms: set[str] = set()
    neg_atoms: set[str] = set()
    eq_pairs: set[tuple[str, str]] = set()
    neq_pairs: set[tuple[str, str]] = set()
    lt_pairs: set[tuple[str, str]] = set()
    le_pairs: set[tuple[str, str]] = set()
    eq_lits: dict[str, set[tuple[type, Any]]] = {}
    int_bounds: list[tuple[str, str, int]] = []  # (expr, op in <,<=,>,>=,!=, lit)

    for raw in flat:
        c = _strip_outer_rust_wrappers(raw)
        if not c:
            continue
        if c[0].text == "!":
            neg_atoms.add(_norm_tok_expr(c[1:]))
        else:
            pos_atoms.add(_norm_tok_expr(c))
        for op in ("==", "!=", "<", "<=", ">", ">="):
            parts = _split_top_level_tokens(c, op)
            if len(parts) != 2 or not parts[0] or not parts[1]:
                continue
            lhs_t = _strip_outer_rust_wrappers(parts[0])
            rhs_t = _strip_outer_rust_wrappers(parts[1])
            a, b = _norm_tok_expr(lhs_t), _norm_tok_expr(rhs_t)
            lv = _rust_literal_value(lhs_t[0]) if len(lhs_t) == 1 else None
            rv = _rust_literal_value(rhs_t[0]) if len(rhs_t) == 1 else None
            if op == "==":
                eq_pairs.add((a, b))
                eq_pairs.add((b, a))
                if rv is not None and lv is None:
                    eq_lits.setdefault(a, set()).add((type(rv), rv))
                elif lv is not None and rv is None:
                    eq_lits.setdefault(b, set()).add((type(lv), lv))
            elif op == "!=":
                neq_pairs.add((a, b))
                neq_pairs.add((b, a))
                if isinstance(rv, int) and not isinstance(rv, bool) and lv is None:
                    int_bounds.append((a, "!=", rv))
                elif isinstance(lv, int) and not isinstance(lv, bool) and rv is None:
                    int_bounds.append((b, "!=", lv))
            elif op == "<":
                lt_pairs.add((a, b))
                if isinstance(rv, int) and not isinstance(rv, bool) and lv is None:
                    int_bounds.append((a, "<", rv))
                elif isinstance(lv, int) and not isinstance(lv, bool) and rv is None:
                    int_bounds.append((b, ">", lv))
            elif op == ">":
                lt_pairs.add((b, a))
                if isinstance(rv, int) and not isinstance(rv, bool) and lv is None:
                    int_bounds.append((a, ">", rv))
                elif isinstance(lv, int) and not isinstance(lv, bool) and rv is None:
                    int_bounds.append((b, "<", lv))
            elif op == "<=":
                le_pairs.add((a, b))
                if isinstance(rv, int) and not isinstance(rv, bool) and lv is None:
                    int_bounds.append((a, "<=", rv))
                elif isinstance(lv, int) and not isinstance(lv, bool) and rv is None:
                    int_bounds.append((b, ">=", lv))
            elif op == ">=":
                le_pairs.add((b, a))
                if isinstance(rv, int) and not isinstance(rv, bool) and lv is None:
                    int_bounds.append((a, ">=", rv))
                elif isinstance(lv, int) and not isinstance(lv, bool) and rv is None:
                    int_bounds.append((b, "<=", lv))
            break

    if (pos_atoms & neg_atoms) or (eq_pairs & neq_pairs):
        return True
    # Conflicting literal equalities on same expression (`x == 1 && x == 2`)
    if any(len(vals) > 1 for vals in eq_lits.values()):
        return True
    # Order contradictions: `a < b && b < a`, `a < b && b <= a` (`a >= b`), `a < b && a == b`
    for a, b in lt_pairs:
        if (b, a) in lt_pairs or (b, a) in le_pairs or (a, b) in eq_pairs:
            return True
    # Conflicting equality vs literal bound (`x == 5 && x < 3`)
    for expr, op, bound in int_bounds:
        for typ, val in eq_lits.get(expr, ()):
            if typ is int and not _LITERAL_CMP_OPS[op](val, bound):
                return True
    return False


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
            is_trusted_body = False
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
                    if leaf == "trusted":
                        is_trusted_body = True
                    rq, en = _extract_contract_clauses(args)
                    req_clauses.extend(rq)
                    ens_clauses.extend(en)
                elif leaf == "external_body" or (
                    leaf == "verifier" and any(t.text == "external_body" for t in args)
                ):
                    # Verus `#[verifier::external_body]` / Creusot `#[trusted]`: the body is
                    # NOT verified, so its contract is as trusted as an extern spec.
                    is_trusted_body = True

            fn_info = _parse_rust_fn_sig(tokens, after_attrs)
            if fn_info is not None:
                fn_name, is_extern_fn, is_diverging, next_pos = fn_info
                is_extern_target = (
                    is_external_spec_attr
                    or (is_spec_attr and (is_extern_fn or bool(in_extern_block_brace_depths)))
                    or is_trusted_body
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
                                    "non-diverging extern/external_spec/trusted-body callable carries unsatisfiable ensures",
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
            # Turbofish `::<...>`: skip balanced generic args and CONTINUE parsing `::method`
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
            continue
        elif i + 1 < n and tokens[i + 1].kind == "IDENT":
            segs.append(tokens[i + 1].text)
            i += 2
        else:
            break
    return segs, i, had_turbofish


def _parse_rust_use_tree(toks: list[Token], prefix: list[str] | None = None) -> list[tuple[list[str], str | None]]:
    """Flatten a Rust `use` tree into `(path_segments, alias)` pairs.

    Handles nested groups `a::{b as c, d::{e as f}}`, `self`, and globs (`*` yields
    `(prefix + ['*'], None)`).
    """
    prefix = list(prefix or [])
    out: list[tuple[list[str], str | None]] = []
    for item in _split_top_level_tokens(toks, ","):
        if not item:
            continue
        segs = list(prefix)
        i = 0
        n = len(item)
        if i < n and item[i].text == "::":
            i += 1
        alias: str | None = None
        handled = False
        while i < n:
            t = item[i]
            if t.text == "{":
                close = _find_matching_delim(item, i, "{", "}")
                out.extend(_parse_rust_use_tree(item[i + 1 : close], segs))
                handled = True
                break
            if t.text == "*":
                out.append((segs + ["*"], None))
                handled = True
                break
            if t.text == "as" and i + 1 < n:
                alias = item[i + 1].text
                break
            if t.kind == "IDENT":
                if t.text != "self":
                    segs.append(t.text)
            i += 1
        if not handled and segs:
            out.append((segs, alias))
    return out


def _rust_block_contexts(tokens: list[Token]) -> list[tuple[str | None, bool]]:
    """Per-token `(enclosing_fn_name, inside_loop_of_that_fn)` brace-context map.

    Handles struct literals and struct patterns inside `for` / `while` headers
    (e.g., `for _ in [S { a: 1 }] { ... }`, `while let Some(S { x }) = e { ... }`,
    `for S { a } in items { ... }`) without mistaking the header brace for the loop body.
    """
    n = len(tokens)
    ctx: list[tuple[str | None, bool]] = [(None, False)] * n
    stack: list[tuple[str, str | None]] = []
    pending_fn: str | None = None
    fn_paren_depth = 0
    pending_loop = False
    loop_kw: str | None = None
    loop_paren_depth = 0
    loop_is_let = False
    loop_seen_eq = False
    loop_seen_in = False
    pending_impl = False
    for i, t in enumerate(tokens):
        cur_fn: str | None = None
        in_loop = False
        for kind, nm in reversed(stack):
            if kind == "loop":
                in_loop = True
            if kind == "fn":
                cur_fn = nm
                break
        ctx[i] = (cur_fn, in_loop)
        txt = t.text
        prev = tokens[i - 1].text if i > 0 else ""
        if txt == "fn" and i + 1 < n and tokens[i + 1].kind == "IDENT":
            pending_fn = tokens[i + 1].text
            fn_paren_depth = 0
        elif txt in ("impl", "trait") and pending_fn is None:
            pending_impl = True
        elif (
            txt in ("loop", "while", "for")
            and prev not in (".", "::")
            and pending_fn is None
            and not pending_impl
            and not pending_loop
        ):
            pending_loop = True
            loop_kw = txt
            loop_paren_depth = 0
            loop_is_let = False
            loop_seen_eq = False
            loop_seen_in = False
        elif pending_fn is not None and txt in ("(", "["):
            fn_paren_depth += 1
        elif pending_fn is not None and txt in (")", "]"):
            fn_paren_depth = max(0, fn_paren_depth - 1)
        elif pending_loop and txt in ("(", "["):
            loop_paren_depth += 1
        elif pending_loop and txt in (")", "]"):
            loop_paren_depth = max(0, loop_paren_depth - 1)
        elif pending_loop and loop_paren_depth == 0 and loop_kw == "while" and txt == "let":
            loop_is_let = True
        elif pending_loop and loop_paren_depth == 0 and loop_kw == "while" and loop_is_let and txt == "=":
            loop_seen_eq = True
        elif pending_loop and loop_paren_depth == 0 and loop_kw == "for" and txt == "in":
            loop_seen_in = True
        elif txt == "{":
            if pending_fn is not None and fn_paren_depth == 0:
                stack.append(("fn", pending_fn))
                pending_fn = None
            elif pending_impl:
                stack.append(("impl", None))
                pending_impl = False
            elif pending_loop:
                is_header_brace = (
                    loop_paren_depth > 0
                    or (loop_kw == "while" and loop_is_let and not loop_seen_eq)
                    or (loop_kw == "for" and not loop_seen_in)
                )
                if is_header_brace:
                    stack.append(("block", None))
                else:
                    stack.append(("loop", None))
                    pending_loop = False
                    loop_kw = None
            else:
                stack.append(("block", None))
        elif txt == "}":
            if stack:
                stack.pop()
        elif txt == ";":
            if fn_paren_depth == 0:
                pending_fn = None
            if loop_paren_depth == 0:
                pending_loop = False
                loop_kw = None
    return ctx


GHOST_TOKEN_AUTHORITY_FNS: frozenset[str] = frozenset({"main"})


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
    path_aliases: dict[str, tuple[str, ...]] = {}
    fn_header_spans: list[tuple[int, int]] = []
    use_spans: list[tuple[int, int]] = []

    impl_stack: list[tuple[int, int, str]] = []  # (start_idx, brace_depth, type_name)
    impl_spans: list[tuple[int, int, str]] = []  # (start_idx, end_idx, type_name)
    brace_depth = 0
    i = 0
    while i < n:
        if tokens[i].text == "{":
            brace_depth += 1
            i += 1
            continue
        if tokens[i].text == "}":
            if impl_stack and brace_depth == impl_stack[-1][1]:
                s_idx, _, t_nm = impl_stack.pop()
                impl_spans.append((s_idx, i, t_nm))
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
                if last_ident:
                    impl_stack.append((j, brace_depth, last_ident))
                i = j + 1
                continue

        # Track `use ...;` trees (nested groups, multiple `as` aliases) and `type A = P;`
        if tokens[i].text == "use":
            u_start = i
            j = i + 1
            while j < n and tokens[j].text != ";":
                j += 1
            use_spans.append((u_start, j))
            for segs, alias in _parse_rust_use_tree(tokens[u_start + 1 : j]):
                if alias is not None and alias != "_" and segs and segs[-1] != "*":
                    path_aliases[alias] = tuple(segs)
            i = j + 1
            continue
        if (
            tokens[i].text == "type"
            and i + 2 < n
            and tokens[i + 1].kind == "IDENT"
            and (i == 0 or tokens[i - 1].text in (";", "{", "}", "pub", ")", "]"))
        ):
            j = i + 2
            if j < n and tokens[j].text == "<":
                d = 1
                j += 1
                while j < n and d > 0:
                    d += 1 if tokens[j].text == "<" else (-1 if tokens[j].text == ">" else 0)
                    j += 1
            if j < n and tokens[j].text == "=":
                segs, after, _ = _parse_rust_path_at(tokens, j + 1)
                if segs:
                    path_aliases[tokens[i + 1].text] = tuple(segs)
                k = j
                while k < n and tokens[k].text != ";":
                    k += 1
                use_spans.append((i, k))
                i = k + 1
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
                    if impl_stack:
                        ctor_suffixes.add((impl_stack[-1][2], fn_name))
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

    # Expand aliases to a fixed point: a `use`/`type` alias of a ctor TYPE (`Tokens`,
    # `#[ghost_token_ctor]` impl types) aliases every ctor fn on it; an alias of a ctor FN
    # path aliases the fn itself.
    expanded_suffixes = set(ctor_suffixes)
    changed = True
    while changed:
        changed = False
        for alias, target in path_aliases.items():
            for suf in list(expanded_suffixes):
                if len(suf) >= 2 and target[-1:] == suf[-2:-1]:
                    cand = (alias, suf[-1])
                    if cand not in expanded_suffixes:
                        expanded_suffixes.add(cand)
                        changed = True
                if len(target) >= len(suf) and target[-len(suf):] == suf:
                    cand1 = (alias,)
                    if cand1 not in expanded_suffixes:
                        expanded_suffixes.add(cand1)
                        changed = True

    def matched_suffix(segs: list[str]) -> tuple[str, ...] | None:
        t_segs = tuple(segs)
        best: tuple[str, ...] | None = None
        for suf in expanded_suffixes:
            if len(t_segs) >= len(suf) and t_segs[-len(suf):] == suf:
                if best is None or len(suf) > len(best):
                    best = suf
        return best

    def enclosing_impl_type(pos: int) -> str | None:
        best: tuple[int, str] | None = None
        for s_idx, e_idx, t_nm in impl_spans:
            if s_idx <= pos <= e_idx:
                span_len = e_idx - s_idx
                if best is None or span_len < best[0]:
                    best = (span_len, t_nm)
        return best[1] if best is not None else None

    block_ctx = _rust_block_contexts(tokens)
    direct_calls: list[tuple[str, int, str]] = []
    authority_calls: list[tuple[str, int, str]] = []

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

        # Qualified-self UFCS path `<Tokens>::new` / `<Tokens as Trait>::new`
        ufcs_segs: list[str] | None = None
        ufcs_next = i
        if tokens[i].text == "<":
            d = 1
            j = i + 1
            while j < n and d > 0 and tokens[j].text not in (";", "{", "}"):
                d += 1 if tokens[j].text == "<" else (-1 if tokens[j].text == ">" else 0)
                j += 1
            if d == 0 and j + 1 < n and tokens[j].text == "::" and tokens[j + 1].kind == "IDENT":
                inner_segs, _, _ = _parse_rust_path_at(tokens, i + 1)
                if inner_segs:
                    rest_segs, rest_next, _ = _parse_rust_path_at(tokens, j + 1)
                    ufcs_segs = inner_segs + rest_segs
                    ufcs_next = rest_next

        if ufcs_segs is not None or tokens[i].kind == "IDENT" or (
            tokens[i].text == "::" and i + 1 < n and tokens[i + 1].kind == "IDENT"
        ):
            if ufcs_segs is not None:
                segs, next_i = ufcs_segs, ufcs_next
            else:
                segs, next_i, _ = _parse_rust_path_at(tokens, i)
            # Resolve `Self::ctor` inside `impl TypeName { ... }`
            if segs and segs[0] == "Self":
                impl_ty = enclosing_impl_type(i)
                if impl_ty is not None:
                    segs = [impl_ty] + segs[1:]
            # Track calls to single-entry authority functions (`main(...)`) for re-entrancy checks
            if (
                segs
                and segs[-1] in GHOST_TOKEN_AUTHORITY_FNS
                and next_i < n
                and tokens[next_i].text == "("
                and (i == 0 or tokens[i - 1].text != ".")
            ):
                authority_calls.append((segs[-1], i, "::".join(segs)))
            if matches_ctor(segs):
                is_direct_call = next_i < n and tokens[next_i].text == "("
                path_str = "::".join(segs)
                if is_direct_call and not closure_end_stack:
                    suf = matched_suffix(segs) or tuple(segs)
                    direct_calls.append(("::".join(suf), i, path_str))
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

    # Single-entry authority (Lean `FnDefGhostTokenGuard`: only `directEntryCall true`, and
    # at most ONE issuance per one-shot ctor): direct calls must sit in the entry function,
    # outside any loop, and occur exactly once per ctor.
    seen_ctor: dict[str, int] = {}
    authority_fns_issuing_tokens: set[str] = set()
    for ctor_key, idx, path_str in direct_calls:
        fn_name, in_loop = block_ctx[idx]
        reason: str | None = None
        if fn_name not in GHOST_TOKEN_AUTHORITY_FNS:
            reason = f"direct call outside the single-entry authority (in fn `{fn_name}`)"
        elif in_loop:
            reason = "direct call inside a loop issues the one-shot token repeatedly"
        elif ctor_key in seen_ctor:
            reason = f"second direct call site (first at line {seen_ctor[ctor_key]}) duplicates the one-shot token"
        else:
            authority_fns_issuing_tokens.add(fn_name)
        seen_ctor.setdefault(ctor_key, tokens[idx].line)
        if reason is not None:
            findings.append(
                _make_peer_finding(
                    "fndef_ghost_token_coercion",
                    path_str,
                    tokens[idx].line,
                    reason,
                    file_path=file_path,
                )
            )
    # Re-entrancy / recursion check: if an authority fn (`main`) issues a one-shot token,
    # any recursive or mutual-recursive call to `main(...)` can duplicate the token!
    for auth_name, call_idx, call_path in authority_calls:
        if auth_name in authority_fns_issuing_tokens:
            caller_fn, _ = block_ctx[call_idx]
            findings.append(
                _make_peer_finding(
                    "fndef_ghost_token_coercion",
                    call_path,
                    tokens[call_idx].line,
                    f"re-entrant call to single-entry authority `{auth_name}` from `{caller_fn}` duplicates the one-shot token",
                    file_path=file_path,
                )
            )
    findings.sort(key=lambda f: (f["line"], f["subject"], f["detail"]))
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

_NO_DROP_WRAPPER_TYPES: frozenset[str] = frozenset({"PhantomData", "ManuallyDrop", "NonNull", "MaybeUninit"})

# Types known to carry NO drop glue of their own (generic wrappers contribute only their
# type arguments' glue, which is tracked separately). Anything outside this set, the
# known-drop set, local items, and generic parameters is a FOREIGN type of unknown drop
# status and fails closed (Guard 5 cannot prove `has_drop_glue == false`).
_KNOWN_NO_DROP_TYPES: frozenset[str] = frozenset(
    {
        "u8", "u16", "u32", "u64", "u128", "usize",
        "i8", "i16", "i32", "i64", "i128", "isize",
        "f32", "f64", "bool", "char", "str", "Self",
        "Option", "Result", "Cell", "Wrapping", "Saturating", "Reverse",
        "NonZeroU8", "NonZeroU16", "NonZeroU32", "NonZeroU64", "NonZeroU128", "NonZeroUsize",
        "NonZeroI8", "NonZeroI16", "NonZeroI32", "NonZeroI64", "NonZeroI128", "NonZeroIsize",
        "NonZero", "Duration", "Instant", "Ordering", "Infallible", "TypeId", "Layout",
        "AtomicBool", "AtomicU8", "AtomicU16", "AtomicU32", "AtomicU64", "AtomicUsize",
        "AtomicI8", "AtomicI16", "AtomicI32", "AtomicI64", "AtomicIsize",
    }
)


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
        if t.text == ";":
            # Array length expression `[T; N]`: skip to the closing `]`
            d = 0
            while i < n and not (type_toks[i].text == "]" and d == 0):
                if type_toks[i].text == "[":
                    d += 1
                elif type_toks[i].text == "]":
                    d -= 1
                i += 1
            continue
        if t.kind == "IDENT" and t.text in ("dyn", "impl", "mut", "const", "where", "for"):
            i += 1
            continue
        if t.text in ("&", "*"):
            # Skip inner borrowed/raw-pointer type (including multi-segment paths, tuples, slices)
            i += 1
            while i < n and (type_toks[i].kind == "LIFETIME" or type_toks[i].text in ("mut", "const", "dyn", "&", "*")):
                i += 1
            if i < n and type_toks[i].text == "(":
                i = _find_matching_delim(type_toks, i, "(", ")") + 1
            elif i < n and type_toks[i].text == "[":
                i = _find_matching_delim(type_toks, i, "[", "]") + 1
            elif i < n and (type_toks[i].kind == "IDENT" or type_toks[i].text == "::"):
                _, after_p, _ = _parse_rust_path_at(type_toks, i)
                i = max(i + 1, after_p)
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
        if t.text == "fn" and i + 1 < n and type_toks[i + 1].text == "(":
            # Function pointer `fn(A) -> B` inside generic args carries no drop glue
            i = _find_matching_delim(type_toks, i + 1, "(", ")") + 1
            if i < n and type_toks[i].text == "->":
                i += 1
                d = 0
                while i < n:
                    tt = type_toks[i].text
                    if tt in ("(", "[", "<"):
                        d += 1
                    elif tt in (")", "]", ">"):
                        if d == 0:
                            break
                        d -= 1
                    elif d == 0 and tt == ",":
                        break
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


def _strip_rust_field_prefix(field_toks: list[Token]) -> list[Token]:
    """Strip leading outer attributes `#[...]` and visibility `pub` / `pub(...)` from a Rust field."""
    i = 0
    n = len(field_toks)
    while i < n:
        if field_toks[i].text == "#" and i + 1 < n and field_toks[i + 1].text == "[":
            _, i = _collect_rust_outer_attrs(field_toks, i)
            continue
        if field_toks[i].text == "pub":
            i += 1
            if i < n and field_toks[i].text == "(":
                i = _find_matching_delim(field_toks, i, "(", ")") + 1
            continue
        break
    return field_toks[i:]


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
    local_types: set[str] = set()
    generic_params: dict[str, set[str]] = {}
    ext_type_items: list[dict[str, Any]] = []

    def _generic_param_names(start: int) -> tuple[set[str], int]:
        names: set[str] = set()
        j = start
        if j < n and tokens[j].text == "<":
            close = j
            d = 0
            while close < n:
                if tokens[close].text == "<":
                    d += 1
                elif tokens[close].text == ">":
                    d -= 1
                    if d == 0:
                        break
                close += 1
            for part in _split_top_level_tokens(tokens[j + 1 : close], ","):
                part = [t for t in part if t.text != "const"]
                if part and part[0].kind == "IDENT":
                    names.add(part[0].text)
            j = close + 1
        return names, j

    i = 0
    while i < n:
        # `type Alias<...> = Target;` aliases contribute their RHS drop glue.
        if (
            tokens[i].text == "type"
            and i + 1 < n
            and tokens[i + 1].kind == "IDENT"
            and (i == 0 or tokens[i - 1].text in (";", "{", "}", "pub", ")", "]"))
        ):
            alias_name = tokens[i + 1].text
            gps, j = _generic_param_names(i + 2)
            if j < n and tokens[j].text == "=":
                k = j + 1
                while k < n and tokens[k].text != ";":
                    k += 1
                type_fields.setdefault(alias_name, set()).update(
                    _extract_owned_type_names(tokens[j + 1 : k])
                )
                local_types.add(alias_name)
                generic_params.setdefault(alias_name, set()).update(gps)
                i = k + 1
                continue

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
                local_types.add(type_name)
                gps, j = _generic_param_names(j)
                generic_params.setdefault(type_name, set()).update(gps)
                # Skip `where ...`
                if j < n and tokens[j].text == "where":
                    while j < n and tokens[j].text not in ("{", "(", ";"):
                        j += 1
                owned_deps: set[str] = set()
                tuple_wrapped: list[str] = []
                if j < n and tokens[j].text == "(":
                    close_p = _find_matching_delim(tokens, j, "(", ")")
                    for field_toks in _split_top_level_tokens(tokens[j + 1 : close_p], ","):
                        # Strip field attributes `#[...]` and `pub` / `pub(...)` visibility
                        ft = _strip_rust_field_prefix(field_toks)
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
                            ft = _strip_rust_field_prefix(field_toks)
                            colon = next((k for k, t in enumerate(ft) if t.text == ":"), -1)
                            if colon != -1:
                                owned_deps.update(_extract_owned_type_names(ft[colon + 1 :]))
                    else:
                        # Enum variants
                        for var_toks in _split_top_level_tokens(body, ","):
                            vt = _strip_rust_field_prefix(var_toks)
                            if "(" in [t.text for t in vt]:
                                lp = next(k for k, t in enumerate(vt) if t.text == "(")
                                rp = _find_matching_delim(vt, lp, "(", ")")
                                for ft in _split_top_level_tokens(vt[lp + 1 : rp], ","):
                                    owned_deps.update(_extract_owned_type_names(_strip_rust_field_prefix(ft)))
                            elif "{" in [t.text for t in vt]:
                                lb = next(k for k, t in enumerate(vt) if t.text == "{")
                                rb = _find_matching_delim(vt, lb, "{", "}")
                                for ft in _split_top_level_tokens(vt[lb + 1 : rb], ","):
                                    ft_s = _strip_rust_field_prefix(ft)
                                    colon = next((k for k, t in enumerate(ft_s) if t.text == ":"), -1)
                                    if colon != -1:
                                        owned_deps.update(_extract_owned_type_names(ft_s[colon + 1 :]))
                    j = close_b + 1

                type_fields.setdefault(type_name, set()).update(owned_deps)

                # Inspect attributes for `external_type_specification`
                has_ext_type = False
                has_ext_body = False
                drop_modeled = False
                explicit_drop = False
                asserted_no_drop = False
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
                    elif leaf == "no_drop_glue":
                        asserted_no_drop = True
                    elif leaf == "verifier" and any(t.text == "external_body" for t in args):
                        has_ext_body = True

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
                            "asserted_no_drop": asserted_no_drop,
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

    known_no_drop = set(_KNOWN_NO_DROP_TYPES)

    def _unknown_foreign(root: str) -> list[str]:
        """Foreign (non-local, non-std-known) types in the owned-type closure of `root`."""
        seen: set[str] = set()
        unknown: set[str] = set()
        stack = [(root, frozenset())]
        while stack:
            tname, params = stack.pop()
            if tname in seen:
                continue
            seen.add(tname)
            if tname in local_types:
                gp = frozenset(generic_params.get(tname, set()))
                for dep in type_fields.get(tname, set()):
                    if dep not in gp:
                        stack.append((dep, gp))
            elif tname in params or tname in direct_drop or tname in known_no_drop:
                continue
            else:
                unknown.add(tname)
        return sorted(unknown)

    # Pass 3: emit findings for `#[external_type_specification]` items
    findings: list[dict[str, Any]] = []
    for item in ext_type_items:
        drop_hits = sorted(t for t in item["targets"] if t in has_drop_glue)
        unknown_hits: list[str] = []
        if not drop_hits and not item["explicit_drop"] and not item["asserted_no_drop"]:
            for tgt in sorted(item["targets"]):
                unknown_hits.extend(_unknown_foreign(tgt))
            unknown_hits = sorted(set(unknown_hits))
        if unknown_hits:
            if item["has_external_body"]:
                findings.append(
                    _make_peer_finding(
                        "external_type_body_with_drop",
                        item["name"],
                        item["line"],
                        "external_type_specification combined with external_body on foreign type(s) "
                        f"of unknown drop glue ({', '.join(unknown_hits)}); fail closed unless #[no_drop_glue]",
                        file_path=file_path,
                    )
                )
            elif not item["drop_modeled"]:
                findings.append(
                    _make_peer_finding(
                        "external_type_drop_omission",
                        item["name"],
                        item["line"],
                        "external_type_specification wraps foreign type(s) of unknown drop glue "
                        f"({', '.join(unknown_hits)}); fail closed: model drop (#[models_drop]) or "
                        "assert #[no_drop_glue]",
                        file_path=file_path,
                    )
                )
            continue
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


_LEAN_IDENT_RE = re.compile(r"[^\W\d][\w'?!]*(?:\.[^\W\d][\w'?!]*)*")
_LEAN_NUMBER_RE = re.compile(r"\d\w*")
_LEAN_WS_RE = re.compile(r"[ \t\r\n]+")


@functools.lru_cache(maxsize=16)
def _lex_lean_tokens_cached(text: str) -> tuple[tuple[Token, ...], tuple[CommentSpan, ...]]:
    toks, comments = _lex_lean_tokens_impl(text)
    return tuple(toks), tuple(comments)


def lex_lean_tokens(text: str) -> tuple[list[Token], list[CommentSpan]]:
    """Nested-comment, raw/interpolated-string, char-literal, and guillemet-aware Lean 4 lexer."""
    toks, comments = _lex_lean_tokens_cached(text)
    return list(toks), list(comments)


def _lex_lean_tokens_impl(text: str) -> tuple[list[Token], list[CommentSpan]]:
    tokens: list[Token] = []
    comments: list[CommentSpan] = []
    n = len(text)
    i = 0
    line = 1
    two_char_ops = {"::", ":=", "->", "/\\", "\\/", "!=", "<=", ">=", "&&", "||", "@["}
    unicode_ops = {"→", "↔", "∧", "∨", "¬", "∀", "∃", "≠", "≤", "≥"}

    while i < n:
        ch = text[i]
        if ch in " \t\r\n":
            m_ws = _LEAN_WS_RE.match(text, i)
            assert m_ws is not None
            line += m_ws.group(0).count("\n")
            i = m_ws.end()
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

        # Raw string literal `r"..."` / `r#"..."#` / `r##"..."##` (no escapes; comment markers
        # inside are inert).
        if ch == "r" and i + 1 < n and text[i + 1] in ('"', "#"):
            j = i + 1
            hashes = 0
            while j < n and text[j] == "#":
                hashes += 1
                j += 1
            if j < n and text[j] == '"':
                closing = '"' + "#" * hashes
                close_at = text.find(closing, j + 1)
                end = n if close_at == -1 else close_at + len(closing)
                seg = text[i:end]
                tokens.append(Token("STRING", seg, i, end, line))
                line += seg.count("\n")
                i = end
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
            # Identifier with dotted projection/namespace suffixes `a.b.c`
            m_id = _LEAN_IDENT_RE.match(text, i)
            j = m_id.end() if m_id is not None else i + 1
            tokens.append(Token("IDENT", text[i:j], i, j, line))
            i = j
            continue

        if ch.isdigit():
            m_num = _LEAN_NUMBER_RE.match(text, i)
            j = m_num.end() if m_num is not None else i + 1
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


_LEAN_BINDER_BRACKETS: dict[str, str] = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}


def _lean_binder_types(toks: list[Token]) -> list[list[Token]]:
    """Types of Lean binders `(a b : T)`, `{x : T}`, `[inst : C]`, anonymous `[C]`, `⦃h : P⦄`, or bare `x y : T`."""
    out: list[list[Token]] = []
    i = 0
    n = len(toks)
    while i < n:
        t = toks[i].text
        if t in _LEAN_BINDER_BRACKETS:
            close = _find_matching_delim(toks, i, t, _LEAN_BINDER_BRACKETS[t])
            inner = toks[i + 1 : close]
            depth = 0
            found_colon = False
            for k, it in enumerate(inner):
                if it.text in ("(", "[", "{", "⦃"):
                    depth += 1
                elif it.text in (")", "]", "}", "⦄"):
                    depth = max(0, depth - 1)
                elif depth == 0 and it.text == ":":
                    found_colon = True
                    ty = inner[k + 1 :]
                    # strip default value `(x : T := v)`
                    cut = next((m for m, tt in enumerate(ty) if tt.text == ":="), len(ty))
                    out.append(ty[:cut])
                    break
            if not found_colon and t == "[" and inner:
                # Anonymous typeclass / instance binder `[PropExpr]`
                out.append(inner)
            i = close + 1
            continue
        if t == ":":
            out.append(toks[i + 1 :])
            break
        i += 1
    return out


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

    # Leading `∀ binders, body` / `∃ binders, body`: a `∀ (h : T), B` binder type `T` is an
    # ANTECEDENT (`T → B`, flipped polarity); an `∃ (h : T), B` binder type is a conjunct
    # (`T ∧ B`, same polarity).
    if toks[0].text in ("∀", "∃", "forall", "exists", "∃!"):
        depth = 0
        for idx in range(1, len(toks)):
            t = toks[idx].text
            if t in ("(", "[", "{", "⦃"):
                depth += 1
            elif t in (")", "]", "}", "⦄"):
                depth = max(0, depth - 1)
            elif depth == 0 and t == ",":
                binder_pol = _flip_pol(pol) if toks[0].text in ("∀", "forall") else pol
                bad_binders: list[Token] = []
                for ty in _lean_binder_types(toks[1:idx]):
                    bad_binders.extend(_check_lean_prop_polarity(ty, binder_pol))
                return bad_binders + _check_lean_prop_polarity(toks[idx + 1 :], pol)

    # Conditional `if [h :] cond then t else e` (`(c → t) ∧ (¬c → e)`): condition is in BOTH polarities!
    if toks[0].text == "if":
        depth = 0
        then_idx = -1
        else_idx = -1
        if_nest = 0
        for idx in range(1, len(toks)):
            t = toks[idx].text
            if t in ("(", "[", "{", "⦃"):
                depth += 1
            elif t in (")", "]", "}", "⦄"):
                depth = max(0, depth - 1)
            elif depth == 0:
                if t == "if":
                    if_nest += 1
                elif t == "then":
                    if if_nest == 0 and then_idx == -1:
                        then_idx = idx
                elif t == "else":
                    if if_nest > 0:
                        if_nest -= 1
                    elif then_idx != -1:
                        else_idx = idx
                        break
        if then_idx != -1 and else_idx != -1:
            cond = toks[1:then_idx]
            if len(cond) >= 3 and cond[0].kind == "IDENT" and cond[1].text == ":":
                cond = cond[2:]
            t_branch = toks[then_idx + 1 : else_idx]
            e_branch = toks[else_idx + 1 :]
            return (
                _check_lean_prop_polarity(cond, "pos")
                + _check_lean_prop_polarity(cond, "neg")
                + _check_lean_prop_polarity(t_branch, pol)
                + _check_lean_prop_polarity(e_branch, pol)
            )

    # Lowest precedence: `↔` / `<->` (both polarities!)
    for op in ("↔", "<->"):
        parts = _split_top_level_tokens(toks, op)
        if len(parts) > 1:
            bad: list[Token] = []
            for p in parts:
                bad.extend(_check_lean_prop_polarity(p, "pos"))
                bad.extend(_check_lean_prop_polarity(p, "neg"))
            return bad

    # Next: `→` / `->` (right-associative! Find FIRST depth-0 arrow, respecting `⦃...⦄`)
    depth = 0
    arrow_idx = -1
    for idx, tok in enumerate(toks):
        if tok.text in ("(", "[", "{", "⦃"):
            depth += 1
        elif tok.text in (")", "]", "}", "⦄"):
            depth = max(0, depth - 1)
        elif depth == 0 and tok.text in ("→", "->"):
            arrow_idx = idx
            break
    if arrow_idx != -1:
        lhs = toks[:arrow_idx]
        rhs = toks[arrow_idx + 1 :]
        # Dependent / implicit / instance / strict-implicit binder `(h : T) → rhs`,
        # `{h : T} → rhs`, `[T] → rhs`, `[h : T] → rhs`, `⦃h : T⦄ → rhs`
        lhs_bad: list[Token] = []
        if (
            lhs
            and lhs[0].text in _LEAN_BINDER_BRACKETS
            and _find_matching_delim(lhs, 0, lhs[0].text, _LEAN_BINDER_BRACKETS[lhs[0].text]) == len(lhs) - 1
        ):
            b_types = _lean_binder_types(lhs)
            if b_types:
                for ty in b_types:
                    lhs_bad.extend(_check_lean_prop_polarity(ty, _flip_pol(pol)))
            else:
                lhs_bad.extend(_check_lean_prop_polarity(lhs[1:-1], _flip_pol(pol)))
        else:
            lhs_bad.extend(_check_lean_prop_polarity(lhs, _flip_pol(pol)))
        return lhs_bad + _check_lean_prop_polarity(rhs, pol)

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

    # Leaf / atomic expression: check sub-bracketed expressions and direct assumes tokens
    bad = []
    i = 0
    while i < len(toks):
        if toks[i].text in _LEAN_BINDER_BRACKETS:
            close = _find_matching_delim(toks, i, toks[i].text, _LEAN_BINDER_BRACKETS[toks[i].text])
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
                if t in ("(", "[", "{", "⦃", "@["):
                    depth += 1
                elif t in (")", "]", "}", "⦄"):
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
                if t in ("(", "[", "{", "⦃", "@["):
                    depth += 1
                elif t in (")", "]", "}", "⦄"):
                    depth = max(0, depth - 1)
                elif depth == 0 and (
                    t in _LEAN_TOP_COMMANDS or t == "@["
                ):
                    break
                body_end += 1

            # Inspect statement (for theorem/lemma) or Prop body + binders (for `: Prop :=` def/abbrev)
            target_slices: list[list[Token]] = []
            binder_bad: list[Token] = []
            if kw in ("theorem", "lemma") and colon_idx != -1:
                stmt_end = assign_idx if assign_idx != -1 else k
                target_slices.append(tokens[colon_idx + 1 : stmt_end])
                # Signature binders `(h : T)` are hypotheses: `theorem t (h : T) : B` is
                # `T → B`, so each binder type is checked in NEGATIVE polarity.
                for ty in _lean_binder_types(tokens[j + 2 : colon_idx]):
                    binder_bad.extend(_check_lean_prop_polarity(ty, "neg"))
            elif kw in ("def", "abbrev") and colon_idx != -1 and assign_idx != -1:
                ret_slice = tokens[colon_idx + 1 : assign_idx]
                if any(t.text == "Prop" for t in ret_slice):
                    target_slices.append(tokens[assign_idx + 1 : body_end])
                    for ty in _lean_binder_types(tokens[j + 2 : colon_idx]):
                        binder_bad.extend(_check_lean_prop_polarity(ty, "neg"))
            if binder_bad:
                findings.append(
                    _make_peer_finding(
                        "assumption_positive_polarity",
                        decl_name,
                        binder_bad[0].line or decl_line,
                        f"assumption `{binder_bad[0].text}` appears in positive polarity inside a hypothesis binder",
                        file_path=file_path,
                    )
                )
                target_slices = []

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


_LEAN_INVALID_CTOR_NAMES: frozenset[str] = _LEAN_TOP_COMMANDS | frozenset(
    {
        "where",
        "private",
        "protected",
        "public",
        "noncomputable",
        "unsafe",
        "partial",
        "scoped",
        "local",
        "extends",
        "with",
        "by",
        "do",
        "fun",
        "match",
        "if",
        "then",
        "else",
        "let",
        "have",
        "show",
        "in",
    }
)


def scan_lean_invariant_struct_sealing(
    text: str,
    *,
    target_structs: set[str] | None = None,
    file_path: str | None = None,
) -> list[dict[str, Any]]:
    """Guard 6b (`Samite` cl/1029680381): verify invariant-bearing Lean `structure`s start with `private <ctor> ::`."""
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

        # Track namespace (splitting dotted `A.B` per segment) / section / end
        if tokens[j].text == "namespace" and j + 1 < n and tokens[j + 1].kind == "IDENT":
            for seg in [s for s in tokens[j + 1].text.split(".") if s]:
                ns_stack.append(seg)
                scope_kinds.append(("namespace", seg))
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
            if end_name is None:
                if scope_kinds:
                    kind, _ = scope_kinds.pop()
                    if kind == "namespace" and ns_stack:
                        ns_stack.pop()
            else:
                end_segs = [s for s in end_name.split(".") if s]
                for eseg in reversed(end_segs):
                    if not scope_kinds:
                        break
                    kind, nm = scope_kinds[-1]
                    if nm == eseg or (kind == "section" and nm == end_name):
                        scope_kinds.pop()
                        if kind == "namespace" and ns_stack:
                            ns_stack.pop()
                    else:
                        break
            i = j + (2 if end_name else 1)
            continue

        if (
            tokens[j].text in ("structure", "class")
            and j + 1 < n
            and tokens[j + 1].kind == "IDENT"
            and tokens[j + 1].text not in ("inductive", "abbrev")
        ):
            raw_name = tokens[j + 1].text
            struct_line = tokens[j].line
            qual_name = ".".join(ns_stack + [raw_name]) if ns_stack else raw_name
            short_leaf = raw_name.split(".")[-1]

            # Check comments before OR interleaved between attributes/modifiers and `structure`/`class`
            leading_comments = _comments_immediately_before(comments, prev_end, tokens[j].start)
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
                if t in ("(", "[", "{", "⦃"):
                    depth += 1
                elif t in (")", "]", "}", "⦄"):
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
                        and "." not in tokens[b + 1].text
                        and tokens[b + 1].text not in _LEAN_INVALID_CTOR_NAMES
                        and tokens[b + 2].text == "::"
                    ):
                        sealed_ok = True
                    else:
                        preview = " ".join(t.text for t in tokens[b : min(b + 4, n)])
                        reason = f"`where` body does not begin with `private <ctor> ::` (found `{preview}`)"
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
