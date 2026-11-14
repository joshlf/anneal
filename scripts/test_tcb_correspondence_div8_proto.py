#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Regression and audit suite for the TCB correspondence + IEEE-754 prototype.

Run with::

    python3 -B -m unittest scripts/test_tcb_correspondence_div8_proto.py -v

The suite checks, against `theory/Anneal/TcbCorrespondenceDiv8AndFloatPrototype.lean`:

1. the prototype never edits `trusted/`, `lakefile.toml`, `minirust/`, or
   `lean-miri/`, and the branch diff only touches the three prototype files;
2. the Lean file compiles (`anneal-lean-run ... lake env lean`) with zero
   errors, zero warnings, and zero forbidden tokens;
3. a live kernel replay on a temporary `/tmp` copy of the file confirms that
   every headline theorem exists and depends only on `propext` / `Quot.sound`
   (no `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or
   `Classical.choice`), and that the in-file `#guard_msgs` axiom block covers
   every headline theorem;
4. differential cross-checks of the pure IEEE-754 casts against (a) Python
   `fractions.Fraction` / `struct` ground truth and (b) a line-by-line Python
   port of `lean-miri/vendor/Miri/Interpreter/Float.lean`;
5. all eight actionable `TRACKED_CORRESPONDENCE_DIVERGENCES` IDs of
   `scripts/run_nightly_verification_suite.py` are addressed in both the Lean
   file and `PROTOTYPE_REPORT.md`.
"""

from __future__ import annotations

import ast
from fractions import Fraction
import math
import os
from pathlib import Path
import random
import re
import shutil
import struct
import subprocess
import sys
import tempfile
from typing import Callable
import unittest

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
LEAN_FILE = REPO / "theory" / "Anneal" / "TcbCorrespondenceDiv8AndFloatPrototype.lean"
REPORT = REPO / "PROTOTYPE_REPORT.md"
SUITE = REPO / "scripts" / "run_nightly_verification_suite.py"
MIRI_FLOAT = REPO / "lean-miri" / "vendor" / "Miri" / "Interpreter" / "Float.lean"
BASE_SHA = "3da6d48d24b4f289c1b4c161a1172f98f4806f27"
NAMESPACE = "Anneal.TcbCorrespondenceDiv8AndFloatPrototype"

ALLOWED_DIFF = {
    "theory/Anneal/TcbCorrespondenceDiv8AndFloatPrototype.lean",
    "scripts/test_tcb_correspondence_div8_proto.py",
    "PROTOTYPE_REPORT.md",
}
PROTECTED_PREFIXES = ("trusted/", "lakefile.toml", "minirust/", "lean-miri/")
FORBIDDEN_TOKENS = (
    "sorry",
    "admit",
    "axiom ",
    "native_decide",
    "import LeanMiriSpec",
    "import Miri",
)
ALLOWED_AXIOMS = {"propext", "Quot.sound"}
BANNED_AXIOMS = {"sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler", "Classical.choice"}

# Every headline theorem of the prototype (Part A and Part B).
HEADLINE_THEOREMS = (
    # String.toList-free MiniRust translator replica (Mach / MachTB ground truth)
    "intrinsicOfDefPathSF_table",
    "translateProgWithIntrinsicsSF_witnesses_isSome",
    # 1. DIV-MR-CALL-TARGET-LOCAL
    "div_mr_call_target_local_trusted_baseline",
    "div_mr_call_target_local_trusted_137",
    "div_mr_call_target_local_mach_tb_42",
    "div_mr_call_target_local_repaired_agrees",
    "div_mr_call_target_local_write_back_canary",
    "div_mr_call_target_local_write_back_trusted",
    # 2. DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL
    "div_mr_caller_borrow_across_scalar_call_trusted_ub",
    "div_mr_caller_borrow_across_scalar_call_mach_tb_42",
    "div_mr_caller_borrow_across_scalar_call_repaired_agrees",
    "div_mr_caller_borrow_frame_isolation",
    "updateBorrowPermAtProjProto_other_frame",
    "entryAccessTransitionProto_other_frame",
    # 3. DIV-MR-TB-TWOPHASE-DIRECT-WRITE
    "div_mr_tb_twophase_direct_write_repaired_agrees",
    # 4. DIV-MR-TB-FNENTRY-LOCAL-DEALLOC
    "div_mr_tb_fnentry_local_dealloc_trusted_ret",
    "div_mr_tb_fnentry_local_dealloc_repaired_agrees",
    "div_mr_tb_fnentry_local_dealloc_ub_at_return",
    "div_mr_tb_fnentry_local_dealloc_callee_return_canary",
    "preventsDeallocation_eq_miniRust",
    "preventsDeallocation_table",
    # 5. DIV-MR-TB-UNSAFECELL-PROTECTED-IM
    "div_mr_tb_unsafecell_protected_im_repaired_agrees",
    "div_mr_tb_unsafecell_coupling_legacy_breaks",
    "div_mr_tb_unsafecell_storage_dead_canary",
    # 6. DIV-LM-RAW-OVERWRITE-CHAR-COPY
    "div_lm_raw_overwrite_char_copy_trusted_steps",
    "div_lm_raw_overwrite_char_copy_repaired_ub",
    "div_lm_raw_overwrite_char_copy_ub_at_load",
    "div_lm_raw_overwrite_char_copy_valid_accepted",
    "isValidCharCode_iff_isValidChar",
    "validateLoadedValueProto_char_eq_miri",
    "miriValidateCharScalar_boundaries",
    # 7. DIV-LM-D6-OFFSET-DISABLED-TAG
    "div_lm_d6_offset_disabled_trusted_ub",
    "div_lm_d6_offset_trusted_evalPtrOffsetBinOp",
    "div_lm_d6_offset_disabled_repaired_steps",
    "div_lm_d6_offset_disabled_deref_canary",
    "evalBinOpOffset_lockstep_miri",
    "div_lm_d6_offset_disabled_tag_repaired_agrees",
    "div_lm_d6_offset_lockstep_examples",
    # 8. DIV-LM-ENUM-SET-DISCR-UNINIT
    "div_lm_enum_set_discr_trusted_uninit_ub",
    "div_lm_enum_set_discr_trusted_faults",
    "div_lm_enum_set_discr_uninit_repaired_agrees",
    "div_lm_enum_set_discr_observed",
    "div_lm_enum_set_discr_payload_canary",
    "div_lm_enum_set_discr_dead_and_init",
    # Part B
    "pack_unpack_f32",
    "unpack_pack_f32",
    "pack_unpack_f64",
    "unpack_pack_f64",
    "decodeBits_agrees_miriDecode",
    "evalFloatToIntSaturating_sound",
    "evalFloatToIntSaturating_nan",
    "evalFloatToIntSaturating_canaries",
    "roundQuotientTiesToEven_half_ulp",
    "roundQuotientTiesToEven_tie_even",
    "roundRatioBits_congr",
    "roundRatioBits_normal",
    "roundRatioBits_subnormal",
    "evalIntToFloatRoundTiesToEven_exact",
    "evalIntToFloat_i32_u32_to_f64_exact",
    "b585733184_ties_to_even_separation",
    "evalIntToFloatRoundTiesToEven_canaries",
    "evalIntToFloatRoundTiesToEven_sound",
    "f32ToF64_exact_and_roundtrip",
    "convertFloatBits_nan_quiet",
    "f64ToF32_signaling_nan_quietized",
    "evalFloatToFloatRoundTiesToEven_canaries",
    "evalFloatToFloatRoundTiesToEven_sound",
    "castKind_end_to_end",
    "castKind_trusted_unsupported",
    # B1 adversarial hardening theorems (Part A & Part B)
    "div_mr_call_target_local_reborrow_in_callee_canary",
    "reborrow_inherits_targetFrameDepth",
    "direct_write_disables_reservedFrz_preserves_cell_and_reservedIM",
    "div_mr_tb_twophase_direct_write_reservedIM_and_cell_survive_canary",
    "hasProtectedLocalBorrowProto_cell_exempt_reservedIM_blocks",
    "disableFrameBorrowsProto_frame_isolation",
    "div_mr_tb_fnentry_dangling_callee_raw_ptr_return_ub",
    "div_lm_raw_overwrite_char_projected_move_canary",
    "evalRetagProto_raw_uninit_or_dead_ub",
    "disabled_tag_deref_and_reborrow_ub",
    "div_lm_enum_set_discr_protected_conflict_ub",
    "div_lm_enum_set_discr_borrow_invalidation_and_protector_canary",
    "f64ToF32_subnormal_and_double_rounding_canaries",
    "roundRatioBits_valid_and_not_nan",
    "roundRatioTiesToEven_float_half_ulp",
    # A1: end-to-end write frame isolation, corpus coverage, correct rounding, overflow
    "writePlaceProto_direct_frame_isolation",
    "writePlaceProto_deref_frame_isolation",
    "overlay_coverage_canaries",
    "roundRatioTiesToEven_correctly_rounded",
    "roundRatioTiesToEven_overflow_of",
    # B2: dead-alloc offset lockstep, WitLM3_1 D6 4-witness + storage-revival suite,
    # local-slot & read/stmt borrow frame isolation, Return destination write invalidation,
    # downstream TCB compatibility, biconditional overflow, and signed-zero underflow
    "div_lm_d6_offset_dead_alloc_lockstep_miri",
    "div_lm_d6_wit_lm3_1_four_witnesses_and_revive_canary",
    "writePlaceProto_frame_local_isolation",
    "readPlaceProto_and_stmt_borrow_frame_isolation",
    "div_mr_call_ref_mut_protected_roundtrip_agrees",
    "div_mr_return_destination_invalidation_and_protector_canary",
    "hasProtectedLocalBorrowProto_of_hasProtectedWriteConflictProto",
    "hasProtectedLocalBorrowProto_disableLocalBorrowsProto",
    "roundRatioTiesToEven_overflow_iff",
    "roundRatioBits_sign_and_underflow_zero_preserved",
    # A2: kernel-checked corpus agreement and out-of-fragment fixes
    "corpus_agreement_kernel",
    "corpus_out_of_fragment_fixes",
    # B3: post-deallocation & storage-revival soundness, multi-function & composite corpus
    # kernel agreement, and IntToFloat -> FloatToInt round-trip
    "disableLocalBorrowsProto_and_disableFrameBorrowsProto_revival_sound",
    "corpus_multifn_agreement_kernel",
    "corpus_composite_agreement_kernel",
    "evalFloatToIntSaturating_roundtrip_of_intToFloat",
    # A3: known Tree Borrows gap shared with Trusted (negative canary)
    "tb_direct_read_freeze_gap_shared_with_trusted",
    # B4: candidate fix for DIV-MR-TB-DIRECT-LOCAL-ACCESS (`directReadTreeBorrows`),
    # direct-read frame isolation, and floatToIntValue monotonicity
    "tb_direct_read_freeze_repaired_by_directReadTreeBorrows",
    "readPlaceProto_direct_frame_isolation",
    "floatToIntValue_monotone",
    # A4: direct reference creation is a Tree Borrows read (candidate-fix coverage)
    "tb_direct_reborrow_read_repaired_by_directReadTreeBorrows",
)


# Kernel-checked bridges between the in-file `String.toList`-free MiniRust translator
# replica and the upstream `ProvenanceWitness` machines. They are replayed only in the
# temporary harness: the upstream definitions depend on `Classical.choice` through core
# `String.toList`, so the bridges may (and today do) mention it, unlike every in-file
# declaration.
MINIRUST_BRIDGES = (
    ("callerRefMutSilentWrongLocalProgSF", "callerRefMutSilentWrongLocalProg"),
    ("callerRefMutSilentWrongLocalMInitSF", "callerRefMutSilentWrongLocalMInit"),
    ("callerRefMutSilentWrongLocalTBInitSF", "callerRefMutSilentWrongLocalTBInit"),
    ("callerBorrowAcrossScalarCallProgSF", "callerBorrowAcrossScalarCallProg"),
    ("callerBorrowAcrossScalarCallMInitSF", "callerBorrowAcrossScalarCallMInit"),
    ("callerBorrowAcrossScalarCallTBInitSF", "callerBorrowAcrossScalarCallTBInit"),
)
BRIDGE_NAMESPACE = "TcbDiv8ProtoBridge"
BRIDGE_ALLOWED_AXIOMS = ALLOWED_AXIOMS | {"Classical.choice"}


# ---------------------------------------------------------------------------
# MiniRust witness corpus: prototype vs. unpatched `Trusted` differential
# ---------------------------------------------------------------------------

CORPUS_DIR = REPO / "minirust" / "lean" / "MiniRustSpec" / "Correspondence"
CORPUS_MODULES = {
    "Witness.lean": "MiniRustSpec.Correspondence.Witness",
    "PointerWitness.lean": "MiniRustSpec.Correspondence.PointerWitness",
    "RefWitness.lean": "MiniRustSpec.Correspondence.RefWitness",
    "TbWitness.lean": "MiniRustSpec.Correspondence.TbWitness",
    "ProvenanceWitness.lean": "MiniRustSpec.Correspondence.ProvenanceWitness",
}
CORPUS_PREFIX = "MiniRustSpec.Correspondence."
# Argument vectors (see `argOfTy`): small positive, all-zero bits, all-one bits.
CORPUS_ARG_VARIANTS = (0, 1, 2)

# Bodies on which the prototype and the unpatched `Trusted` stepper both produce a
# definite outcome (value or UB) but disagree. Each entry is (prototype, Trusted) and is
# justified by an upstream MiniRust ground-truth theorem that the prototype agrees with.
EXPECTED_CORPUS_DIVERGENCES = {
    # DIV-MR-CALL-TARGET-LOCAL (`callerRefMutSilentWrongLocal_divergence`: Mach/MachTB = 42 at
    # x = 5): the callee's `*r = *r + 37` lands in the caller's `x`; Trusted returns 137.
    "ProvenanceWitness.callerRefMutSilentWrongLocalMir#0": ("ok 42/4", "ok 137/4"),
    "ProvenanceWitness.callerRefMutSilentWrongLocalMir#1": ("ok 37/4", "ok 137/4"),
    "ProvenanceWitness.callerRefMutSilentWrongLocalMir#2": ("ok 36/4", "ok 137/4"),
    # DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL (Mach/MachTB = 42).
    "ProvenanceWitness.callerBorrowAcrossScalarCallMir#0": ("ok 42/4", "ub"),
    "ProvenanceWitness.callerBorrowAcrossScalarCallMir#1": ("ok 42/4", "ub"),
    "ProvenanceWitness.callerBorrowAcrossScalarCallMir#2": ("ok 42/4", "ub"),
    # Same frame-qualification bug (`callRefMutProtectedRoundTrip_mach_and_tb`: 84 at x = 5).
    "ProvenanceWitness.callerRefMutProtectedMir#0": ("ok 84/4", "ub"),
    "ProvenanceWitness.callerRefMutProtectedMir#1": ("ok 74/4", "ub"),
    "ProvenanceWitness.callerRefMutProtectedMir#2": ("ok 72/4", "ub"),
    # Same frame-qualification bug; the call writes its result to the borrowed `_1`.
    "ProvenanceWitness.callerRefMutProtectedBadCallDstMir#0": ("ok 42/4", "ub"),
    "ProvenanceWitness.callerRefMutProtectedBadCallDstMir#1": ("ok 37/4", "ub"),
    "ProvenanceWitness.callerRefMutProtectedBadCallDstMir#2": ("ok 36/4", "ub"),
    # DIV-MR-TB-FNENTRY-LOCAL-DEALLOC (`retagFnEntryLocalDeallocUb_tb_direct`: UB).
    "RefWitness.retagFnEntryLocalDeallocUb#0": ("ub", "ok 5/4"),
    "RefWitness.retagFnEntryLocalDeallocUb#1": ("ub", "ok 0/4"),
    "RefWitness.retagFnEntryLocalDeallocUb#2": ("ub", "ok 4294967295/4"),
    # `argCountMismatch_minirust_ub`: MiniRust reports a call-ABI arity violation.
    "Witness.argCountMismatchCaller#0": ("ub", "ok 5/4"),
    "Witness.argCountMismatchCaller#1": ("ub", "ok 5/4"),
    "Witness.argCountMismatchCaller#2": ("ub", "ok 5/4"),
    # `uninitProjCallDest_minirust_ret`: MiniRust writes the field of the uninit tuple
    # (`neg_i8(5) = 251` at x = 5).
    "Witness.uninitProjCallDestCaller#0": ("ok 251/1", "ub"),
    "Witness.uninitProjCallDestCaller#1": ("ok 0/1", "ub"),
    "Witness.uninitProjCallDestCaller#2": ("ok 1/1", "ub"),
}

# Bodies that `Trusted` evaluates definitively but on which the prototype fails closed
# (`.unsupported`): the deliberately unmodeled exposed-provenance / int-to-pointer /
# transmute / wide-pointer / sub-local byte-offset constructs (PROTOTYPE_REPORT.md §6).
FAIL_CLOSED_CORPUS: frozenset[str] = frozenset({
    # `pointerExposeProvenance` / `pointerWithExposedProvenance` (exposed provenance,
    # int-to-pointer casts): not modeled by the frame-qualified borrow table.
    "PointerWitness.exposeTwice",
    "ProvenanceWitness.assumeReborrowExposeRoundTrip",
    "ProvenanceWitness.calleeBorrowAssumeAddMir",
    "ProvenanceWitness.callerBorrowExposeAndScalarCallMir",
    "ProvenanceWitness.callerCrossFrameExposeMir",
    "ProvenanceWitness.callerLoopCallExposeCalleeMir",
    "ProvenanceWitness.callerPrePostCallExposeMir",
    "ProvenanceWitness.int2ptrAdjacentArgsAmbiguous",
    "ProvenanceWitness.int2ptrAfterStorageDeadTwoExposed",
    "ProvenanceWitness.int2ptrAfterStorageDeadUb",
    "ProvenanceWitness.int2ptrForgedTag",
    "ProvenanceWitness.transmuteExposedAddrToRawPtrDerefUb",
    "TbWitness.exposeSharedRefWriteUb",
    "TbWitness.exposeSingleRefMutRoundTrip",
    "TbWitness.exposeTwoRefMutAngelicUnsupported",
    "TbWitness.int2ptrDeadAllocDerefUb",
    "TbWitness.int2ptrMultiAllocBoundaryUnsupported",
    "TbWitness.int2ptrRawRoundTripOk",
    "TbWitness.int2ptrUnexposedDerefUb",
    # `CastKind.transmute` (byte-level reinterpretation, `Trusted.evalByteCast`).
    "RefWitness.refRawTransmuteChain",
    "RefWitness.transmuteDanglingIntToRawPtrNoDerefOk",
    "RefWitness.transmuteDanglingIntToRefDiscrepancy",
    "RefWitness.transmuteSharedRefToMutWriteDiscrepancy",
    "RefWitness.transmuteUninitRefUb",
    "TbWitness.boolInvalidByteRefUb",
    "TbWitness.boolInvalidLoadDirectUb",
    "TbWitness.stdOrderingMutRefCmp",
    # Array-element pointer re-derivation in `ptrToPtr` (`deriveStackElemThinPtr`).
    "PointerWitness.arrayElemPtr",
    # Sub-local byte offsets: deref / `&*p` with `offsetBytes ≠ 0` (misaligned pointers).
    "PointerWitness.misaligned",
    "RefWitness.misalignedRef",
})

CORPUS_LEAN = r"""
namespace TcbDiv8ProtoCorpus
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.TcbCorrespondenceDiv8AndFloatPrototype

/-- Argument vectors: `0` = small positive (`5`, `true`, `'A'`), `1` = all-zero bits,
`2` = all-one bits (`-1` / `MAX`, `true`, `char::MAX`). -/
def scalarArg (variant bytes : Nat) : Value :=
  .scalar ⟨match variant with | 0 => 5 | 1 => 0 | _ => 2 ^ (8 * bytes) - 1, bytes⟩

def argOfTy (variant : Nat) : RigidTy → Option Value
  | .bool => some (.scalar ⟨match variant with | 1 => 0 | _ => 1, 1⟩)
  | .char => some (.scalar ⟨match variant with | 0 => 0x41 | 1 => 0 | _ => 0x10FFFF, 4⟩)
  | .uint .u8 => some (scalarArg variant 1)
  | .int .i8 => some (scalarArg variant 1)
  | .uint .u16 => some (scalarArg variant 2)
  | .int .i16 => some (scalarArg variant 2)
  | .uint .u32 => some (scalarArg variant 4)
  | .int .i32 => some (scalarArg variant 4)
  | .uint .u64 => some (scalarArg variant 8)
  | .int .i64 => some (scalarArg variant 8)
  | .uint .usize => some (scalarArg variant 8)
  | .int .isize => some (scalarArg variant 8)
  | .uint .u128 => some (scalarArg variant 16)
  | .int .i128 => some (scalarArg variant 16)
  | _ => none

def argsFor (variant : Nat) (body : CapturedMir) : Option (List Value) :=
  ((body.localDecls.drop 1).take body.argCount).mapM (fun d => argOfTy variant d.ty.kind)

partial def valStr : Value → String
  | .unit => "unit"
  | .scalar sc => s!"{sc.bits}/{sc.sizeBytes}"
  | .ptr _ sz => s!"ptr/{sz}"
  | .aggregate i vs => s!"agg{i}(" ++ ",".intercalate (vs.map valStr) ++ ")"

def protoClass : ProtoOutcome → String
  | .ok v => "ok " ++ valStr v
  | .ub => "ub"
  | .unsupported => "unsupported"
  | .outOfFuel => "fuel"

def trustedClass (callees : List CapturedMir) (body : CapturedMir) (args : List Value) : String :=
  match MiniRustSpec.Correspondence.runA body 256 (initMachineStateWithCallees body args callees) with
  | some (_, .normal (v, _)) => "ok " ++ valStr v
  | some _ => "other"
  | none =>
    if MiniRustSpec.Correspondence.faultsA body 256 (initMachineStateWithCallees body args callees)
    then "ub" else "none"

def line (callees : List CapturedMir) (variant : Nat) (name : String) (body : CapturedMir) :
    String :=
  match argsFor variant body with
  | none => s!"CORPUS|{name}#{variant}|skip|skip"
  | some a =>
    s!"CORPUS|{name}#{variant}|{protoClass (runMirProto body callees a)}|{trustedClass callees body a}"
"""


def corpus_bodies() -> list[str]:
    """Every `def _ : CapturedMir` body of the five MiniRust witness modules."""
    bodies: list[str] = []
    for fname, ns in CORPUS_MODULES.items():
        text = (CORPUS_DIR / fname).read_text(encoding="utf-8")
        for m in re.finditer(r"(?m)^def (\w+) : CapturedMir(?: :=| where)", text):
            bodies.append(f"{ns}.{m.group(1)}")
    return bodies


def corpus_harness_lines(bodies: list[str]) -> list[str]:
    lines = [CORPUS_LEAN, "def corpus : List CapturedMir := [", "  " + ",\n  ".join(bodies) + "]"]
    lines.append("end TcbDiv8ProtoCorpus")
    for b in bodies:
        for variant in CORPUS_ARG_VARIANTS:
            lines.append(
                f'#eval IO.println (TcbDiv8ProtoCorpus.line TcbDiv8ProtoCorpus.corpus {variant} "{b}" {b})'
            )
    return lines


def _parse_corpus(stdout: str) -> dict[str, tuple[str, str]]:
    out: dict[str, tuple[str, str]] = {}
    for line in stdout.splitlines():
        parts = line.strip().split("|")
        if len(parts) == 4 and parts[0] == "CORPUS":
            out[parts[1].removeprefix(CORPUS_PREFIX)] = (parts[2], parts[3])
    return out


def _definite(outcome: str) -> bool:
    return outcome == "ub" or outcome.startswith("ok ")


def declared_names(source: str) -> list[str]:
    """Fully qualified names of every `theorem` / `def` / `abbrev` in the Lean file."""
    names: list[str] = []
    stack: list[str] = []
    for line in source.splitlines():
        m = re.match(r"^namespace\s+(\S+)", line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r"^end\s+(\S+)", line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
            continue
        m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+)?(?:theorem|def|abbrev)\s+([^\s:(\[{]+)",
                     line)
        if m:
            names.append(".".join(stack + [m.group(1)]))
    return names


def _env() -> dict[str, str]:
    env = os.environ.copy()
    elan = str(Path.home() / ".elan" / "bin")
    env["PATH"] = elan + os.pathsep + env.get("PATH", "")
    return env


def _lean_cmd(path: Path) -> list[str]:
    lean_run = shutil.which("anneal-lean-run", path=_env()["PATH"])
    if lean_run is None:
        lean_run = str(REPO / "scripts" / "anneal-lean-run")
    return [lean_run, "--mode", "file", "--concurrency", "1", "--", "lake", "env", "lean", str(path)]


def _run_lean(path: Path, timeout: int = 3600) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        _lean_cmd(path),
        cwd=str(REPO),
        env=_env(),
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )


def _git(*args: str) -> str:
    proc = subprocess.run(
        ["git", *args], cwd=str(REPO), capture_output=True, text=True, check=True
    )
    return proc.stdout


# ---------------------------------------------------------------------------
# Python ground truth: exact rationals + struct
# ---------------------------------------------------------------------------

FORMATS = {
    "binary32": {"eb": 8, "fb": 23, "bias": 127, "w": 32},
    "binary64": {"eb": 11, "fb": 52, "bias": 1023, "w": 64},
}


def decode_ref(fmt: str, bits: int):
    """Independent decoding to ('zero'|'fin'|'inf'|'nan', neg, value/payload)."""
    p = FORMATS[fmt]
    neg = (bits >> (p["w"] - 1)) & 1
    e = (bits >> p["fb"]) & ((1 << p["eb"]) - 1)
    f = bits & ((1 << p["fb"]) - 1)
    if e == (1 << p["eb"]) - 1:
        return ("inf", neg, None) if f == 0 else ("nan", neg, f)
    if e == 0 and f == 0:
        return ("zero", neg, Fraction(0))
    if e == 0:
        return ("fin", neg, Fraction(f, 1 << (p["fb"] + p["bias"] - 1)))
    return ("fin", neg, Fraction((1 << p["fb"]) + f) * Fraction(2) ** (e - p["bias"] - p["fb"]))


def encode_ref(fmt: str, neg: int, e: int, f: int) -> int:
    p = FORMATS[fmt]
    return (neg << (p["w"] - 1)) | (e << p["fb"]) | f


def round_ref(fmt: str, neg: int, val: Fraction, ties_even: bool = True) -> int:
    """Independent correctly rounded encoding of a nonnegative rational."""
    p = FORMATS[fmt]
    fb, bias, eb = p["fb"], p["bias"], p["eb"]
    emin = 1 - bias
    if val == 0:
        return encode_ref(fmt, neg, 0, 0)
    # floor(log2(val)) via exact comparisons
    e = val.numerator.bit_length() - val.denominator.bit_length()
    while Fraction(2) ** e > val:
        e -= 1
    while Fraction(2) ** (e + 1) <= val:
        e += 1
    e = max(e, emin)
    quantum = Fraction(2) ** (e - fb)
    q = val / quantum
    fl = math.floor(q)
    rem = q - fl
    if rem > Fraction(1, 2) or (rem == Fraction(1, 2) and (not ties_even or fl % 2 == 1)):
        fl += 1
    sig = fl
    if sig >= (1 << (fb + 1)):
        sig //= 2
        e += 1
    if e > bias:
        return encode_ref(fmt, neg, (1 << eb) - 1, 0)
    if sig < (1 << fb):
        return encode_ref(fmt, neg, 0, sig)
    return encode_ref(fmt, neg, e + bias, sig - (1 << fb))


def struct_narrow_f64_to_f32(bits: int) -> int:
    x = struct.unpack("<d", struct.pack("<Q", bits))[0]
    try:
        return struct.unpack("<I", struct.pack("<f", x))[0]
    except OverflowError:
        return 0xFF800000 if x < 0 else 0x7F800000


def struct_widen_f32_to_f64(bits: int) -> int:
    x = struct.unpack("<f", struct.pack("<I", bits))[0]
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def int_target(spec: str, pw: int) -> tuple[bool, int]:
    signed = spec.startswith("i")
    width = pw if spec[1:] == "size" else int(spec[1:])
    return signed, width


def f2i_ref(fmt: str, bits: int, spec: str, pw: int) -> int:
    signed, width = int_target(spec, pw)
    lo = -(1 << (width - 1)) if signed else 0
    hi = (1 << (width - 1)) - 1 if signed else (1 << width) - 1
    kind, neg, val = decode_ref(fmt, bits)
    if kind == "nan" or kind == "zero":
        v = 0
    elif kind == "inf":
        v = lo if neg else hi
    else:
        t = math.trunc(val)
        v = max(lo, min(hi, -t if neg else t))
    return v % (1 << width)


def i2f_ref(signed: bool, width: int, bits: int, fmt: str) -> int:
    b = bits % (1 << width)
    v = b - (1 << width) if signed and b >= (1 << (width - 1)) else b
    return round_ref(fmt, 1 if v < 0 else 0, Fraction(abs(v)))


def f2f_ref(src: str, dst: str, bits: int) -> int:
    kind, neg, val = decode_ref(src, bits)
    pd = FORMATS[dst]
    if kind == "zero":
        return encode_ref(dst, neg, 0, 0)
    if kind == "inf":
        return encode_ref(dst, neg, (1 << pd["eb"]) - 1, 0)
    if kind == "nan":
        ps = FORMATS[src]
        quiet = val | (1 << (ps["fb"] - 1))
        if pd["fb"] >= ps["fb"]:
            payload = quiet << (pd["fb"] - ps["fb"])
        else:
            payload = quiet >> (ps["fb"] - pd["fb"])
        return encode_ref(dst, neg, (1 << pd["eb"]) - 1, payload | (1 << (pd["fb"] - 1)))
    return round_ref(dst, neg, val)


# ---------------------------------------------------------------------------
# Line-by-line port of lean-miri/vendor/Miri/Interpreter/Float.lean
# ---------------------------------------------------------------------------


class MiriError(Exception):
    pass


def miri_pow_scale(n: int, d: int, exponent: int) -> tuple[int, int]:
    return (n * 2**exponent, d) if exponent >= 0 else (n, d * 2 ** (-exponent))


def miri_encode(fmt: str, negative: bool, exponent: int, fraction: int) -> int:
    p = FORMATS[fmt]
    return ((2 ** (p["w"] - 1) if negative else 0) + exponent * 2 ** p["fb"] + fraction) % 2**128


def miri_decode(fmt: str, bits: int):
    p = FORMATS[fmt]
    if bits >= 2 ** p["w"]:
        raise MiriError("encodingExceedsWidth")
    negative = bits // 2 ** (p["w"] - 1) != 0
    exponent = (bits // 2 ** p["fb"]) % 2 ** p["eb"]
    fraction = bits % 2 ** p["fb"]
    if exponent == 2 ** p["eb"] - 1:
        return negative, ("infinite",) if fraction == 0 else ("nan", fraction)
    significand = fraction if exponent == 0 else 2 ** p["fb"] + fraction
    unbiased = (1 - p["bias"]) if exponent == 0 else exponent - p["bias"]
    n, d = miri_pow_scale(significand, 1, unbiased - p["fb"])
    return negative, ("finite", n, d)


def miri_ratio_exponent(n: int, d: int) -> int:
    if n >= d:
        return (n // d).bit_length() - 1
    k = (d // n).bit_length() - 1
    return -k if n * 2**k >= d else -(k + 1)


def miri_round_quotient_even(n: int, d: int) -> int:
    q, r = n // d, n % d
    return q + 1 if r * 2 > d or (r * 2 == d and q % 2 == 1) else q


def miri_round_ratio(fmt: str, negative: bool, n: int, d: int) -> int:
    p = FORMATS[fmt]
    fb, bias, eb = p["fb"], p["bias"], p["eb"]
    min_exp, max_exp = 1 - bias, bias
    if d == 0:
        raise MiriError("zeroDenominator")
    if n == 0:
        return miri_encode(fmt, negative, 0, 0)
    exponent = max(miri_ratio_exponent(n, d), min_exp)
    if exponent > max_exp:
        return miri_encode(fmt, negative, 2**eb - 1, 0)
    scaled_n, scaled_d = miri_pow_scale(n, d, fb - exponent)
    significand = miri_round_quotient_even(scaled_n, scaled_d)
    if significand >= 2 ** (fb + 1):
        significand, exponent = significand // 2, exponent + 1
    if exponent > max_exp:
        return miri_encode(fmt, negative, 2**eb - 1, 0)
    if significand < 2**fb:
        if exponent != min_exp:
            raise MiriError("inconsistentRounding")
        return miri_encode(fmt, negative, 0, significand)
    if significand >= 2 ** (fb + 1):
        raise MiriError("inconsistentRounding")
    return miri_encode(fmt, negative, exponent + bias, significand - 2**fb)


def miri_convert(src: str, bits: int, target: str) -> int:
    negative, value = miri_decode(src, bits)
    ps, pt = FORMATS[src], FORMATS[target]
    if value[0] == "finite":
        return miri_round_ratio(target, negative, value[1], value[2])
    if value[0] == "infinite":
        return miri_encode(target, negative, 2 ** pt["eb"] - 1, 0)
    payload = value[1]
    quiet = payload | 2 ** (ps["fb"] - 1)
    if pt["fb"] >= ps["fb"]:
        payload = quiet * 2 ** (pt["fb"] - ps["fb"])
    else:
        payload = quiet // 2 ** (ps["fb"] - pt["fb"])
    return miri_encode(target, negative, 2 ** pt["eb"] - 1, payload | 2 ** (pt["fb"] - 1))


def miri_from_integer(fmt: str, value: int) -> int:
    return miri_round_ratio(fmt, value < 0, abs(value), 1)


def miri_to_integer(fmt: str, bits: int, width: int, is_signed: bool) -> int:
    if width == 0 or width > 128:
        raise MiriError("invalidIntegerWidth")
    negative, value = miri_decode(fmt, bits)
    min_value = -(2 ** (width - 1)) if is_signed else 0
    max_value = 2 ** (width - 1) - 1 if is_signed else 2**width - 1
    if value[0] == "nan":
        return 0
    if value[0] == "infinite":
        return min_value if negative else max_value
    n, d = value[1], value[2]
    return max(min_value, min(max_value, -(n // d) if negative else n // d))


# ---------------------------------------------------------------------------
# Test vectors
# ---------------------------------------------------------------------------

INT_SPECS = ("i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize")
LEAN_INT_TARGET = {
    "i8": ".signed .i8", "i16": ".signed .i16", "i32": ".signed .i32", "i64": ".signed .i64",
    "i128": ".signed .i128", "isize": ".signed .isize", "u8": ".unsigned .u8",
    "u16": ".unsigned .u16", "u32": ".unsigned .u32", "u64": ".unsigned .u64",
    "u128": ".unsigned .u128", "usize": ".unsigned .usize",
}


def f64_bits(x: float) -> int:
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def f32_bits(x: float) -> int:
    return struct.unpack("<I", struct.pack("<f", x))[0]


def build_vectors(seed: int = 585733184):
    rng = random.Random(seed)
    f64_special = [
        0, 1 << 63, 0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000000,
        0x7FF0000000000001, 0xFFF8000000000123, 0x7FEFFFFFFFFFFFFF, 0x0000000000000001,
        0x000FFFFFFFFFFFFF, 0x0010000000000000, 0x3690000000000000, 0x3690000000000001,
        0xB690000000000000, 0xB690000000000001,
        0x36A8000000000000, 0x47EFFFFFF0000000, 0x47EFFFFFEFFFFFFF, 0x3FF0000010000000,
        0x3FF0000030000000, 0x3FD5555555555555, 0x380000005FFFFFFF, 0x380FFFFFDFFFFFFF,
        0x380FFFFFE0000000,
    ]
    for x in (0.5, -0.5, 1.5, 2.5, -2.5, 2.7, -2.7, 0.999999, -0.999999, 1e-300, 1e300, 255.5,
              -128.5, 127.99, 2.0**31, -2.0**31, 2.0**31 - 0.5, 2.0**63, -2.0**63, 2.0**64,
              2.0**127, -2.0**127, 2.0**128, 1e40, -1e40, 4294967295.5, 65535.9, -32768.9):
        f64_special.append(f64_bits(x))
    f64_random = [rng.getrandbits(64) for _ in range(48)]
    f64_random += [f64_bits(rng.uniform(-3e38, 3e38)) for _ in range(16)]
    f64_random += [f64_bits(rng.uniform(-1e5, 1e5)) for _ in range(16)]
    f64_vals = f64_special + f64_random
    f32_vals = [
        0, 1 << 31, 0x7F800000, 0xFF800000, 0x7FC00000, 0x7F800001, 0xFFC00123, 0x7F7FFFFF,
        0x00000001, 0x007FFFFF, 0x00800000, 0x3F000000, 0xBF000000, 0x4B800000, 0xCF000000,
        0x4F800000, 0x5F000000, 0xDF000000, 0x7F000000, 0xFF000000,
    ] + [rng.getrandbits(32) for _ in range(48)]
    ints = []
    for signed in (False, True):
        for width in (8, 16, 32, 64, 128):
            m = 1 << width
            cands = {0, 1, m - 1, m // 2, m // 2 - 1, m // 2 + 1}
            cands |= {rng.getrandbits(width) for _ in range(10)}
            if width >= 32:
                for base in ((1 << 24), (1 << 53)):
                    for k in (-3, -1, 0, 1, 2, 3):
                        if 0 <= base + k < m:
                            cands.add(base + k)
                        if signed and 0 < base + k < m // 2:
                            cands.add(m - (base + k))
            if width == 64:
                cands.add(0x400000BFFFFFFF)
            if width == 128:
                cands |= {m - (1 << 103), m - (1 << 103) - 1, m - (1 << 104), m - 1}
            for c in sorted(cands):
                ints.append((signed, width, c))
    return f64_vals, f32_vals, ints


# ---------------------------------------------------------------------------
# Lean harness (kernel replay + #eval differential probes)
# ---------------------------------------------------------------------------


def _lean_list(xs) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


def build_harness(source: str, f64_vals, f32_vals, ints) -> tuple[str, list[tuple[str, list]]]:
    probes: list[tuple[str, list]] = []
    lines = [source, ""]
    for name in declared_names(source):
        lines.append(f"#print axioms {name}")
    lines.append(f"namespace {BRIDGE_NAMESPACE}")
    for ours, theirs in MINIRUST_BRIDGES:
        lines.append(
            f"theorem bridge_{theirs} : {NAMESPACE}.{ours} = "
            f"MiniRustSpec.Correspondence.ProvenanceWitness.{theirs} := rfl"
        )
        lines.append(f"#print axioms bridge_{theirs}")
    lines += [f"end {BRIDGE_NAMESPACE}", ""]
    lines += corpus_harness_lines(corpus_bodies())
    lines += ["", "open Trusted.Rustc.V2026_06_01.MirAst", f"open {NAMESPACE}", ""]
    # float -> int
    for fmt, vals in (("binary64", f64_vals), ("binary32", f32_vals)):
        for spec in INT_SPECS:
            for pw in (64, 32) if spec.endswith("size") else (64,):
                tag = f"F2I|{fmt}|{spec}|{pw}"
                pws = ".bits64" if pw == 64 else ".bits32"
                lines.append(
                    f'#eval IO.println ("{tag}|" ++ toString ({_lean_list(vals)}.map '
                    f"(fun b => (evalFloatToIntSaturating .{fmt} b ({LEAN_INT_TARGET[spec]}) {pws}).bits)))"
                )
                probes.append((tag, list(vals)))
    # int -> float
    for fmt in ("binary32", "binary64"):
        tag = f"I2F|{fmt}"
        triples = ", ".join(f"({'true' if s else 'false'}, {w}, {b})" for s, w, b in ints)
        lines.append(
            f'#eval IO.println ("{tag}|" ++ toString ([{triples}].map '
            f"(fun (t : Bool × Nat × Nat) => evalIntToFloatRoundTiesToEven t.1 t.2.1 t.2.2 .{fmt})))"
        )
        probes.append((tag, list(ints)))
    # float -> float
    for src, dst, vals in (("binary64", "binary32", f64_vals), ("binary32", "binary64", f32_vals)):
        tag = f"F2F|{src}|{dst}"
        lines.append(
            f'#eval IO.println ("{tag}|" ++ toString ({_lean_list(vals)}.map '
            f"(fun b => evalFloatToFloatRoundTiesToEven .{src} .{dst} b)))"
        )
        probes.append((tag, list(vals)))
    return "\n".join(lines) + "\n", probes


class _HarnessCache:
    result: subprocess.CompletedProcess[str] | None = None
    probes: list[tuple[str, list]] = []
    vectors = None

    @classmethod
    def get(cls):
        if cls.result is None:
            f64_vals, f32_vals, ints = build_vectors()
            cls.vectors = (f64_vals, f32_vals, ints)
            source = LEAN_FILE.read_text(encoding="utf-8")
            text, cls.probes = build_harness(source, f64_vals, f32_vals, ints)
            with tempfile.TemporaryDirectory(prefix="tcb_div8_proto_") as tmp:
                harness = Path(tmp) / "TcbDiv8ProtoHarness.lean"
                harness.write_text(text, encoding="utf-8")
                cls.result = _run_lean(harness)
        return cls.result


def _parse_probe_outputs(stdout: str) -> dict[str, list[int]]:
    out: dict[str, list[int]] = {}
    for line in stdout.splitlines():
        m = re.match(r"^((?:F2I|I2F|F2F)\|[^\[]*)\|\[(.*)\]\s*$", line.strip())
        if m:
            body = m.group(2).strip()
            out[m.group(1)] = [int(x) for x in body.split(",")] if body else []
    return out


def _parse_axioms(stdout: str) -> dict[str, set[str]]:
    text = re.sub(r"\s+", " ", stdout)
    result: dict[str, set[str]] = {}
    # Names may contain `'` (e.g. `if_pos'`), so match lazily up to the closing quote.
    for m in re.finditer(r"'(\S+?)' depends on axioms: \[([^\]]*)\]", text):
        result[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
    for m in re.finditer(r"'(\S+?)' does not depend on any axioms", text):
        result[m.group(1)] = set()
    return result


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


class TrustedBoundaryTests(unittest.TestCase):
    def test_no_protected_path_edits(self) -> None:
        changed = set(_git("diff", "--name-only", BASE_SHA).split())
        changed |= {line[3:] for line in _git("status", "--porcelain").splitlines() if line}
        offending = sorted(p for p in changed if p.startswith(PROTECTED_PREFIXES))
        self.assertEqual(offending, [], f"protected paths modified: {offending}")

    def test_diff_only_touches_prototype_files(self) -> None:
        changed = set(_git("diff", "--name-only", BASE_SHA).split())
        self.assertTrue(changed <= ALLOWED_DIFF, f"unexpected files in diff: {sorted(changed - ALLOWED_DIFF)}")


class LeanSourceTests(unittest.TestCase):
    def test_forbidden_tokens_absent(self) -> None:
        source = LEAN_FILE.read_text(encoding="utf-8")
        for token in FORBIDDEN_TOKENS:
            self.assertNotIn(token, source, f"forbidden token {token!r} present")

    def test_imports_are_root_lakefile_modules(self) -> None:
        source = LEAN_FILE.read_text(encoding="utf-8")
        imports = re.findall(r"^import\s+(\S+)", source, flags=re.M)
        self.assertIn("Trusted.MirAst", imports)
        self.assertIn("Trusted.MirSemantics", imports)
        for mod in ("ProvenanceWitness", "RefWitness", "TbWitness"):
            self.assertIn(f"MiniRustSpec.Correspondence.{mod}", imports)
        for imp in imports:
            self.assertTrue(imp.startswith(("Trusted.", "MiniRustSpec.", "Anneal.")), imp)

    def test_headline_theorems_declared_and_guarded(self) -> None:
        source = LEAN_FILE.read_text(encoding="utf-8")
        for thm in HEADLINE_THEOREMS:
            self.assertRegex(source, rf"(?m)^theorem {re.escape(thm)}\b", thm)
            guard = re.search(
                rf"/--\s*info:\s*'{re.escape(NAMESPACE)}\.{re.escape(thm)}'\s+"
                rf"(?:depends\s+on\s+axioms:\s*\[(?P<axioms>[^\]]*)\]|does\s+not\s+depend\s+on\s+any\s+axioms)"
                rf"\s*-/\s*\n#guard_msgs\b[^\n]*\bin\s*\n#print axioms {re.escape(thm)}[ \t]*$",
                source,
                flags=re.M,
            )
            self.assertIsNotNone(guard, f"{thm} lacks a `#guard_msgs in #print axioms` block")
            pinned = {a.strip() for a in (guard.group("axioms") or "").split(",") if a.strip()}
            self.assertTrue(pinned <= ALLOWED_AXIOMS, f"{thm} guard pins non-standard axioms {pinned}")

    def test_lean_file_compiles_cleanly(self) -> None:
        proc = _run_lean(LEAN_FILE)
        combined = proc.stdout + proc.stderr
        self.assertEqual(proc.returncode, 0, combined[-4000:])
        self.assertNotRegex(combined, r"\berror\b", combined[-4000:])
        self.assertNotRegex(combined, r"\bwarning\b", combined[-4000:])


class KernelReplayTests(unittest.TestCase):
    def test_harness_runs(self) -> None:
        proc = _HarnessCache.get()
        self.assertEqual(proc.returncode, 0, (proc.stdout + proc.stderr)[-4000:])
        self.assertNotRegex(proc.stdout + proc.stderr, r"\berror\b")

    def test_headline_axioms_standard(self) -> None:
        proc = _HarnessCache.get()
        axioms = _parse_axioms(proc.stdout)
        for thm in HEADLINE_THEOREMS:
            full = f"{NAMESPACE}.{thm}"
            self.assertIn(full, axioms, f"missing #print axioms output for {full}")
            used = axioms[full]
            self.assertFalse(used & BANNED_AXIOMS, f"{full} uses banned axioms {used & BANNED_AXIOMS}")
            self.assertTrue(used <= ALLOWED_AXIOMS, f"{full} uses non-standard axioms {used}")


    def test_every_declaration_axiom_clean(self) -> None:
        proc = _HarnessCache.get()
        axioms = _parse_axioms(proc.stdout)
        names = declared_names(LEAN_FILE.read_text(encoding="utf-8"))
        self.assertGreater(len(names), 200)
        for name in names:
            self.assertIn(name, axioms, f"missing #print axioms output for {name}")
            used = axioms[name]
            self.assertTrue(used <= ALLOWED_AXIOMS, f"{name} uses non-standard axioms {used}")

    def test_minirust_translator_replica_bridges(self) -> None:
        proc = _HarnessCache.get()
        axioms = _parse_axioms(proc.stdout)
        for _, theirs in MINIRUST_BRIDGES:
            full = f"{BRIDGE_NAMESPACE}.bridge_{theirs}"
            self.assertIn(full, axioms, f"bridge {full} failed to elaborate")
            used = axioms[full]
            self.assertTrue(used <= BRIDGE_ALLOWED_AXIOMS, f"{full} uses unexpected axioms {used}")


class CorpusDifferentialTests(unittest.TestCase):
    """Prototype vs. unpatched `Trusted` on every MiniRust witness body, three argument vectors."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.results = _parse_corpus(_HarnessCache.get().stdout)
        cls.bodies = [b.removeprefix(CORPUS_PREFIX) for b in corpus_bodies()]
        cls.keys = [f"{b}#{v}" for b in cls.bodies for v in CORPUS_ARG_VARIANTS]

    def test_every_corpus_body_executed(self) -> None:
        self.assertGreater(len(self.bodies), 200)
        missing = [k for k in self.keys if k not in self.results]
        self.assertEqual(missing, [], f"corpus runs without a result: {missing}")

    def test_no_unexpected_definite_divergence(self) -> None:
        unexpected = {}
        for key, (proto, trusted) in self.results.items():
            if proto != trusted and _definite(proto) and _definite(trusted):
                if EXPECTED_CORPUS_DIVERGENCES.get(key) != (proto, trusted):
                    unexpected[key] = (proto, trusted)
        self.assertEqual(unexpected, {}, f"unexpected prototype/Trusted divergences: {unexpected}")

    def test_expected_divergences_observed(self) -> None:
        for key, expected in EXPECTED_CORPUS_DIVERGENCES.items():
            self.assertEqual(self.results.get(key), expected, key)

    def test_fail_closed_boundary(self) -> None:
        for variant in CORPUS_ARG_VARIANTS:
            fail_closed = {
                key.rsplit("#", 1)[0] for key, (proto, trusted) in self.results.items()
                if key.endswith(f"#{variant}") and not _definite(proto) and _definite(trusted)
            }
            self.assertEqual(sorted(fail_closed - FAIL_CLOSED_CORPUS), [],
                             f"prototype newly fails closed where Trusted is definite (#{variant})")
            self.assertEqual(sorted(FAIL_CLOSED_CORPUS - fail_closed), [],
                             f"stale FAIL_CLOSED_CORPUS entries (#{variant}; shrink the allowlist)")

    def test_kernel_agreement_list_consistent(self) -> None:
        """`corpusAgreementBodies` (`114` single-function bodies) +
        `corpusMultiFnAgreementBodies` (`24` multi-function caller bodies) list *exactly* all
        `138` scalar-argument corpus bodies that agree definitively at the default arguments,
        and `corpusCompositeAgreementBodies` covers the composite-argument bodies."""
        source = LEAN_FILE.read_text(encoding="utf-8")
        m_single = re.search(r"def corpusAgreementBodies : List CapturedMir := \[(.*?)\]", source, re.S)
        m_multi = re.search(r"def corpusMultiFnAgreementBodies : List CapturedMir := \[(.*?)\]", source, re.S)
        m_comp = re.search(r"def corpusCompositeAgreementBodies : List CapturedMir := \[(.*?)\]", source, re.S)
        self.assertIsNotNone(m_single)
        self.assertIsNotNone(m_multi)
        self.assertIsNotNone(m_comp)
        single = [n.strip().removeprefix(CORPUS_PREFIX) for n in m_single.group(1).split(",") if n.strip()]
        multi = [n.strip().removeprefix(CORPUS_PREFIX) for n in m_multi.group(1).split(",") if n.strip()]
        comp = [n.strip().removeprefix(CORPUS_PREFIX) for n in m_comp.group(1).split(",") if n.strip()]
        self.assertEqual(len(single), 114)
        self.assertEqual(len(multi), 24)
        self.assertEqual(len(single), len(set(single)))
        self.assertEqual(len(multi), len(set(multi)))
        self.assertEqual(len(comp), len(set(comp)))
        self.assertEqual(set(single) & set(multi), set())
        self.assertEqual((set(single) | set(multi)) & set(comp), set())
        expected_138 = {
            key.rsplit("#", 1)[0]
            for key, (proto, trusted) in self.results.items()
            if key.endswith("#0") and proto == trusted and _definite(proto)
        }
        self.assertEqual(set(single) | set(multi), expected_138)
        for body in single + multi:
            proto, trusted = self.results[f"{body}#0"]
            self.assertTrue(proto == trusted and _definite(proto), f"{body}: {proto} vs {trusted}")

    def test_no_definite_prototype_result_where_trusted_is_indefinite(self) -> None:
        extra = {
            key: res for key, res in self.results.items()
            if _definite(res[0]) and res[1] in ("none", "other")
        }
        self.assertEqual(extra, {}, f"prototype defines behavior Trusted does not: {extra}")


class Ieee754DifferentialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        proc = _HarnessCache.get()
        cls.outputs = _parse_probe_outputs(proc.stdout)
        cls.probes = dict(_HarnessCache.probes)

    def _lean(self, tag: str) -> list[int]:
        self.assertIn(tag, self.outputs, f"missing Lean probe output {tag}")
        got = self.outputs[tag]
        self.assertEqual(len(got), len(self.probes[tag]))
        return got

    def test_python_reference_matches_struct(self) -> None:
        f64_vals, f32_vals, _ = build_vectors()
        for b in f64_vals:
            kind, _, _ = decode_ref("binary64", b)
            if kind != "nan":
                self.assertEqual(f2f_ref("binary64", "binary32", b), struct_narrow_f64_to_f32(b), hex(b))
        for b in f32_vals:
            kind, _, _ = decode_ref("binary32", b)
            if kind != "nan":
                self.assertEqual(f2f_ref("binary32", "binary64", b), struct_widen_f32_to_f64(b), hex(b))

    def test_python_reference_matches_miri_port(self) -> None:
        f64_vals, f32_vals, ints = build_vectors()
        for src, dst, vals in (("binary64", "binary32", f64_vals), ("binary32", "binary64", f32_vals)):
            for b in vals:
                self.assertEqual(f2f_ref(src, dst, b), miri_convert(src, b, dst), hex(b))
        for signed, width, b in ints:
            v = b - (1 << width) if signed and b >= (1 << (width - 1)) else b
            for fmt in ("binary32", "binary64"):
                self.assertEqual(i2f_ref(signed, width, b, fmt), miri_from_integer(fmt, v))

    def test_float_to_int_matches_reference(self) -> None:
        for tag, vals in self.probes.items():
            if not tag.startswith("F2I"):
                continue
            _, fmt, spec, pw = tag.split("|")
            got = self._lean(tag)
            signed, width = int_target(spec, int(pw))
            for b, g in zip(vals, got):
                self.assertEqual(g, f2i_ref(fmt, b, spec, int(pw)), f"{tag} {hex(b)}")
                self.assertEqual(g, miri_to_integer(fmt, b, width, signed) % (1 << width), f"{tag} {hex(b)}")

    def test_int_to_float_matches_reference(self) -> None:
        for fmt in ("binary32", "binary64"):
            tag = f"I2F|{fmt}"
            got = self._lean(tag)
            for (signed, width, b), g in zip(self.probes[tag], got):
                self.assertEqual(g, i2f_ref(signed, width, b, fmt), f"{tag} {(signed, width, b)}")
                v = b - (1 << width) if signed and b >= (1 << (width - 1)) else b
                if fmt == "binary64":
                    try:
                        self.assertEqual(g, f64_bits(float(v)), f"{tag} {v}")
                    except OverflowError:
                        pass
                elif abs(v) < (1 << 53):
                    self.assertEqual(g, f32_bits(float(v)), f"{tag} {v}")

    def test_float_to_float_matches_reference(self) -> None:
        for src, dst in (("binary64", "binary32"), ("binary32", "binary64")):
            tag = f"F2F|{src}|{dst}"
            got = self._lean(tag)
            for b, g in zip(self.probes[tag], got):
                self.assertEqual(g, f2f_ref(src, dst, b), f"{tag} {hex(b)}")
                self.assertEqual(g, miri_convert(src, b, dst), f"{tag} {hex(b)}")

    def test_brief_witness_values(self) -> None:
        # b/585733184 separation witnesses, signaling-NaN canary, and subnormal/double-rounding canaries.
        self.assertEqual(i2f_ref(False, 32, 16777217, "binary32"), 0x4B800000)
        self.assertEqual(round_ref("binary32", 0, Fraction(16777217), ties_even=False), 0x4B800001)
        self.assertEqual(i2f_ref(False, 32, 16777219, "binary32"), 0x4B800002)
        self.assertEqual(i2f_ref(False, 64, 2**53 + 1, "binary64"), 0x4340000000000000)
        self.assertEqual(f2f_ref("binary64", "binary32", 0x7FF0000000000001), 0x7FC00000)
        self.assertEqual(i2f_ref(False, 128, 2**128 - 1, "binary32"), 0x7F800000)
        # Subnormal single-rounding vs normal-then-subnormal double-rounding
        self.assertEqual(f2f_ref("binary64", "binary32", 0x380000005FFFFFFF), 0x00400001)
        self.assertEqual(f2f_ref("binary64", "binary32", 0x380FFFFFDFFFFFFF), 0x007FFFFF)
        self.assertEqual(f2f_ref("binary64", "binary32", 0x380FFFFFE0000000), 0x00800000)
        # Negative finite gradual underflow to -0.0 vs negative smallest subnormal
        self.assertEqual(f2f_ref("binary64", "binary32", 0xB690000000000000), 0x80000000)
        self.assertEqual(f2f_ref("binary64", "binary32", 0xB690000000000001), 0x80000001)
        # u64 -> f32 direct vs u64 -> f64 -> f32 double-rounding
        self.assertEqual(i2f_ref(False, 64, 0x400000BFFFFFFF, "binary32"), 0x5A800001)
        self.assertEqual(
            f2f_ref("binary64", "binary32", i2f_ref(False, 64, 0x400000BFFFFFFF, "binary64")),
            0x5A800002,
        )

    def test_miri_float_source_pinned(self) -> None:
        text = MIRI_FLOAT.read_text(encoding="utf-8")
        for needle in ("def roundRatio", "def decode", "def convert", "def toInteger", "def fromInteger",
                       "roundQuotientEven"):
            self.assertIn(needle, text)


class DivergenceCoverageTests(unittest.TestCase):
    def test_all_eight_tracked_divergences_addressed(self) -> None:
        tree = ast.parse(SUITE.read_text(encoding="utf-8"))
        items = None
        for node in ast.walk(tree):
            target = None
            if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
                target = node.target.id
            elif isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                target = node.targets[0].id
            if target == "TRACKED_CORRESPONDENCE_DIVERGENCES":
                items = ast.literal_eval(node.value)
        self.assertIsNotNone(items)
        ids = [it["id"] for it in items if it["category"] == "actionable_anneal_bug"]
        self.assertEqual(len(ids), 8, ids)
        lean = LEAN_FILE.read_text(encoding="utf-8")
        report = REPORT.read_text(encoding="utf-8")
        for div_id in ids:
            self.assertIn(div_id, lean, f"{div_id} missing from Lean file")
            self.assertIn(div_id, report, f"{div_id} missing from PROTOTYPE_REPORT.md")


if __name__ == "__main__":
    unittest.main()
