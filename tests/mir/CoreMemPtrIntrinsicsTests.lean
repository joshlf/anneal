/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Anneal.Mir.CoreMemPtrIntrinsicsBundle
import MiniRustSpec.CoreMemPtrIntrinsicsMR
import Trusted.Rustc.V2026_08_01.MirSemantics.Machine

/-!
# Episode 2 Dual-Authority Correspondence Tests & Cross-Root Kernel Bridge
# (the 8 core memory & pointer intrinsics)

Verifies `core::intrinsics::{copy, compare_bytes, raw_eq,
typed_swap_nonoverlapping, ptr_offset_from, ptr_offset_from_unsigned, ptr_mask,
black_box}` end-to-end across all three authorities:

1. **Root-Lake witnesses**: positive, UB, flip-direction, and mode-sensitivity
   witnesses on Trusted Anneal (`stepMirFn`) and MiniRust (`Mach`/`MachTB`);
   edge cases on Trusted (`copy` null/misaligned at `count = 0`, `compare_bytes`
   null at `bytes = 0`, `typed_swap_nonoverlapping` overlap and invalid `bool`
   (`kani#5205`), `ptr_mask` without `exposedAllocIds` mutation, diverging calls
   to returning intrinsics); and `V2026_06_01` <-> `V2026_08_01` dialect parity
   on the corpus fixtures (re-elaborated in the `V2026_08_01` AST and executed
   by `Trusted.Rustc.V2026_08_01.MirSemantics.stepMirFn`).
2. **Cross-root kernel bridge (`run_cmd`)**: loads `.lake/build/lib/lean`
   (`Anneal.Mir.CoreMemPtrIntrinsicsBundle`, `MiniRustSpec.CoreMemPtrIntrinsicsMR`)
   and `examples/.lake/build/lib/lean` (`LeanMiriSpec.CoreMemPtrIntrinsicsLM`)
   into one kernel environment, builds the LeanMiri `ObsAuthority` directly over
   `LeanMiriSpec.CoreMemPtrIntrinsicsLM.cmLmObserve`, and kernel-checks the
   unified and all 8 per-intrinsic `DualCorrespondenceBundle`s, the lifted
   theorems, `Eq.refl` locks of all 18 shared fixtures, negative controls each
   paired with an accepted positive control, transitive reachability of
   `Trusted` (`stepMirFn` + the 7 `eval*Call` evaluators), `MiniRustSpec.Interp`,
   and vendored `Miri.Interpreter.{Step.step, Intrinsics.eval}`, and the axiom /
   non-triviality audit.
3. **Constructive audit** of the bundle (`[propext, Quot.sound]`).
-/

/-! ## §0. `V2026_08_01` Renderings of the Corpus Fixtures (dialect parity, §1) -/

namespace Anneal.Mir.CoreMemPtrIntrinsicsTests.V08

open Trusted.Rustc.V2026_08_01 Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-- The `V2026_08_01` rendering of the corpus body builder. -/
def body08 (name : String) (decls : List MirAst.Ty) (argCount : Nat) (f : String)
    (tys : List RigidTy) (args : List Operand) (dest : Nat) (after : List MirAst.Statement)
    (allocs : List CapturedAllocation) : CapturedMir :=
  { defPath := name, phase := .runtimePostCleanup, role := .subject, argCount,
    localDecls := decls.map fun ty => { mutability := .mut, ty, debugName := none },
    basicBlocks :=
      [{ statements := [],
         terminator := { kind := .call (.constant { ty := { kind := .fnDef f tys, layoutIdx := 0 },
                                                       val := .zeroSized })
                                  args { local_ := dest, projection := [] } (some 1) .continue_,
                         span := "ep2.rs:1:1" },
         isCleanup := false },
       { statements := after, terminator := { kind := .return_, span := "ep2.rs:1:1" },
         isCleanup := false }],
    layouts := emptyLayoutTable, allocations := allocs,
    fnAbi := { args := [], ret := { layout := { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .scalar (.initialized (.int 8 true) ⟨0, 255⟩), fields := .primitive, variants := .single 0, isUninhabited := false }, mode := .direct },
               conv := .rust, canUnwind := true } }

def ty (k : RigidTy) : MirAst.Ty := { kind := k, layoutIdx := 0 }
def loc (i : Nat) (proj : List ProjectionElem := []) : Place := { local_ := i, projection := proj }
def usz (n : Nat) : Operand := .constant { ty := ty (.uint .usize), val := .scalar (.int ⟨n, 8⟩) }
def glob (aid : Nat) (bytes : List (Option UInt8)) (al : Nat := 4) : CapturedAllocation :=
  { allocId := aid, bytes, relocations := [], align := ⟨al⟩, mutability := .mut }
def readDeref (i : Nat) : MirAst.Statement :=
  { kind := .assign (loc 0) (.use (.copy (loc i [.deref]))), span := "ep2.rs:1:1" }

def copy08 : CapturedMir :=
  body08 "cm::copy_u32" [ty (.uint .u32), ty (.rawPtr .not (.uint .u32)), ty (.rawPtr .mut (.uint .u32)),
    ty (.tuple [])] 2 "core::intrinsics::copy" [.uint .u32] [.copy (loc 1), .copy (loc 2), usz 1] 3
    [readDeref 2] [glob 100 [some 42, some 0, some 0, some 0], glob 101 [some 1, some 2, some 3, some 4]]
def cmp08 : CapturedMir :=
  body08 "cm::compare_bytes_3" [ty (.int .i32), ty (.rawPtr .not (.uint .u8)), ty (.rawPtr .not (.uint .u8))] 2
    "core::intrinsics::compare_bytes" [] [.copy (loc 1), .copy (loc 2), usz 3] 0 []
    [glob 100 [some 1, some 2, some 3] 1, glob 101 [some 1, some 2, some 4] 1, glob 102 [some 2, some 0, none] 1]
def rawEq08 : CapturedMir :=
  body08 "cm::raw_eq_u32" [ty .bool, ty (.ref .not (.uint .u32)), ty (.ref .not (.uint .u32))] 2
    "core::intrinsics::raw_eq" [.uint .u32] [.copy (loc 1), .copy (loc 2)] 0 []
    [glob 100 [some 7, some 0, some 0, some 0], glob 101 [some 7, some 0, some 0, some 0],
     glob 103 [some 7, none, some 0, some 0]]
def swap08 : CapturedMir :=
  body08 "cm::typed_swap_read_x" [ty (.uint .u32), ty (.rawPtr .mut (.uint .u32)), ty (.rawPtr .mut (.uint .u32)),
    ty (.tuple [])] 2 "core::intrinsics::typed_swap_nonoverlapping" [.uint .u32] [.copy (loc 1), .copy (loc 2)] 3
    [readDeref 1] [glob 100 [some 7, some 0, some 0, some 0], glob 101 [some 9, some 0, some 0, some 0]]
def pof08 (unsigned : Bool) : CapturedMir :=
  body08 "cm::pof" [ty (if unsigned then .uint .usize else .int .isize), ty (.rawPtr .not (.uint .u32)),
    ty (.rawPtr .not (.uint .u32))] 2
    (if unsigned then "core::intrinsics::ptr_offset_from_unsigned" else "core::intrinsics::ptr_offset_from")
    [.uint .u32] [.copy (loc 1), .copy (loc 2)] 0 [] [glob 100 (List.replicate 16 (some 0)), glob 101 (List.replicate 16 (some 0))]
def mask08 : CapturedMir :=
  body08 "cm::ptr_mask_not7" [ty (.rawPtr .not (.uint .u32)), ty (.rawPtr .not (.uint .u32))] 1
    "core::intrinsics::ptr_mask" [.uint .u32] [.copy (loc 1), usz (2 ^ 64 - 8)] 0 [] [glob 100 (List.replicate 16 (some 0)) 16]
def bb08 : CapturedMir :=
  body08 "cm::black_box_u32" [ty (.uint .u32), ty (.uint .u32)] 1 "core::intrinsics::black_box" [.uint .u32]
    [.copy (loc 1)] 0 [] []

/-- Initial `V2026_08_01` state with all locals live. -/
def init08 (body : CapturedMir) (args : List Value) : MachineState :=
  let base := initMachineState body args
  { base with frame := { base.frame with locals := base.frame.locals.map fun
      | .dead => .uninit
      | slot => slot } }

/-- Bounded `V2026_08_01` `stepMirFn` run, observed in the shared observation type. -/
def run08 (body : CapturedMir) : Nat → MachineState → MiniRustSpec.CoreMemPtrIntrinsicsMR.CmTrustedObs
  | 0, _ => .stuck
  | n + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => run08 body n s'
    | .ret (.normal r) =>
      match r.1 with
      | .scalar sc => .scalar sc.bits sc.sizeBytes
      | .ptr p 8 => .ptr p.allocId p.offsetBytes
      | _ => .stuck
    | .vis (.inl (.fail .ub)) _ => .ub
    | .vis (.inl (.fail .unsupported)) _ => .unsupported
    | _ => .stuck

def gp (aid off : Nat) : Value := .ptr ⟨aid, off⟩ 8

end Anneal.Mir.CoreMemPtrIntrinsicsTests.V08

namespace Anneal.Mir.CoreMemPtrIntrinsicsTests

open Anneal.DualCorrespondenceBundle
open Anneal.Mir.CoreMemPtrIntrinsicsBundle
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.UnwindSetDiscrAndFnPtrMR
open MiniRustSpec.CoreMemPtrIntrinsicsMR

/-! ## §1. Root-Lake Witnesses -/

/-- Constructive codec laws & tight validity witness for `cmCodec`. -/
theorem cm_codec_constructive_laws :
    cmCodec.decode (cmCodec.encode (.scalar 42 4)) = some (.scalar 42 4) ∧
    cmCodec.decode (cmCodec.encode (.ptr 100 8)) = some (.ptr 100 8) ∧
    cmCodec.decode (7, 0, 0) = none ∧
    cmCodec.TightValidRep :=
  ⟨rfl, rfl, rfl, cmCodec_tight⟩

/-- Every one of the 8 intrinsics has a non-vacuous positive normal return AND a
non-vacuous UB fault on BOTH Trusted Anneal and MiniRust (each conjunct
evaluated by the kernel running `stepMirFn`, respectively `Interp.steps`). -/
theorem cm_all_8_intrinsics_flip_verdict :
    ∀ v : CmVariant,
      (∃ a, cmAnnealEval .basic v .okPrimary () = some (.returns a) ∧
            mrAuthority.verdict (.basic, v, .okPrimary) = some (.returns a)) ∧
      cmAnnealEval .basic v .ubFault () = some .undefinedBehavior ∧
      mrAuthority.verdict (.basic, v, .ubFault) = some .undefinedBehavior := by
  intro v
  cases v with
  | copy => exact ⟨⟨.scalar 42 4, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | compareBytes =>
    exact ⟨⟨.scalar 0xFFFFFFFF 4, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | rawEq => exact ⟨⟨.scalar 1 1, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | typedSwap => exact ⟨⟨.scalar 9 4, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | ptrOffsetFrom => exact ⟨⟨.scalar 2 8, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | ptrOffsetFromUnsigned =>
    exact ⟨⟨.scalar 2 8, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | ptrMask => exact ⟨⟨.ptr 100 8, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩
  | blackBox => exact ⟨⟨.scalar 77 4, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩

/-- Genuine mode sensitivity across Trusted Anneal and MiniRust on `copy`:
`basic` / `BasicMemory` returns `42` while `protectedTB` / `TreeBorrowsMemory`
faults. -/
theorem cm_copy_mode_sensitivity_root :
    cmAnnealEval .basic .copy .modeCase () = some (.returns (.scalar 42 4)) ∧
    mrAuthority.verdict (.basic, .copy, .modeCase) = some (.returns (.scalar 42 4)) ∧
    cmAnnealEval .protectedTB .copy .modeCase () = some .undefinedBehavior ∧
    mrAuthority.verdict (.protectedTB, .copy, .modeCase) = some .undefinedBehavior ∧
    (mrSide.flipW cmModel mrSide_check).isSome = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   mr_modeSensitivity_present⟩

/-- Both root-Lake authorities realize the frozen 64-key verdict table. -/
theorem cm_two_authority_table_root (mode : CmMode) (v : CmVariant) (c : CmCase) :
    cmAnnealEval mode v c () = cmExpectedVerdict mode v c ∧
    mrAuthority.verdict (mode, v, c) = cmExpectedVerdict mode v c :=
  ⟨cmAnnealEval_eq mode v c (), mrAuthority_verdict_eq mode v c⟩

/-- Re-exported MR universal laws and witnesses (reachable from this module). -/
theorem cm_mr_deep_theorems_used :
    cmMrObsDictDistinct = true ∧
    cmMrObserve .basicMemory .copy .modeCase =
      .retBytes ((scalarBytes cmU32It 42).map (projByteTB ∘ liftByteTB)) ∧
    cmMrObserve .treeBorrows .copy .modeCase = .ub := by
  have _ := @cm_classify_core_mem_ptr_intrinsics
  have _ := @cm_evalCoreMemPtrIntrinsicCall?_routes
  have _ := @cm_compareUnsignedBytesI32_refl
  have _ := @cm_compareUnsignedBytesI32_range
  have _ := @cm_compareUnsignedBytesI32_antisymm
  have _ := @cm_evalPtrOffsetFromDistance_same_offset
  have _ := @cm_evalPtrOffsetFromDistance_zst
  have _ := @cm_evalPtrOffsetFromDistance_unsigned_negative
  have _ := @cm_evalPtrOffsetFromDistance_exact
  have _ := @cm_divExact_byte_distance
  have _ := @cm_copy_three_way_witness
  have _ := @cm_compareBytes_three_way_witness
  have _ := @cm_rawEq_three_way_witness
  have _ := @cm_typedSwap_three_way_witness
  have _ := @cm_ptrOffsetFrom_three_way_witness
  have _ := @cm_ptrOffsetFromUnsigned_three_way_witness
  have _ := @cm_ptrMask_three_way_witness
  have _ := @cm_blackBox_three_way_witness
  have _ := @cmTrustedObserve_table
  have _ := @cmMrObserveClass_table
  have _ := @cm_variant_outcomes_distinct
  exact ⟨cmMrObsDict_distinct, cmMrObserve_copy_mode_sensitivity.1,
    cmMrObserve_copy_mode_sensitivity.2⟩

/-! ### Trusted edge cases (`V2026_06_01`) -/

/-- Run `stepMirFn` and observe the returned memory's exposed allocation ids. -/
def cmRunTrustedExposed (body : CapturedMir) : Nat → MachineState → Option (List Nat)
  | 0, _ => none
  | n + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => cmRunTrustedExposed body n s'
    | .ret (.normal r) => some r.2.exposedAllocIds
    | _ => none

/-- A diverging (`target = none`) call to a returning intrinsic. -/
def cmRawEqDivergingMir : CapturedMir :=
  { mkMirBody "cm::raw_eq_diverging" [mkDecl boolMirTy, mkDecl cmRefU32Ty, mkDecl cmRefU32Ty] 2
      [mkBb [] (.call (cmIntrinsicOp "core::intrinsics::raw_eq" [.uint .u32])
        [.copy (locPlace 1), .copy (locPlace 2)] (locPlace 0) none .continue_)] with
    allocations := [cmGlobal 100 (cmU32Bytes 7), cmGlobal 101 (cmU32Bytes 7)] }

/-- `typed_swap_nonoverlapping::<bool>` over a global holding an invalid `bool`
(`2`) and a valid one. -/
def cmSwapBoolMir : CapturedMir :=
  cmCallBody "cm::typed_swap_bool"
    [mkDecl boolMirTy, mkDecl { kind := .rawPtr .mut .bool, layoutIdx := 0 },
     mkDecl { kind := .rawPtr .mut .bool, layoutIdx := 0 }, mkDecl unitMirTy] 2
    (cmIntrinsicOp "core::intrinsics::typed_swap_nonoverlapping" [.bool])
    [.copy (locPlace 1), .copy (locPlace 2)] 3
    [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.deref]))))]
    [cmGlobal 100 [some 2] 1, cmGlobal 101 [some 1] 1]

/-- `compare_bytes(_1, _2, 0)`. -/
def cmCmpBytes0Mir : CapturedMir :=
  cmCallBody "cm::compare_bytes_0"
    [mkDecl i32MirTy, mkDecl cmRawConstU8Ty, mkDecl cmRawConstU8Ty] 2
    (cmIntrinsicOp "core::intrinsics::compare_bytes" [])
    [.copy (locPlace 1), .copy (locPlace 2), cmUsizeConst 0] 0 [] []

/-- `copy::<u32>(_1, _2, 0); _0 = 7u32`. -/
def cmCopy0Mir : CapturedMir :=
  cmCallBody "cm::copy_0"
    [mkDecl u32MirTy, mkDecl rawConstU32MirTy, mkDecl rawMutU32MirTy, mkDecl unitMirTy] 2
    (cmIntrinsicOp "core::intrinsics::copy" [.uint .u32])
    [.copy (locPlace 1), .copy (locPlace 2), cmUsizeConst 0] 3
    [mkSt (.assign (locPlace 0) (.use (.constant { ty := u32MirTy, val := .scalar (.int ⟨7, 4⟩) })))]
    []

/-- **Trusted edge cases on `stepMirFn`**:
1. `copy::<u32>` with null pointers at `count = 0` completes (alignment checked,
   validity exempted); with a misaligned source at `count = 0` it is UB;
2. `compare_bytes` with null pointers at `bytes = 0` is UB (deliberate delta);
3. `typed_swap_nonoverlapping::<u32>` on overlapping ranges (`&G[0]`, `&G[2]`)
   is UB, while disjoint elements of one allocation swap (corpus `modeCase`);
4. `typed_swap_nonoverlapping::<bool>` with an invalid `bool` (`2`) is UB
   (`kani#5205` typed validity);
5. `ptr_mask` returns a pointer with the SAME provenance and leaves
   `exposedAllocIds` empty (no `expose`, `ucg#630`);
6. a diverging (`target = none`) call to the returning intrinsic `raw_eq` is UB. -/
theorem cm_trusted_edge_cases :
    cmRunTrusted cmCopy0Mir 8 (cmInitLiveState cmCopy0Mir [cmIntPtr 0, cmIntPtr 0]) = .scalar 7 4 ∧
    cmRunTrusted cmCopy0Mir 8 (cmInitLiveState cmCopy0Mir [cmIntPtr 2, cmIntPtr 0]) = .ub ∧
    cmRunTrusted cmCmpBytes0Mir 8 (cmInitLiveState cmCmpBytes0Mir [cmIntPtr 0, cmIntPtr 0]) = .ub ∧
    cmRunTrusted cmSwapSameAllocMir 8
      (cmInitLiveState cmSwapSameAllocMir [cmGPtr 100 0, cmGPtr 100 2]) = .ub ∧
    cmRunTrusted cmSwapBoolMir 8 (cmInitLiveState cmSwapBoolMir [cmGPtr 100 0, cmGPtr 101 0]) = .ub ∧
    cmRunTrustedExposed cmMaskAlign8Mir 8 (cmInitLiveState cmMaskAlign8Mir [cmGPtr 100 12]) = some [] ∧
    cmRunTrusted cmRawEqDivergingMir 8
      (cmInitLiveState cmRawEqDivergingMir [cmGPtr 100 0, cmGPtr 101 0]) = .ub := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### `V2026_06_01` <-> `V2026_08_01` dialect parity -/


/-- **`V2026_06_01` <-> `V2026_08_01` parity**: the `V2026_08_01` dialect's
`stepMirFn`, run on the `V2026_08_01` rendering of the corpus fixtures, yields
exactly the `V2026_06_01` corpus observations (`cmTrustedObserve`) for all 8
intrinsics, on positive and UB keys. -/
theorem cm_v2026_08_01_parity :
    V08.run08 V08.copy08 8 (V08.init08 V08.copy08 [V08.gp 100 0, V08.gp 101 0]) =
      cmTrustedObserve false .copy .okPrimary ∧
    V08.run08 V08.copy08 8 (V08.init08 V08.copy08 [.ptr ⟨0, 0⟩ 8, V08.gp 101 0]) =
      cmTrustedObserve false .copy .ubFault ∧
    V08.run08 V08.cmp08 8 (V08.init08 V08.cmp08 [V08.gp 100 0, V08.gp 101 0]) =
      cmTrustedObserve false .compareBytes .okPrimary ∧
    V08.run08 V08.cmp08 8 (V08.init08 V08.cmp08 [V08.gp 102 0, V08.gp 101 0]) =
      cmTrustedObserve false .compareBytes .ubFault ∧
    V08.run08 V08.rawEq08 8 (V08.init08 V08.rawEq08 [V08.gp 100 0, V08.gp 101 0]) =
      cmTrustedObserve false .rawEq .okPrimary ∧
    V08.run08 V08.rawEq08 8 (V08.init08 V08.rawEq08 [V08.gp 103 0, V08.gp 101 0]) =
      cmTrustedObserve false .rawEq .ubFault ∧
    V08.run08 V08.swap08 8 (V08.init08 V08.swap08 [V08.gp 100 0, V08.gp 101 0]) =
      cmTrustedObserve false .typedSwap .okPrimary ∧
    V08.run08 (V08.pof08 false) 8 (V08.init08 (V08.pof08 false) [V08.gp 100 4, V08.gp 100 12]) =
      cmTrustedObserve false .ptrOffsetFrom .okSecondary ∧
    V08.run08 (V08.pof08 false) 8 (V08.init08 (V08.pof08 false) [V08.gp 100 4, V08.gp 101 12]) =
      cmTrustedObserve false .ptrOffsetFrom .ubFault ∧
    V08.run08 (V08.pof08 true) 8 (V08.init08 (V08.pof08 true) [V08.gp 100 4, V08.gp 100 12]) =
      cmTrustedObserve false .ptrOffsetFromUnsigned .ubFault ∧
    V08.run08 V08.mask08 8 (V08.init08 V08.mask08 [V08.gp 100 12]) =
      cmTrustedObserve false .ptrMask .okPrimary ∧
    V08.run08 V08.bb08 8 (V08.init08 V08.bb08 [.scalar ⟨77, 4⟩]) =
      cmTrustedObserve false .blackBox .okPrimary ∧
    V08.run08 V08.bb08 8 (V08.init08 V08.bb08 []) =
      cmTrustedObserve false .blackBox .ubFault := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **Episode 2 Root Capstone**: the root-Lake projection of
`ep2_core_mem_ptr_intrinsics_capstone` for EVERY LeanMiri authority passing the
unified 64-key check. -/
theorem ep2_core_mem_ptr_intrinsics_root_capstone
    (lmAuth : Anneal.Mir.DropBinderAndSubtypeBundle.Corpus.ObsAuthority CmKey CmObsVal)
    (hLM : lmCheckOf lmAuth = true) :
    cmCodec.TightValidRep ∧
    mrAuthority.denoteConsistent = true ∧
    mrSide.check cmModel = true ∧
    (∀ v, (mrVariantSide v).check cmModel = true) ∧
    (mrSide.flipW cmModel mrSide_check).isSome = true ∧
    ((lmSideOf lmAuth).flipW cmModel hLM).isSome = true ∧
    (∀ (mMR : CmMrMode) (mLM : Bool) (p : CmVariant) (q : CmCase),
      ExactBehaviorEq (bundleOf lmAuth hLM).mrRel mMR p q ∧
      ExactBehaviorEq (bundleOf lmAuth hLM).lmRel mLM p q) ∧
    cmMrObsDictDistinct = true := by
  obtain ⟨hTight, hDen, hSide, hVar, _, _, hExact, hMrFlip, hLmFlip, _, _⟩ :=
    ep2_core_mem_ptr_intrinsics_capstone lmAuth hLM
  exact ⟨hTight, hDen, hSide, hVar, hMrFlip, hLmFlip, hExact, cmMrObsDict_distinct⟩

/-! ## §2. Cross-Root Dual-Authority Kernel Bridge (`MiniRustSpec` + `LeanMiriSpec`) -/

open Lean Elab Command Meta in
run_cmd do
  let opts := (← getOptions).setBool `Elab.async false
  let sp : SearchPath := [System.FilePath.mk ".lake/build/lib/lean",
                          System.FilePath.mk "examples/.lake/build/lib/lean"]
  initSearchPath (← findSysroot) sp
  let baseEnv ← importModules
    #[{ module := `Anneal.Mir.CoreMemPtrIntrinsicsBundle },
      { module := `MiniRustSpec.CoreMemPtrIntrinsicsMR },
      { module := `LeanMiriSpec.CoreMemPtrIntrinsicsLM }]
    {} 0
  let ns := `Anneal.Mir.CoreMemPtrIntrinsicsTests.CrossRoot
  let bNs := `Anneal.Mir.CoreMemPtrIntrinsicsBundle
  let cNs := `Anneal.Mir.DropBinderAndSubtypeBundle.Corpus
  let mrNs := `MiniRustSpec.CoreMemPtrIntrinsicsMR
  let lmNs := `LeanMiriSpec.CoreMemPtrIntrinsicsLM
  let act : CoreM (Nat × Nat × Nat × Nat × Array Name) := do
    let addDef (name : Name) (val : Expr) : CoreM Expr := do
      let ty ← MetaM.run' <| inferType val
      addDecl <| .defnDecl {
        name, levelParams := [], type := ty, value := val,
        hints := .regular 0, safety := .safe }
      return ty
    let addThm (name : Name) (ty pf : Expr) : CoreM Unit := do
      addDecl <| .thmDecl { name, levelParams := [], type := ty, value := pf }
    let boolTy := mkConst ``Bool
    let boolTrue := mkConst ``Bool.true
    let boolFalse := mkConst ``Bool.false
    let natTy := mkConst ``Nat
    let eqTrue (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e boolTrue
    let reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [1]) boolTy boolTrue
    let eqFalse (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e boolFalse
    let reflFalse : Expr := mkApp2 (mkConst ``Eq.refl [1]) boolTy boolFalse

    -- Encoders from `CmVariant` / `CmCase` to the Nat indices of `cmLmObserve`.
    let mkVariantToNat : MetaM Expr := do
      let varTy := mkConst (mrNs ++ `CmVariant)
      withLocalDeclD `v varTy fun v => do
        let recApp := mkAppN (mkConst (mrNs ++ `CmVariant.rec) [1])
          #[mkLambda `x .default varTy natTy,
            mkNatLit 0, mkNatLit 1, mkNatLit 2, mkNatLit 3, mkNatLit 4, mkNatLit 5, mkNatLit 6,
            mkNatLit 7, v]
        mkLambdaFVars #[v] recApp
    let mkCaseToNat : MetaM Expr := do
      let caseTy := mkConst (mrNs ++ `CmCase)
      withLocalDeclD `c caseTy fun c => do
        let recApp := mkAppN (mkConst (mrNs ++ `CmCase.rec) [1])
          #[mkLambda `x .default caseTy natTy, mkNatLit 0, mkNatLit 1, mkNatLit 2, mkNatLit 3, c]
        mkLambdaFVars #[c] recApp
    let varToNatName := ns ++ `variantToNat
    let caseToNatName := ns ++ `caseToNat
    let _ ← addDef varToNatName (← MetaM.run' mkVariantToNat)
    let _ ← addDef caseToNatName (← MetaM.run' mkCaseToNat)

    -- 1. The genuine LeanMiri `ObsAuthority CmKey CmObsVal` over `cmLmObserve`.
    let keyTy := mkConst (bNs ++ `CmKey)
    let obsValTy := mkConst (bNs ++ `CmObsVal)
    let lmObsTy := mkConst (lmNs ++ `CmLmObs)
    let verdTy := mkApp (mkConst (cNs ++ `Verdict)) obsValTy
    let mkRet (v : Expr) : Expr := mkApp2 (mkConst (cNs ++ `Verdict.returns)) obsValTy v
    let mkSc (b s : Nat) : Expr := mkRet (mkApp2 (mkConst (bNs ++ `CmObsVal.scalar)) (mkNatLit b) (mkNatLit s))
    let mkPtr (a o : Nat) : Expr := mkRet (mkApp2 (mkConst (bNs ++ `CmObsVal.ptr)) (mkNatLit a) (mkNatLit o))
    let mkScO (b s : Nat) : Expr := mkApp2 (mkConst (lmNs ++ `CmLmObs.scalar)) (mkNatLit b) (mkNatLit s)
    let mkPtrO (a o : Nat) : Expr := mkApp2 (mkConst (lmNs ++ `CmLmObs.ptr)) (mkNatLit a) (mkNatLit o)
    let mkPair (a b : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [0, 0]) verdTy lmObsTy a b
    let mkLmAuth (invertMode : Bool := false) (collideDenote : Bool := false) : MetaM Expr := do
      let decLmObs := mkConst (lmNs ++ `instDecidableEqCmLmObs)
      let observeFn ← withLocalDeclD `k keyTy fun k => do
        let mExpr := mkProj ``Prod 0 k
        let rest := mkProj ``Prod 1 k
        let vExpr := mkProj ``Prod 0 rest
        let cExpr := mkProj ``Prod 1 rest
        let tb0 := mkApp (mkConst (bNs ++ `cmModeToLmTreeBorrows)) mExpr
        let tb := if invertMode then mkApp (mkConst ``Bool.not) tb0 else tb0
        let call := mkApp3 (mkConst (lmNs ++ `cmLmObserve)) tb
          (mkApp (mkConst varToNatName) vExpr) (mkApp (mkConst caseToNatName) cExpr)
        mkLambdaFVars #[k] (mkApp2 (mkConst ``Option.some [0]) lmObsTy call)
      let entries : List Expr :=
        [ mkPair (mkSc 42 4) (mkScO 42 4),
          mkPair (mkSc 0x08070403 4) (mkScO 0x08070403 4),
          mkPair (mkSc 0xFFFFFFFF 4) (mkScO 0xFFFFFFFF 4),
          mkPair (mkSc 1 4) (mkScO 1 4),
          mkPair (mkSc 0 4) (mkScO 0 4),
          mkPair (mkSc 1 1) (mkScO 1 1),
          mkPair (mkSc 0 1) (if collideDenote then mkScO 1 1 else mkScO 0 1),
          mkPair (mkSc 9 4) (mkScO 9 4),
          mkPair (mkSc 7 4) (mkScO 7 4),
          mkPair (mkSc 6 4) (mkScO 6 4),
          mkPair (mkSc 2 8) (mkScO 2 8),
          mkPair (mkSc (2 ^ 64 - 2) 8) (mkScO (2 ^ 64 - 2) 8),
          mkPair (mkSc 0 8) (mkScO 0 8),
          mkPair (mkSc 4 8) (mkScO 4 8),
          mkPair (mkPtr 100 8) (mkPtrO 100 1032),
          mkPair (mkPtr 100 12) (mkPtrO 100 1036),
          mkPair (mkPtr 100 4) (mkPtrO 100 1028),
          mkPair (mkSc 77 4) (mkScO 77 4),
          mkPair (mkApp (mkConst (cNs ++ `Verdict.undefinedBehavior)) obsValTy)
            (mkConst (lmNs ++ `CmLmObs.ub)),
          mkPair (mkApp (mkConst (cNs ++ `Verdict.unsupported)) obsValTy)
            (mkConst (lmNs ++ `CmLmObs.unsupported)) ]
      let pairTy := mkApp2 (mkConst ``Prod [0, 0]) verdTy lmObsTy
      let denoteList := entries.foldr (fun h t => mkApp3 (mkConst ``List.cons [0]) pairTy h t)
        (mkApp (mkConst ``List.nil [0]) pairTy)
      return mkApp6 (mkConst (cNs ++ `ObsAuthority.mk))
        keyTy obsValTy lmObsTy decLmObs observeFn denoteList

    let lmAuthName := ns ++ `lmAuthority
    let _ ← addDef lmAuthName (← MetaM.run' <| mkLmAuth false false)
    let lmAuthC := mkConst lmAuthName
    let mut added : Array Name := #[varToNatName, caseToNatName, lmAuthName]

    -- 2. Kernel-checked `denoteConsistent`, unified `lmSide_check`, lifted theorems.
    let decObsVal := mkConst (bNs ++ `instDecidableEqCmObsVal)
    let denoteConsExpr := mkApp4 (mkConst (cNs ++ `ObsAuthority.denoteConsistent))
      keyTy obsValTy decObsVal lmAuthC
    let denoteConsName := ns ++ `lmAuthority_denoteConsistent
    addThm denoteConsName (eqTrue denoteConsExpr) reflTrue
    added := added.push denoteConsName
    let lmCheckName := ns ++ `lmSide_check
    addThm lmCheckName (eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) lmAuthC)) reflTrue
    added := added.push lmCheckName
    let unifiedBundleName := ns ++ `unifiedDualBundle
    let unifiedTy ← addDef unifiedBundleName
      (mkApp2 (mkConst (bNs ++ `bundleOf)) lmAuthC (mkConst lmCheckName))
    unless unifiedTy.getAppFn.isConstOf ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle do
      throwError "cross-root: {unifiedBundleName} is not a DualCorrespondenceBundle"
    added := added.push unifiedBundleName
    for thmName in [`threeWayNormalAgreement, `crossAuthorityFaultEquiv,
                    `exactBehaviorEq_both, `lm_modeSensitivity_present,
                    `ep2_core_mem_ptr_intrinsics_capstone] do
      let val := mkApp2 (mkConst (bNs ++ thmName)) lmAuthC (mkConst lmCheckName)
      let ty ← MetaM.run' <| inferType val
      addThm (ns ++ thmName) ty val
      added := added.push (ns ++ thmName)
    let unifiedC := mkConst unifiedBundleName
    let projPosVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectPositive #[unifiedC]
    addThm (ns ++ `unified_projectPositive) (← MetaM.run' <| inferType projPosVal) projPosVal
    added := added.push (ns ++ `unified_projectPositive)
    let projFaultVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectFault #[unifiedC]
    addThm (ns ++ `unified_projectFault) (← MetaM.run' <| inferType projFaultVal) projFaultVal
    added := added.push (ns ++ `unified_projectFault)

    -- All 8 per-intrinsic bundles, claims, and projections.
    let variantCtors : List Name :=
      [`copy, `compareBytes, `rawEq, `typedSwap, `ptrOffsetFrom, `ptrOffsetFromUnsigned,
       `ptrMask, `blackBox]
    let mut bundleCount : Nat := 1
    for vc in variantCtors do
      let vConst := mkConst (mrNs ++ `CmVariant ++ vc)
      let chkName := ns ++ `variantCheck ++ vc
      addThm chkName (eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf)) vConst lmAuthC)) reflTrue
      added := added.push chkName
      let vbName := ns ++ `variantBundle ++ vc
      let vbTy ← addDef vbName
        (mkApp3 (mkConst (bNs ++ `variantBundleOf)) vConst lmAuthC (mkConst chkName))
      unless vbTy.getAppFn.isConstOf ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle do
        throwError "cross-root: {vbName} is not a DualCorrespondenceBundle"
      added := added.push vbName
      bundleCount := bundleCount + 1
      let clName := ns ++ `variantClaims ++ vc
      let clVal := mkApp3 (mkConst (bNs ++ `variant_bundle_claims)) vConst lmAuthC (mkConst chkName)
      addThm clName (← MetaM.run' <| inferType clVal) clVal
      added := added.push clName
      let vbC := mkConst vbName
      let vpVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectPositive #[vbC]
      addThm (ns ++ `variantProjectPositive ++ vc) (← MetaM.run' <| inferType vpVal) vpVal
      added := added.push (ns ++ `variantProjectPositive ++ vc)
      let vfVal ← MetaM.run' <| mkAppM ``DualCorrespondenceBundle.projectFault #[vbC]
      addThm (ns ++ `variantProjectFault ++ vc) (← MetaM.run' <| inferType vfVal) vfVal
      added := added.push (ns ++ `variantProjectFault ++ vc)

    -- 3. Definitional `Eq.refl` locks of ALL 18 shared `CapturedMir` fixtures.
    let capMirTy := mkConst `Trusted.Rustc.V2026_06_01.MirAst.CapturedMir
    let fixtureNames : List Name :=
      [ `cmCopyMir, `cmCopyOverlapMir, `cmCopyModeMir, `cmCmpBytes3Mir, `cmCmpBytes1Mir,
        `cmRawEqU32Mir, `cmRawEqZstMir, `cmSwapReadXMir, `cmSwapReadYMir, `cmSwapSameAllocMir,
        `cmPofMir, `cmPofuMir, `cmMaskAlign8Mir, `cmMaskIdentityMir, `cmMaskAlign4Mir,
        `cmBlackBoxU32Mir, `cmBlackBoxPtrMir, `cmBlackBoxBoolMir ]
    let mut lockCount : Nat := 0
    for tag in fixtureNames do
      let lockName := ns ++ `fixtureLock ++ tag
      let lhs := mkConst (mrNs ++ tag)
      let rhs := mkConst (lmNs ++ tag)
      addThm lockName (mkApp3 (mkConst ``Eq [1]) capMirTy lhs rhs)
        (mkApp2 (mkConst ``Eq.refl [1]) capMirTy lhs)
      added := added.push lockName
      lockCount := lockCount + 1
    unless lockCount = 18 do
      throwError "cross-root: expected 18 fixture locks, got {lockCount}"

    -- 4. Negative controls, each paired with a positive control that the kernel
    -- ACCEPTS in the same scratch environment (so a rejection is never caused by
    -- an unrelated elaboration failure).
    let saved ← getEnv
    let accepts (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure true catch _ => pure false
      setEnv saved
      return r
    let invertedAuth ← MetaM.run' <| mkLmAuth true false
    let collidingAuth ← MetaM.run' <| mkLmAuth false true
    let denoteOf (a : Expr) : Expr :=
      mkApp4 (mkConst (cNs ++ `ObsAuthority.denoteConsistent)) keyTy obsValTy decObsVal a
    let lmObsEq (tb v c : Nat) (o : Expr) : Expr :=
      mkApp3 (mkConst ``Eq [1]) lmObsTy
        (mkApp3 (mkConst (lmNs ++ `cmLmObserve)) (if tb = 1 then boolTrue else boolFalse) (mkNatLit v) (mkNatLit c)) o
    let lmObsRefl (tb v c : Nat) : Expr :=
      mkApp2 (mkConst ``Eq.refl [1]) lmObsTy
        (mkApp3 (mkConst (lmNs ++ `cmLmObserve)) (if tb = 1 then boolTrue else boolFalse) (mkNatLit v) (mkNatLit c))
    let trObsTy := mkConst (mrNs ++ `CmTrustedObs)
    let trEq (pm : Bool) (v c : Name) (o : Expr) : Expr :=
      mkApp3 (mkConst ``Eq [1]) trObsTy
        (mkApp3 (mkConst (mrNs ++ `cmTrustedObserve)) (if pm then boolTrue else boolFalse)
          (mkConst (mrNs ++ `CmVariant ++ v)) (mkConst (mrNs ++ `CmCase ++ c))) o
    let trRefl (pm : Bool) (v c : Name) : Expr :=
      mkApp2 (mkConst ``Eq.refl [1]) trObsTy
        (mkApp3 (mkConst (mrNs ++ `cmTrustedObserve)) (if pm then boolTrue else boolFalse)
          (mkConst (mrNs ++ `CmVariant ++ v)) (mkConst (mrNs ++ `CmCase ++ c)))
    let trSc (b s : Nat) : Expr := mkApp2 (mkConst (mrNs ++ `CmTrustedObs.scalar)) (mkNatLit b) (mkNatLit s)
    let thm (n : Name) (ty pf : Expr) : Declaration := .thmDecl { name := ns ++ n, levelParams := [], type := ty, value := pf }
    let pairs : List (String × Declaration × Declaration) :=
      [ ("LM check certificate (true vs. negated false)",
          thm `pos.lmCheckTrue (eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) lmAuthC)) reflTrue,
          thm `neg.lmCheckFalse (eqFalse (mkApp (mkConst (bNs ++ `lmCheckOf)) lmAuthC)) reflFalse),
        ("LM authority mode (faithful vs. mode-inverted)",
          thm `pos.modeFaithful (eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) lmAuthC)) reflTrue,
          thm `neg.modeInverted (eqTrue (mkApp (mkConst (bNs ++ `lmCheckOf)) invertedAuth)) reflTrue),
        ("per-variant copy certificate (faithful vs. mode-inverted)",
          thm `pos.copyVariant (eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf))
            (mkConst (mrNs ++ `CmVariant.copy)) lmAuthC)) reflTrue,
          thm `neg.copyVariantInverted (eqTrue (mkApp2 (mkConst (bNs ++ `lmVariantCheckOf))
            (mkConst (mrNs ++ `CmVariant.copy)) invertedAuth)) reflTrue),
        ("LM denote table (consistent vs. colliding)",
          thm `pos.denote (eqTrue (denoteOf lmAuthC)) reflTrue,
          thm `neg.collidingDenote (eqTrue (denoteOf collidingAuth)) reflTrue),
        ("fixture lock (same fixture vs. swapped copy/compare_bytes)",
          thm `pos.lockCopy (mkApp3 (mkConst ``Eq [1]) capMirTy (mkConst (mrNs ++ `cmCopyMir))
            (mkConst (lmNs ++ `cmCopyMir))) (mkApp2 (mkConst ``Eq.refl [1]) capMirTy (mkConst (mrNs ++ `cmCopyMir))),
          thm `neg.lockSwapped (mkApp3 (mkConst ``Eq [1]) capMirTy (mkConst (mrNs ++ `cmCopyMir))
            (mkConst (lmNs ++ `cmCmpBytes3Mir))) (mkApp2 (mkConst ``Eq.refl [1]) capMirTy (mkConst (mrNs ++ `cmCopyMir)))),
        ("fixture lock (same mask vs. swapped !7/!3 masks)",
          thm `pos.lockMask (mkApp3 (mkConst ``Eq [1]) capMirTy (mkConst (mrNs ++ `cmMaskAlign8Mir))
            (mkConst (lmNs ++ `cmMaskAlign8Mir))) (mkApp2 (mkConst ``Eq.refl [1]) capMirTy (mkConst (mrNs ++ `cmMaskAlign8Mir))),
          thm `neg.lockMaskSwapped (mkApp3 (mkConst ``Eq [1]) capMirTy (mkConst (mrNs ++ `cmMaskAlign8Mir))
            (mkConst (lmNs ++ `cmMaskAlign4Mir))) (mkApp2 (mkConst ``Eq.refl [1]) capMirTy (mkConst (mrNs ++ `cmMaskAlign8Mir)))),
        ("vendored copy observation (42 vs. forged 43)",
          thm `pos.lmCopy42 (lmObsEq 0 0 0 (mkScO 42 4)) (lmObsRefl 0 0 0),
          thm `neg.lmCopy43 (lmObsEq 0 0 0 (mkScO 43 4)) (lmObsRefl 0 0 0)),
        ("vendored ptr_mask provenance/address (1032 vs. forged 1036)",
          thm `pos.lmMask1032 (lmObsEq 0 6 0 (mkPtrO 100 1032)) (lmObsRefl 0 6 0),
          thm `neg.lmMask1036 (lmObsEq 0 6 0 (mkPtrO 100 1036)) (lmObsRefl 0 6 0)),
        ("vendored copy mode case under Tree Borrows (UB vs. forged 42)",
          thm `pos.lmCopyModeTbUb (lmObsEq 1 0 3 (mkConst (lmNs ++ `CmLmObs.ub))) (lmObsRefl 1 0 3),
          thm `neg.lmCopyModeTb42 (lmObsEq 1 0 3 (mkScO 42 4)) (lmObsRefl 1 0 3)),
        ("Trusted compare_bytes (-1 vs. forged +1)",
          thm `pos.trCmpNeg (trEq false `compareBytes `okPrimary (trSc 0xFFFFFFFF 4)) (trRefl false `compareBytes `okPrimary),
          thm `neg.trCmpPos (trEq false `compareBytes `okPrimary (trSc 1 4)) (trRefl false `compareBytes `okPrimary)) ]
    let mut rejected : Nat := 0
    let mut acceptedPos : Nat := 0
    for (what, pos, neg) in pairs do
      unless ← accepts pos do
        throwError "cross-root positive control FAILED: kernel rejected {what}"
      acceptedPos := acceptedPos + 1
      if ← accepts neg then
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1

    -- 5. Axiom, safety, non-triviality, & transitive reachability audit.
    let env ← getEnv
    let isStdAx (a : Name) : Bool :=
      a == ``propext || a == ``Classical.choice || a == ``Quot.sound
    let rec isTrivialProp : Expr → Bool
      | .forallE _ _ body _ => isTrivialProp body
      | .letE _ _ _ body _ => isTrivialProp body
      | e =>
        if e.isConstOf ``True then true
        else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
        else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
        else false
    let mut crAxioms : NameSet := {}
    for n in added do
      let some ci := env.find? n | throwError "cross-root: {n} missing"
      match ci with
      | .defnInfo v =>
        if v.safety != .safe then throwError "cross-root: {n} is not safe"
      | .thmInfo v =>
        if isTrivialProp v.type then throwError "cross-root: {n} is a trivial theorem"
      | _ => throwError "cross-root: {n} is not a defn or thm"
      for a in ← collectAxioms n do
        unless isStdAx a do
          throwError "cross-root: {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a
    let lmDeepThms : List Name :=
      [ lmNs ++ `cmMemCopy_basic_mode, lmNs ++ `cmIntrinsic_ofDefId_defId,
        lmNs ++ `cmIntrinsic_ofDefPath_defPath, lmNs ++ `cmDecodeFnItemTyId_cmFnItemTyId,
        lmNs ++ `cmIntrinsic_names, lmNs ++ `cmLmTableCheck_true, lmNs ++ `cmLmObserve_table,
        lmNs ++ `cmLmObserve_copy_mode_sensitivity, lmNs ++ `cm_lm_trusted_null_zero_size_deltas,
        lmNs ++ `cm_lm_trusted_side_witness ]
    for n in lmDeepThms do
      let some (.thmInfo v) := env.find? n
        | throwError "cross-root: required LM theorem {n} missing"
      if isTrivialProp v.type then
        throwError "cross-root: LM theorem {n} is trivial"
      for a in ← collectAxioms n do
        unless isStdAx a do
          throwError "cross-root: LM theorem {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a
    unless !(← collectAxioms ``sorryAx).all isStdAx do
      throwError "cross-root self-test: sorryAx was not detected"
    unless !(← collectAxioms ``Lean.ofReduceBool).all isStdAx do
      throwError "cross-root self-test: Lean.ofReduceBool was not detected"
    let trivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 1)
    let nonTrivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 2)
    unless isTrivialProp (mkConst ``True) && isTrivialProp trivEq && !isTrivialProp nonTrivEq do
      throwError "cross-root self-test: trivial theorem detector failed"
    let mut reach : NameSet := {}
    let mut todo : Array Name := #[unifiedBundleName]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if reach.contains n then continue
      reach := reach.insert n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if !reach.contains d then todo := todo.push d
    let requiredReach : List Name :=
      [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyCall,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalCompareBytesCall,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalRawEqCall,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalTypedSwapNonOverlappingCall,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalPtrOffsetFromCall,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalPtrMaskCall,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalBlackBoxCall,
        `MiniRustSpec.Interp.steps,
        `MiniRustSpec.Interp.stepsTB,
        `MiniRustSpec.CoreMemPtrIntrinsicsMR.cmRunTrusted,
        `MiniRustSpec.CoreMemPtrIntrinsicsMR.cmMrObserve,
        `MiniRustSpec.CoreMemPtrIntrinsicsMR.cmTrustedObserve_table,
        `MiniRustSpec.CoreMemPtrIntrinsicsMR.cmMrObserveClass_table,
        `Miri.Interpreter.Step.step,
        `Miri.Interpreter.Intrinsics.eval,
        `LeanMiriSpec.CoreMemPtrIntrinsicsLM.cmLmObserve,
        `LeanMiriSpec.CoreMemPtrIntrinsicsLM.cmIntrinsicHooks ]
    for req in requiredReach do
      unless reach.contains req do
        throwError "cross-root reachability failure: unifiedDualBundle does not reach {req}"
    return (added.size, bundleCount, acceptedPos, rejected, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<cm-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, bundleCount, acceptedCount, rejectedCount, crAxioms), _) ←
    liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount ≥ 70 && bundleCount = 9 && acceptedCount = 10 && rejectedCount = 10 do
    throwError "cross-root: unexpected counts (added={addedCount}, bundles={bundleCount}, accepted={acceptedCount}, rejected={rejectedCount})"
  logInfo m!"cm cross-root kernel bridge: added {addedCount} declarations ({bundleCount} bundles, 18 fixture locks), {acceptedCount} positive controls accepted / {rejectedCount} paired negative controls rejected, reached Trusted+MiniRust+Miri, axioms {crAxioms}"

/-! ## §3. Constructive Axiom Audit of `Anneal.Mir.CoreMemPtrIntrinsicsBundle` & Test Module -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constructiveDecls : List Name :=
    [ ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.cmCodec,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.cmCodec_tight,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.allCmModes_complete,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.allCmMrModes_complete,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.allCmLmModes_complete,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.allCmVariants_complete,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.allCmCases_complete,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.cmAnnealEval,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.cmAnnealEval_eq,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.cmAnnealEval_funext,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mrAuthority,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mrAuthority_denoteConsistent,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mrAuthority_verdict_eq,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mrVerdictFn_funext,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mrSide_check,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mrVariantSide_check,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.lmCheckOf_congr,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.lmVariantCheckOf_congr,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.bundleOf,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.variantBundleOf,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.threeWayNormalAgreement,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.crossAuthorityFaultEquiv,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.exactBehaviorEq_both,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.mr_modeSensitivity_present,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.lm_modeSensitivity_present,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.variant_bundle_claims,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.cm_variant_outcomes_distinct,
      ``Anneal.Mir.CoreMemPtrIntrinsicsBundle.ep2_core_mem_ptr_intrinsics_capstone ]
  for d in constructiveDecls do
    let axs ← liftCoreM <| Lean.collectAxioms d
    for a in axs do
      unless a == ``propext || a == ``Quot.sound do
        throwError "constructive audit failure: {d} uses non-constructive axiom {a}"
  let rec isTrivialProp : Expr → Bool
    | .forallE _ _ body _ => isTrivialProp body
    | .letE _ _ _ body _ => isTrivialProp body
    | e =>
      if e.isConstOf ``True then true
      else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
      else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
      else false
  let mut bundleDecls : Nat := 0
  for (c, ci) in env.constants.map₁.toList do
    if (`Anneal.Mir.CoreMemPtrIntrinsicsBundle).isPrefixOf c then
      if let .thmInfo v := ci then
        let u := (Lean.privateToUserName? c).getD c
        if !u.isInternal && isTrivialProp v.type then
          throwError "bundle audit failure: {c} is a trivial theorem"
      for a in ← liftCoreM <| Lean.collectAxioms c do
        if a == ``sorryAx then throwError "bundle audit failure: {c} uses sorryAx"
        unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
          throwError "bundle audit failure: {c} uses non-standard axiom {a}"
      bundleDecls := bundleDecls + 1
  for (c, ci) in env.constants.map₂.toList do
    if let .thmInfo v := ci then
      let u := (Lean.privateToUserName? c).getD c
      if !u.isInternal && isTrivialProp v.type then
        throwError "test audit failure: {c} is a trivial theorem"
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "test audit failure: {c} uses sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "test audit failure: {c} uses non-standard axiom {a}"
  logInfo m!"cm constructive audit: verified {constructiveDecls.length} bundle declarations in [propext, Quot.sound], {bundleDecls} bundle declarations non-trivial and sorry-free (0 Classical.choice in codecs/bundles, 0 sorryAx, 0 ofReduceBool)"

end Anneal.Mir.CoreMemPtrIntrinsicsTests
