/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted
import Anneal.MirFuelFree
import MiniRustSpec.UnwindSetDiscrAndFnPtrMR
import Lean.Elab.Command

set_option Elab.async false

/-!
# End-to-End Tests: MiniRust Unwind/`SetDiscriminant` & `C1..C10` MIR Variants

Exercises Episode 1's 100% MiniRust `Statement` (`7/7`) and `Terminator` (`9/9`)
interpretation across `Mach` (`BasicMemory`) and `MachTB` (`TreeBorrowsMemory`)
together with Episode 2's correspondence, boundary, and divergence theorems for
`C1` (`setDiscriminant`), `C2` (`unwindResume`), `C3` (`unwindTerminate`), `C4`
(`coverage`), `C5` (`backwardIncompatibleDropHint`), `C6` (`fnPtrToPtr`), `C7`
(`subtype`), `C8` (all 5 non-`Unsize` `pointerCoercion`s), `C9`
(`unwrapUnsafeBinder`), and `C10` (`AggregateKind.closure`).
-/

namespace Anneal.UnwindSetDiscrAndFnPtrTests

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.Gen
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness hiding constU32
open MiniRustSpec.Correspondence.PointerWitness
open MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness
open MiniRustSpec.Correspondence.WideSliceDst
open MiniRustSpec.UnwindSetDiscrAndFnPtrMR

/-! ## §1. MiniRust 100% `Statement` (7/7) & `Terminator` (9/9) Pipeline -/

/-- Two-frame MiniRust machine exercising `Validate` (installing a Tree Borrows
protector on caller's `TwoVar` local `_0`), `StartUnwind` (pushing payload
`4096`), `ResumeUnwind` (releasing the callee's protector before deallocating
frame local `_1`), `StopUnwind` (popping payload `4096`), and `SetDiscriminant`
(flipping caller's `TwoVar` discriminant `0 → 1` while preserving payload `42`)
across both `Mach` and `MachTB`. -/
def mrFullUnwindSetDiscrMach : Mach :=
  let calleeFn := mkMrFn
    [(localName 0, unitType), (localName 1, refTy .mut u32)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[.Validate (.Local (localName 1)) true],
        .StartUnwind (.Constant (.PointerWithoutProvenance 4096) thinRawPtrTy)
          (bbName 1), .Regular⟩),
     (bbName 1, ⟨[], .ResumeUnwind, .Cleanup⟩)]
  let callerFn := mkMrFn
    [(localName 0, twoVarEnumMrTy)] [] (localName 0)
    [(bbName 0, ⟨[], .Goto (bbName 1), .Regular⟩),
     (bbName 1, ⟨[], .StopUnwind (bbName 2), .Cleanup⟩),
     (bbName 2, ⟨[.SetDiscriminant (.Local (localName 0)) 1],
        .Return, .Regular⟩)]
  let callerFr := mkRootFrame callerFn
    [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]
  let calleeFr : Frame :=
    { func := calleeFn
      locals := ⟨[(localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]⟩
      stack_pop_action := .BackToCaller (some (bbName 0)) (some (bbName 1))
        dummyRetPtr
      next_block := bbName 0
      next_stmt := 0
      extra := () }
  mkMrMach (mkMrProg [(fnName 0, callerFn), (fnName 1, calleeFn)])
    [mkStackAlloc 128 c1LocalInitBytes 4,
     mkStackAlloc 256 (ptrBytes 128 (some (⟨0⟩, ()))) 8]
    [callerFr, calleeFr]

/-- Five-step `Mach` and `MachTB` execution through `Validate → StartUnwind →
ResumeUnwind → StopUnwind → SetDiscriminant`, preserving `MachTB.wfLive`,
emptying `unwind_payloads`, deallocating callee frame storage, and mutating only
tag byte `0` (`0 → 1`) while preserving payload `42` at offset `4`. -/
theorem mr_full_unwind_and_setDiscriminant_pipeline :
    (∃ m5 : Mach, Interp.steps 5 mrFullUnwindSetDiscrMach = .ok m5 ∧
      (m5.threads[0]?.map (fun t =>
         (t.stack.length, t.unwind_payloads.length,
          t.stack[0]?.map (·.next_stmt))),
       m5.mem.memory.allocations[0]?.map
         (fun a => a.data.map (projByteTB ∘ liftByteTB)),
       m5.mem.memory.allocations[1]?.map (·.live)) =
      (some (1, 0, some 1),
       some (c1LocalExpectedBytes.map (projByteTB ∘ liftByteTB)),
       some false)) ∧
    (∃ m5 : MachTB,
      Interp.stepsTB 5 (liftMachToTB mrFullUnwindSetDiscrMach) = .ok m5 ∧
      MachTB.wfLive m5 ∧
      (m5.threads[0]?.map (fun t =>
         (t.stack.length, t.unwind_payloads.length)),
       m5.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB),
       m5.mem.memory.mem.allocations[1]?.map (·.live)) =
      (some (1, 0),
       some (c1LocalExpectedBytes.map (projByteTB ∘ liftByteTB)),
       some false)) :=
  ⟨ok_of_map_toOption (by decide +kernel),
   ok_stepsTB_wfLive (by decide +kernel)⟩

/-! ## §2 (`C1`): `StatementKind.setDiscriminant` Round-Trip & Witnesses -/

/-- Fresh `CapturedMir` enum body toggling discriminant `0 → 1 → 0` on `_1`,
reading `Rvalue.discriminant` after each flip, and extracting downcast field `0`
(`77`) to prove payload preservation across multiple discriminant writes. -/
def c1ToggleEnumMir : CapturedMir :=
  mkMirBody "tests::c1_toggle_enum"
    [mkDecl u32MirTy, mkDecl twoVarMirTy, mkDecl u64MirTy, mkDecl u64MirTy] 1
    [mkBb
      [mkSt (.storageLive 2),
       mkSt (.storageLive 3),
       mkSt (.setDiscriminant (locPlace 1) 1),
       mkSt (.assign (locPlace 2) (.discriminant (locPlace 1))),
       mkSt (.setDiscriminant (locPlace 1) 0),
       mkSt (.assign (locPlace 3) (.discriminant (locPlace 1))),
       mkSt (.assign (locPlace 0)
         (.use (.copy (locPlace 1 [.downcast "A" 0, .field 0 u32MirTy]))))]
      .return_]
    twoVarLayouts

/-- Exercises `C1` multi-flip discriminant updates, `Rvalue.discriminant`
read-back (`1` then `0`), payload preservation (`77`), niche
`Option<NonZeroU8>`,
deref/uninit/dead/misaligned/frozen UB, and invalid-variant divergence. -/
theorem test_c1_setDiscriminant_suite :
    (let s0 := initMachineState c1ToggleEnumMir [.aggregate 0 [.scalar ⟨77, 4⟩]]
     match runA c1ToggleEnumMir 12 s0 with
     | some ([], .normal (vRet, _)) => vRet = .scalar ⟨77, 4⟩
     | _ => False) ∧
    (let s0 := initMachineState c1ToggleEnumMir [.aggregate 0 [.scalar ⟨77, 4⟩]]
     match stepMirFn c1ToggleEnumMir s0 with
     | .tau (.running s1) =>
       match stepMirFn c1ToggleEnumMir s1 with
       | .tau (.running s2) =>
         match stepMirFn c1ToggleEnumMir s2 with
         | .tau (.running s3) =>
           match stepMirFn c1ToggleEnumMir s3 with
           | .tau (.running s4) =>
             get? s4.frame.locals 2 = some (.init (.scalar ⟨1, 8⟩)) ∧
             get? s4.frame.locals 1 =
               some (.init (.aggregate 1 [.scalar ⟨77, 4⟩]))
           | _ => False
         | _ => False
       | _ => False
     | _ => False) ∧
    translateStatement [] { kind := .setDiscriminant (locPlace 1) 1,
                            span := dummySpan } twoVarLayouts = none :=
  ⟨rfl, ⟨rfl, rfl⟩,
   translateStatement_setDiscriminant_none [] (locPlace 1) 1 dummySpan
     twoVarLayouts⟩

/-- Bundles all `C1` three-way `Trusted` + `Mach` + `MachTB` witnesses from
`MiniRustSpec.UnwindSetDiscrAndFnPtrMR`. -/
theorem test_c1_three_way_witness_bundle :
    (∃ p, p = c1_setDiscriminant_local_three_way_witness) ∧
    (∃ p, p = c1_niche_optionNonZeroU8_three_way_witness) ∧
    (∃ p, p = c1_setDiscriminant_deref_three_way_witness) ∧
    (∃ p, p = c1_setDiscriminant_uninit_shell_witness) ∧
    (∃ p, p = c1_setDiscriminant_dead_local_ub_witness) ∧
    (∃ p, p = c1_setDiscriminant_misaligned_and_frozen_ub_witness) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-! ## §3 (`C2` & `C3`): Multi-Frame `unwindResume` & `unwindTerminate` -/

/-- Caller MIR body that recovers in cleanup block `1` by writing `91` to `_0`
and jumping to normal return block `2` (plus block `3` executing
`unwindTerminate` on a double-panic cleanup fault). -/
def c2c3CallerRecoveryMir : CapturedMir :=
  mkMirBody "tests::c2c3_caller" [mkDecl u32MirTy] 0
    [mkBb [] (.goto 2) false,
     mkBb [mkSt (.assign (locPlace 0) (.use (constU32 91)))] (.goto 2) true,
     mkBb [] .return_ false,
     mkBb [] .unwindTerminate true]

/-- Exercises 3-frame `unwindResume` recovery (`leaf → mid(.continue_) →
caller(.cleanup 1) → 91`), callee borrow disabling & protector release,
`.unreachable` UB, `.terminate` / `unwindTerminate` `.abort`, and root
`.panic`. -/
theorem test_c2_c3_unwind_resume_and_terminate_suite :
    (let midSaved : SavedCallerFrame :=
       { callerBody := c2LeafMir
         frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
         destination := locPlace 0
         returnTarget := 0
         returnUnwind := .continue_
         calleeProtectors := [21] }
     let rootSaved (ua : UnwindAction) : SavedCallerFrame :=
       { callerBody := c2c3CallerRecoveryMir
         frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
         destination := locPlace 0
         returnTarget := 2
         returnUnwind := ua
         calleeProtectors := [11] }
     let bCallee : BorrowEntry :=
       { tag := 30, targetLocal := 0, targetProjection := [],
         perm := .active, targetFrameDepth := 2 }
     let bRoot : BorrowEntry :=
       { tag := 10, targetLocal := 0, targetProjection := [],
         perm := .active, targetFrameDepth := 0 }
     let mkLeafState (cs : List SavedCallerFrame) : MachineState :=
       { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
         memory := { (initMachineState c2LeafMir []).memory with
                     activeCallee := some c2LeafMir
                     callStack := cs
                     activeProtectors := [11, 21, 99]
                     borrows := [bCallee, bRoot] } }
     (match stepMirFn c2c3CallerRecoveryMir
              (mkLeafState [midSaved, rootSaved (.cleanup 1)]) with
      | .tau (.running sRec) =>
        sRec.frame.blockIdx = 1 ∧ sRec.memory.callStack = [] ∧
        sRec.memory.activeCallee = some c2c3CallerRecoveryMir ∧
        sRec.memory.activeProtectors = [11] ∧
        (sRec.memory.borrows.map (·.perm)) = [.disabled, .active] ∧
        runAVal c2c3CallerRecoveryMir 4 sRec = some (.scalar ⟨91, 4⟩)
      | _ => False) ∧
     stepMirFn c2c3CallerRecoveryMir
       (mkLeafState [midSaved, rootSaved .unreachable]) = MirStepNode.fail .ub ∧
     stepMirFn c2c3CallerRecoveryMir
       (mkLeafState [midSaved, rootSaved .terminate]) =
       MirStepNode.retOutcome .abort ∧
     stepMirFn c2LeafMir (mkLeafState []) = MirStepNode.retOutcome .panic ∧
     stepMirFn c2c3CallerRecoveryMir
       { frame := { blockIdx := 3, stmtIdx := 0, locals := [.uninit] },
         memory := (initMachineState c2c3CallerRecoveryMir []).memory } =
       MirStepNode.retOutcome .abort) ∧
    (∃ p, p = c2_unwindResume_all_five_regimes_witness) ∧
    (∃ p, p = c2_start_resume_stop_unwind_composition_witness) ∧
    (∃ p, p = c2_machTB_protector_release_on_resumeUnwind_witness) ∧
    (∃ p, p = c3_unwindTerminate_three_way_witness) :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩,
   ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-! ## §4 (`C4` & `C5`): `coverage` & `backwardIncompatibleDropHint` -/

/-- Interleaved `coverage` and `backwardIncompatibleDropHint` over dead/OOB
places vs. `placeMention` UB on the same dead local `_1`. -/
def c4c5NoopChainMir (usePlaceMention : Bool) : CapturedMir :=
  mkMirBody "tests::c4c5_chain" [mkDecl u32MirTy, mkDecl rawMutU32MirTy] 0
    [mkBb
      [mkSt (.storageDead 1),
       mkSt .coverage,
       mkSt (if usePlaceMention then .placeMention (locPlace 1)
             else .backwardIncompatibleDropHint (locPlace 1 [.deref])),
       mkSt .coverage,
       mkSt (.backwardIncompatibleDropHint (locPlace 77)),
       mkSt (.assign (locPlace 0) (.use (constU32 63)))]
      .return_]

/-- Initial post-`storageDead 1` state for `c4c5NoopChainMir false`. -/
def c4c5DeadState : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 1, locals := [.uninit, .dead] }
    memory := (initMachineState (c4c5NoopChainMir false) []).memory }

/-- Instantiates universal `erasedNoopStmt_chain_stuttering` (`TauSteps`) on the
4-statement `[coverage, dropHint, coverage, dropHint]` block slice and contrasts
`backwardIncompatibleDropHint` safety on dead `_1` with `placeMention` UB. -/
theorem test_c4_c5_stuttering_and_placeMention_contrast :
    (TauSteps (c4c5NoopChainMir false) 4 c4c5DeadState
       { c4c5DeadState with frame := { c4c5DeadState.frame with stmtIdx := 5 } } ∧
     runA (c4c5NoopChainMir false) 6 c4c5DeadState =
       runA (c4c5NoopChainMir false) 2
         { c4c5DeadState with frame := { c4c5DeadState.frame with stmtIdx := 5 } }) ∧
    runAVal (c4c5NoopChainMir false) 8
      (initMachineState (c4c5NoopChainMir false) []) = some (.scalar ⟨63, 4⟩) ∧
    stepMirFn (c4c5NoopChainMir true)
      { frame := { blockIdx := 0, stmtIdx := 2, locals := [.uninit, .dead] }
        memory := (initMachineState (c4c5NoopChainMir true) []).memory } =
      MirStepNode.fail .ub ∧
    (∃ p, p = c4_coverage_stuttering_three_way_witness) ∧
    (∃ p, p = c5_backwardIncompatibleDropHint_dead_place_no_ub_witness) := by
  let bb0 : BasicBlockData :=
    mkBb
      [mkSt (.storageDead 1),
       mkSt .coverage,
       mkSt (.backwardIncompatibleDropHint (locPlace 1 [.deref])),
       mkSt .coverage,
       mkSt (.backwardIncompatibleDropHint (locPlace 77)),
       mkSt (.assign (locPlace 0) (.use (constU32 63)))]
      .return_
  let noops : List MirAst.Statement :=
    [mkSt .coverage,
     mkSt (.backwardIncompatibleDropHint (locPlace 1 [.deref])),
     mkSt .coverage,
     mkSt (.backwardIncompatibleDropHint (locPlace 77))]
  have hAll : ∀ st ∈ noops, IsErasedNoopStmt st.kind := by
    intro st hMem
    simp only [noops, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact .coverage
    · exact .dropHint _
    · exact .coverage
    · exact .dropHint _
  have hChain := erasedNoopStmt_chain_stuttering (c4c5NoopChainMir false) bb0
    c3AbortMach noops [mkSt (.storageDead 1)]
    [mkSt (.assign (locPlace 0) (.use (constU32 63)))]
    c4c5DeadState hAll rfl rfl rfl rfl
  exact ⟨⟨hChain.1, (hChain.2.1 2).1⟩, rfl, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-! ## §5 (`C6`–`C8`): Composite Coercions, `fnPtrToPtr`, & `subtype` -/

/-- Composite `CapturedMir` body exercising `AggregateKind.closure` (`0`
captures) → `"ClosureFnPointer"` → `"UnsafeFnPointer"` → `fnPtrToPtr` →
`subtype`, plus `[u32; 2]` → `"ArrayToPointer"` → `"MutToConstPointer"` →
deref load (`64`). -/
def c6c7c8CompositeMir : CapturedMir :=
  mkMirBody "tests::c6c7c8_composite"
    [mkDecl u32MirTy,
     mkDecl (closureZstMirTy "tests::zst_cl"),
     mkDecl fnPtrSafeU32MirTy,
     mkDecl fnPtrUnsafeU32MirTy,
     mkDecl rawConstUnitMirTy,
     mkDecl rawConstU32MirTy,
     mkDecl arr2U32MirTy,
     mkDecl rawMutArr2U32MirTy,
     mkDecl rawMutU32MirTy,
     mkDecl rawConstU32MirTy] 0
    [mkBb
      [mkSt (.storageLive 1), mkSt (.storageLive 2), mkSt (.storageLive 3),
       mkSt (.storageLive 4), mkSt (.storageLive 5), mkSt (.storageLive 6),
       mkSt (.storageLive 7), mkSt (.storageLive 8), mkSt (.storageLive 9),
       mkSt (.assign (locPlace 1) (.aggregate (.closure "tests::zst_cl") [])),
       mkSt (.assign (locPlace 2)
         (.cast (.pointerCoercion "ClosureFnPointer") (.copy (locPlace 1))
           fnPtrSafeU32MirTy)),
       mkSt (.assign (locPlace 3)
         (.cast (.pointerCoercion "UnsafeFnPointer") (.copy (locPlace 2))
           fnPtrUnsafeU32MirTy)),
       mkSt (.assign (locPlace 4)
         (.cast .fnPtrToPtr (.copy (locPlace 3)) rawConstUnitMirTy)),
       mkSt (.assign (locPlace 5)
         (.cast .subtype (.copy (locPlace 4)) rawConstU32MirTy)),
       mkSt (.assign (locPlace 6)
         (.aggregate (.array u32MirTy) [constU32 64, constU32 128])),
       mkSt (.assign (locPlace 7) (.rawPtr .mut (locPlace 6))),
       mkSt (.assign (locPlace 8)
         (.cast (.pointerCoercion "ArrayToPointer") (.copy (locPlace 7))
           rawMutU32MirTy)),
       mkSt (.assign (locPlace 9)
         (.cast (.pointerCoercion "MutToConstPointer") (.copy (locPlace 8))
           rawConstU32MirTy)),
       mkSt (.assign (locPlace 0) (.use (.copy (locPlace 9 [.deref]))))]
      .return_]

/-- Exercises `C6..C8` composite pipeline, `NonZeroU8`/`bool` range-checked
`subtype` validity vs. UB, `unsafeFnPointer_trusted_unsupported_divergence`, and
all 4 `C6..C8` three-way witness bundles. -/
theorem test_c6_c7_c8_coercions_fnPtrToPtr_and_subtype_suite :
    (match runA c6c7c8CompositeMir 24 (initMachineState c6c7c8CompositeMir []) with
     | some ([], .normal (vRet, memEnd)) =>
       vRet = .scalar ⟨64, 4⟩ ∧ length memEnd.fnPtrs = 1
     | _ => False) ∧
    runAVal c7SubtypeU8ToNzMir 4
      (initMachineState c7SubtypeU8ToNzMir [.scalar ⟨5, 1⟩]) =
      some (.aggregate 0 [.scalar ⟨5, 1⟩]) ∧
    stepMirFn c7SubtypeU8ToNzMir
      (initMachineState c7SubtypeU8ToNzMir [.scalar ⟨0, 1⟩]) =
      MirStepNode.fail .ub ∧
    runAVal c7SubtypeU8ToBoolMir 4
      (initMachineState c7SubtypeU8ToBoolMir [.scalar ⟨1, 1⟩]) =
      some (.scalar ⟨1, 1⟩) ∧
    stepMirFn c7SubtypeU8ToBoolMir
      (initMachineState c7SubtypeU8ToBoolMir [.scalar ⟨2, 1⟩]) =
      MirStepNode.fail .ub ∧
    (let locs := [LocalSlot.uninit,
                  LocalSlot.init (.ptr { allocId := fnPtrAllocBase,
                                         offsetBytes := 0 } 8)]
     let decls := [mkDecl fnPtrUnsafeU32MirTy, mkDecl fnPtrSafeU32MirTy]
     let mem := (initMachineState c6FnPtrToPtrMir []).memory
     let div := unsafeFnPointer_trusted_unsupported_divergence
       locs locs (.copy (locPlace 1)) fnPtrUnsafeU32MirTy mem decls
       emptyLayoutTable { allocId := fnPtrAllocBase, offsetBytes := 0 } 4096
       (by decide) (some (⟨0⟩, ())) (some (⟨0⟩, [])) none none rfl
       "CustomUnknownCoercion"
     div.2.1 = rfl ∧ div.2.2.1 = rfl) ∧
    (∃ p, p = c6_fnPtrToPtr_three_way_and_ub_witness) ∧
    (∃ p, p = c7_subtype_positive_and_invalid_ub_three_way_witness) ∧
    (∃ p, p = c8_all_five_pointer_coercions_three_way_witness) ∧
    (∃ p, p = c8_capturing_closure_wide_and_unknown_tag_witness) :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩,
   ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-! ## §6 (`C9` & `C10`): `unwrapUnsafeBinder` + `AggregateKind.closure` -/

/-- Composite `CapturedMir` body that writes `19` through `.unwrapUnsafeBinder`,
borrows `&raw const (_1.unwrapUnsafeBinder)`, constructs a 2-capture closure
`[move (_1.unwrapUnsafeBinder), copy _2]`, mutates capture `_3.0 = 44`, copies
`_5 = _3.1`, reads `*_5` (`19`), and verifies `_1` remains live after projected
`.move` (`44 + 19 = 63`). -/
def c9c10CompositeMir : CapturedMir :=
  mkMirBody "tests::c9c10_composite"
    [mkDecl u32MirTy,
     mkDecl u32MirTy,
     mkDecl rawConstU32MirTy,
     mkDecl (closureCapMirTy "tests::cap_cl"),
     mkDecl u32MirTy,
     mkDecl rawConstU32MirTy] 1
    [mkBb
      [mkSt (.storageLive 2), mkSt (.storageLive 3),
       mkSt (.storageLive 4), mkSt (.storageLive 5),
       mkSt (.assign (locPlace 1 [.unwrapUnsafeBinder u32MirTy])
         (.use (constU32 19))),
       mkSt (.assign (locPlace 2)
         (.rawPtr .not (locPlace 1 [.unwrapUnsafeBinder u32MirTy]))),
       mkSt (.assign (locPlace 3)
         (.aggregate (.closure "tests::cap_cl")
           [.move (locPlace 1 [.unwrapUnsafeBinder u32MirTy]),
            .copy (locPlace 2)])),
       mkSt (.assign (locPlace 3 [.field 0 u32MirTy]) (.use (constU32 44))),
       mkSt (.assign (locPlace 4) (.use (.copy (locPlace 1)))),
       mkSt (.assign (locPlace 5)
         (.use (.copy (locPlace 3 [.field 1 rawConstU32MirTy])))),
       mkSt (.assign (locPlace 0)
         (.binaryOp .add
           (.copy (locPlace 3 [.field 0 u32MirTy]))
           (.copy (locPlace 5 [.deref]))))]
      .return_]

/-- Exercises `C9 + C10` composite execution (`44 + 19 = 63` while `_1 = 19`
remains initialized after projected `.move`), plus `C9` and `C10` three-way
`Trusted` + `Mach` + `MachTB` (`MachTB.wfLive`) witness bundles. -/
theorem test_c9_c10_binder_and_closure_suite :
    (match runA c9c10CompositeMir 16
             (initMachineState c9c10CompositeMir [.scalar ⟨0, 4⟩]) with
     | some ([], .normal (vRet, _)) => vRet = .scalar ⟨63, 4⟩
     | _ => False) ∧
    translatePlace [] ⟨1, [.unwrapUnsafeBinder u32MirTy]⟩ = none ∧
    translateRvalue emptyLayoutTable [] none
      (.aggregate (.closure "tests::cap_cl") []) = none ∧
    (∃ p, p = c9_unwrapUnsafeBinder_three_way_len_and_ub_witness) ∧
    (∃ p, p = c10_closure_zst_capture_and_ub_three_way_witness) :=
  ⟨rfl,
   (translatePlace_unwrapUnsafeBinder_none [] 1 u32MirTy []
     (.Local (localName 1))).1,
   translateRvalue_closure_none emptyLayoutTable [] none "tests::cap_cl" [],
   ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- Master conjunction bundling §1..§6 across `Interp` + `C1..C10`. -/
theorem all_c1_to_c10_correspondence_and_witnesses :
    (∃ p, p = mr_full_unwind_and_setDiscriminant_pipeline) ∧
    (∃ p, p = test_c1_setDiscriminant_suite) ∧
    (∃ p, p = test_c1_three_way_witness_bundle) ∧
    (∃ p, p = test_c2_c3_unwind_resume_and_terminate_suite) ∧
    (∃ p, p = test_c4_c5_stuttering_and_placeMention_contrast) ∧
    (∃ p, p = test_c6_c7_c8_coercions_fnPtrToPtr_and_subtype_suite) ∧
    (∃ p, p = test_c9_c10_binder_and_closure_suite) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-! ## §7. Bounded Axiom & Semantic-Reachability Audit -/

section Audit
open Lean Elab Command

/-- Bounded constant-dependency BFS (`maxNodes` cap prevents unbounded traversal
over huge generated upstream AST tables while still reaching all operational
entry points of `Trusted.MirSemantics` and `MiniRustSpec.Interp`). -/
private def boundedReachable (env : Environment) (seeds : Array Lean.Name)
    (targets : Lean.NameSet) (maxNodes : Nat := 12000) :
    Lean.NameSet := Id.run do
  let mut visited : Lean.NameSet := {}
  let mut found : Lean.NameSet := {}
  let mut queue : Array Lean.Name := seeds
  let mut idx : Nat := 0
  while idx < queue.size && visited.size < maxNodes &&
        found.size < targets.size do
    let cur := queue[idx]!
    idx := idx + 1
    unless visited.contains cur do
      visited := visited.insert cur
      if targets.contains cur then
        found := found.insert cur
      if let some info := env.find? cur then
        for dep in info.type.getUsedConstants do
          unless visited.contains dep do queue := queue.push dep
        if let some val := info.value? then
          for dep in val.getUsedConstants do
            unless visited.contains dep do queue := queue.push dep
  return found

/-- Verifies:
1. Every local declaration in `UnwindSetDiscrAndFnPtrTests` plus the bounded
   `C1..C10` anchor manifest in `MiniRustSpec.UnwindSetDiscrAndFnPtrMR` and
   `MiniRustSpec.Interp` uses only standard axioms (`propext`, `Quot.sound`,
   `Classical.choice`) with zero `sorryAx`, `Lean.ofReduceBool`, or
   `Lean.trustCompiler`.
2. Bounded constant reachability from the `C1..C10` anchor manifest reaches the
   ground operational definitions in `Trusted.Rustc.V2026_06_01.MirSemantics`
   and `MiniRustSpec.Interp`. -/
elab "#audit_unwind_setdiscr_fnptr_tests" : command => do
  let env ← getEnv
  let anchors : Array Lean.Name := #[
    ``all_c1_to_c10_correspondence_and_witnesses,
    ``mr_full_unwind_and_setDiscriminant_pipeline,
    ``setDiscriminant_twoVar_coupled_lockstep_and_wfLive,
    ``setDiscriminant_discriminant_readback_and_invalid_divergence,
    ``unwindResume_continue_chain_coupled_steps_and_wfLive,
    ``minirust_start_resume_stop_unwind_tb_wfLive,
    ``unwindTerminate_lockstep_abort_mach_and_tb,
    ``coverage_stuttering_step,
    ``backwardIncompatibleDropHint_stuttering_step,
    ``erasedNoopStmt_chain_stuttering,
    ``fnPtrToPtr_lockstep_mach_and_tb,
    ``subtype_thinPtr_and_u32_coupled_lockstep,
    ``reify_unsafe_fnPtrToPtr_pipeline,
    ``reify_cached_and_fnFromPtrM_roundtrip,
    ``unsafeFnPointer_trusted_unsupported_divergence,
    ``mutToConstPointer_all_shapes_and_ub,
    ``arrayToPointer_global_stack_scalar_and_ub,
    ``unwrapUnsafeBinder_assign_coupled_lockstep_and_wfLive,
    ``unwrapUnsafeBinder_uninit_assign_and_move,
    ``closure_assign_coupled_lockstep_and_wfLive,
    ``closure_cap_field_projection_lockstep_M
  ]
  let mut localCount : Nat := 0
  for (c, _) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    localCount := localCount + 1
  for c in anchors do
    unless env.contains c do
      throwError "missing anchor declaration {c}"
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "anchor {c} depends on sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "anchor {c} depends on non-standard axiom {a}"
  let requiredTargets : Array Lean.Name := #[
    ``Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.unwindFromCallStack,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.evalFnPtrToPtr,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.evalUnsafeFnPointer,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.evalByteCast,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue,
    ``MiniRustSpec.Interp.evalSetDiscriminantM,
    ``MiniRustSpec.Interp.evalResumeUnwindM,
    ``MiniRustSpec.Interp.evalStatementM,
    ``MiniRustSpec.Interp.evalTerminatorM,
    ``MiniRustSpec.Interp.stepM
  ]
  let targetSet := requiredTargets.foldl (fun s n => s.insert n)
    ({} : Lean.NameSet)
  let reached := boundedReachable env anchors targetSet 12000
  for req in requiredTargets do
    unless reached.contains req do
      throwError "reachability audit failed: {req} not reached from C1..C10"
  logInfo m!"[UNWIND-SETDISCR-FNPTR-TESTS] local_decls={localCount} anchors={anchors.size} reached={reached.size}/{requiredTargets.size} axioms=standard_only ok=true"

#audit_unwind_setdiscr_fnptr_tests

end Audit

end Anneal.UnwindSetDiscrAndFnPtrTests
