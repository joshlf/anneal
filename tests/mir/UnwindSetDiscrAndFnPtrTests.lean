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

Exercises Episode 1's MiniRust `SetDiscriminant`, `Validate`, `StartUnwind`,
`ResumeUnwind`, and `StopUnwind` interpretation across `Mach` (`BasicMemory`)
and `MachTB` (`TreeBorrowsMemory`) together with Episode 2's correspondence,
boundary, and divergence theorems for `C1` (`setDiscriminant`), `C2`
(`unwindResume`), `C3` (`unwindTerminate`), `C4` (`coverage`), `C5`
(`backwardIncompatibleDropHint`), `C6` (`fnPtrToPtr`), `C7` (`subtype`), `C8`
(all 5 non-`Unsize` `pointerCoercion`s), `C9` (`unwrapUnsafeBinder`), and
`C10` (`AggregateKind.closure`).
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

/-! ## §1. MiniRust Unwind & `SetDiscriminant` (`Mach` & `MachTB`) Pipeline -/

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

/-! ## §1b. Fault Injection on the Unwind & `SetDiscriminant` Pipeline -/

/-- Single-point mutations of `mrFullUnwindSetDiscrMach`: `calleeUnwind` is the
unwind block the caller registered for the callee frame, `skipStart` replaces
the callee's `StartUnwind` by a plain `Goto` (so no payload is ever pushed), and
`tag` is the discriminant written by the caller's `SetDiscriminant`. -/
def mrUnwindFaultMach (calleeUnwind : Option Gen.BbName) (skipStart : Bool)
    (tag : Int) : Mach :=
  let calleeFn := mkMrFn
    [(localName 0, unitType), (localName 1, refTy .mut u32)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[.Validate (.Local (localName 1)) true],
        if skipStart then .Goto (bbName 1)
        else .StartUnwind (.Constant (.PointerWithoutProvenance 4096)
          thinRawPtrTy) (bbName 1), .Regular⟩),
     (bbName 1, ⟨[], .ResumeUnwind, .Cleanup⟩)]
  let callerFn := mkMrFn
    [(localName 0, twoVarEnumMrTy)] [] (localName 0)
    [(bbName 0, ⟨[], .Goto (bbName 1), .Regular⟩),
     (bbName 1, ⟨[], .StopUnwind (bbName 2), .Cleanup⟩),
     (bbName 2, ⟨[.SetDiscriminant (.Local (localName 0)) tag],
        .Return, .Regular⟩)]
  let callerFr := mkRootFrame callerFn
    [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]
  let calleeFr : Frame :=
    { func := calleeFn
      locals := ⟨[(localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]⟩
      stack_pop_action := .BackToCaller (some (bbName 0)) calleeUnwind
        dummyRetPtr
      next_block := bbName 0
      next_stmt := 0
      extra := () }
  mkMrMach (mkMrProg [(fnName 0, callerFn), (fnName 1, calleeFn)])
    [mkStackAlloc 128 c1LocalInitBytes 4,
     mkStackAlloc 256 (ptrBytes 128 (some (⟨0⟩, ()))) 8]
    [callerFr, calleeFr]

/-- Root frame whose only block executes `ResumeUnwind`. -/
def mrRootResumeUnwindMach : Mach :=
  let fn := mkMrFn [] [] (localName 0)
    [(bbName 0, ⟨[], .ResumeUnwind, .Cleanup⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [] [mkRootFrame fn []]

/-- Negative counterpart of `mr_full_unwind_and_setDiscriminant_pipeline` on
both `Mach` and `MachTB`. The unmutated instance IS the positive machine;
each mutation runs its fault-free prefix (pinned by the surviving stack depth
and payload count) and then faults at the mutated step: a callee frame
without a registered unwind block (`ResumeUnwind` UB at step `3`), unwinding
without `StartUnwind` (`StopUnwind` empty-payload UB at step `4`), and an
out-of-range discriminant (`SetDiscriminant` `specPanic` at step `5`). A root
frame executing `ResumeUnwind` is UB, the MiniRust half of the root-frame
divergence whose Trusted half (`.retOutcome .panic`) is in §3. -/
theorem mr_unwind_and_setDiscriminant_fault_injection :
    mrUnwindFaultMach (some (bbName 1)) false 1 = mrFullUnwindSetDiscrMach ∧
    (∃ m2, Interp.steps 2 (mrUnwindFaultMach none false 1) = .ok m2 ∧
      m2.threads[0]?.map (fun t =>
        (t.stack.length, t.unwind_payloads.length)) = some (2, 1)) ∧
    Interp.steps 3 (mrUnwindFaultMach none false 1) = .error (.ub
      "unwinding from a function where the caller did not specify an unwind_block") ∧
    Interp.stepsTB 3 (liftMachToTB (mrUnwindFaultMach none false 1)) = .error (.ub
      "unwinding from a function where the caller did not specify an unwind_block") ∧
    (∃ m3, Interp.steps 3 (mrUnwindFaultMach (some (bbName 1)) true 1) = .ok m3 ∧
      m3.threads[0]?.map (fun t =>
        (t.stack.length, t.unwind_payloads.length)) = some (1, 0)) ∧
    Interp.steps 4 (mrUnwindFaultMach (some (bbName 1)) true 1) =
      .error (.ub "StopUnwind: the payload stack is empty") ∧
    Interp.stepsTB 4 (liftMachToTB (mrUnwindFaultMach (some (bbName 1)) true 1)) =
      .error (.ub "StopUnwind: the payload stack is empty") ∧
    (∃ m4, Interp.steps 4 (mrUnwindFaultMach (some (bbName 1)) false 2) = .ok m4 ∧
      m4.threads[0]?.map (fun t =>
        (t.stack.length, t.unwind_payloads.length)) = some (1, 0)) ∧
    Interp.steps 5 (mrUnwindFaultMach (some (bbName 1)) false 2) =
      .error (.specPanic "setting an invalid discriminant (2)") ∧
    Interp.stepsTB 5 (liftMachToTB (mrUnwindFaultMach (some (bbName 1)) false 2)) =
      .error (.specPanic "setting an invalid discriminant (2)") ∧
    Interp.step mrRootResumeUnwindMach = .error (.ub
      "the function at the bottom of the stack must not unwind") ∧
    Interp.stepTB (liftMachToTB mrRootResumeUnwindMach) = .error (.ub
      "the function at the bottom of the stack must not unwind") :=
  ⟨rfl, ok_of_map_toOption (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   ok_of_map_toOption (by decide +kernel),
   eq_error_specPanic_of_interpSpecPanic (by decide +kernel),
   eq_error_specPanic_of_interpSpecPanic (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ## §2 (`C1`): `StatementKind.setDiscriminant` Round-Trip & Niche Checks -/

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

/-- Exercises `C1` multi-flip discriminant updates (`0 → 1 → 0`), verifying BOTH
`Rvalue.discriminant` read-backs (`_2 = 1` at step 4 and `_3 = 0` at step 6),
payload preservation (`77`), niche `Option<NonZeroU8>` valid & invalid-variant
divergence (Trusted `.ub` vs. MiniRust `.specPanic` on `Mach` & `MachTB`), and
the `translateStatement = none` fragment boundary. -/
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
               some (.init (.aggregate 1 [.scalar ⟨77, 4⟩])) ∧
             (match stepMirFn c1ToggleEnumMir s4 with
              | .tau (.running s5) =>
                match stepMirFn c1ToggleEnumMir s5 with
                | .tau (.running s6) =>
                  get? s6.frame.locals 3 = some (.init (.scalar ⟨0, 8⟩)) ∧
                  get? s6.frame.locals 1 =
                    some (.init (.aggregate 0 [.scalar ⟨77, 4⟩]))
                | _ => False
              | _ => False)
           | _ => False
         | _ => False
       | _ => False
     | _ => False) ∧
    (let optMir (tag : Nat) := mkMirBody "ep2::c1_niche_opt"
       [mkDecl u64MirTy, mkDecl optionNonZeroU8MirTy] 1
       [mkBb [mkSt (.setDiscriminant (locPlace 1) tag),
              mkSt (.assign (locPlace 0) (.discriminant (locPlace 1)))] .return_]
       optionNonZeroU8Layouts
     let optMach (tag : Int) : Mach :=
       let fn := mkMrFn
         [(localName 0, optionNonZeroU8MrTy),
          (localName 1, optionNonZeroU8MrTy)]
         [localName 1] (localName 0)
         [(bbName 0, ⟨[.SetDiscriminant (.Local (localName 1)) tag,
                       .Assign (.Local (localName 0))
                         (.Load (.Local (localName 1)))],
                       .Return, .Regular⟩)]
       mkMrMach (mkMrProg [(fnName 0, fn)])
         [mkStackAlloc 128 [.Uninit] 1, mkStackAlloc 256 [.Init 7 none] 1]
         [mkRootFrame fn
           [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
            (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]
     runAVal (optMir 1) 5
       (initMachineState (optMir 1) [.aggregate 1 [.scalar ⟨7, 1⟩]]) =
       some (.scalar ⟨1, 8⟩) ∧
     runAVal (optMir 0) 5
       (initMachineState (optMir 0) [.aggregate 1 [.scalar ⟨7, 1⟩]]) =
       some (.scalar ⟨0, 8⟩) ∧
     (match stepMirFn (optMir 2)
              (initMachineState (optMir 2) [.aggregate 1 [.scalar ⟨7, 1⟩]]) with
      | .tau (.running s1) => stepMirFn (optMir 2) s1 = MirStepNode.fail .ub
      | _ => False) ∧
     Interp.step (optMach 2) =
       .error (.specPanic "setting an invalid discriminant (2)") ∧
     Interp.stepTB (liftMachToTB (optMach 2)) =
       .error (.specPanic "setting an invalid discriminant (2)")) ∧
    translateStatement [] { kind := .setDiscriminant (locPlace 1) 1,
                            span := dummySpan } twoVarLayouts = none :=
  ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩,
   ⟨c1_niche_optionNonZeroU8_three_way_witness.1,
    c1_niche_optionNonZeroU8_three_way_witness.2.2.2.1,
    c1_niche_optionNonZeroU8_three_way_witness.2.2.2.2.2.2.1,
    c1_niche_optionNonZeroU8_three_way_witness.2.2.2.2.2.2.2.1,
    c1_niche_optionNonZeroU8_three_way_witness.2.2.2.2.2.2.2.2⟩,
   translateStatement_setDiscriminant_none [] (locPlace 1) 1 dummySpan
     twoVarLayouts⟩

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
`.unreachable` UB, `.terminate` / `unwindTerminate` `.abort` (including lockstep
MiniRust `Mach` & `MachTB` `buildAbort`), root `.panic`, and
`translateTerminator = none` boundaries. -/
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
    Interp.step c3AbortMach = .error .abort ∧
    Interp.stepTB (liftMachToTB c3AbortMach) = .error .abort ∧
    translateTerminator emptyLayoutTable []
      { kind := .unwindResume, span := dummySpan } = none ∧
    translateTerminator emptyLayoutTable []
      { kind := .unwindTerminate, span := dummySpan } = none :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩,
   c3_unwindTerminate_three_way_witness.2.1,
   c3_unwindTerminate_three_way_witness.2.2,
   translateTerminator_unwindResume_none emptyLayoutTable [] dummySpan,
   translateTerminator_unwindTerminate_none emptyLayoutTable [] dummySpan⟩

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
4-statement `[coverage, dropHint, coverage, dropHint]` block slice, contrasts
`backwardIncompatibleDropHint` safety on dead `_1` with `placeMention` UB, and
pins both `translateStatement = none` fragment boundaries. -/
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
    translateStatement [] { kind := .coverage, span := dummySpan }
      emptyLayoutTable = none ∧
    translateStatement []
      { kind := .backwardIncompatibleDropHint (locPlace 1), span := dummySpan }
      emptyLayoutTable = none := by
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
    noops [mkSt (.storageDead 1)]
    [mkSt (.assign (locPlace 0) (.use (constU32 63)))]
    c4c5DeadState hAll rfl rfl rfl rfl
  exact ⟨⟨hChain.1, (hChain.2 2).1⟩, rfl, rfl,
    translateStatement_coverage_none [] dummySpan emptyLayoutTable,
    translateStatement_backwardIncompatibleDropHint_none [] (locPlace 1)
      dummySpan emptyLayoutTable⟩

/-! ## §5 (`C6`–`C8`): Composite Coercions, `fnPtrToPtr`, & `subtype` -/

/-- Composite `CapturedMir` body exercising `AggregateKind.closure` (`0`
captures) → `"ClosureFnPointer(Safe)"` → `"UnsafeFnPointer"` → `fnPtrToPtr` →
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
         (.cast (.pointerCoercion "ClosureFnPointer(Safe)") (.copy (locPlace 1))
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

/-- Pointer-to-integer `CastKind.subtype` (`*const u32 → usize`) body used to
verify provenance-stripping UB in `Trusted.MirSemantics`. -/
def c7SubtypePtrToUsizeMir : CapturedMir :=
  mkMirBody "tests::c7_ptr_to_usize"
    [mkDecl UnwindSetDiscrAndFnPtrMR.usizeMirTy, mkDecl rawConstU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0)
      (.cast .subtype (.copy (locPlace 1))
        UnwindSetDiscrAndFnPtrMR.usizeMirTy))] .return_]

/-- Wide-slice `CastKind.subtype` (`*mut [u32] → *const [u32]`) body. -/
def c7SubtypeWideSliceMir : CapturedMir :=
  mkMirBody "tests::c7_wide_slice"
    [mkDecl rawConstSliceU32MirTy, mkDecl rawMutSliceU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0)
      (.cast .subtype (.copy (locPlace 1)) rawConstSliceU32MirTy))] .return_]

/-- Exercises `C6..C8` composite pipeline, `fnPtrToPtr` nonzero-offset &
non-fn-alloc UB, `subtype` (`NonZeroU8`, `bool`, pointer-to-`usize` UB, wide
slice), explicit `unsafeFnPointer_trusted_unsupported_divergence` propositions
(Trusted `.unsupported`/`.ub` vs. MiniRust `Mach`/`MachTB` `Transmute`),
disabled-borrow `ArrayToPointer` UB, `"ClosureFnPointer"` tag variants, and
`translateRvalue = none` boundaries (capturing-closure and strict-check UB
live in `test_c1_c8_c9_strict_check_and_validity_ub_suite`). -/
theorem test_c6_c7_c8_coercions_fnPtrToPtr_and_subtype_suite :
    (match runA c6c7c8CompositeMir 24 (initMachineState c6c7c8CompositeMir []) with
     | some ([], .normal (vRet, memEnd)) =>
       vRet = .scalar ⟨64, 4⟩ ∧ length memEnd.fnPtrs = 1
     | _ => False) ∧
    stepMirFn c6FnPtrToPtrMir
      (initMachineState c6FnPtrToPtrMir
        [.ptr { allocId := fnPtrAllocBase, offsetBytes := 1 } 8]) =
      MirStepNode.fail .ub ∧
    stepMirFn c6FnPtrToPtrMir
      (initMachineState c6FnPtrToPtrMir [.ptr { allocId := 1, offsetBytes := 0 } 8]) =
      MirStepNode.fail .ub ∧
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
    stepMirFn c7SubtypePtrToUsizeMir
      (initMachineState c7SubtypePtrToUsizeMir
        [.ptr { allocId := 5, offsetBytes := 0 } 8]) =
      MirStepNode.fail .ub ∧
    runAVal c7SubtypeWideSliceMir 4
      (initMachineState c7SubtypeWideSliceMir
        [annealWidePtrVal { allocId := 5, offsetBytes := 0 } 3 8]) =
      some (annealWidePtrVal { allocId := 5, offsetBytes := 0 } 3 8) ∧
    (let locs := [LocalSlot.uninit,
                  LocalSlot.init (.ptr { allocId := fnPtrAllocBase,
                                         offsetBytes := 0 } 8)]
     let decls := [mkDecl fnPtrUnsafeU32MirTy, mkDecl fnPtrSafeU32MirTy]
     let mem := (initMachineState c6FnPtrToPtrMir []).memory
     evalRvalue locs
       (.cast (.pointerCoercion "CustomUnknownCoercion") (.copy (locPlace 1))
         fnPtrUnsafeU32MirTy) mem decls emptyLayoutTable = .unsupported ∧
     evalRvalue locs
       (.cast (.pointerCoercion "UnsafeFnPointer(Unsafe)") (.copy (locPlace 1))
         fnPtrUnsafeU32MirTy) mem decls emptyLayoutTable = .unsupported ∧
     evalRvalue locs
       (.cast (.pointerCoercion "ClosureFnPointer(Normal)") (.copy (locPlace 1))
         fnPtrSafeU32MirTy) mem decls emptyLayoutTable = .unsupported ∧
     evalRvalue locs
       (.cast (.pointerCoercion "UnsafeFnPointer") (.copy (locPlace 1))
         fnPtrSafeU32MirTy) mem decls emptyLayoutTable = .ub ∧
     evalRvalue locs
       (.cast (.pointerCoercion "UnsafeFnPointer") (.copy (locPlace 1))
         fnPtrIntrinsicU32MirTy) mem decls emptyLayoutTable = .ub ∧
     evalCastOp (.Transmute thinRawPtrTy)
       (.Ptr (ThinPointer.widen { addr := 4096, provenance := some (⟨0⟩, ()) } none),
        thinRawPtrTy) none =
       .ok (.Ptr (ThinPointer.widen { addr := 4096, provenance := some (⟨0⟩, ()) } none),
            thinRawPtrTy) ∧
     evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
       (.Ptr (ThinPointer.widen { addr := 4096, provenance := some (⟨0⟩, []) } none),
        thinRawPtrTy) none =
       .ok (.Ptr (ThinPointer.widen { addr := 4096, provenance := some (⟨0⟩, []) } none),
            thinRawPtrTy)) ∧
    (let memDis := { (initMachineState c6FnPtrToPtrMir []).memory with
       borrows := [{ tag := 1, targetLocal := 2, targetProjection := [],
                     perm := .disabled, targetFrameDepth := 0 }] }
     evalRvalue
       [.uninit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
        .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩])]
       (.cast (.pointerCoercion "ArrayToPointer") (.copy (locPlace 1))
         rawMutU32MirTy)
       memDis [mkDecl rawMutU32MirTy, mkDecl rawMutArr2U32MirTy, mkDecl arr2U32MirTy]
       emptyLayoutTable = .ub) ∧
    translateRvalue emptyLayoutTable [] none
      (.cast .fnPtrToPtr (.copy (locPlace 1)) rawConstUnitMirTy) = none ∧
    translateRvalue emptyLayoutTable [] none
      (.cast .subtype (.copy (locPlace 1)) rawConstU32MirTy) = none ∧
    translateRvalue emptyLayoutTable [] none
      (.cast (.pointerCoercion "ClosureFnPointer(Unsafe)") (.copy (locPlace 1))
        fnPtrUnsafeU32MirTy) = none := by
  let locs := [LocalSlot.uninit,
               LocalSlot.init (.ptr { allocId := fnPtrAllocBase,
                                      offsetBytes := 0 } 8)]
  let decls := [mkDecl fnPtrUnsafeU32MirTy, mkDecl fnPtrSafeU32MirTy]
  let mem := (initMachineState c6FnPtrToPtrMir []).memory
  have hDiv := unsafeFnPointer_trusted_unsupported_divergence
    locs locs (.copy (locPlace 1)) fnPtrUnsafeU32MirTy mem decls
    emptyLayoutTable { allocId := fnPtrAllocBase, offsetBytes := 0 } 4096
    (by decide) (some (⟨0⟩, ())) (some (⟨0⟩, [])) none none rfl
    "CustomUnknownCoercion"
  exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨hDiv.1 rfl rfl rfl rfl, hDiv.2.1, rfl, hDiv.2.2.1, hDiv.2.2.2.2.1,
     hDiv.2.2.2.2.2.1, hDiv.2.2.2.2.2.2⟩,
    rfl,
    translateRvalue_fnPtrToPtr_none emptyLayoutTable [] none (.copy (locPlace 1))
      rawConstUnitMirTy,
    translateRvalue_subtype_none emptyLayoutTable [] none (.copy (locPlace 1))
      rawConstU32MirTy,
    translateRvalue_pointerCoercion_none emptyLayoutTable [] none
      "ClosureFnPointer(Unsafe)" (.copy (locPlace 1)) fnPtrUnsafeU32MirTy⟩

/-! ## §6 (`C9` & `C10`): `unwrapUnsafeBinder` + `AggregateKind.closure` -/

/-- Composite `CapturedMir` body that writes `19` through `.unwrapUnsafeBinder`,
borrows `&raw const (_1.unwrapUnsafeBinder)`, constructs a 2-capture closure
`[move (_1.unwrapUnsafeBinder), copy _2]`, mutates capture `_3.0 = 44`, copies
`_4 = _1` (verifying `_1` stays initialized after projected `.move`), copies
`_5 = _3.1`, and reads `*_5` (`44 + 19 = 63`). -/
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

/-- Unprojected `.move _1` into a 2-capture closure followed by `copy _1`,
contrasting whole-local `.move` deinitialization UB against projected
`.move (_1.unwrapUnsafeBinder)` in `c9c10CompositeMir`. -/
def c10UnprojectedMoveUbMir : CapturedMir :=
  mkMirBody "tests::c10_unprojected_move_ub"
    [mkDecl u32MirTy,
     mkDecl u32MirTy,
     mkDecl rawConstU32MirTy,
     mkDecl (closureCapMirTy "tests::cap_mv")] 1
    [mkBb
      [mkSt (.storageLive 2), mkSt (.storageLive 3),
       mkSt (.assign (locPlace 2) (.rawPtr .not (locPlace 1))),
       mkSt (.assign (locPlace 3)
         (.aggregate (.closure "tests::cap_mv")
           [.move (locPlace 1), .copy (locPlace 2)])),
       mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1))))]
      .return_]

/-- Deterministic `n`-step `stepMirFn` runner returning `some s'` when every
step produces `.tau (.running _)`. -/
private def stepN (body : CapturedMir) : Nat → MachineState → Option MachineState
  | 0, s => some s
  | n + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => stepN body n s'
    | _ => none

/-- Exercises `C9 + C10` composite execution (`44 + 19 = 63` with explicit
step check `_4 = 19` proving `_1` remains initialized after projected `.move`),
contrasting whole-local `.move` post-move UB in `c10UnprojectedMoveUbMir`, `C9`
`.uninit`-destination assign UB, `Rvalue.len` through `.unwrapUnsafeBinder`, and
`translatePlace`/`translateRvalue = none` fragment boundaries. -/
theorem test_c9_c10_binder_and_closure_suite :
    (match runA c9c10CompositeMir 16
             (initMachineState c9c10CompositeMir [.scalar ⟨0, 4⟩]) with
     | some ([], .normal (vRet, _)) => vRet = .scalar ⟨63, 4⟩
     | _ => False) ∧
    (let s0 := initMachineState c9c10CompositeMir [.scalar ⟨0, 4⟩]
     match stepN c9c10CompositeMir 9 s0 with
     | some s9 =>
       get? s9.frame.locals 4 = some (.init (.scalar ⟨19, 4⟩)) ∧
       get? s9.frame.locals 1 = some (.init (.scalar ⟨19, 4⟩))
     | none => False) ∧
    (let s0 := initMachineState c10UnprojectedMoveUbMir [.scalar ⟨19, 4⟩]
     match stepN c10UnprojectedMoveUbMir 4 s0 with
     | some s4 =>
       get? s4.frame.locals 1 = some .uninit ∧
       stepMirFn c10UnprojectedMoveUbMir s4 = MirStepNode.fail .ub
     | none => False) ∧
    stepMirFn c9BinderReadWriteMir
      { frame := { blockIdx := 0, stmtIdx := 2,
                   locals := [.uninit, .uninit, .uninit, .uninit, .uninit] },
        memory := (initMachineState c9BinderReadWriteMir []).memory } =
      MirStepNode.fail .ub ∧
    evalRvalue
      [.init (annealWidePtrVal { allocId := 9, offsetBytes := 0 } 4 8)]
      (.len (locPlace 0 [.deref,
        .unwrapUnsafeBinder { kind := .slice (.uint .u32), layoutIdx := 0 }]))
      (initMachineState c9BinderReadWriteMir []).memory
      [mkDecl rawConstSliceU32MirTy] emptyLayoutTable =
      .ok (.scalar ⟨4, 8⟩)
        [.init (annealWidePtrVal { allocId := 9, offsetBytes := 0 } 4 8)]
        (initMachineState c9BinderReadWriteMir []).memory ∧
    translatePlace [] ⟨1, [.unwrapUnsafeBinder u32MirTy]⟩ = none ∧
    translateRvalue emptyLayoutTable [] none
      (.aggregate (.closure "tests::cap_cl") []) = none :=
  ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl,
   (translatePlace_unwrapUnsafeBinder_none [] 1 u32MirTy []
     (.Local (localName 1))).1,
   translateRvalue_closure_none emptyLayoutTable [] none "tests::cap_cl" []⟩

/-! ## §6b. Strict-Check & Validity Fault Cases (`C1`, `C8.2`, `C9`) -/

/-- `_0 = copy (_1 as unwrap_binder<ty>)` reading `_1 : srcTy` at `ty`. -/
def c9BinderValidityMir (ty srcTy : MirAst.Ty) : CapturedMir :=
  mkMirBody "tests::c9_binder_validity" [mkDecl ty, mkDecl srcTy] 1
    [mkBb [mkSt (.assign (locPlace 0)
      (.use (.copy (locPlace 1 [.unwrapUnsafeBinder ty]))))] .return_]

/-- Fault cases the positive suites leave implicit, each paired with a passing
control so no conjunct holds vacuously: `C1` `setDiscriminant` on a `.dead`
enum local; `C8.2` `ClosureFnPointer` on a capturing closure, on a
safety-tag/target mismatch (both directions), and on a `rust-intrinsic` ABI
target (control: `(Unsafe)` and bare tags intern `fnPtrAllocBase`); and `C9`
`unwrapUnsafeBinder` reads of bytes invalid at the inner type (`bool` byte
`2`; control: byte `1`). -/
theorem test_c1_c8_c9_strict_check_and_validity_ub_suite :
    stepMirFn c1ToggleEnumMir
      { frame := { blockIdx := 0, stmtIdx := 2,
                   locals := [.uninit, .dead, .uninit, .uninit] },
        memory := (initMachineState c1ToggleEnumMir []).memory } =
      MirStepNode.fail .ub ∧
    (let mem := (initMachineState c6FnPtrToPtrMir []).memory
     let zstTy := closureZstMirTy "tests::zst_cl"
     let zst : List LocalSlot := [.uninit, .init (.aggregate 0 [])]
     let cl (tag : String) (dst clTy : MirAst.Ty) (locs : List LocalSlot) :=
       evalRvalue locs
         (.cast (.pointerCoercion tag) (.copy (locPlace 1)) dst) mem
         [mkDecl dst, mkDecl clTy] emptyLayoutTable
     let interned (tag : String) (dst : MirAst.Ty) : Prop :=
       match cl tag dst zstTy zst with
       | .ok (.ptr p 8) _ mem' =>
         p = { allocId := fnPtrAllocBase, offsetBytes := 0 } ∧
         length mem'.fnPtrs = 1
       | _ => False
     cl "ClosureFnPointer(Safe)" fnPtrSafeU32MirTy
       (closureCapMirTy "tests::cap_cl")
       [.uninit, .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨0, 8⟩])] = .ub ∧
     cl "ClosureFnPointer(Safe)" fnPtrUnsafeU32MirTy zstTy zst = .ub ∧
     cl "ClosureFnPointer(Unsafe)" fnPtrSafeU32MirTy zstTy zst = .ub ∧
     cl "ClosureFnPointer(Safe)" fnPtrIntrinsicU32MirTy zstTy zst = .ub ∧
     interned "ClosureFnPointer(Unsafe)" fnPtrUnsafeU32MirTy ∧
     interned "ClosureFnPointer" fnPtrSafeU32MirTy) ∧
    runAVal (c9BinderValidityMir boolMirTy u8MirTy) 4
      (initMachineState (c9BinderValidityMir boolMirTy u8MirTy)
        [.scalar ⟨1, 1⟩]) = some (.scalar ⟨1, 1⟩) ∧
    stepMirFn (c9BinderValidityMir boolMirTy u8MirTy)
      (initMachineState (c9BinderValidityMir boolMirTy u8MirTy)
        [.scalar ⟨2, 1⟩]) = MirStepNode.fail .ub :=
  ⟨rfl, ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, rfl, rfl⟩

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
1. Every local declaration in `UnwindSetDiscrAndFnPtrTests` plus every
   universal and three-way witness anchor in
   `MiniRustSpec.UnwindSetDiscrAndFnPtrMR` uses only standard axioms
   (`propext`, `Quot.sound`, `Classical.choice`) with zero `sorryAx`,
   `Lean.ofReduceBool`, or `Lean.trustCompiler`.
2. Bounded constant reachability from the local test theorems ALONE (not the
   imported `MiniRustSpec.UnwindSetDiscrAndFnPtrMR` anchors, which would
   satisfy it regardless of what this file tests) reaches all ground
   operational definitions in `Trusted.Rustc.V2026_06_01.MirSemantics` and
   `MiniRustSpec.Interp`. -/
elab "#audit_unwind_setdiscr_fnptr_tests" : command => do
  let env ← getEnv
  let localTests : Array Lean.Name := #[
    ``mr_full_unwind_and_setDiscriminant_pipeline,
    ``mr_unwind_and_setDiscriminant_fault_injection,
    ``test_c1_setDiscriminant_suite,
    ``test_c2_c3_unwind_resume_and_terminate_suite,
    ``test_c4_c5_stuttering_and_placeMention_contrast,
    ``test_c6_c7_c8_coercions_fnPtrToPtr_and_subtype_suite,
    ``test_c9_c10_binder_and_closure_suite,
    ``test_c1_c8_c9_strict_check_and_validity_ub_suite]
  let anchors : Array Lean.Name := localTests ++ #[
    ``setDiscriminant_twoVar_coupled_lockstep_and_wfLive,
    ``setDiscriminant_discriminant_readback_and_invalid_divergence,
    ``c1_setDiscriminant_local_three_way_witness,
    ``c1_niche_optionNonZeroU8_three_way_witness,
    ``c1_setDiscriminant_deref_three_way_witness,
    ``c1_setDiscriminant_uninit_shell_witness,
    ``c1_setDiscriminant_dead_local_ub_witness,
    ``c1_setDiscriminant_misaligned_and_frozen_ub_witness,
    ``unwindResume_continue_chain_coupled_steps_and_wfLive,
    ``minirust_start_resume_stop_unwind_tb_wfLive,
    ``c2_unwindResume_all_five_regimes_witness,
    ``c2_start_resume_stop_unwind_composition_witness,
    ``c2_machTB_protector_release_on_resumeUnwind_witness,
    ``unwindTerminate_lockstep_abort_mach_and_tb,
    ``c3_unwindTerminate_three_way_witness,
    ``coverage_stuttering_step,
    ``c4_coverage_stuttering_three_way_witness,
    ``backwardIncompatibleDropHint_stuttering_step,
    ``erasedNoopStmt_chain_stuttering,
    ``c5_backwardIncompatibleDropHint_dead_place_no_ub_witness,
    ``fnPtrToPtr_lockstep_mach_and_tb,
    ``c6_fnPtrToPtr_three_way_and_ub_witness,
    ``subtype_thinPtr_and_u32_coupled_lockstep,
    ``c7_subtype_positive_and_invalid_ub_three_way_witness,
    ``reify_unsafe_fnPtrToPtr_pipeline,
    ``reify_cached_and_fnFromPtrM_roundtrip,
    ``unsafeFnPointer_trusted_unsupported_divergence,
    ``mutToConstPointer_all_shapes_and_ub,
    ``arrayToPointer_global_stack_scalar_and_ub,
    ``c8_all_five_pointer_coercions_three_way_witness,
    ``c8_capturing_closure_wide_and_unknown_tag_witness,
    ``unwrapUnsafeBinder_assign_coupled_lockstep_and_wfLive,
    ``unwrapUnsafeBinder_uninit_assign_and_move,
    ``c9_unwrapUnsafeBinder_three_way_len_and_ub_witness,
    ``closure_assign_coupled_lockstep_and_wfLive,
    ``closure_cap_field_projection_lockstep_M,
    ``c10_closure_zst_capture_and_ub_three_way_witness
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
  let reached := boundedReachable env localTests targetSet 12000
  for req in requiredTargets do
    unless reached.contains req do
      throwError "reachability audit failed: {req} not reached from local tests"
  logInfo m!"[UNWIND-SETDISCR-FNPTR-TESTS] local_decls={localCount} anchors={anchors.size} reached={reached.size}/{requiredTargets.size} axioms=standard_only ok=true"

#audit_unwind_setdiscr_fnptr_tests

end Audit

end Anneal.UnwindSetDiscrAndFnPtrTests
