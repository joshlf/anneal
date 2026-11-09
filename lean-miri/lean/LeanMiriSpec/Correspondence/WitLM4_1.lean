/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM4_1
import LeanMiriSpec.Correspondence.Witness

/-!
# Concrete Multi-Frame Call Stack & `FnEntry` Protector Witnesses (`LM-4.1`)

Concrete, kernel-checked executions of Anneal's `stepMirFn` and `lean-miri`'s
`Miri.Interpreter.Step.step (annealStepHooksLM4_1 ...)` across multi-frame
`Terminator.Call`, `Terminator.Return` (both non-root callee return with stack
local deallocation & `CallId` protector release and root-frame return),
`Terminator.Drop`, and `Terminator.Unreachable`:

* (a) `wit_lm4_1_call_push_simulation`, `wit_lm4_1_callee_return_simulation`,
  `wit_lm4_1_root_return_simulation`: end-to-end 2-frame call + callee return +
  root return (`step_terminator_call_simulation`,
  `step_terminator_return_callee_simulation`,
  `step_terminator_return_root_simulation`), pushing a callee frame onto
  `s.memory.callStack` and `m.stack.frames`, returning `_0` into the caller's
  destination `_1`, releasing the callee's `CallId` protector (`cid = 1`) in
  both `s.memory.activeProtectors` and `m.machine.borrowTracker`
  (`Miri.TreeBorrows.GlobalState.endCall` on a borrow of caller local `_1`),
  deallocating the callee's stack locals, and returning `_0` from the root frame.
* (b) `wit_lm4_1_return_callee_uninit_ub`: returning from a non-root callee
  frame when `_0` is `.uninit` faults with undefined behavior in both Anneal
  and `lean-miri` (`StepRelMultiFrame.ub`).
* (c) `wit_lm4_1_drop_live_and_dead_ub`: `step_terminator_drop_noop_simulation`
  deinitializes a live local and advances to `(target, 0)` in both machines.
* (d) `wit_lm4_1_unreachable_ub` and `wit_lm4_1_call_unreachable_unchecked_ub`:
  `step_terminator_unreachable_ub_simulation` and
  `step_terminator_call_unreachable_unchecked_ub_simulation` fault with
  undefined behavior in both machines.
* (e) `wit_lm4_1_releaseProtector_conflicted_reservedFrz_ok_vs_disabled_ub`:
  concrete `BorrowTree.releaseProtector` witness certifying that releasing a
  conflicted `ReservedFrz true` tag at function exit succeeds (`status = .Released`)
  and preserves the 2-node borrow tree, whereas releasing a `.disabled` tag fails
  with `ChildAccessForbidden .Disabled`.
* (f) `wit_lm4_1_zst_unit_return_simulation` (`H1`): concrete 2-frame callee
  `()` return and root `()` return witness on zero-sized unit type `()`.
* (g) `wit_lm4_1_indirect_dest_call_and_return_simulation` (`H2`): concrete
  call + callee return witness where the caller destination local `_1` is
  `.indirect` (`CallerDestinationRel.indirect`), resolving `_1` to
  `RuntimeStackPlace.memory` on call and writing the returned scalar into the
  caller's stack allocation on return.
* (h) `wit_lm4_1_call_with_copy_and_move_args_simulation` (`M2`): concrete
  2-argument call + return witness with a scalar `.copy` argument (`_2`) and a
  destructive `.move` argument (`_3`), verifying that `_2` stays initialized and
  `_3` is deinitialized in the caller while callee locals `_1, _2` receive the
  argument values.
* (i) `wit_lm4_1_unscoped_borrow_cross_frame_divergence` (`H4`): concrete
  divergence witness certifying that `Trusted` `BorrowEntry.targetLocal` carries
  no frame identifier and persists in `s.memory.borrows` across `TerminatorKind.return_`,
  whereas `lean-miri`'s `Stack.cleanupStackFrame` deallocates the popped callee's
  `.indirect` stack allocation (`deallocFrameLocals`).
-/

namespace LeanMiriSpec.Correspondence.WitnessLM4_1

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-- `u8` type used across the `LM-4.1` multi-frame witnesses. -/
def u8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }

/-- Zero-sized unit type `()` used in the `H1` ZST return witness. -/
def unitTy : Ty := { kind := .tuple .nil, layoutIdx := 0 }

/-- `fn() -> u8` function item type for `"crate::callee"`. -/
def calleeFnTy : Ty := { kind := .fnDef "crate::callee" [], layoutIdx := 0 }

/-- `fn() -> ()` function item type for `"crate::unit_callee"`. -/
def unitCalleeFnTy : Ty := { kind := .fnDef "crate::unit_callee" [], layoutIdx := 0 }

/-- `fn(u8, u8) -> u8` function item type for `"crate::add_args"`. -/
def binaryCalleeFnTy : Ty := { kind := .fnDef "crate::add_args" [], layoutIdx := 0 }

/-- `fn() -> !` function item type for `"core::hint::unreachable_unchecked"`. -/
def unreachableUncheckedFnTy : Ty :=
  { kind := .fnDef "core::hint::unreachable_unchecked" [], layoutIdx := 0 }

/-- Constant operand referencing `"crate::callee"`. -/
def calleeFuncOp : MirAst.Operand :=
  .constant { ty := calleeFnTy, val := .zeroSized }

/-- Constant operand referencing `"crate::unit_callee"`. -/
def unitCalleeFuncOp : MirAst.Operand :=
  .constant { ty := unitCalleeFnTy, val := .zeroSized }

/-- Constant operand referencing `"crate::add_args"`. -/
def binaryCalleeFuncOp : MirAst.Operand :=
  .constant { ty := binaryCalleeFnTy, val := .zeroSized }

/-- Constant operand referencing `"core::hint::unreachable_unchecked"`. -/
def unreachableUncheckedFuncOp : MirAst.Operand :=
  .constant { ty := unreachableUncheckedFnTy, val := .zeroSized }

/-- Local declaration for `u8`. -/
def u8Decl : LocalDecl :=
  { mutability := .mut, ty := u8Ty, debugName := none }

/-- Local declaration for `()`. -/
def unitDecl : LocalDecl :=
  { mutability := .mut, ty := unitTy, debugName := none }

def u8Layout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiU8 : FnAbi :=
  { args := [], ret := { layout := u8Layout, mode := .direct }, conv := .rust, canUnwind := false }

def mkTerm (k : TerminatorKind) : MirAst.Terminator :=
  { kind := k, span := "lm-4.1-witness" }

/-- Concrete `u8` scalar `1` (`boolToScalar true`). -/
def sc1 : MirAst.ScalarInt := boolToScalar true

/-- Concrete `lean-miri` `ScalarInt` for `1u8`. -/
def msc1 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofBool true

theorem val1_immRel :
    ImmediateRel u8Ty emptyLayoutTable (.scalar sc1) (.scalar (.fromScalarInt msc1)) :=
  .scalar sc1 msc1 (ScalarRel.of_boolToScalar true) rfl (fun h => nomatch h) (fun h => nomatch h)

theorem unit_immRel :
    ImmediateRel unitTy emptyLayoutTable .unit .uninit :=
  .unit rfl

/-- Callee MIR body `"crate::callee"`:
`bb0`: `return` (returns `_0 : u8`). -/
def witCalleeBody : CapturedMir where
  defPath := "crate::callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl]
  basicBlocks :=
    [{ statements := []
       terminator := mkTerm .return_
       isCleanup := false }]
  fnAbi := fnAbiU8
  layouts := emptyLayoutTable
  allocations := []

/-- Caller MIR body `"crate::caller"`:
* `bb0`: `_1 = call crate::callee() -> bb1`
* `bb1`: `return`
* `bb2`: `drop(_1) -> bb1`
* `bb3`: `unreachable`
* `bb4`: `_1 = call core::hint::unreachable_unchecked() -> !` -/
def witCallerBody : CapturedMir where
  defPath := "crate::caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl, u8Decl]
  basicBlocks :=
    [ { statements := []
        terminator := mkTerm (.call calleeFuncOp [] ⟨1, .nil⟩ (some 1) .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm .return_
        isCleanup := false }
    , { statements := []
        terminator := mkTerm (.drop ⟨1, .nil⟩ 1 .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm .unreachable
        isCleanup := false }
    , { statements := []
        terminator := mkTerm (.call unreachableUncheckedFuncOp [] ⟨1, .nil⟩ none .unreachable)
        isCleanup := false } ]
  fnAbi := fnAbiU8
  layouts := emptyLayoutTable
  allocations := []

/-- Root `lean-miri` frame for `witCallerBody` at `(bbIdx, 0)`. -/
def mkWitCallerMiriFrame
    (bbIdx : Nat)
    (ls0 ls1 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody witCallerBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy u8Ty emptyLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[ls0, ls1]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨bbIdx, 0⟩ }

/-- Callee `lean-miri` frame for `witCalleeBody` at `(0, 0)` returning into
caller frame `0`, local `1`, target block `1`. -/
def mkWitCalleeMiriFrame
    (ls0 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
    (retPlace : Miri.Interpreter.RuntimeStackPlace AnnealProv :=
      .frameLocal 0 1 none (translateTy u8Ty emptyLayoutTable) (.ofAllocationToken 0)) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody witCalleeBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .goto (some 1) .Continue
    returnPlace := retPlace
    localsIdentity := .ofAllocationToken 0
    locals := #[ls0]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- Saved caller frame on `s.memory.callStack` when `witCallerBody` is waiting
for `witCalleeBody` to return into `_1` at `bb1`. -/
def witSavedCallerFrame (slot0 slot1 : LocalSlot) (callerProts : List Nat := []) :
  SavedCallerFrame :=
  { callerBody := witCallerBody
    frame := { blockIdx := 0, stmtIdx := 0, locals := [slot0, slot1] }
    destination := ⟨1, .nil⟩
    returnTarget := 1
    callerProtector := none
    calleeProtectors := callerProts }

theorem witCallerFrame_rel
    {mach : AnnealMachine}
    (bbIdx : Nat)
    (slot0 slot1 : LocalSlot)
    (ls0 ls1 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
    (h0 : LocalRel mach u8Decl emptyLayoutTable slot0 ls0)
    (h1 : LocalRel mach u8Decl emptyLayoutTable slot1 ls1) :
    FrameRel witCallerBody mach
      { blockIdx := bbIdx, stmtIdx := 0, locals := [slot0, slot1] }
      (mkWitCallerMiriFrame bbIdx ls0 ls1) where
  body_eq := rfl
  location_eq := rfl
  af_locals_len := rfl
  mf_locals_size := rfl
  locals_rel i decl slot mls hdecl hslot hmls := by
    rcases i with _ | ⟨_ | i⟩
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact h0
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact h1
    · cases hdecl

theorem witCalleeFrame_rel
    {mach : AnnealMachine}
    (slot0 : LocalSlot)
    (ls0 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
    (h0 : LocalRel mach u8Decl emptyLayoutTable slot0 ls0)
    (retPlace : Miri.Interpreter.RuntimeStackPlace AnnealProv :=
      .frameLocal 0 1 none (translateTy u8Ty emptyLayoutTable) (.ofAllocationToken 0)) :
    FrameRel witCalleeBody mach
      { blockIdx := 0, stmtIdx := 0, locals := [slot0] }
      (mkWitCalleeMiriFrame ls0 retPlace) where
  body_eq := rfl
  location_eq := rfl
  af_locals_len := rfl
  mf_locals_size := rfl
  locals_rel i decl slot mls hdecl hslot hmls := by
    rcases i with _ | i
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact h0
    · cases hdecl

theorem wit_multiFrameAllocDisjoint_two
    (ls_c0 ls_c1 ls_e0 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
    (hc0 : ∀ mp, ls_c0.value ≠ .live (.indirect mp))
    (hc1 : ∀ mp, ls_c1.value ≠ .live (.indirect mp))
    (he0 : ∀ mp, ls_e0.value ≠ .live (.indirect mp)) :
    MultiFrameAllocDisjoint
      #[mkWitCallerMiriFrame 0 ls_c0 ls_c1, mkWitCalleeMiriFrame ls_e0] where
  intra_frame mf hmf := by
    intro i j mp₁ mp₂ lay₁ lay₂ _ hi _
    rcases List.mem_cons.mp hmf with rfl | hmf1
    · dsimp only [mkWitCallerMiriFrame] at hi
      rcases i with _ | ⟨_ | i⟩
      · injection hi with h; exact False.elim (hc0 mp₁ (congrArg Miri.Interpreter.LocalState.value h))
      · injection hi with h; exact False.elim (hc1 mp₁ (congrArg Miri.Interpreter.LocalState.value h))
      · cases hi
    · rcases List.mem_singleton.mp hmf1 with rfl
      dsimp only [mkWitCalleeMiriFrame] at hi
      rcases i with _ | i
      · injection hi with h; exact False.elim (he0 mp₁ (congrArg Miri.Interpreter.LocalState.value h))
      · cases hi
  inter_frame f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ _ hf₁ _ hi _ := by
    rcases f₁ with _ | ⟨_ | f₁⟩
    · injection hf₁ with hmf₁; subst hmf₁
      dsimp only [mkWitCallerMiriFrame] at hi
      rcases i with _ | ⟨_ | i⟩
      · injection hi with h; exact False.elim (hc0 mp₁ (congrArg Miri.Interpreter.LocalState.value h))
      · injection hi with h; exact False.elim (hc1 mp₁ (congrArg Miri.Interpreter.LocalState.value h))
      · cases hi
    · injection hf₁ with hmf₁; subst hmf₁
      dsimp only [mkWitCalleeMiriFrame] at hi
      rcases i with _ | i
      · injection hi with h; exact False.elim (he0 mp₁ (congrArg Miri.Interpreter.LocalState.value h))
      · cases hi
    · cases hf₁

/-! ## (a) End-to-End Multi-Frame Call -> Callee Return (with `GlobalState.endCall` Protector Release) -> Root Return -/

/-- Depth-2 state where `witCallerBody` has called `witCalleeBody`, `witCalleeBody`
has computed `_0 = 1u8` and holds active `FnEntry` protector `CallId = 1` on a
protected `ReservedFrz true` borrow entry (`tag = 10`) borrowing caller local
`_1` (`targetLocal = 1`), and is about to execute `TerminatorKind.return_`. -/
def witCalleeReadyToReturnAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init (.scalar sc1)] }
    memory :=
      { borrows :=
          [{ tag := 10
             targetLocal := 1
             targetProjection := []
             perm := .reservedFrz true
             protector := some 1
             parentTag := none }]
        callStack := [witSavedCallerFrame .uninit .uninit []]
        callees := [witCalleeBody]
        activeCallee := some witCalleeBody
        activeProtectors := [1]
        nextProtector := 2 } }

/-- Active `BorrowState` in `m.machine.borrowTracker` at stack depth 2 with
callee-protected tag `10` (`protectedTags.entries = #[(⟨10⟩, .StrongProtector)]`)
and a live allocation root tag `5` for `AllocId = 1`
(`rootPointerTags = #[(⟨1⟩, ⟨5⟩)]`). -/
def witCalleeBorrowTracker : Miri.Interpreter.MachineHooks.BorrowState :=
  { global :=
      { protectedTags := { entries := #[(⟨10, by decide⟩, .StrongProtector)] }
        rootPointerTags := #[(⟨1, by decide⟩, ⟨5, by decide⟩)] }
    retagMode := .Default }

def witCalleeReadyToReturnMiri : AnnealStepState :=
  { stack :=
      ⟨#[mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩,
         mkWitCalleeMiriFrame ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩]⟩
    machine := { AnnealMachine.empty with borrowTracker := some witCalleeBorrowTracker } }

theorem witCalleeReadyToReturn_borrowTrackerRel :
    BorrowTrackerStackRel
      witCalleeReadyToReturnAnneal.memory.borrows
      witCalleeReadyToReturnAnneal.memory.activeProtectors
      witCalleeReadyToReturnAnneal.memory.callStack
      witCalleeReadyToReturnMiri.machine.borrowTracker := by
  refine .cons [1] (witSavedCallerFrame .uninit .uninit []) []
    (some witCalleeBorrowTracker) ?_ ?_
  · intro tracker hbt e he
    injection hbt with htr; subst htr
    rcases List.mem_singleton.mp he with rfl
    decide
  · refine .root []
      (popFrameBorrowTracker
        (poppedCalleeFrameState
          witCalleeReadyToReturnAnneal.memory.borrows
          [1]
          (callerRestoredProtectors [witSavedCallerFrame .uninit .uninit []]))
        (some witCalleeBorrowTracker)) ?_
    intro tracker hbt e he
    injection hbt with htr; subst htr
    rcases List.mem_singleton.mp he with rfl
    decide

theorem witCalleeReadyToReturn_rel :
    MultiFrameStateRel witCallerBody witCalleeReadyToReturnAnneal witCalleeReadyToReturnMiri := by
  have hfr_caller :=
    witCallerFrame_rel (mach := witCalleeReadyToReturnMiri.machine) 0 .uninit .uninit
      ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  have hfr_callee :=
    witCalleeFrame_rel (mach := witCalleeReadyToReturnMiri.machine) (.init (.scalar sc1))
      ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩
      (.immediate (.init (.scalar sc1)) (.scalar (.fromScalarInt msc1)) none
        (fun _ h => nomatch h) (Or.inr ⟨.scalar sc1, rfl, val1_immRel⟩))
  have hlinks_root :
      CallerStackLinksRel witCallerBody witCalleeReadyToReturnMiri.machine witCallerBody
        { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
        [] []
        [mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩] :=
    .root _ _ [] rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr_caller
  have hdest :
      CallerDestinationRel witCalleeReadyToReturnMiri.machine 0 (witSavedCallerFrame .uninit .uninit [])
        (mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
        (mkWitCalleeMiriFrame ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩).returnPlace :=
    .immediate 1 u8Decl .uninit .uninit none rfl rfl rfl (fun h => nomatch h) rfl
  have hlinks :
      CallerStackLinksRel witCallerBody witCalleeReadyToReturnMiri.machine
        (activeMirBody witCallerBody witCalleeReadyToReturnAnneal)
        witCalleeReadyToReturnAnneal.frame
        witCalleeReadyToReturnAnneal.memory.callStack
        witCalleeReadyToReturnAnneal.memory.activeProtectors
        witCalleeReadyToReturnMiri.stack.frames.toList.reverse :=
    .cons witCalleeBody
      witCalleeReadyToReturnAnneal.frame
      (witSavedCallerFrame .uninit .uninit []) [] [1] []
      (mkWitCalleeMiriFrame ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩)
      (mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
      [] .Continue
      rfl hdest hfr_callee (fun _ _ _ _ _ h _ _ _ => nomatch h) rfl (by intro _ _; rfl) hlinks_root
  refine .mk
    (mkWitCalleeMiriFrame ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩)
    rfl
    (fun hnil => nomatch hnil)
    (fun _ => rfl)
    hlinks.toFrameStackRel
    hlinks
    (wit_multiFrameAllocDisjoint_two _ _ _ (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h))
    ⟨by decide, by decide, rfl, rfl, rfl⟩
    (by decide)
    (by decide)
    (by intro cid hcid; rcases List.mem_singleton.mp hcid with rfl; decide)
    (by intro e he cid hprot
        rcases List.mem_singleton.mp he with rfl
        injection hprot with h; subst h; decide)
    witCalleeReadyToReturn_borrowTrackerRel

/-- **Witness (a.1)**: Executing `TerminatorKind.return_` in `witCalleeBody` at
depth 2 copies `_0 = 1u8` into caller local `_1`, pops the callee frame,
releases protector `CallId = 1` in both `s.memory.activeProtectors` (`[]`) and
`m.machine.borrowTracker` (`protectedTags.entries = #[]` via `GlobalState.endCall`
while preserving `rootTag? ⟨1, by decide⟩ = some ⟨5, by decide⟩` in `rootPointerTags`),
and advances `witCallerBody` to `(bb1, 0)` in both Anneal and `lean-miri`. -/
theorem wit_lm4_1_callee_return_simulation :
    StepRelMultiFrame witCallerBody witCalleeReadyToReturnMiri
      (stepMirFn witCallerBody witCalleeReadyToReturnAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCalleeReadyToReturnAnneal)
          witCalleeReadyToReturnAnneal.memory.callees
          (annealPoppedFrameState witCalleeReadyToReturnAnneal))
        () witCalleeReadyToReturnMiri) ∧
    (∃ s',
      stepMirFn witCallerBody witCalleeReadyToReturnAnneal = .step s' ∧
      s'.memory.callStack = [] ∧
      s'.memory.activeProtectors = [] ∧
      s'.frame.blockIdx = 1 ∧
      get? s'.frame.locals 1 = some (.init (.scalar sc1))) ∧
    witCalleeBorrowTracker.global.rootTag? ⟨1, by decide⟩ = some ⟨5, by decide⟩ ∧
    (∃ tracker',
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCalleeReadyToReturnAnneal)
          witCalleeReadyToReturnAnneal.memory.callees
          (annealPoppedFrameState witCalleeReadyToReturnAnneal))
        () witCalleeReadyToReturnMiri).1.machine.borrowTracker = some tracker' ∧
      tracker'.global.protectedTags.entries = #[] ∧
      tracker'.global.rootPointerTags = #[(⟨1, by decide⟩, ⟨5, by decide⟩)] ∧
      tracker'.global.rootTag? ⟨1, by decide⟩ = some ⟨5, by decide⟩) := by
  have hsim :
      StepRelMultiFrame witCallerBody witCalleeReadyToReturnMiri
        (stepMirFn witCallerBody witCalleeReadyToReturnAnneal)
        (Miri.Interpreter.Step.step
          (annealStepHooksLM4_1
            (activeMirBody witCallerBody witCalleeReadyToReturnAnneal)
            witCalleeReadyToReturnAnneal.memory.callees
            (annealPoppedFrameState witCalleeReadyToReturnAnneal))
          () witCalleeReadyToReturnMiri) := by
    apply step_terminator_return_callee_simulation
      witCalleeReadyToReturn_rel rfl
      (by intro tf htf; injection htf with h; subst h; rfl)
      (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm .return_, isCleanup := false })
      (decl0 := u8Decl)
      rfl rfl rfl rfl rfl rfl (fun h => nomatch h)
    intro destIdx destDecl hcf hdecl_d v imm himm
    injection hcf with hd _; subst hd
    injection hdecl_d with hdd; subst hdd
    exact himm
  exact ⟨hsim, ⟨_, rfl, rfl, rfl, rfl, rfl⟩, rfl, ⟨_, rfl, rfl, rfl, rfl⟩⟩

/-- **Witness (a.2)**: Executing `TerminatorKind.call` in `witCallerBody` at
depth 1 pushes `witCalleeBody` onto `s.memory.callStack` and `m.stack.frames`,
establishing `MultiFrameStateRel` at depth 2. -/
def witCallerAtCallAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
    memory := { callees := [witCalleeBody], nextProtector := 1 } }

def witCallerAtCallMiri : AnnealStepState :=
  { stack :=
      ⟨#[mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩]⟩
    machine := AnnealMachine.empty }

theorem witCallerAtCall_rel :
    MultiFrameStateRel witCallerBody witCallerAtCallAnneal witCallerAtCallMiri := by
  have hfr_caller :=
    witCallerFrame_rel (mach := AnnealMachine.empty) 0 .uninit .uninit
      ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  have hstate0 : StateRel witCallerBody witCallerAtCallAnneal witCallerAtCallMiri :=
    .mk _ rfl rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr_caller
      rfl rfl rfl rfl rfl
      (by
        intro i j mp₁ mp₂ lay₁ lay₂ _ hi _
        rcases i with _ | ⟨_ | i⟩ <;> cases hi)
  exact (StateRel.iff_multiFrameStateRel_depth1 rfl rfl rfl rfl rfl (by decide)).mp hstate0

theorem wit_lm4_1_call_push_simulation :
    StepRelMultiFrame witCallerBody witCallerAtCallMiri
      (stepMirFn witCallerBody witCallerAtCallAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCallerAtCallAnneal)
          witCallerAtCallAnneal.memory.callees)
        () witCallerAtCallMiri) ∧
    (∃ s',
      stepMirFn witCallerBody witCallerAtCallAnneal = .step s' ∧
      s'.memory.callStack.length = 1 ∧
      s'.memory.activeCallee = some witCalleeBody) := by
  have hsim :
      StepRelMultiFrame witCallerBody witCallerAtCallMiri
        (stepMirFn witCallerBody witCallerAtCallAnneal)
        (Miri.Interpreter.Step.step
          (annealStepHooksLM4_1
            (activeMirBody witCallerBody witCallerAtCallAnneal)
            witCallerAtCallAnneal.memory.callees)
          () witCallerAtCallMiri) := by
    apply step_terminator_call_simulation
      witCallerAtCall_rel (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.call calleeFuncOp [] ⟨1, .nil⟩ (some 1) .continue_)
               isCleanup := false })
      (destDecl := u8Decl)
      (calleeBody := witCalleeBody)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by intro tf htf
          apply CallerDestSlotWf.of_immediate
          intro mls hmls mp hmp
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hmp)
      (by intro tf htf mls hmls hdead
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hdead)
      (fun _ _ => .nil [])
  exact ⟨hsim, _, rfl, rfl, rfl⟩

/-- **Witness (a.3)**: Returning from the root frame (`witCallerBody` at `bb1`
with `_0 = 1u8` and `callStack = []`) produces `.retNormal (.scalar sc1)` in
Anneal and empties `lean-miri`'s call stack (`frames = #[]`) with related return
value `msc1`. -/
def witCallerAtRootReturnAnneal : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 0, locals := [.init (.scalar sc1), .init (.scalar sc1)] }
    memory := { callees := [witCalleeBody], activeCallee := some witCallerBody, nextProtector := 2 } }

def witCallerAtRootReturnMiri : AnnealStepState :=
  { stack :=
      ⟨#[mkWitCallerMiriFrame 1
          ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩
          ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩]⟩
    machine := AnnealMachine.empty }

theorem wit_lm4_1_root_return_simulation :
    StepRelMultiFrame witCallerBody witCallerAtRootReturnMiri
      (stepMirFn witCallerBody witCallerAtRootReturnAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCallerAtRootReturnAnneal)
          witCallerAtRootReturnAnneal.memory.callees)
        () witCallerAtRootReturnMiri) ∧
    stepMirFn witCallerBody witCallerAtRootReturnAnneal =
      .retNormal (.scalar sc1) witCallerAtRootReturnAnneal.memory ∧
    (Miri.Interpreter.Step.step
      (annealStepHooksLM4_1
        (activeMirBody witCallerBody witCallerAtRootReturnAnneal)
        witCallerAtRootReturnAnneal.memory.callees)
      () witCallerAtRootReturnMiri).1.stack.frames = #[] := by
  have hrel1 :
      LocalRel AnnealMachine.empty u8Decl emptyLayoutTable (.init (.scalar sc1))
        ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩ :=
    .immediate (.init (.scalar sc1)) (.scalar (.fromScalarInt msc1)) none
      (fun _ h => nomatch h) (Or.inr ⟨.scalar sc1, rfl, val1_immRel⟩)
  have hfr := witCallerFrame_rel 1 _ _ _ _ hrel1 hrel1
  have htb_state : TreeBorrowsStateRel witCallerBody witCallerAtRootReturnAnneal witCallerAtRootReturnMiri :=
    .mk _ rfl rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr
      (Or.inr rfl) rfl rfl
      (by intro i j mp₁ mp₂ lay₁ lay₂ _ hi _; rcases i with _ | ⟨_ | i⟩ <;> cases hi)
      ⟨by decide, by decide, rfl, rfl, rfl⟩
      (ActiveProtectorsValid.nil _)
      (BorrowTrackerStackRel.of_none _ _ _)
  have hstate : MultiFrameStateRel witCallerBody witCallerAtRootReturnAnneal witCallerAtRootReturnMiri :=
    htb_state.toMultiFrameStateRel (by decide) (fun _ h => nomatch h) (fun _ h => nomatch h)
  have hsim :=
    step_terminator_return_root_simulation hstate rfl (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm .return_, isCleanup := false })
      (decl0 := u8Decl)
      rfl rfl rfl rfl rfl rfl (fun h => nomatch h)
      (by intro tf htf
          apply RootIndirectRetWf.of_immediate
          intro mls hmls mp hmp
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hmp)
  exact ⟨hsim, rfl, rfl⟩

/-! ## (b) UB Canary: Callee Return with `.uninit` `_0` -/

def witCalleeUninitRetAnneal : MachineState :=
  { witCalleeReadyToReturnAnneal with
    frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] } }

def witCalleeUninitRetMiri : AnnealStepState :=
  { stack :=
      ⟨#[mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩,
         mkWitCalleeMiriFrame ⟨.live (.immediate .uninit), none⟩]⟩
    machine := AnnealMachine.empty }

theorem wit_lm4_1_return_callee_uninit_ub :
    StepRelMultiFrame witCallerBody witCalleeUninitRetMiri
      (stepMirFn witCallerBody witCalleeUninitRetAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCalleeUninitRetAnneal)
          witCalleeUninitRetAnneal.memory.callees
          (annealPoppedFrameState witCalleeUninitRetAnneal))
        () witCalleeUninitRetMiri) ∧
    stepMirFn witCallerBody witCalleeUninitRetAnneal = .fail .ub ∧
    ∃ msg,
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCalleeUninitRetAnneal)
          witCalleeUninitRetAnneal.memory.callees
          (annealPoppedFrameState witCalleeUninitRetAnneal))
        () witCalleeUninitRetMiri).2 = .error (.undefinedBehavior msg) := by
  have hfr_caller :=
    witCallerFrame_rel (mach := AnnealMachine.empty) 0 .uninit .uninit
      ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  have hfr_callee :=
    witCalleeFrame_rel (mach := AnnealMachine.empty) .uninit ⟨.live (.immediate .uninit), none⟩
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  have hlinks_root :
      CallerStackLinksRel witCallerBody AnnealMachine.empty witCallerBody
        { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
        [] []
        [mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩] :=
    .root _ _ [] rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr_caller
  have hdest :
      CallerDestinationRel AnnealMachine.empty 0 (witSavedCallerFrame .uninit .uninit [])
        (mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
        (mkWitCalleeMiriFrame ⟨.live (.immediate .uninit), none⟩).returnPlace :=
    .immediate 1 u8Decl .uninit .uninit none rfl rfl rfl (fun h => nomatch h) rfl
  have hlinks :
      CallerStackLinksRel witCallerBody AnnealMachine.empty
        (activeMirBody witCallerBody witCalleeUninitRetAnneal)
        witCalleeUninitRetAnneal.frame
        witCalleeUninitRetAnneal.memory.callStack
        witCalleeUninitRetAnneal.memory.activeProtectors
        witCalleeUninitRetMiri.stack.frames.toList.reverse :=
    .cons witCalleeBody
      witCalleeUninitRetAnneal.frame
      (witSavedCallerFrame .uninit .uninit []) [] [1] []
      (mkWitCalleeMiriFrame ⟨.live (.immediate .uninit), none⟩)
      (mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
      [] .Continue
      rfl hdest hfr_callee (fun _ _ _ _ _ h _ _ _ => nomatch h) rfl (by intro _ _; rfl) hlinks_root
  have hstate : MultiFrameStateRel witCallerBody witCalleeUninitRetAnneal witCalleeUninitRetMiri :=
    .mk _ rfl (fun hnil => nomatch hnil) (fun _ => rfl)
      hlinks.toFrameStackRel hlinks
      (wit_multiFrameAllocDisjoint_two _ _ _ (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h))
      ⟨by decide, by decide, rfl, rfl, rfl⟩
      (by decide) (by decide)
      (by intro cid hcid; rcases List.mem_singleton.mp hcid with rfl; decide)
      (by intro e he cid hprot
          rcases List.mem_singleton.mp he with rfl
          injection hprot with h; subst h; decide)
      (BorrowTrackerStackRel.of_none _ _ _)
  have hsim :=
    step_terminator_return_callee_simulation hstate rfl
      (by intro tf htf; injection htf with h; subst h; rfl)
      (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm .return_, isCleanup := false })
      (decl0 := u8Decl)
      rfl rfl rfl rfl rfl rfl (fun h => nomatch h)
      (by intro destIdx destDecl hcf hdecl_d v imm himm
          injection hcf with hd _; subst hd
          injection hdecl_d with hdd; subst hdd
          exact himm)
  exact ⟨hsim, rfl, (hsim.ub_iff).mp rfl⟩

/-! ## (c) `Terminator.Drop` Live vs `.dead` UB Witness -/

def witCallerAtDropLiveAnneal : MachineState :=
  { frame := { blockIdx := 2, stmtIdx := 0, locals := [.uninit, .init (.scalar sc1)] }
    memory := { callees := [witCalleeBody], nextProtector := 1 } }

def witCallerAtDropLiveMiri : AnnealStepState :=
  { stack :=
      ⟨#[mkWitCallerMiriFrame 2
          ⟨.live (.immediate .uninit), none⟩
          ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩]⟩
    machine := AnnealMachine.empty }

theorem wit_lm4_1_drop_live_and_dead_ub :
    StepRelMultiFrame witCallerBody witCallerAtDropLiveMiri
      (stepMirFn witCallerBody witCallerAtDropLiveAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCallerAtDropLiveAnneal)
          witCallerAtDropLiveAnneal.memory.callees)
        () witCallerAtDropLiveMiri) ∧
    (∃ s',
      stepMirFn witCallerBody witCallerAtDropLiveAnneal = .step s' ∧
      s'.frame.blockIdx = 1 ∧
      get? s'.frame.locals 1 = some .uninit) := by
  have hrel0 :
      LocalRel AnnealMachine.empty u8Decl emptyLayoutTable .uninit
        ⟨.live (.immediate .uninit), none⟩ :=
    .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  have hrel1 :
      LocalRel AnnealMachine.empty u8Decl emptyLayoutTable (.init (.scalar sc1))
        ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩ :=
    .immediate (.init (.scalar sc1)) (.scalar (.fromScalarInt msc1)) none
      (fun _ h => nomatch h) (Or.inr ⟨.scalar sc1, rfl, val1_immRel⟩)
  have hfr := witCallerFrame_rel 2 _ _ _ _ hrel0 hrel1
  have hstate0 : StateRel witCallerBody witCallerAtDropLiveAnneal witCallerAtDropLiveMiri :=
    .mk _ rfl rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr rfl rfl rfl rfl rfl
      (by intro i j mp₁ mp₂ lay₁ lay₂ _ hi _; rcases i with _ | ⟨_ | i⟩ <;> cases hi)
  have hstate :=
    (StateRel.iff_multiFrameStateRel_depth1 rfl rfl rfl rfl rfl (by decide)).mp hstate0
  have hsim :=
    step_terminator_drop_noop_simulation hstate (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.drop ⟨1, .nil⟩ 1 .continue_)
               isCleanup := false })
      (decl := u8Decl)
      rfl rfl rfl rfl rfl
      (by intro tf htf mls hmls mp hmp
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hmp)
  exact ⟨hsim, _, rfl, rfl, rfl⟩

/-! ## (d) `Terminator.Unreachable` and Diverging `unreachable_unchecked` Call UB Witnesses -/

def witCallerAtUnreachableAnneal : MachineState :=
  { frame := { blockIdx := 3, stmtIdx := 0, locals := [.uninit, .uninit] }
    memory := { callees := [witCalleeBody], nextProtector := 1 } }

def witCallerAtUnreachableMiri : AnnealStepState :=
  { stack :=
      ⟨#[mkWitCallerMiriFrame 3 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩]⟩
    machine := AnnealMachine.empty }

theorem wit_lm4_1_unreachable_ub :
    StepRelMultiFrame witCallerBody witCallerAtUnreachableMiri
      (stepMirFn witCallerBody witCallerAtUnreachableAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCallerAtUnreachableAnneal)
          witCallerAtUnreachableAnneal.memory.callees)
        () witCallerAtUnreachableMiri) ∧
    stepMirFn witCallerBody witCallerAtUnreachableAnneal = .fail .ub ∧
    ∃ msg,
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCallerAtUnreachableAnneal)
          witCallerAtUnreachableAnneal.memory.callees)
        () witCallerAtUnreachableMiri).2 = .error (.undefinedBehavior msg) := by
  have hfr :=
    witCallerFrame_rel (mach := AnnealMachine.empty) 3 .uninit .uninit
      ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  have hstate0 : StateRel witCallerBody witCallerAtUnreachableAnneal witCallerAtUnreachableMiri :=
    .mk _ rfl rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr rfl rfl rfl rfl rfl
      (by intro i j mp₁ mp₂ lay₁ lay₂ _ hi _; rcases i with _ | ⟨_ | i⟩ <;> cases hi)
  have hstate :=
    (StateRel.iff_multiFrameStateRel_depth1 rfl rfl rfl rfl rfl (by decide)).mp hstate0
  have hsim :=
    step_terminator_unreachable_ub_simulation hstate (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm .unreachable, isCleanup := false })
      rfl rfl rfl rfl
  exact ⟨hsim, rfl, (hsim.ub_iff).mp rfl⟩

def witCallerAtUnreachableCallAnneal : MachineState :=
  { frame := { blockIdx := 4, stmtIdx := 0, locals := [.uninit, .uninit] }
    memory := { callees := [witCalleeBody], nextProtector := 1 } }

def witCallerAtUnreachableCallMiri : AnnealStepState :=
  { stack :=
      ⟨#[mkWitCallerMiriFrame 4 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩]⟩
    machine := AnnealMachine.empty }

theorem wit_lm4_1_call_unreachable_unchecked_ub :
    StepRelMultiFrame witCallerBody witCallerAtUnreachableCallMiri
      (stepMirFn witCallerBody witCallerAtUnreachableCallAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCallerAtUnreachableCallAnneal)
          witCallerAtUnreachableCallAnneal.memory.callees)
        () witCallerAtUnreachableCallMiri) ∧
    stepMirFn witCallerBody witCallerAtUnreachableCallAnneal = .fail .ub ∧
    ∃ msg,
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCallerAtUnreachableCallAnneal)
          witCallerAtUnreachableCallAnneal.memory.callees)
        () witCallerAtUnreachableCallMiri).2 = .error (.undefinedBehavior msg) := by
  have hfr :=
    witCallerFrame_rel (mach := AnnealMachine.empty) 4 .uninit .uninit
      ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  have hstate0 : StateRel witCallerBody witCallerAtUnreachableCallAnneal witCallerAtUnreachableCallMiri :=
    .mk _ rfl rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr rfl rfl rfl rfl rfl
      (by intro i j mp₁ mp₂ lay₁ lay₂ _ hi _; rcases i with _ | ⟨_ | i⟩ <;> cases hi)
  have hstate :=
    (StateRel.iff_multiFrameStateRel_depth1 rfl rfl rfl rfl rfl (by decide)).mp hstate0
  have hsim :=
    step_terminator_call_unreachable_unchecked_ub_simulation hstate (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.call unreachableUncheckedFuncOp [] ⟨1, .nil⟩ none .unreachable)
               isCleanup := false })
      rfl rfl rfl rfl rfl
  exact ⟨hsim, rfl, (hsim.ub_iff).mp rfl⟩

/-! ## (e) `BorrowTree.releaseProtector` End-of-Call Implicit Read Witness -/

/-- **Witness (e)**: Concrete `BorrowTree.releaseProtector` contrast between:
1. A conflicted `ReservedFrz true` protected child tag (`perm = .reservedFrz true`),
   where releasing the protector at function exit succeeds (`status = .Released`)
   and preserves `hooksTwoNodeTree (.reservedFrz true)`; and
2. A `.disabled` protected child tag (`perm = .disabled`), where releasing the
   protector fails with `.AccessFailure ⟨0, 8⟩ (.AccessFailure ⟨0, 8⟩ (.TransitionError 1 (.ChildAccessForbidden .Disabled)))`. -/
theorem wit_lm4_1_releaseProtector_conflicted_reservedFrz_ok_vs_disabled_ub :
    (Miri.TreeBorrows.BorrowTree.releaseProtector
      (hooksTwoNodeTree (.reservedFrz true))
      retagChildTag
      (hooksForChildProtected true).protectedTags).status = .Released ∧
    (Miri.TreeBorrows.BorrowTree.releaseProtector
      (hooksTwoNodeTree (.reservedFrz true))
      retagChildTag
      (hooksForChildProtected true).protectedTags).tree = hooksTwoNodeTree (.reservedFrz true) ∧
    (Miri.TreeBorrows.BorrowTree.releaseProtector
      (hooksTwoNodeTree .disabled)
      retagChildTag
      (hooksForChildProtected true).protectedTags).status =
        .AccessFailure ⟨0, 8⟩
          (.AccessFailure ⟨0, 8⟩ (.TransitionError 1 (.ChildAccessForbidden .Disabled))) := by
  have hok := borrowTree_releaseProtector_full_simulation (.reservedFrz true)
  have hub := borrowTree_releaseProtector_full_simulation .disabled
  exact ⟨hok.1.mpr nofun, hok.2.1 nofun, hub.2.2.1 rfl⟩

/-! ## (f) ZST `()` Callee and Root Return Witness (`H1`) -/

/-- Callee MIR body `"crate::unit_callee"` returning `_0 : ()`. -/
def witUnitCalleeBody : CapturedMir where
  defPath := "crate::unit_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [unitDecl]
  basicBlocks :=
    [{ statements := []
       terminator := mkTerm .return_
       isCleanup := false }]
  fnAbi := fnAbiU8
  layouts := emptyLayoutTable
  allocations := []

/-- Caller MIR body `"crate::unit_caller"` calling `unit_callee` into `_1 : ()`
and returning `_0 : ()`. -/
def witUnitCallerBody : CapturedMir where
  defPath := "crate::unit_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [unitDecl, unitDecl]
  basicBlocks :=
    [ { statements := []
        terminator := mkTerm (.call unitCalleeFuncOp [] ⟨1, .nil⟩ (some 1) .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm .return_
        isCleanup := false } ]
  fnAbi := fnAbiU8
  layouts := emptyLayoutTable
  allocations := []

def mkWitUnitCallerMiriFrame
    (bbIdx : Nat)
    (ls0 ls1 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody witUnitCallerBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy unitTy emptyLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[ls0, ls1]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨bbIdx, 0⟩ }

def mkWitUnitCalleeMiriFrame
    (ls0 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody witUnitCalleeBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .goto (some 1) .Continue
    returnPlace :=
      .frameLocal 0 1 none (translateTy unitTy emptyLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[ls0]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def witUnitCalleeAtReturnAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init .unit] }
    memory :=
      { callStack :=
          [{ callerBody := witUnitCallerBody
             frame := { blockIdx := 0, stmtIdx := 0, locals := [.init .unit, .uninit] }
             destination := ⟨1, .nil⟩
             returnTarget := 1 }]
        callees := [witUnitCalleeBody]
        activeCallee := some witUnitCalleeBody
        nextProtector := 1 } }

def witUnitCalleeAtReturnMiri : AnnealStepState :=
  { stack :=
      ⟨#[mkWitUnitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩,
         mkWitUnitCalleeMiriFrame ⟨.live (.immediate .uninit), none⟩]⟩
    machine := AnnealMachine.empty }

def witUnitRootAtReturnAnneal : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 0, locals := [.init .unit, .init .unit] }
    memory := { callees := [witUnitCalleeBody], activeCallee := some witUnitCallerBody, nextProtector := 1 } }

def witUnitRootAtReturnMiri : AnnealStepState :=
  { stack :=
      ⟨#[mkWitUnitCallerMiriFrame 1 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩]⟩
    machine := AnnealMachine.empty }

/-- **Witness (f, `H1`)**: Returning `()` (`unitTy`, `size = ZERO`) from both a
non-root callee frame (`step_terminator_return_callee_simulation`) and the root
frame (`step_terminator_return_root_simulation`) succeeds in lockstep (`_0 = .init .unit`
in Anneal ↔ `.live (.immediate .uninit)` in `lean-miri`). -/
theorem wit_lm4_1_zst_unit_return_simulation :
    StepRelMultiFrame witUnitCallerBody witUnitCalleeAtReturnMiri
      (stepMirFn witUnitCallerBody witUnitCalleeAtReturnAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witUnitCallerBody witUnitCalleeAtReturnAnneal)
          witUnitCalleeAtReturnAnneal.memory.callees)
        () witUnitCalleeAtReturnMiri) ∧
    StepRelMultiFrame witUnitCallerBody witUnitRootAtReturnMiri
      (stepMirFn witUnitCallerBody witUnitRootAtReturnAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witUnitCallerBody witUnitRootAtReturnAnneal)
          witUnitRootAtReturnAnneal.memory.callees)
        () witUnitRootAtReturnMiri) ∧
    stepMirFn witUnitCallerBody witUnitRootAtReturnAnneal =
      .retNormal .unit witUnitRootAtReturnAnneal.memory := by
  have hloc_unit :
      LocalRel AnnealMachine.empty unitDecl emptyLayoutTable (.init .unit)
        ⟨.live (.immediate .uninit), none⟩ :=
    .immediate (.init .unit) .uninit none (fun _ h => nomatch h) (Or.inr ⟨.unit, rfl, unit_immRel⟩)
  have hloc_uninit :
      LocalRel AnnealMachine.empty unitDecl emptyLayoutTable .uninit
        ⟨.live (.immediate .uninit), none⟩ :=
    .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  have hfr_caller0 :
      FrameRel witUnitCallerBody AnnealMachine.empty
        { blockIdx := 0, stmtIdx := 0, locals := [.init .unit, .uninit] }
        (mkWitUnitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩) := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    rcases i with _ | ⟨_ | i⟩
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact hloc_unit
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact hloc_uninit
    · cases hdecl
  have hfr_callee :
      FrameRel witUnitCalleeBody AnnealMachine.empty
        { blockIdx := 0, stmtIdx := 0, locals := [.init .unit] }
        (mkWitUnitCalleeMiriFrame ⟨.live (.immediate .uninit), none⟩) := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    rcases i with _ | i
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact hloc_unit
    · cases hdecl
  have hlinks_root0 :
      CallerStackLinksRel witUnitCallerBody AnnealMachine.empty witUnitCallerBody
        { blockIdx := 0, stmtIdx := 0, locals := [.init .unit, .uninit] }
        [] []
        [mkWitUnitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩] :=
    .root _ _ [] rfl ⟨translateTy unitTy emptyLayoutTable, rfl⟩ hfr_caller0
  have hdest :
      CallerDestinationRel AnnealMachine.empty 0
        { callerBody := witUnitCallerBody
          frame := { blockIdx := 0, stmtIdx := 0, locals := [.init .unit, .uninit] }
          destination := ⟨1, .nil⟩
          returnTarget := 1 }
        (mkWitUnitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
        (mkWitUnitCalleeMiriFrame ⟨.live (.immediate .uninit), none⟩).returnPlace :=
    .immediate 1 unitDecl .uninit .uninit none rfl rfl rfl (fun h => nomatch h) rfl
  have hlinks_callee :
      CallerStackLinksRel witUnitCallerBody AnnealMachine.empty
        (activeMirBody witUnitCallerBody witUnitCalleeAtReturnAnneal)
        witUnitCalleeAtReturnAnneal.frame
        witUnitCalleeAtReturnAnneal.memory.callStack
        witUnitCalleeAtReturnAnneal.memory.activeProtectors
        witUnitCalleeAtReturnMiri.stack.frames.toList.reverse :=
    .cons witUnitCalleeBody
      witUnitCalleeAtReturnAnneal.frame
      _ [] [] []
      (mkWitUnitCalleeMiriFrame ⟨.live (.immediate .uninit), none⟩)
      (mkWitUnitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
      [] .Continue
      rfl hdest hfr_callee (fun _ _ _ _ _ h _ _ _ => nomatch h) rfl (fun _ h => nomatch h) hlinks_root0
  have hdisj_callee : MultiFrameAllocDisjoint witUnitCalleeAtReturnMiri.stack.frames := by
    refine ⟨?_, ?_⟩
    · intro mf hmf i j mp₁ mp₂ lay₁ lay₂ _ hi _
      rcases List.mem_cons.mp hmf with rfl | hmf1
      · dsimp only [mkWitUnitCallerMiriFrame] at hi
        rcases i with _ | ⟨_ | i⟩ <;> cases hi
      · rcases List.mem_singleton.mp hmf1 with rfl
        dsimp only [mkWitUnitCalleeMiriFrame] at hi
        rcases i with _ | i <;> cases hi
    · intro f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ _ hf₁ _ hi _
      rcases f₁ with _ | ⟨_ | f₁⟩
      · injection hf₁ with hmf₁; subst hmf₁
        rcases i with _ | ⟨_ | i⟩ <;> cases hi
      · injection hf₁ with hmf₁; subst hmf₁
        rcases i with _ | i <;> cases hi
      · cases hf₁
  have hstate_callee :
      MultiFrameStateRel witUnitCallerBody witUnitCalleeAtReturnAnneal witUnitCalleeAtReturnMiri :=
    .mk _ rfl (fun hnil => nomatch hnil) (fun _ => rfl)
      hlinks_callee.toFrameStackRel hlinks_callee hdisj_callee
      ⟨by decide, by decide, rfl, rfl, rfl⟩
      (ActiveProtectorsValid.nil _) (by decide)
      (fun _ h => nomatch h) (fun _ h => nomatch h)
      (BorrowTrackerStackRel.of_none _ _ _)
  have hsim_callee :=
    step_terminator_return_callee_simulation hstate_callee rfl
      (by intro tf htf; injection htf with h; subst h; rfl)
      (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm .return_, isCleanup := false })
      (decl0 := unitDecl)
      rfl rfl rfl rfl rfl rfl
      (by intro _ h; cases h)
      (by intro destIdx destDecl hcf hdecl_d v imm himm
          injection hcf with hd _; subst hd
          injection hdecl_d with hdd; subst hdd
          exact himm)
  have hfr_root :
      FrameRel witUnitCallerBody AnnealMachine.empty
        { blockIdx := 1, stmtIdx := 0, locals := [.init .unit, .init .unit] }
        (mkWitUnitCallerMiriFrame 1 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩) := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    rcases i with _ | ⟨_ | i⟩
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact hloc_unit
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact hloc_unit
    · cases hdecl
  have htb_root : TreeBorrowsStateRel witUnitCallerBody witUnitRootAtReturnAnneal witUnitRootAtReturnMiri :=
    .mk _ rfl rfl ⟨translateTy unitTy emptyLayoutTable, rfl⟩ hfr_root
      (Or.inr rfl) rfl rfl
      (by intro i j mp₁ mp₂ lay₁ lay₂ _ hi _; rcases i with _ | ⟨_ | i⟩ <;> cases hi)
      ⟨by decide, by decide, rfl, rfl, rfl⟩
      (ActiveProtectorsValid.nil _)
      (BorrowTrackerStackRel.of_none _ _ _)
  have hstate_root :=
    htb_root.toMultiFrameStateRel (by decide) (fun _ h => nomatch h) (fun _ h => nomatch h)
  have hsim_root :=
    step_terminator_return_root_simulation hstate_root rfl (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm .return_, isCleanup := false })
      (decl0 := unitDecl)
      rfl rfl rfl rfl rfl rfl
      (by intro _ h; cases h)
      (by intro tf htf
          apply RootIndirectRetWf.of_immediate
          intro mls hmls mp hmp
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hmp)
  exact ⟨hsim_callee, hsim_root, rfl⟩

/-! ## (g) `.indirect` Caller Destination Call + Callee Return Witness (`H2`) -/

def witIndirectDestCallMiri : AnnealStepState :=
  { stack :=
      ⟨#[mkWitCallerMiriFrame 0
          ⟨.live (.immediate .uninit), none⟩
          ⟨.live (.indirect Witness.witnessMemPlace), none⟩]⟩
    machine := Witness.witnessMachineOf Witness.witnessUninitAlloc }

def witIndirectDestReturnMiri : AnnealStepState :=
  { stack :=
      ⟨#[mkWitCallerMiriFrame 0
          ⟨.live (.immediate .uninit), none⟩
          ⟨.live (.indirect Witness.witnessMemPlace), none⟩,
         mkWitCalleeMiriFrame
          ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩
          (.memory ⟨Witness.witnessMemPlace, translateTy u8Ty emptyLayoutTable⟩)]⟩
    machine := Witness.witnessMachineOf Witness.witnessUninitAlloc }

/-- **Witness (g, `H2`)**: When caller local `_1` is `.indirect Witness.witnessMemPlace`,
`step_terminator_call_simulation` resolves `_1` to `RuntimeStackPlace.memory`
(`CallerDestinationRel.indirect`) and pushes `witCalleeBody`, and
`step_terminator_return_callee_simulation` writes `_0 = 1u8` into
`Witness.witnessMemPlace`'s backing stack allocation and advances the caller to
`(bb1, 0)`. -/
theorem wit_lm4_1_indirect_dest_call_and_return_simulation :
    StepRelMultiFrame witCallerBody witIndirectDestCallMiri
      (stepMirFn witCallerBody witCallerAtCallAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCallerAtCallAnneal)
          witCallerAtCallAnneal.memory.callees)
        () witIndirectDestCallMiri) ∧
    StepRelMultiFrame witCallerBody witIndirectDestReturnMiri
      (stepMirFn witCallerBody witCalleeReadyToReturnAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCalleeReadyToReturnAnneal)
          witCalleeReadyToReturnAnneal.memory.callees
          (annealPoppedFrameState witCalleeReadyToReturnAnneal))
        () witIndirectDestReturnMiri) := by
  have hloc0 :
      LocalRel (Witness.witnessMachineOf Witness.witnessUninitAlloc) u8Decl emptyLayoutTable
        .uninit ⟨.live (.immediate .uninit), none⟩ :=
    .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  have hloc1 := Witness.indirect_localRel_uninit_witness
  have hfr_caller := witCallerFrame_rel 0 .uninit .uninit _ _ hloc0 hloc1
  have hd_caller :
      MemoryAllocDisjoint
        (mkWitCallerMiriFrame 0
          ⟨.live (.immediate .uninit), none⟩
          ⟨.live (.indirect Witness.witnessMemPlace), none⟩) := by
    intro i j mp₁ mp₂ lay₁ lay₂ hne hi hj
    dsimp only [mkWitCallerMiriFrame] at hi hj
    rcases i with _ | ⟨_ | i⟩
    · cases hi
    · rcases j with _ | ⟨_ | j⟩
      · cases hj
      · exact False.elim (hne rfl)
      · cases hj
    · cases hi
  have hstate_call0 : StateRel witCallerBody witCallerAtCallAnneal witIndirectDestCallMiri :=
    .mk _ rfl rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr_caller
      rfl rfl rfl rfl rfl hd_caller
  have hstate_call :=
    (StateRel.iff_multiFrameStateRel_depth1 rfl rfl rfl rfl rfl (by decide)).mp hstate_call0
  have hu8_prim : IsPrimScalarTy u8Ty := Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))
  have hmask_uninit :
      InitMaskWordRel Witness.witnessUninitAlloc.initializationMask
        Witness.witnessUninitAlloc.byteSize (initWordsFalse (Miri.ABI.Size.ofBytes 8)) :=
    ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  have hsim_call :=
    step_terminator_call_simulation hstate_call (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.call calleeFuncOp [] ⟨1, .nil⟩ (some 1) .continue_)
               isCleanup := false })
      (destDecl := u8Decl)
      (calleeBody := witCalleeBody)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by intro tf htf
          injection htf with h; subst h
          refine Or.inr ⟨hu8_prim, by decide, ?_⟩
          intro mp lay allocId tag localAlloc _ _ hlive
          rcases List.mem_singleton.mp hlive with hpair
          injection hpair with _ hla
          subst hla
          exact ⟨rfl, rfl, _, hmask_uninit⟩)
      (by intro tf htf mls hmls hdead
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hdead)
      (fun _ _ => .nil [])
  have hfr_callee :=
    witCalleeFrame_rel (mach := Witness.witnessMachineOf Witness.witnessUninitAlloc)
      (.init (.scalar sc1))
      ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩
      (.immediate (.init (.scalar sc1)) (.scalar (.fromScalarInt msc1)) none
        (fun _ h => nomatch h) (Or.inr ⟨.scalar sc1, rfl, val1_immRel⟩))
      (.memory ⟨Witness.witnessMemPlace, translateTy u8Ty emptyLayoutTable⟩)
  have hmp1 :
      MemPlaceRel (Witness.witnessMachineOf Witness.witnessUninitAlloc)
        u8Decl.ty emptyLayoutTable none Witness.witnessMemPlace := by
    cases hloc1 with
    | indirect _ _ _ _ _ hmp => exact hmp
  have hdest_ind :
      CallerDestinationRel (Witness.witnessMachineOf Witness.witnessUninitAlloc) 0
        (witSavedCallerFrame .uninit .uninit [])
        (mkWitCallerMiriFrame 0
          ⟨.live (.immediate .uninit), none⟩
          ⟨.live (.indirect Witness.witnessMemPlace), none⟩)
        (.memory ⟨Witness.witnessMemPlace, translateTy u8Ty emptyLayoutTable⟩) :=
    .indirect 1 u8Decl .uninit Witness.witnessMemPlace none
      (.memory ⟨Witness.witnessMemPlace, translateTy u8Ty emptyLayoutTable⟩)
      Witness.witnessAllocId Witness.witnessTag Witness.witnessBaseAddr Witness.witnessRelOffset
      { kind := .stack, allocation := Witness.witnessUninitAlloc }
      (initWordsFalse (Miri.ABI.Size.ofBytes 8))
      rfl rfl hu8_prim rfl (fun h => nomatch h) rfl (Or.inl rfl)
      rfl rfl rfl (List.Mem.head _) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl rfl hmask_uninit (by decide) (by decide) hmp1
  have hlinks_root :
      CallerStackLinksRel witCallerBody (Witness.witnessMachineOf Witness.witnessUninitAlloc)
        witCallerBody
        { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
        [] []
        [mkWitCallerMiriFrame 0
          ⟨.live (.immediate .uninit), none⟩
          ⟨.live (.indirect Witness.witnessMemPlace), none⟩] :=
    .root _ _ [] rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr_caller
  have hlinks_ret :
      CallerStackLinksRel witCallerBody (Witness.witnessMachineOf Witness.witnessUninitAlloc)
        (activeMirBody witCallerBody witCalleeReadyToReturnAnneal)
        witCalleeReadyToReturnAnneal.frame
        witCalleeReadyToReturnAnneal.memory.callStack
        witCalleeReadyToReturnAnneal.memory.activeProtectors
        witIndirectDestReturnMiri.stack.frames.toList.reverse :=
    .cons witCalleeBody
      witCalleeReadyToReturnAnneal.frame
      (witSavedCallerFrame .uninit .uninit []) [] [1] []
      _ _ [] .Continue
      rfl hdest_ind hfr_callee (fun _ _ _ _ _ h _ _ _ => nomatch h) rfl (by intro _ _; rfl) hlinks_root
  have hdisj_ret : MultiFrameAllocDisjoint witIndirectDestReturnMiri.stack.frames := by
    refine ⟨?_, ?_⟩
    · intro mf hmf
      rcases List.mem_cons.mp hmf with rfl | hmf1
      · exact hd_caller
      · rcases List.mem_singleton.mp hmf1 with rfl
        intro i j mp₁ mp₂ lay₁ lay₂ _ hi _
        dsimp only [mkWitCalleeMiriFrame] at hi
        rcases i with _ | i <;> cases hi
    · intro f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ hne hf₁ hf₂ hi hj
      rcases f₁ with _ | ⟨_ | f₁⟩
      · rcases f₂ with _ | ⟨_ | f₂⟩
        · exact False.elim (hne rfl)
        · injection hf₂ with hmf₂; subst hmf₂
          rcases j with _ | j <;> cases hj
        · cases hf₂
      · injection hf₁ with hmf₁; subst hmf₁
        rcases i with _ | i <;> cases hi
      · cases hf₁
  have hstate_ret :
      MultiFrameStateRel witCallerBody witCalleeReadyToReturnAnneal witIndirectDestReturnMiri :=
    .mk _ rfl (fun hnil => nomatch hnil) (fun _ => rfl)
      hlinks_ret.toFrameStackRel hlinks_ret hdisj_ret
      ⟨by decide, by decide, rfl, rfl, rfl⟩
      (by decide) (by decide)
      (by intro cid hcid; rcases List.mem_singleton.mp hcid with rfl; decide)
      (by intro e he cid hprot
          rcases List.mem_singleton.mp he with rfl
          injection hprot with h; subst h; decide)
      (BorrowTrackerStackRel.of_none _ _ _)
  have hsim_ret :=
    step_terminator_return_callee_simulation hstate_ret rfl
      (by intro tf htf; injection htf with h; subst h; rfl)
      (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm .return_, isCleanup := false })
      (decl0 := u8Decl)
      rfl rfl rfl rfl rfl rfl (fun h => nomatch h)
      (by intro destIdx destDecl hcf hdecl_d v imm himm
          injection hcf with hd _; subst hd
          injection hdecl_d with hdd; subst hdd
          exact himm)
  exact ⟨hsim_call, hsim_ret⟩

/-! ## (h) Call with Scalar `copy` and `move` Arguments Witness (`M2`) -/

/-- Callee MIR body `"crate::add_args"` taking two `u8` parameters (`_1, _2`)
with return local `_0`. -/
def witBinaryCalleeBody : CapturedMir where
  defPath := "crate::add_args"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u8Decl, u8Decl, u8Decl]
  basicBlocks :=
    [{ statements := []
       terminator := mkTerm .return_
       isCleanup := false }]
  fnAbi := fnAbiU8
  layouts := emptyLayoutTable
  allocations := []

/-- Caller MIR body `"crate::binary_caller"` calling
`add_args(copy _2, move _3) -> _1, bb1`. -/
def witBinaryCallerBody : CapturedMir where
  defPath := "crate::binary_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl, u8Decl, u8Decl, u8Decl]
  basicBlocks :=
    [ { statements := []
        terminator :=
          mkTerm (.call binaryCalleeFuncOp [.copy ⟨2, .nil⟩, .move ⟨3, .nil⟩] ⟨1, .nil⟩ (some 1) .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm .return_
        isCleanup := false } ]
  fnAbi := fnAbiU8
  layouts := emptyLayoutTable
  allocations := []

def witBinaryCallerAtCallAnneal : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .uninit, .init (.scalar sc1), .init (.scalar sc1)] }
    memory := { callees := [witBinaryCalleeBody], nextProtector := 1 } }

def witBinaryCallerMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody witBinaryCallerBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy u8Ty emptyLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals :=
      #[⟨.live (.immediate .uninit), none⟩,
        ⟨.live (.immediate .uninit), none⟩,
        ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩,
        ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def witBinaryCallerAtCallMiri : AnnealStepState :=
  { stack := ⟨#[witBinaryCallerMiriFrame]⟩
    machine := AnnealMachine.empty }

/-- **Witness (h, `M2`)**: Calling `witBinaryCalleeBody(copy _2, move _3)` from
`witBinaryCallerBody`:
* preserves `_2 = .init (.scalar sc1)` and deinitializes `_3` to `.uninit` in
  the saved caller frame;
* initializes callee parameter locals `_1` and `_2` to `.init (.scalar sc1)` in
  Anneal and `.live (.immediate (.scalar (.fromScalarInt msc1)))` in `lean-miri`. -/
theorem wit_lm4_1_call_with_copy_and_move_args_simulation :
    StepRelMultiFrame witBinaryCallerBody witBinaryCallerAtCallMiri
      (stepMirFn witBinaryCallerBody witBinaryCallerAtCallAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witBinaryCallerBody witBinaryCallerAtCallAnneal)
          witBinaryCallerAtCallAnneal.memory.callees)
        () witBinaryCallerAtCallMiri) ∧
    (∃ s' cf,
      stepMirFn witBinaryCallerBody witBinaryCallerAtCallAnneal = .step s' ∧
      s'.memory.callStack = [cf] ∧
      get? cf.frame.locals 2 = some (.init (.scalar sc1)) ∧
      get? cf.frame.locals 3 = some .uninit ∧
      s'.frame.locals = [.uninit, .init (.scalar sc1), .init (.scalar sc1)]) := by
  have hloc_uninit :
      LocalRel AnnealMachine.empty u8Decl emptyLayoutTable .uninit
        ⟨.live (.immediate .uninit), none⟩ :=
    .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  have hloc_sc1 :
      LocalRel AnnealMachine.empty u8Decl emptyLayoutTable (.init (.scalar sc1))
        ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩ :=
    .immediate (.init (.scalar sc1)) (.scalar (.fromScalarInt msc1)) none
      (fun _ h => nomatch h) (Or.inr ⟨.scalar sc1, rfl, val1_immRel⟩)
  have hfr :
      FrameRel witBinaryCallerBody AnnealMachine.empty
        witBinaryCallerAtCallAnneal.frame witBinaryCallerMiriFrame := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    rcases i with _ | ⟨_ | ⟨_ | ⟨_ | i⟩⟩⟩
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact hloc_uninit
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact hloc_uninit
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact hloc_sc1
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact hloc_sc1
    · cases hdecl
  have hstate0 : StateRel witBinaryCallerBody witBinaryCallerAtCallAnneal witBinaryCallerAtCallMiri :=
    .mk _ rfl rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr rfl rfl rfl rfl rfl
      (by intro i j mp₁ mp₂ lay₁ lay₂ _ hi _
          dsimp only [witBinaryCallerMiriFrame] at hi
          rcases i with _ | ⟨_ | ⟨_ | ⟨_ | i⟩⟩⟩ <;> cases hi)
  have hstate :=
    (StateRel.iff_multiFrameStateRel_depth1 rfl rfl rfl rfl rfl (by decide)).mp hstate0
  have hsim :=
    step_terminator_call_simulation hstate (fun _ h => nomatch h)
      (bb := { statements := []
               terminator :=
                 mkTerm (.call binaryCalleeFuncOp [.copy ⟨2, .nil⟩, .move ⟨3, .nil⟩] ⟨1, .nil⟩ (some 1) .continue_)
               isCleanup := false })
      (destDecl := u8Decl)
      (calleeBody := witBinaryCalleeBody)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by intro tf htf
          apply CallerDestSlotWf.of_immediate
          intro mls hmls mp hmp
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hmp)
      (by intro tf htf mls hmls hdead
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hdead)
      (by intro tf htf
          injection htf with h; subst h
          refine .cons (.copy ⟨2, .nil⟩) [.move ⟨3, .nil⟩] u8Decl [u8Decl] ?_
            (.cons (.move ⟨3, .nil⟩) [] u8Decl [] ?_ (.nil []))
          · exact .scalarOp (.copy ⟨2, .nil⟩) u8Ty u8Decl
              (.copyLocal 2 u8Decl rfl (by decide)
                (by intro mls hmls mp hmp; injection hmls with hm; subst hm; nomatch hmp))
              rfl (fun _ _ h => h)
          · exact .moveLocal 3 u8Decl u8Decl rfl (by decide)
              (by intro mls hmls mp hmp; injection hmls with hm; subst hm; nomatch hmp)
              rfl (fun _ _ h => h))
  exact ⟨hsim, _, _, rfl, rfl, rfl, rfl, rfl⟩

/-! ## (i) Cross-Frame Unscoped `BorrowEntry.targetLocal` Divergence Witness (`H4`) -/

/-- **Witness (i, `H4`)**:
In Anneal's `Trusted` semantics (`Places.lean` / `Terminators.lean`),
`BorrowEntry` records `targetLocal : Local` without a frame identifier, and
`TerminatorKind.return_` preserves `s.memory.borrows` unchanged:
1. If a callee frame records a borrow entry `e = { tag := 10, targetLocal := 0, perm := .reservedFrz true, protector := none, parentTag := none }`
   for callee local `_0`, returning to the caller (`Terminators.lean:247-281`)
   leaves `e ∈ s'.memory.borrows`, where `hasTreeWriteUB s'.memory.borrows [] 0 [] 0`
   Would still match `e.targetLocal == 0` on caller local `_0`;
2. In `lean-miri`, indirect stack locals are keyed by `AllocId` and deallocated
   by `Stack.cleanupStackFrame` (`deallocFrameLocals`), removing `witnessAllocId`
   from `mem'.live` (`(deallocFrameLocals (Witness.witnessMachineOf Witness.witnessUninitAlloc).memory (mkWitCalleeMiriFrame ⟨.live (.indirect Witness.witnessMemPlace), none⟩)).live = #[]`). -/
theorem wit_lm4_1_unscoped_borrow_cross_frame_divergence :
    let e0 : BorrowEntry :=
      { tag := 10
        targetLocal := 0
        targetProjection := []
        perm := .reservedFrz true
        protector := none
        parentTag := none }
    let sCallee : MachineState :=
      { witCalleeReadyToReturnAnneal with
        memory := { witCalleeReadyToReturnAnneal.memory with
          borrows := [e0]
          activeProtectors := [] } }
    (∃ sCaller,
      stepMirFn witCallerBody sCallee = .step sCaller ∧
      sCaller.memory.borrows = [e0]) ∧
    (deallocFrameLocals
      (Witness.witnessMachineOf Witness.witnessUninitAlloc).memory
      (mkWitCalleeMiriFrame ⟨.live (.indirect Witness.witnessMemPlace), none⟩)).live = #[] := by
  exact ⟨⟨_, rfl, rfl⟩, rfl⟩

end LeanMiriSpec.Correspondence.WitnessLM4_1
