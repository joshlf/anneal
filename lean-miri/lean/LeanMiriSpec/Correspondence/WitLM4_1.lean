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
* (j) `wit_lm4_1_return_from_diverging_callee_ub`: returning from a callee whose
  saved caller frame has `isDiverging = true` faults with UB in both machines.
* (k) `wit_lm4_1_diverging_call_push_simulation` and
  `wit_lm4_1_diverging_call_then_return_ub`: Stage-1 diverging call to a linked
  callee (`pushDivergingCalleeFrame`) is simulated by
  `step_terminator_call_diverging_simulation` from a concrete related state, and
  a genuine 3-step lockstep run (push, `_0 = const 1_u8`, `return`) faults with
  UB in both machines (`isDiverging = true` vs. `ControlFlow.returnToBlock none`).
* (l) `wit_lm4_1_end_of_call_foreign_unique_frozen_step_divergence`: concrete
  step-level witness for `cex_end_of_call_foreign_unique_frozen_divergence`,
  executing `stepMirFn` and `Step.step` (`annealStepHooksLM4_1`, whose
  `AnnealMachine` holds no per-allocation `BorrowTree`s and therefore steps in
  lockstep with Stage-1 `stepMirFn`) on a returning callee with
  `borrows = cexForeignUniqueBorrows` and `activeProtectors = [7]`, whereas
  canonical Miri's end-of-call protector release on `basedNormalTree` freezes
  the foreign sibling from `.unique` to `.frozen`.
* (m) `wit_lm4_1_drop_projected_and_canonical_divergence`: concrete multi-case
  witness for `step_terminator_drop_projected_simulation` (`.dead` UB, `.uninit`
  Stage-1 UB vs. canonical no-glue jump, and live 2-field tuple projected
  `Drop(_1.0)` advancing without deinitializing `_1`) and
  `step_terminator_drop_canonical_no_glue_step_divergence`.
* (n) `wit_lm4_1_unwindResume_cleanup_and_unreachable_ub_simulation` and
  `wit_lm4_1_unwindResume_root_panic_vs_ub_divergence`: concrete witnesses for
  `step_terminator_unwindResume_callee_simulation` (covering `cf.returnUnwind = .cleanup 1`
  and `cf.returnUnwind = .unreachable`) and
  `step_terminator_unwindResume_root_panic_vs_ub_divergence` (root-frame
  `UnwindResume` returning `.retOutcome .panic` in Stage-1 vs. top-frame UB in
  `lean-miri`).
* (o) `wit_lm4_1_multiFrame_continue_unwind_and_assert_terminate`: concrete
  3-frame (`k = 2` `.continue_ -> .cleanup 1`) unwinding witness for
  `step_terminator_unwindResume_multiFrame_simulation` releasing stacked
  protectors `[2, 1] -> []` across `MiriUnwindSteps` of length `2`, combined with
  `step_terminator_unwindTerminate_abort_vs_unsupported`,
  `step_terminator_assert_local_simulation`, and
  `step_terminator_call_diverging_panic_vs_unlinked`.
* (p) `wit_lm4_1_nonConst_fnDef_and_indirect_fnPtr_call_and_safety_divergence`:
  concrete witness for `step_terminator_call_fnDef_local_simulation`,
  `step_terminator_call_fnPtr_dangling_or_uninit_ub_simulation`,
  `step_terminator_call_indirect_fnPtr_move_simulation`, and
  `step_terminator_call_indirect_unsafe_to_safe_fnPtr_divergence`.
* (q) `wit_lm4_1_nounwind_callee_unwind_divergence`: genuine 2-step execution
  certifying the Stage-1 `FnAbi.canUnwind`-blindness vs. canonical
  `Call.initStackFrame` unwinding divergence.
* (r) `wit_lm4_1_reifyFnPointer_chain_layoutCompat_and_directUnwind`: concrete
  2-step `MultiFrameStateRel` → `ReifyFnPointer` → `IndirectFnPtrMovePre` →
  `TerminatorKind.call (.move ⟨3, .nil⟩)` → `MultiFrameStateRel` simulation,
  indirect `FnPtr` ABI mismatch UB (`fn() -> u64` called as `fn() -> u8`),
  `LayoutCompat` (`usize` vs. `u64`) divergence
  (`step_terminator_call_indirect_layoutCompat_fnPtr_divergence`), canonical
  `Miri.Interpreter.FunctionPointers.Registry` lookup bridge, and linked
  `"core::panicking::panic"` 2-step call + unwind & direct-unwind failed
  `Assert` / `UnwindTerminate` simulations.
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
  { args := [], ret := { layout := u8Layout, mode := .direct }, conv := .rust, canUnwind := true }

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
      []
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
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
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
      []
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
      rfl rfl rfl rfl rfl rfl rfl rfl
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
      []
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
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
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
      _ _ []
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
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
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
   for callee local `_0`, returning to the caller (`Terminators.lean:3005-3039`)
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
    (∃ sCaller mCaller,
      stepMirFn witCallerBody sCallee = .step sCaller ∧
      sCaller.memory.borrows = [e0] ∧
      Miri.Interpreter.Step.step
        (annealStepHooksLM4_1 (activeMirBody witCallerBody sCallee)
          sCallee.memory.callees (annealPoppedFrameState sCallee))
        () witCalleeReadyToReturnMiri = (mCaller, .ok true) ∧
      mCaller.stack.frames.size = 1) ∧
    (deallocFrameLocals
      (Witness.witnessMachineOf Witness.witnessUninitAlloc).memory
      (mkWitCalleeMiriFrame ⟨.live (.indirect Witness.witnessMemPlace), none⟩)).live = #[] := by
  exact ⟨⟨_, _, rfl, rfl, rfl, rfl⟩, rfl⟩

/-! ## (j) Stage-1 Diverging Caller Frame Return UB Witness (`SavedCallerFrame.isDiverging = true`) -/

def witDivergingSavedCallerFrame : SavedCallerFrame :=
  { witSavedCallerFrame .uninit .uninit [] with isDiverging := true }

def witDivergingCalleeMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { mkWitCalleeMiriFrame ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩ with
    returnContinuation := .goto none .Continue }

def witDivergingCalleeReturnAnneal : MachineState :=
  { witCalleeReadyToReturnAnneal with
    memory := { witCalleeReadyToReturnAnneal.memory with
      borrows := []
      activeProtectors := []
      callStack := [witDivergingSavedCallerFrame] } }

def witDivergingCalleeReturnMiri : AnnealStepState :=
  { stack :=
      ⟨#[mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩,
         witDivergingCalleeMiriFrame]⟩
    machine := AnnealMachine.empty }

/-- **Witness (j)**: Returning from a non-root callee frame whose saved caller
frame has `isDiverging = true` (`returnContinuation = .goto none .Continue`)
faults with undefined behavior in both Anneal (`Terminators.lean:3011`) and
`lean-miri` (`ControlFlow.returnToBlock none`). -/
theorem wit_lm4_1_return_from_diverging_callee_ub :
    StepRelMultiFrame witCallerBody witDivergingCalleeReturnMiri
      (stepMirFn witCallerBody witDivergingCalleeReturnAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witDivergingCalleeReturnAnneal)
          witDivergingCalleeReturnAnneal.memory.callees
          (annealPoppedFrameState witDivergingCalleeReturnAnneal))
        () witDivergingCalleeReturnMiri) ∧
    stepMirFn witCallerBody witDivergingCalleeReturnAnneal = .fail .ub ∧
    ∃ msg,
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witDivergingCalleeReturnAnneal)
          witDivergingCalleeReturnAnneal.memory.callees
          (annealPoppedFrameState witDivergingCalleeReturnAnneal))
        () witDivergingCalleeReturnMiri).2 = .error (.undefinedBehavior msg) := by
  have hfr_caller :=
    witCallerFrame_rel (mach := AnnealMachine.empty) 0 .uninit .uninit
      ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  have hfr_callee :
      FrameRel witCalleeBody AnnealMachine.empty
        { blockIdx := 0, stmtIdx := 0, locals := [.init (.scalar sc1)] }
        witDivergingCalleeMiriFrame := by
    refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
    rcases i with _ | i
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate (.init (.scalar sc1)) (.scalar (.fromScalarInt msc1)) none
        (fun _ h => nomatch h) (Or.inr ⟨.scalar sc1, rfl, val1_immRel⟩)
    · cases hdecl
  have hlinks_root :
      CallerStackLinksRel witCallerBody AnnealMachine.empty witCallerBody
        { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
        [] []
        [mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩] :=
    .root _ _ [] rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr_caller
  have hdest :
      CallerDestinationRel AnnealMachine.empty 0 witDivergingSavedCallerFrame
        (mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
        witDivergingCalleeMiriFrame.returnPlace :=
    .immediate 1 u8Decl .uninit .uninit none rfl rfl rfl (fun h => nomatch h) rfl
  have hlinks :
      CallerStackLinksRel witCallerBody AnnealMachine.empty
        (activeMirBody witCallerBody witDivergingCalleeReturnAnneal)
        witDivergingCalleeReturnAnneal.frame
        witDivergingCalleeReturnAnneal.memory.callStack
        witDivergingCalleeReturnAnneal.memory.activeProtectors
        witDivergingCalleeReturnMiri.stack.frames.toList.reverse :=
    .cons witCalleeBody
      witDivergingCalleeReturnAnneal.frame
      witDivergingSavedCallerFrame [] [] []
      witDivergingCalleeMiriFrame
      (mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
      []
      rfl hdest hfr_callee (fun _ _ _ _ _ h _ _ _ => nomatch h) rfl (fun _ h => nomatch h) hlinks_root
  have hdisj : MultiFrameAllocDisjoint witDivergingCalleeReturnMiri.stack.frames := by
    refine ⟨?_, ?_⟩
    · intro mf hmf i j mp₁ mp₂ lay₁ lay₂ _ hi _
      rcases List.mem_cons.mp hmf with rfl | hmf1
      · dsimp only [mkWitCallerMiriFrame] at hi
        rcases i with _ | ⟨_ | i⟩ <;> cases hi
      · rcases List.mem_singleton.mp hmf1 with rfl
        dsimp only [witDivergingCalleeMiriFrame, mkWitCalleeMiriFrame] at hi
        rcases i with _ | i <;> cases hi
    · intro f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ _ hf₁ _ hi _
      rcases f₁ with _ | ⟨_ | f₁⟩
      · injection hf₁ with hmf₁; subst hmf₁
        rcases i with _ | ⟨_ | i⟩ <;> cases hi
      · injection hf₁ with hmf₁; subst hmf₁
        rcases i with _ | i <;> cases hi
      · cases hf₁
  have hstate :
      MultiFrameStateRel witCallerBody witDivergingCalleeReturnAnneal witDivergingCalleeReturnMiri :=
    .mk _ rfl (fun hnil => nomatch hnil) (fun _ => rfl)
      hlinks.toFrameStackRel hlinks hdisj
      ⟨by decide, by decide, rfl, rfl, rfl⟩
      (ActiveProtectorsValid.nil _) (by decide)
      (fun _ h => nomatch h) (fun _ h => nomatch h)
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

/-! ## (k) Stage-1 Diverging Call to a Linked Callee: Push, `_0` Write, Return UB -/

/-- `fn() -> u8` function item type for the linked callee `"crate::div_callee"`,
invoked through a *diverging* call (`target = none`). -/
def divCalleeFnTy : Ty := { kind := .fnDef "crate::div_callee" [], layoutIdx := 0 }

/-- Constant operand referencing `"crate::div_callee"`. -/
def divCalleeFuncOp : MirAst.Operand :=
  .constant { ty := divCalleeFnTy, val := .zeroSized }

/-- Linked callee body `"crate::div_callee"`:
`bb0`: `_0 = const 1_u8; return`, so that `_0` is initialized and its final
`return` faults only because the saved caller frame is diverging. -/
def witDivCalleeBody : CapturedMir where
  defPath := "crate::div_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl]
  basicBlocks :=
    [{ statements :=
         [{ kind := .assign ⟨0, .nil⟩ (.use (.constant { ty := u8Ty, val := .scalar (.int sc1) }))
            span := "lm-4.1-witness" }]
       terminator := mkTerm .return_
       isCleanup := false }]
  fnAbi := fnAbiU8
  layouts := emptyLayoutTable
  allocations := []

/-- Root caller body `"crate::div_caller"`:
`bb0`: `_1 = call crate::div_callee() -> [return: none, unwind: continue]`. -/
def witDivCallerBody : CapturedMir where
  defPath := "crate::div_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl, u8Decl]
  basicBlocks :=
    [{ statements := []
       terminator := mkTerm (.call divCalleeFuncOp [] ⟨1, .nil⟩ none .continue_)
       isCleanup := false }]
  fnAbi := fnAbiU8
  layouts := emptyLayoutTable
  allocations := []

/-- Root `lean-miri` frame for `witDivCallerBody` at `(bb0, 0)`. -/
def witDivCallerMiriFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody witDivCallerBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy u8Ty emptyLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate .uninit), none⟩]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def witDivCallAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
    memory := { callees := [witDivCalleeBody], nextProtector := 1 } }

def witDivCallMiri : AnnealStepState :=
  { stack := ⟨#[witDivCallerMiriFrame]⟩
    machine := AnnealMachine.empty }

theorem witDivCall_rel :
    MultiFrameStateRel witDivCallerBody witDivCallAnneal witDivCallMiri := by
  have hfr_caller :
      FrameRel witDivCallerBody AnnealMachine.empty witDivCallAnneal.frame witDivCallerMiriFrame := by
    refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
    rcases i with _ | ⟨_ | i⟩
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · cases hdecl
  have hstate0 : StateRel witDivCallerBody witDivCallAnneal witDivCallMiri :=
    .mk _ rfl rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr_caller
      rfl rfl rfl rfl rfl
      (by
        intro i j mp₁ mp₂ lay₁ lay₂ _ hi _
        rcases i with _ | ⟨_ | i⟩ <;> cases hi)
  exact (StateRel.iff_multiFrameStateRel_depth1 rfl rfl rfl rfl rfl (by decide)).mp hstate0

/-- **Witness (k.1)**: the premises of `step_terminator_call_diverging_simulation`
are satisfiable: executing the diverging call
`_1 = call crate::div_callee() -> [return: none, unwind: continue]` of
`witDivCallerBody` from `witDivCallAnneal` / `witDivCallMiri` steps both machines
to `MultiFrameStateRel`-related depth-2 states, where Stage-1 `Trusted` has pushed
a diverging `SavedCallerFrame` (`pushDivergingCalleeFrame`, `isDiverging = true`,
`returnUnwind = .continue_`) and `lean-miri`'s callee frame carries the return
continuation `.goto none .Continue`. -/
theorem wit_lm4_1_diverging_call_push_simulation :
    StepRelMultiFrame witDivCallerBody witDivCallMiri
      (stepMirFn witDivCallerBody witDivCallAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witDivCallerBody witDivCallAnneal)
          witDivCallAnneal.memory.callees
          (annealPoppedFrameState witDivCallAnneal))
        () witDivCallMiri) ∧
    ∃ s₁,
      stepMirFn witDivCallerBody witDivCallAnneal = .step s₁ ∧
      s₁.memory.activeCallee = some witDivCalleeBody ∧
      s₁.memory.callStack.map SavedCallerFrame.isDiverging = [true] ∧
      s₁.memory.callStack.map SavedCallerFrame.returnUnwind = [.continue_] ∧
      get? s₁.frame.locals 0 = some .uninit := by
  have hsim :
      StepRelMultiFrame witDivCallerBody witDivCallMiri
        (stepMirFn witDivCallerBody witDivCallAnneal)
        (Miri.Interpreter.Step.step
          (annealStepHooksLM4_1
            (activeMirBody witDivCallerBody witDivCallAnneal)
            witDivCallAnneal.memory.callees
            (annealPoppedFrameState witDivCallAnneal))
          () witDivCallMiri) := by
    apply step_terminator_call_diverging_simulation
      witDivCall_rel (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.call divCalleeFuncOp [] ⟨1, .nil⟩ none .continue_)
               isCleanup := false })
      (destDecl := u8Decl)
      (calleeBody := witDivCalleeBody)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by intro tf htf
          apply CallerDestSlotWf.of_immediate
          intro mls hmls mp hmp
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hmp)
      (by intro tf htf mls hmls hdead
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hdead)
      (fun _ _ => .nil [])
  exact ⟨hsim, _, rfl, rfl, rfl, rfl, rfl⟩

/-- `lean-miri` successor of `m` under the `LM-4.1` hooks paired with the
lockstep Anneal state `s` (`annealStepHooksLM4_1 (activeMirBody rootBody s)
s.memory.callees (annealPoppedFrameState s)`), for steps that continue
(`.ok true`). -/
def miriNextLM4_1 (rootBody : CapturedMir) (s : MachineState) (m : AnnealStepState) :
    Option AnnealStepState :=
  match Miri.Interpreter.Step.step
      (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s))
      () m with
  | (m', .ok true) => some m'
  | _ => none

/-- The `StepError.undefinedBehavior` message of `lean-miri`'s next step from `m`
(under the `LM-4.1` hooks paired with the lockstep Anneal state `s`), if that step
reports undefined behavior. -/
def miriStepUBMsgLM4_1 (rootBody : CapturedMir) (s : MachineState) (m : AnnealStepState) :
    Option String :=
  match Miri.Interpreter.Step.step
      (annealStepHooksLM4_1 (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s))
      () m with
  | (_, .error (.undefinedBehavior msg)) => some msg
  | _ => none

/-- Whether `m`'s top frame is a callee frame with diverging return continuation
`.goto none .Continue` whose return place `_0` holds an initialized immediate
scalar (so a normal return from it can only fault on `returnToBlock none`). -/
def miriTopIsDivergingWithInitRet (m : AnnealStepState) : Bool :=
  match m.stack.frames.back? with
  | some tf =>
    match tf.returnContinuation, tf.locals[0]? with
    | .goto none .Continue,
      some (Miri.Interpreter.LocalState.mk (.live (.immediate (.scalar _))) _) => true
    | _, _ => false
  | none => false

/-- **Witness (k.2)**: genuine 3-step lockstep execution of both machines from
`witDivCallAnneal` / `witDivCallMiri` (kernel evaluation via `decide`, no
hand-built intermediate states):
1. the diverging call pushes `witDivCalleeBody` (Stage-1
   `pushDivergingCalleeFrame`, `isDiverging = true`; `lean-miri` continuation
   `.goto none .Continue`; cf. `wit_lm4_1_diverging_call_push_simulation`);
2. the callee executes `_0 = const 1_u8` in both machines;
3. the callee's normal `return` faults with undefined behavior in both machines
   although `_0` is initialized: Stage-1 `Trusted` on
   `SavedCallerFrame.isDiverging = true` (`Terminators.lean:3011-3012`), and
   `lean-miri` on `ControlFlow.returnToBlock none` (Miri's `throw_ub!(Unreachable)`). -/
theorem wit_lm4_1_diverging_call_then_return_ub :
    ∃ s₁ s₂ : MachineState,
      stepMirFn witDivCallerBody witDivCallAnneal = .step s₁ ∧
      stepMirFn witDivCallerBody s₁ = .step s₂ ∧
      s₂.memory.callStack.map SavedCallerFrame.isDiverging = [true] ∧
      get? s₂.frame.locals 0 = some (.init (.scalar sc1)) ∧
      stepMirFn witDivCallerBody s₂ = .fail .ub ∧
      ((miriNextLM4_1 witDivCallerBody witDivCallAnneal witDivCallMiri).bind
          (miriNextLM4_1 witDivCallerBody s₁)).map
        (fun m₂ => (miriTopIsDivergingWithInitRet m₂, miriStepUBMsgLM4_1 witDivCallerBody s₂ m₂)) =
        some (true, some "Unreachable") := by
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-! ## (l) Step-Level Bi-Side End-of-Call Foreign-`Unique` Frozen Divergence Witness (`C2`) -/

def witCexCalleeReturnAnneal : MachineState :=
  { witCalleeReadyToReturnAnneal with
    memory :=
      { witCalleeReadyToReturnAnneal.memory with
        borrows := cexForeignUniqueBorrows
        activeProtectors := [7]
        nextProtector := 8 } }

def witCexCalleeReturnMiri : AnnealStepState :=
  { witCalleeReadyToReturnMiri with machine := AnnealMachine.empty }

/-- **Witness (l, `C2`)**: Step-level certification of the end-of-call
foreign-`Unique` protector-release divergence on `witCexCalleeReturnAnneal` /
`witCexCalleeReturnMiri`:
1. Both states satisfy `MultiFrameStateRel witCallerBody` with
   `borrows = cexForeignUniqueBorrows = [e{ReservedFrz false, prot = some 7}, f{Unique, prot = none}]`
   and `activeProtectors = [7]`;
2. `stepMirFn witCallerBody witCexCalleeReturnAnneal` steps `TerminatorKind.return_`
   to `sCaller` with `sCaller.memory.activeProtectors = []` and
   `sCaller.memory.borrows = cexForeignUniqueBorrows` (preserving foreign sibling
   `f.perm = .unique`). Because `AnnealMachine` holds no per-allocation
   `BorrowTree`s, `Step.step (annealStepHooksLM4_1 ...)` steps in lockstep with
   Stage-1 `stepMirFn` under `StepRelMultiFrame`;
3. Canonical Miri's end-of-call protector release access at `e` on `basedNormalTree`
   (`(basedNormalTree cexForeignUniqueBorrows [7]).performAccess 0 .Read .SkipChildrenOfAccessed`)
   instead freezes foreign sibling `f` from `.unique` to `.frozen`
   (`normalTreePerms res.tree 2 = [some (.reservedFrz false), some .frozen] ≠ sCaller.memory.borrows.map (fun b => some b.perm)`). -/
theorem wit_lm4_1_end_of_call_foreign_unique_frozen_step_divergence :
    MultiFrameStateRel witCallerBody witCexCalleeReturnAnneal witCexCalleeReturnMiri ∧
    StepRelMultiFrame witCallerBody witCexCalleeReturnMiri
      (stepMirFn witCallerBody witCexCalleeReturnAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody witCexCalleeReturnAnneal)
          witCexCalleeReturnAnneal.memory.callees
          (annealPoppedFrameState witCexCalleeReturnAnneal))
        () witCexCalleeReturnMiri) ∧
    (∃ sCaller,
      stepMirFn witCallerBody witCexCalleeReturnAnneal = .step sCaller ∧
      sCaller.memory.activeProtectors = [] ∧
      sCaller.memory.borrows = cexForeignUniqueBorrows ∧
      let res :=
        (basedNormalTree cexForeignUniqueBorrows [7]).performAccess 0 .Read .SkipChildrenOfAccessed
      res.status = .Completed ∧
      normalTreePerms res.tree 2 = [some (.reservedFrz false), some .frozen] ∧
      normalTreePerms res.tree 2 ≠ sCaller.memory.borrows.map (fun b => some b.perm)) := by
  have hfr_caller :=
    witCallerFrame_rel (mach := AnnealMachine.empty) 0 .uninit .uninit
      ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  have hfr_callee :=
    witCalleeFrame_rel (mach := AnnealMachine.empty) (.init (.scalar sc1))
      ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩
      (.immediate (.init (.scalar sc1)) (.scalar (.fromScalarInt msc1)) none
        (fun _ h => nomatch h) (Or.inr ⟨.scalar sc1, rfl, val1_immRel⟩))
  have hlinks_root :
      CallerStackLinksRel witCallerBody AnnealMachine.empty witCallerBody
        { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
        [] []
        [mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩] :=
    .root _ _ [] rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr_caller
  have hdest :
      CallerDestinationRel AnnealMachine.empty 0 (witSavedCallerFrame .uninit .uninit [])
        (mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
        (mkWitCalleeMiriFrame ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩).returnPlace :=
    .immediate 1 u8Decl .uninit .uninit none rfl rfl rfl (fun h => nomatch h) rfl
  have hlinks :
      CallerStackLinksRel witCallerBody AnnealMachine.empty
        (activeMirBody witCallerBody witCexCalleeReturnAnneal)
        witCexCalleeReturnAnneal.frame
        witCexCalleeReturnAnneal.memory.callStack
        witCexCalleeReturnAnneal.memory.activeProtectors
        witCexCalleeReturnMiri.stack.frames.toList.reverse :=
    .cons witCalleeBody
      witCexCalleeReturnAnneal.frame
      (witSavedCallerFrame .uninit .uninit []) [] [7] []
      _ _ []
      rfl hdest hfr_callee (fun _ _ _ _ _ h _ _ _ => nomatch h) rfl (by intro _ _; rfl) hlinks_root
  have hdisj : MultiFrameAllocDisjoint witCexCalleeReturnMiri.stack.frames :=
    wit_multiFrameAllocDisjoint_two _ _ _
      (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
  have hcex := cex_end_of_call_foreign_unique_frozen_divergence
  have hstate :
      MultiFrameStateRel witCallerBody witCexCalleeReturnAnneal witCexCalleeReturnMiri :=
    .mk _ rfl (fun hnil => nomatch hnil) (fun _ => rfl)
      hlinks.toFrameStackRel hlinks hdisj
      hcex.2.1 hcex.1 (by decide)
      (by intro cid hcid; rcases List.mem_singleton.mp hcid with rfl; decide)
      (by intro e he cid hprot
          rcases List.mem_cons.mp he with rfl | he1
          · injection hprot with h; subst h; decide
          · rcases List.mem_singleton.mp he1 with rfl
            cases hprot)
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
  exact ⟨hstate, hsim, ⟨_, rfl, rfl, rfl, hcex.2.2.2.1, hcex.2.2.2.2.1, hcex.2.2.2.2.2⟩⟩

/-! ## (m) Projected `Terminator.Drop` Simulation & Canonical No-Glue `Drop` Divergence Witness -/

def u8PairTy : Ty := { kind := .tuple [.uint .u8, .uint .u8], layoutIdx := 0 }

def u8PairDecl : MirAst.LocalDecl := { mutability := .mut, ty := u8PairTy, debugName := none }

/-- Realistic `rustc` layout of `(u8, u8)`: size `2`, alignment `1`,
`BackendRepr::ScalarPair(u8, u8)` with fields at offsets `0` and `1`. -/
def u8PairLayout : TypeLayout :=
  { size := { bytes := 2 }
    align := { bytes := 1 }
    backendRepr :=
      .scalarPair
        (.initialized (.int 8 false) { start := 0, end_ := 255 })
        (.initialized (.int 8 false) { start := 0, end_ := 255 })
    fields := .arbitrary [{ bytes := 0 }, { bytes := 1 }] [0, 1]
    variants := .single 0
    isUninhabited := false }

def witProjDropLayouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries := [u8PairLayout] }

def witProjDropBody : CapturedMir where
  defPath := "crate::proj_drop"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl, u8PairDecl]
  basicBlocks :=
    [ { statements := []
        terminator := mkTerm (.drop ⟨1, [.field 0 u8Ty]⟩ 1 .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm .return_
        isCleanup := false } ]
  fnAbi := fnAbiU8
  layouts := witProjDropLayouts
  allocations := []

def mkWitProjDropMiriFrame
    (bbIdx : Nat)
    (ls1 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody witProjDropBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy u8Ty witProjDropLayouts) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[⟨.live (.immediate .uninit), none⟩, ls1]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨bbIdx, 0⟩ }

def mkWitProjDropAnneal (slot1 : LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, slot1] }
    memory := { nextProtector := 1 } }

def mkWitProjDropMiri (ls1 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    AnnealStepState :=
  { stack := ⟨#[mkWitProjDropMiriFrame 0 ls1]⟩
    machine := AnnealMachine.empty }

/-- **Witness (m)** on `Drop(_1.0)` in `witProjDropBody`, where `_1 : (u8, u8)` has
the realistic `ScalarPair` layout `u8PairLayout`:
1. `step_terminator_drop_projected_simulation` applies (initial-state
   satisfiability of its premises) and both machines fault with UB when `_1`
   is `.dead`;
2. when `_1` holds `(1_u8, 1_u8)` (`.aggregate 0 [.scalar sc1, .scalar sc1]` ↔
   `.scalarPair`), both machines advance to `(bb1, 0)` without deinitializing `_1`;
3. when `_1` is `.uninit`, `step_terminator_drop_projected_uninit_divergence`
   certifies the residual Stage-1 divergence: Stage-1 faults (`.fail .ub`)
   while `lean-miri` (canonical no-glue `Drop`) jumps to `(bb1, 0)`;
4. `step_terminator_drop_canonical_no_glue_step_divergence` on unprojected
   `Drop(_1)` in `witCallerBody` (`witCallerAtDropLiveAnneal` / `witCallerAtDropLiveMiri`):
   Stage-1 `stepMirFn` deinitializes `_1` to `.uninit`, whereas canonical
   `lean-miri`'s no-glue `Drop` step (`ControlFlow.goToBlock`) leaves `_1`
   initialized to `1_u8`. -/
theorem wit_lm4_1_drop_projected_and_canonical_divergence :
    let pairVal : Value := .aggregate 0 [.scalar sc1, .scalar sc1]
    let pairLs : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
      ⟨.live (.immediate (.scalarPair (.fromScalarInt msc1) (.fromScalarInt msc1))), none⟩
    StepRelMultiFrame witProjDropBody (mkWitProjDropMiri ⟨.dead, none⟩)
      (stepMirFn witProjDropBody (mkWitProjDropAnneal .dead))
      (Miri.Interpreter.Step.step (annealStepHooksLM4_1 witProjDropBody) ()
        (mkWitProjDropMiri ⟨.dead, none⟩)) ∧
    stepMirFn witProjDropBody (mkWitProjDropAnneal .dead) = .fail .ub ∧
    StepRelMultiFrame witProjDropBody (mkWitProjDropMiri pairLs)
      (stepMirFn witProjDropBody (mkWitProjDropAnneal (.init pairVal)))
      (Miri.Interpreter.Step.step (annealStepHooksLM4_1 witProjDropBody) ()
        (mkWitProjDropMiri pairLs)) ∧
    (∃ s',
      stepMirFn witProjDropBody (mkWitProjDropAnneal (.init pairVal)) = .step s' ∧
      s'.frame.blockIdx = 1 ∧
      get? s'.frame.locals 1 = some (.init pairVal)) ∧
    stepMirFn witProjDropBody (mkWitProjDropAnneal .uninit) = .fail .ub ∧
    (∃ m' tf',
      Miri.Interpreter.Step.step (annealStepHooksLM4_1 witProjDropBody) ()
        (mkWitProjDropMiri ⟨.live (.immediate .uninit), none⟩) = (m', .ok true) ∧
      m'.stack.frames.back? = some tf' ∧
      tf'.location = .mir ⟨1, 0⟩ ∧
      ∃ lay, tf'.locals[1]? = some ⟨.live (.immediate .uninit), lay⟩) ∧
    (∃ s',
      stepMirFn witCallerBody witCallerAtDropLiveAnneal = .step s' ∧
      get? s'.frame.locals 1 = some .uninit) ∧
    (∃ m_canon gf msc lay,
      Miri.Interpreter.Step.step
        { annealStepHooksLM4_1
            (activeMirBody witCallerBody witCallerAtDropLiveAnneal)
            witCallerAtDropLiveAnneal.memory.callees
            (annealPoppedFrameState witCallerAtDropLiveAnneal) with
          terminator := fun choice term state =>
            Miri.Interpreter.ControlFlow.evalTerminator
              { annealTerminatorHooksLM4_1
                  (activeMirBody witCallerBody witCallerAtDropLiveAnneal)
                  witCallerAtDropLiveAnneal.memory.callees
                  (annealPoppedFrameState witCallerAtDropLiveAnneal) with
                drop := fun _ _ tgt _ st => Miri.Interpreter.ControlFlow.goToBlock tgt st }
              choice term state }
        () witCallerAtDropLiveMiri = (m_canon, .ok true) ∧
      m_canon.stack.frames.back? = some gf ∧
      gf.location = .mir ⟨1, 0⟩ ∧
      gf.locals[1]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc))), lay⟩) := by
  have mk_proj_state :
      ∀ (slot1 : LocalSlot) (ls1 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
        (∀ mp, ls1.value ≠ .live (.indirect mp)) →
        LocalRel AnnealMachine.empty u8PairDecl witProjDropLayouts slot1 ls1 →
        MultiFrameStateRel witProjDropBody (mkWitProjDropAnneal slot1) (mkWitProjDropMiri ls1) := by
    intro slot1 ls1 hno_ind hloc1
    have hfr :
        FrameRel witProjDropBody AnnealMachine.empty
          (mkWitProjDropAnneal slot1).frame (mkWitProjDropMiriFrame 0 ls1) := by
      refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
      rcases i with _ | ⟨_ | i⟩
      · injection hdecl with hd; subst hd
        injection hslot with hs; subst hs
        injection hmls with hm; subst hm
        exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
      · injection hdecl with hd; subst hd
        injection hslot with hs; subst hs
        injection hmls with hm; subst hm
        exact hloc1
      · cases hdecl
    have hst0 : StateRel witProjDropBody (mkWitProjDropAnneal slot1) (mkWitProjDropMiri ls1) :=
      .mk _ rfl rfl ⟨translateTy u8Ty witProjDropLayouts, rfl⟩ hfr rfl rfl rfl rfl rfl
        (by intro i j mp₁ mp₂ lay₁ lay₂ _ hi _
            dsimp only [mkWitProjDropMiriFrame] at hi
            rcases i with _ | ⟨_ | i⟩
            · cases hi
            · injection hi with h_eq
              exact False.elim (hno_ind mp₁ (congrArg Miri.Interpreter.LocalState.value h_eq))
            · cases hi)
    exact (StateRel.iff_multiFrameStateRel_depth1 rfl rfl rfl rfl rfl (Nat.zero_lt_succ 0)).mp hst0
  have hst_dead :=
    mk_proj_state .dead ⟨.dead, none⟩ (fun _ h => nomatch h) (.dead none (fun _ h => nomatch h))
  have hst_uninit :=
    mk_proj_state .uninit ⟨.live (.immediate .uninit), none⟩ (fun _ h => nomatch h)
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  have hpair_rel :
      ImmediateRel u8PairTy witProjDropLayouts
        (.aggregate 0 [.scalar sc1, .scalar sc1])
        (.scalarPair (.fromScalarInt msc1) (.fromScalarInt msc1)) :=
    .scalarPair sc1 sc1 msc1 msc1 (ScalarRel.of_boolToScalar true) (ScalarRel.of_boolToScalar true)
      (Or.inl ⟨[.uint .u8, .uint .u8], rfl⟩)
      (fun _ h => by cases h)
  have hst_live :=
    mk_proj_state (.init (.aggregate 0 [.scalar sc1, .scalar sc1]))
      ⟨.live (.immediate (.scalarPair (.fromScalarInt msc1) (.fromScalarInt msc1))), none⟩
      (fun _ h => nomatch h)
      (.immediate _ _ none (fun _ h => nomatch h) (Or.inr ⟨_, rfl, hpair_rel⟩))
  have himm_of :
      ∀ (ls1 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
        (∀ mp, ls1.value ≠ .live (.indirect mp)) →
        ∀ tf, (mkWitProjDropMiri ls1).stack.frames.back? = some tf → IsImmediateFrameLocal tf 1 := by
    intro ls1 hno_ind tf htf mls hmls mp hmp
    injection htf with h; subst h
    injection hmls with hm; subst hm
    exact hno_ind mp hmp
  have hsim_dead :=
    step_terminator_drop_projected_simulation hst_dead (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm (.drop ⟨1, [.field 0 u8Ty]⟩ 1 .continue_), isCleanup := false })
      (decl := u8PairDecl)
      rfl rfl rfl rfl rfl (Or.inl rfl)
      (himm_of _ (fun _ h => nomatch h))
      (Or.inl rfl)
  have hsim_live :=
    step_terminator_drop_projected_simulation hst_live (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm (.drop ⟨1, [.field 0 u8Ty]⟩ 1 .continue_), isCleanup := false })
      (decl := u8PairDecl)
      rfl rfl rfl rfl rfl (Or.inl rfl)
      (himm_of _ (fun _ h => nomatch h))
      (Or.inr ⟨sc1, sc1, rfl⟩)
  have hdiv_uninit :=
    step_terminator_drop_projected_uninit_divergence hst_uninit (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm (.drop ⟨1, [.field 0 u8Ty]⟩ 1 .continue_), isCleanup := false })
      (decl := u8PairDecl)
      rfl rfl rfl rfl rfl (Or.inl rfl)
      (himm_of _ (fun _ h => nomatch h))
      rfl
  have hrel0 :
      LocalRel AnnealMachine.empty u8Decl emptyLayoutTable .uninit
        ⟨.live (.immediate .uninit), none⟩ :=
    .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  have hrel1 :
      LocalRel AnnealMachine.empty u8Decl emptyLayoutTable (.init (.scalar sc1))
        ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩ :=
    .immediate (.init (.scalar sc1)) (.scalar (.fromScalarInt msc1)) none
      (fun _ h => nomatch h) (Or.inr ⟨.scalar sc1, rfl, val1_immRel⟩)
  have hfr_c := witCallerFrame_rel 2 _ _ _ _ hrel0 hrel1
  have hst_c0 : StateRel witCallerBody witCallerAtDropLiveAnneal witCallerAtDropLiveMiri :=
    .mk _ rfl rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr_c rfl rfl rfl rfl rfl
      (by intro i j mp₁ mp₂ lay₁ lay₂ _ hi _; rcases i with _ | ⟨_ | i⟩ <;> cases hi)
  have hst_c :=
    (StateRel.iff_multiFrameStateRel_depth1 rfl rfl rfl rfl rfl (by decide)).mp hst_c0
  have hdiv :=
    step_terminator_drop_canonical_no_glue_step_divergence hst_c (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm (.drop ⟨1, .nil⟩ 1 .continue_), isCleanup := false })
      (decl := u8Decl) (sc := sc1)
      rfl rfl rfl rfl rfl rfl
      (by intro tf htf mls hmls mp hmp
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hmp)
  exact ⟨hsim_dead, rfl, hsim_live, ⟨_, rfl, rfl, rfl⟩, hdiv_uninit.1, hdiv_uninit.2,
    hdiv.2.1, hdiv.2.2⟩

/-! ## (n) `Terminator.UnwindResume` Cleanup Catch & `.unreachable` Unwind ABI UB Witness -/

def witUnwindCalleeBody : CapturedMir where
  defPath := "crate::unwind_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl]
  basicBlocks :=
    [{ statements := []
       terminator := mkTerm .unwindResume
       isCleanup := true }]
  fnAbi := { fnAbiU8 with canUnwind := true }
  layouts := emptyLayoutTable
  allocations := []

def mkWitUnwindSavedCaller (unwindAct : MirAst.UnwindAction) : SavedCallerFrame :=
  { witSavedCallerFrame .uninit .uninit [] with returnUnwind := unwindAct }

def mkWitUnwindCalleeMiriFrame (unwindAct : Miri.MIR.UnwindAction) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody witUnwindCalleeBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .goto (some 1) unwindAct
    returnPlace :=
      .frameLocal 0 1 none (translateTy u8Ty emptyLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[⟨.live (.immediate .uninit), none⟩]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def witProtectedCalleeBorrow : BorrowEntry :=
  { tag := 10
    targetLocal := 1
    targetProjection := []
    perm := .reservedFrz true
    protector := some 1
    parentTag := none }

def mkWitUnwindAnneal (unwindAct : MirAst.UnwindAction) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
    memory :=
      { callStack := [mkWitUnwindSavedCaller unwindAct]
        callees := [witUnwindCalleeBody]
        activeCallee := some witUnwindCalleeBody
        borrows := [witProtectedCalleeBorrow]
        activeProtectors := [1]
        nextProtector := 2 } }

def mkWitUnwindMiri (unwindAct : Miri.MIR.UnwindAction) : AnnealStepState :=
  { stack :=
      ⟨#[mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩,
         mkWitUnwindCalleeMiriFrame unwindAct]⟩
    machine := AnnealMachine.empty }

/-- **Witness (n)**: Executing `TerminatorKind.unwindResume` from a cleanup basic
block (`isCleanup = true`) of `witUnwindCalleeBody` even when `_0` is `.uninit`
on non-ZST `u8`:
1. When `cf.returnUnwind = .cleanup 1`, `step_terminator_unwindResume_callee_simulation`
   pops the callee frame, releases callee protector `1` (`s'.memory.activeProtectors = []`),
   leaves caller `_1 = .uninit`, and resumes `witCallerBody` at cleanup target
   `(bb1, 0)` in lockstep (`StepRelMultiFrame`);
2. When `cf.returnUnwind = .unreachable`, both Stage-1 `stepMirFn` and `lean-miri`
   fault with undefined behavior (`StepRelMultiFrame.ub`). -/
theorem wit_lm4_1_unwindResume_cleanup_and_unreachable_ub_simulation :
    StepRelMultiFrame witCallerBody (mkWitUnwindMiri (.Cleanup 1))
      (stepMirFn witCallerBody (mkWitUnwindAnneal (.cleanup 1)))
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody (mkWitUnwindAnneal (.cleanup 1)))
          (mkWitUnwindAnneal (.cleanup 1)).memory.callees
          (annealPoppedFrameState (mkWitUnwindAnneal (.cleanup 1))))
        () (mkWitUnwindMiri (.Cleanup 1))) ∧
    (∃ s',
      stepMirFn witCallerBody (mkWitUnwindAnneal (.cleanup 1)) = .step s' ∧
      s'.frame.blockIdx = 1 ∧
      s'.memory.activeProtectors = [] ∧
      get? s'.frame.locals 1 = some .uninit) ∧
    StepRelMultiFrame witCallerBody (mkWitUnwindMiri .Unreachable)
      (stepMirFn witCallerBody (mkWitUnwindAnneal .unreachable))
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody (mkWitUnwindAnneal .unreachable))
          (mkWitUnwindAnneal .unreachable).memory.callees
          (annealPoppedFrameState (mkWitUnwindAnneal .unreachable)))
        () (mkWitUnwindMiri .Unreachable)) ∧
    stepMirFn witCallerBody (mkWitUnwindAnneal .unreachable) = .fail .ub ∧
    ∃ msg,
      (Miri.Interpreter.Step.step
        (annealStepHooksLM4_1
          (activeMirBody witCallerBody (mkWitUnwindAnneal .unreachable))
          (mkWitUnwindAnneal .unreachable).memory.callees
          (annealPoppedFrameState (mkWitUnwindAnneal .unreachable)))
        () (mkWitUnwindMiri .Unreachable)).2 = .error (.undefinedBehavior msg) := by
  have mk_unwind_state :
      ∀ (ua : MirAst.UnwindAction),
        MultiFrameStateRel witCallerBody (mkWitUnwindAnneal ua)
          (mkWitUnwindMiri (translateUnwindAction ua)) := by
    intro ua
    have hfr_caller :=
      witCallerFrame_rel (mach := AnnealMachine.empty) 0 .uninit .uninit
        ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩
        (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
        (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
    have hfr_callee :
        FrameRel witUnwindCalleeBody AnnealMachine.empty
          { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
          (mkWitUnwindCalleeMiriFrame (translateUnwindAction ua)) := by
      refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
      rcases i with _ | i
      · injection hdecl with hd; subst hd
        injection hslot with hs; subst hs
        injection hmls with hm; subst hm
        exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
      · cases hdecl
    have hlinks_root :
        CallerStackLinksRel witCallerBody AnnealMachine.empty witCallerBody
          { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
          [] []
          [mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩] :=
      .root _ _ [] rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr_caller
    have hdest :
        CallerDestinationRel AnnealMachine.empty 0 (mkWitUnwindSavedCaller ua)
          (mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
          (mkWitUnwindCalleeMiriFrame (translateUnwindAction ua)).returnPlace :=
      .immediate 1 u8Decl .uninit .uninit none rfl rfl rfl (fun h => nomatch h) rfl
    have hlinks :
        CallerStackLinksRel witCallerBody AnnealMachine.empty
          (activeMirBody witCallerBody (mkWitUnwindAnneal ua))
          (mkWitUnwindAnneal ua).frame
          (mkWitUnwindAnneal ua).memory.callStack
          (mkWitUnwindAnneal ua).memory.activeProtectors
          (mkWitUnwindMiri (translateUnwindAction ua)).stack.frames.toList.reverse :=
      .cons witUnwindCalleeBody
        (mkWitUnwindAnneal ua).frame
        (mkWitUnwindSavedCaller ua) [] [1] []
        _ _ []
        rfl hdest hfr_callee (fun _ _ _ _ _ h _ _ _ => nomatch h) rfl (by intro _ _; rfl) hlinks_root
    have hdisj : MultiFrameAllocDisjoint (mkWitUnwindMiri (translateUnwindAction ua)).stack.frames := by
      refine ⟨?_, ?_⟩
      · intro mf hmf i j mp₁ mp₂ lay₁ lay₂ _ hi _
        rcases List.mem_cons.mp hmf with rfl | hmf1
        · dsimp only [mkWitCallerMiriFrame] at hi
          rcases i with _ | ⟨_ | i⟩ <;> cases hi
        · rcases List.mem_singleton.mp hmf1 with rfl
          dsimp only [mkWitUnwindCalleeMiriFrame] at hi
          rcases i with _ | i <;> cases hi
      · intro f₁ f₂ i j mf₁ mf₂ mp₁ mp₂ lay₁ lay₂ _ hf₁ _ hi _
        rcases f₁ with _ | ⟨_ | f₁⟩
        · injection hf₁ with hmf₁; subst hmf₁
          rcases i with _ | ⟨_ | i⟩ <;> cases hi
        · injection hf₁ with hmf₁; subst hmf₁
          rcases i with _ | i <;> cases hi
        · cases hf₁
    exact .mk _ rfl (fun hnil => nomatch hnil) (fun _ => rfl)
      hlinks.toFrameStackRel hlinks hdisj
      ⟨by dsimp [mkWitUnwindAnneal]; decide,
       by dsimp [mkWitUnwindAnneal]; decide,
       rfl, rfl, rfl⟩
      (by dsimp [mkWitUnwindAnneal]; decide)
      (Nat.zero_lt_succ 1)
      (by intro cid hcid
          dsimp [mkWitUnwindAnneal] at hcid ⊢
          rcases List.mem_singleton.mp hcid with rfl
          decide)
      (by intro e he cid hprot
          dsimp [mkWitUnwindAnneal] at he ⊢
          rcases List.mem_singleton.mp he with rfl
          injection hprot with h; subst h; decide)
      (BorrowTrackerStackRel.of_none _ _ _)
  have hsim_clean :=
    step_terminator_unwindResume_callee_simulation (mk_unwind_state (.cleanup 1)) rfl
      (by intro tf htf; injection htf with h; subst h; rfl)
      (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm .unwindResume, isCleanup := true })
      (decl0 := u8Decl)
      rfl rfl rfl rfl rfl rfl (fun h => nomatch h) (Or.inr ⟨1, rfl⟩)
  have hsim_unreach :=
    step_terminator_unwindResume_callee_simulation (mk_unwind_state .unreachable) rfl
      (by intro tf htf; injection htf with h; subst h; rfl)
      (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm .unwindResume, isCleanup := true })
      (decl0 := u8Decl)
      rfl rfl rfl rfl rfl rfl (fun h => nomatch h) (Or.inl rfl)
  exact ⟨hsim_clean, ⟨_, rfl, rfl, rfl, rfl⟩, hsim_unreach, rfl, (hsim_unreach.ub_iff).mp rfl⟩

def witUnwindRootAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
    memory := { nextProtector := 1 } }

def witUnwindRootMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { mkWitUnwindCalleeMiriFrame .Continue with
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy u8Ty emptyLayoutTable) (.ofAllocationToken 0) }

def witUnwindRootMiri : AnnealStepState :=
  { stack := ⟨#[witUnwindRootMiriFrame]⟩
    machine := AnnealMachine.empty }

/-- **Witness (n.2)**: Concrete root-frame `TerminatorKind.unwindResume` witness
for `step_terminator_unwindResume_root_panic_vs_ub_divergence`: in the root frame
(`callStack = []`), Stage-1 `stepMirFn` halts with `.retOutcome .panic`, whereas
`lean-miri` faults with `.error (.undefinedBehavior "unwinding past the topmost stack frame")`. -/
theorem wit_lm4_1_unwindResume_root_panic_vs_ub_divergence :
    stepMirFn witUnwindCalleeBody witUnwindRootAnneal = .retOutcome .panic ∧
    (Miri.Interpreter.Step.step
      (annealStepHooksLM4_1
        (activeMirBody witUnwindCalleeBody witUnwindRootAnneal)
        witUnwindRootAnneal.memory.callees
        (annealPoppedFrameState witUnwindRootAnneal))
      () witUnwindRootMiri).2 =
      .error (.undefinedBehavior "unwinding past the topmost stack frame") := by
  have hfr_root :
      FrameRel witUnwindCalleeBody AnnealMachine.empty
        witUnwindRootAnneal.frame witUnwindRootMiriFrame := by
    refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
    rcases i with _ | i
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · cases hdecl
  have hlinks :
      CallerStackLinksRel witUnwindCalleeBody AnnealMachine.empty
        witUnwindCalleeBody witUnwindRootAnneal.frame [] [] [witUnwindRootMiriFrame] :=
    .root _ _ [] rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr_root
  have hdisj : MultiFrameAllocDisjoint witUnwindRootMiri.stack.frames := by
    refine ⟨?_, ?_⟩
    · intro mf hmf i _ mp₁ _ _ _ _ hi _
      rcases List.mem_singleton.mp hmf with rfl
      rcases i with _ | i <;> cases hi
    · intro f₁ f₂ _ _ _ _ _ _ _ _ hne hf₁ hf₂ _ _
      rcases f₁ with _ | f₁ <;> rcases f₂ with _ | f₂
      · exact False.elim (hne rfl)
      · cases hf₂
      · cases hf₁
      · cases hf₁
  have hstate : MultiFrameStateRel witUnwindCalleeBody witUnwindRootAnneal witUnwindRootMiri :=
    .mk _ rfl (fun _ => Or.inl rfl) (fun h => False.elim (h rfl))
      hlinks.toFrameStackRel hlinks hdisj
      ⟨by decide, by decide, rfl, rfl, rfl⟩
      (ActiveProtectorsValid.nil _) (by decide)
      (fun _ h => nomatch h) (fun _ h => nomatch h)
      (BorrowTrackerStackRel.of_none _ _ _)
  exact step_terminator_unwindResume_root_panic_vs_ub_divergence hstate rfl
    (fun _ h => nomatch h)
    (bb := { statements := [], terminator := mkTerm .unwindResume, isCleanup := true })
    rfl rfl rfl rfl rfl

/-! ## (o) 3-Frame `k = 2` `.continue_` Unwinding + `UnwindTerminate` + `Assert` + Diverging Panic Witness -/

def witMidCallerBody : CapturedMir :=
  { witCallerBody with
    defPath := "crate::mid_caller"
    fnAbi := { fnAbiU8 with canUnwind := true } }

def witMidSavedCaller : SavedCallerFrame :=
  { callerBody := witMidCallerBody
    frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
    destination := ⟨1, .nil⟩
    returnTarget := 1
    callerProtector := none
    calleeProtectors := [1]
    returnUnwind := .continue_ }

def witMidMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody witMidCallerBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .goto (some 1) (.Cleanup 1)
    returnPlace :=
      .frameLocal 0 1 none (translateTy u8Ty emptyLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate .uninit), none⟩]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def witTopUnwind3MiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { mkWitUnwindCalleeMiriFrame .Continue with
    returnPlace :=
      .frameLocal 1 1 none (translateTy u8Ty emptyLayoutTable) (.ofAllocationToken 0) }

def witUnwind3Anneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
    memory :=
      { callStack := [witMidSavedCaller, mkWitUnwindSavedCaller (.cleanup 1)]
        callees := [witMidCallerBody, witUnwindCalleeBody]
        activeCallee := some witUnwindCalleeBody
        borrows := []
        activeProtectors := [2, 1]
        nextProtector := 3 } }

def witUnwind3Miri : AnnealStepState :=
  { stack :=
      ⟨#[mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩,
         witMidMiriFrame,
         witTopUnwind3MiriFrame]⟩
    machine := AnnealMachine.empty }

def boolTy : Ty := { kind := .bool, layoutIdx := 0 }
def boolDecl : LocalDecl := { mutability := .mut, ty := boolTy, debugName := none }
def panicFnTy : Ty := { kind := .fnDef "core::panicking::panic" [], layoutIdx := 0 }
def panicFuncOp : MirAst.Operand := .constant { ty := panicFnTy, val := .zeroSized }

def witAssertTermPanicBody : CapturedMir where
  defPath := "crate::assert_term_panic"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl, boolDecl]
  basicBlocks :=
    [ { statements := [], terminator := mkTerm .unwindTerminate, isCleanup := true }
    , { statements := []
        terminator := mkTerm (.assert (.copy ⟨1, .nil⟩) true 2 (.cleanup 0))
        isCleanup := false }
    , { statements := []
        terminator := mkTerm (.call panicFuncOp [] ⟨0, .nil⟩ none (.cleanup 0))
        isCleanup := false } ]
  fnAbi := { fnAbiU8 with canUnwind := true }
  layouts := emptyLayoutTable
  allocations := []

def mkWitAssertTermPanicAnneal (bbIdx : Nat) (slot1 : LocalSlot) : MachineState :=
  { frame := { blockIdx := bbIdx, stmtIdx := 0, locals := [.uninit, slot1] }
    memory := { nextProtector := 1 } }

def mkWitAssertTermPanicMiriFrame
    (bbIdx : Nat)
    (ls1 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody witAssertTermPanicBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy u8Ty emptyLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[⟨.live (.immediate .uninit), none⟩, ls1]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨bbIdx, 0⟩ }

def mkWitAssertTermPanicMiri
    (bbIdx : Nat)
    (ls1 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    AnnealStepState :=
  { stack := ⟨#[mkWitAssertTermPanicMiriFrame bbIdx ls1]⟩
    machine := AnnealMachine.empty }

theorem witAssertTermPanic_rel
    (bbIdx : Nat) (slot1 : LocalSlot)
    (ls1 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
    (h1 : LocalRel AnnealMachine.empty boolDecl emptyLayoutTable slot1 ls1)
    (hno1 : ∀ mp, ls1.value ≠ .live (.indirect mp)) :
    MultiFrameStateRel witAssertTermPanicBody
      (mkWitAssertTermPanicAnneal bbIdx slot1)
      (mkWitAssertTermPanicMiri bbIdx ls1) := by
  have hfr :
      FrameRel witAssertTermPanicBody AnnealMachine.empty
        (mkWitAssertTermPanicAnneal bbIdx slot1).frame
        (mkWitAssertTermPanicMiriFrame bbIdx ls1) := by
    refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
    rcases i with _ | ⟨_ | i⟩
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact h1
    · cases hdecl
  have hlinks :
      CallerStackLinksRel witAssertTermPanicBody AnnealMachine.empty
        witAssertTermPanicBody (mkWitAssertTermPanicAnneal bbIdx slot1).frame [] []
        [mkWitAssertTermPanicMiriFrame bbIdx ls1] :=
    .root _ _ [] rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr
  have hdisj : MultiFrameAllocDisjoint (mkWitAssertTermPanicMiri bbIdx ls1).stack.frames := by
    refine ⟨?_, ?_⟩
    · intro mf hmf i _ mp₁ _ _ _ _ hi _
      rcases List.mem_singleton.mp hmf with rfl
      rcases i with _ | ⟨_ | i⟩
      · cases hi
      · injection hi with h; exact False.elim (hno1 mp₁ (congrArg Miri.Interpreter.LocalState.value h))
      · cases hi
    · intro f₁ f₂ _ _ _ _ _ _ _ _ hne hf₁ hf₂ _ _
      rcases f₁ with _ | f₁ <;> rcases f₂ with _ | f₂
      · exact False.elim (hne rfl)
      · cases hf₂
      · cases hf₁
      · cases hf₁
  exact .mk _ rfl (fun _ => Or.inl rfl) (fun h => False.elim (h rfl))
    hlinks.toFrameStackRel hlinks hdisj
    ⟨by dsimp only [mkWitAssertTermPanicAnneal]; decide,
     by dsimp only [mkWitAssertTermPanicAnneal]; decide,
     rfl, rfl, rfl⟩
    (ActiveProtectorsValid.nil _) (Nat.zero_lt_succ 0)
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (BorrowTrackerStackRel.of_none _ _ _)

/-- **Witness (o)**:
1. `step_terminator_unwindResume_multiFrame_simulation` at depth 3 (`k = 2`):
   `witUnwindCalleeBody` unwinds through `witMidCallerBody` (`returnUnwind = .continue_`)
   into `witCallerBody` (`returnUnwind = .cleanup 1`), releasing stacked protectors
   `[2, 1] -> []` in 1 Stage-1 step and `k = 2` `MiriUnwindSteps` to a
   `MultiFrameStateRel`-related state at `(bb1, 0)`;
2. `step_terminator_unwindTerminate_abort_vs_unsupported` (`bb0`): Stage-1 halts
   with `.retOutcome .abort` and Miri returns `.error (.unsupported "unwindTerminate")`;
3. `step_terminator_assert_local_simulation` (`bb1`): `_1 = true` steps to `(bb2, 0)`
   in lockstep (`StepRelMultiFrame`), while `_1 = false` unwinds to cleanup `(bb0, 0)`
   in Stage-1 vs. `.error (.unsupported "assert panic without linked panic lang item")`
   in Miri;
4. `step_terminator_call_diverging_panic_vs_unlinked` (`bb2`): unlinked
   `"core::panicking::panic"` unwinds to cleanup `(bb0, 0)` in Stage-1 vs.
   `.error (.unsupported "diverging call to unlinked non-unreachable callee")` in Miri. -/
theorem wit_lm4_1_multiFrame_continue_unwind_and_assert_terminate :
    (∃ s_caught m',
      stepMirFn witCallerBody witUnwind3Anneal = .step s_caught ∧
      s_caught.memory.callStack = [] ∧
      s_caught.frame.blockIdx = 1 ∧
      s_caught.memory.activeProtectors = [] ∧
      MiriUnwindSteps witCallerBody 2 witUnwind3Anneal witUnwind3Miri (m', .ok true) ∧
      MultiFrameStateRel witCallerBody s_caught m') ∧
    (stepMirFn witAssertTermPanicBody (mkWitAssertTermPanicAnneal 0 .uninit) = .retOutcome .abort ∧
      Miri.Interpreter.Step.step
        (annealStepHooksForState witAssertTermPanicBody (mkWitAssertTermPanicAnneal 0 .uninit))
        () (mkWitAssertTermPanicMiri 0 ⟨.live (.immediate .uninit), none⟩) =
        (mkWitAssertTermPanicMiri 0 ⟨.live (.immediate .uninit), none⟩,
         .error (.unsupported "unwindTerminate"))) ∧
    StepRelMultiFrame witAssertTermPanicBody
      (mkWitAssertTermPanicMiri 1 ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩)
      (stepMirFn witAssertTermPanicBody (mkWitAssertTermPanicAnneal 1 (.init (.scalar sc1))))
      (Miri.Interpreter.Step.step
        (annealStepHooksForState witAssertTermPanicBody
          (mkWitAssertTermPanicAnneal 1 (.init (.scalar sc1))))
        () (mkWitAssertTermPanicMiri 1 ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩)) ∧
    (stepMirFn witAssertTermPanicBody
        (mkWitAssertTermPanicAnneal 1 (.init (.scalar (boolToScalar false)))) =
      .step { frame := { blockIdx := 0, stmtIdx := 0,
                         locals := [.uninit, .init (.scalar (boolToScalar false))] },
              memory := { nextProtector := 1 } } ∧
      (Miri.Interpreter.Step.step
        (annealStepHooksForState witAssertTermPanicBody
          (mkWitAssertTermPanicAnneal 1 (.init (.scalar (boolToScalar false)))))
        () (mkWitAssertTermPanicMiri 1
          ⟨.live (.immediate (.scalar (.fromScalarInt (.ofBool false)))), none⟩)).2 =
      .error (.unsupported "assert panic without linked panic lang item")) ∧
    (stepMirFn witAssertTermPanicBody (mkWitAssertTermPanicAnneal 2 .uninit) =
      .step { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] },
              memory := { nextProtector := 1 } } ∧
      (Miri.Interpreter.Step.step
        (annealStepHooksForState witAssertTermPanicBody (mkWitAssertTermPanicAnneal 2 .uninit))
        () (mkWitAssertTermPanicMiri 2 ⟨.live (.immediate .uninit), none⟩)).2 =
      .error (.unsupported "diverging call to unlinked non-unreachable callee")) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hfr_root :=
      witCallerFrame_rel (mach := AnnealMachine.empty) 0 .uninit .uninit
        ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩
        (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
        (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
    have hfr_mid :
        FrameRel witMidCallerBody AnnealMachine.empty
          witMidSavedCaller.frame witMidMiriFrame := by
      refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
      rcases i with _ | ⟨_ | i⟩
      · injection hdecl with hd; subst hd
        injection hslot with hs; subst hs
        injection hmls with hm; subst hm
        exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
      · injection hdecl with hd; subst hd
        injection hslot with hs; subst hs
        injection hmls with hm; subst hm
        exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
      · cases hdecl
    have hfr_top :
        FrameRel witUnwindCalleeBody AnnealMachine.empty
          witUnwind3Anneal.frame witTopUnwind3MiriFrame := by
      refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
      rcases i with _ | i
      · injection hdecl with hd; subst hd
        injection hslot with hs; subst hs
        injection hmls with hm; subst hm
        exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
      · cases hdecl
    have hlinks0 :
        CallerStackLinksRel witCallerBody AnnealMachine.empty witCallerBody
          { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
          [] []
          [mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩] :=
      .root _ _ [] rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr_root
    have hdest1 :
        CallerDestinationRel AnnealMachine.empty 0 (mkWitUnwindSavedCaller (.cleanup 1))
          (mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
          witMidMiriFrame.returnPlace :=
      .immediate 1 u8Decl .uninit .uninit none rfl rfl rfl (fun h => nomatch h) rfl
    have hlinks1 :
        CallerStackLinksRel witCallerBody AnnealMachine.empty witMidCallerBody
          witMidSavedCaller.frame [mkWitUnwindSavedCaller (.cleanup 1)] [1]
          [witMidMiriFrame,
           mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩] :=
      .cons witMidCallerBody witMidSavedCaller.frame (mkWitUnwindSavedCaller (.cleanup 1))
        [] [1] [] _ _ []
        rfl hdest1 hfr_mid (fun _ _ _ _ _ h _ _ _ => nomatch h) rfl (by intro _ _; rfl) hlinks0
    have hdest2 :
        CallerDestinationRel AnnealMachine.empty 1 witMidSavedCaller
          witMidMiriFrame witTopUnwind3MiriFrame.returnPlace :=
      .immediate 1 u8Decl .uninit .uninit none rfl rfl rfl (fun h => nomatch h) rfl
    have hlinks2 :
        CallerStackLinksRel witCallerBody AnnealMachine.empty
          (activeMirBody witCallerBody witUnwind3Anneal)
          witUnwind3Anneal.frame witUnwind3Anneal.memory.callStack
          witUnwind3Anneal.memory.activeProtectors
          witUnwind3Miri.stack.frames.toList.reverse :=
      .cons witUnwindCalleeBody witUnwind3Anneal.frame witMidSavedCaller
        [mkWitUnwindSavedCaller (.cleanup 1)] [2] [1] _ _
        [mkWitCallerMiriFrame 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩]
        rfl hdest2 hfr_top (fun _ _ _ _ _ h _ _ _ => nomatch h) rfl
        (by intro cid hcid; rcases List.mem_singleton.mp hcid with rfl; rfl) hlinks1
    have hdisj : MultiFrameAllocDisjoint witUnwind3Miri.stack.frames := by
      refine ⟨?_, ?_⟩
      · intro mf hmf i _ mp₁ _ _ _ _ hi _
        rcases List.mem_cons.mp hmf with rfl | hmf1
        · rcases i with _ | ⟨_ | i⟩ <;> cases hi
        · rcases List.mem_cons.mp hmf1 with rfl | hmf2
          · rcases i with _ | ⟨_ | i⟩ <;> cases hi
          · rcases List.mem_singleton.mp hmf2 with rfl
            rcases i with _ | i <;> cases hi
      · intro f₁ _ i _ _ _ _ _ _ _ _ hf₁ _ hi _
        rcases f₁ with _ | ⟨_ | ⟨_ | f₁⟩⟩
        · injection hf₁ with hmf; subst hmf; rcases i with _ | ⟨_ | i⟩ <;> cases hi
        · injection hf₁ with hmf; subst hmf; rcases i with _ | ⟨_ | i⟩ <;> cases hi
        · injection hf₁ with hmf; subst hmf; rcases i with _ | i <;> cases hi
        · cases hf₁
    have hstate3 : MultiFrameStateRel witCallerBody witUnwind3Anneal witUnwind3Miri :=
      .mk _ rfl (fun hnil => nomatch hnil) (fun _ => rfl)
        hlinks2.toFrameStackRel hlinks2 hdisj
        ⟨by decide, by decide, rfl, rfl, rfl⟩
        (by decide) (by decide)
        (by intro cid hcid
            dsimp [witUnwind3Anneal] at hcid ⊢
            rcases List.mem_cons.mp hcid with rfl | h1
            · decide
            · rcases List.mem_singleton.mp h1 with rfl; decide)
        (fun _ h => nomatch h)
        (BorrowTrackerStackRel.of_none _ _ _)
    have hwf3 : UnwindChainWf witCallerBody witUnwind3Anneal witUnwind3Miri := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro mf hmf
        rcases List.mem_cons.mp hmf with rfl | h1
        · rfl
        · rcases List.mem_cons.mp h1 with rfl | h2
          · rfl
          · rcases List.mem_singleton.mp h2 with rfl; rfl
      · intro _; exact ⟨u8Decl, rfl⟩
      · intro _ h; cases h
      · intro cf hcf
        rcases List.mem_cons.mp hcf with rfl | h1
        · exact ⟨u8Decl, rfl⟩
        · rcases List.mem_singleton.mp h1 with rfl; exact ⟨u8Decl, rfl⟩
      · intro cf hcf h
        rcases List.mem_cons.mp hcf with rfl | h1
        · cases h
        · rcases List.mem_singleton.mp h1 with rfl; cases h
    have hsim3 :=
      (step_terminator_unwindResume_multiFrame_simulation hstate3 hwf3
        (fun _ h => nomatch h)
        (bb := { statements := [], terminator := mkTerm .unwindResume, isCleanup := true })
        rfl rfl rfl rfl rfl).1 _ rfl
    obtain ⟨k, m', hk1, hk2, hprot, hsteps, hrel'⟩ := hsim3
    rcases k with _ | ⟨_ | ⟨_ | k⟩⟩
    · omega
    · dsimp [witUnwind3Anneal, releaseCallProtectors, restoreCallerProtectors, witMidSavedCaller] at hprot
      cases hprot
    · exact ⟨_, m', rfl, rfl, rfl, rfl, hsteps, hrel'⟩
    · dsimp [witUnwind3Anneal] at hk2; omega
  · exact step_terminator_unwindTerminate_abort_vs_unsupported
      (witAssertTermPanic_rel 0 .uninit ⟨.live (.immediate .uninit), none⟩
        (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
        (fun _ h => nomatch h))
      (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm .unwindTerminate, isCleanup := true })
      rfl rfl rfl rfl
  · have hstate_true :=
      witAssertTermPanic_rel 1 (.init (.scalar sc1))
        ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), none⟩
        (.immediate (.init (.scalar sc1)) (.scalar (.fromScalarInt msc1)) none
          (fun _ h => nomatch h)
          (Or.inr ⟨.scalar sc1, rfl,
            .scalar sc1 msc1 (ScalarRel.of_boolToScalar true) rfl
              (fun _ => ⟨rfl, Or.inr rfl⟩) (fun h => nomatch h)⟩))
        (fun _ h => nomatch h)
    exact (step_terminator_assert_local_simulation hstate_true
      (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.assert (.copy ⟨1, .nil⟩) true 2 (.cleanup 0))
               isCleanup := false })
      (condDecl := boolDecl)
      rfl rfl rfl rfl rfl rfl
      (by intro tf htf mls hmls mp hmp
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hmp)).2.1 sc1 rfl rfl
  · have hstate_false :=
      witAssertTermPanic_rel 1 (.init (.scalar (boolToScalar false)))
        ⟨.live (.immediate (.scalar (.fromScalarInt (.ofBool false)))), none⟩
        (.immediate (.init (.scalar (boolToScalar false)))
          (.scalar (.fromScalarInt (.ofBool false))) none
          (fun _ h => nomatch h)
          (Or.inr ⟨.scalar (boolToScalar false), rfl,
            .scalar (boolToScalar false) (.ofBool false) (ScalarRel.of_boolToScalar false) rfl
              (fun _ => ⟨rfl, Or.inl rfl⟩) (fun h => nomatch h)⟩))
        (fun _ h => nomatch h)
    have hfail :=
      (step_terminator_assert_local_simulation hstate_false
        (fun _ h => nomatch h)
        (bb := { statements := []
                 terminator := mkTerm (.assert (.copy ⟨1, .nil⟩) true 2 (.cleanup 0))
                 isCleanup := false })
        (condDecl := boolDecl)
        rfl rfl rfl rfl rfl rfl
        (by intro tf htf mls hmls mp hmp
            injection htf with h; subst h
            injection hmls with hm; subst hm; nomatch hmp)).2.2
        (boolToScalar false) rfl (by decide)
    exact ⟨rfl, hfail.2⟩
  · have hpan :=
      step_terminator_call_diverging_panic_vs_unlinked
        (witAssertTermPanic_rel 2 .uninit ⟨.live (.immediate .uninit), none⟩
          (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
          (fun _ h => nomatch h))
        (fun _ h => nomatch h)
        (bb := { statements := []
                 terminator := mkTerm (.call panicFuncOp [] ⟨0, .nil⟩ none (.cleanup 0))
                 isCleanup := false })
        (defPath := "core::panicking::panic")
        rfl rfl rfl rfl rfl rfl rfl rfl
    exact ⟨hpan.2.1 rfl rfl, hpan.2.2⟩

/-! ## (p) Non-Constant `FnDef` Local & Indirect `FnPtr` Calls + `Safety` Divergence Witness -/

def safeFnPtrTy : Ty := { kind := .fnPtr [] (.uint .u8) .safe .rust, layoutIdx := 0 }
def calleeFnDecl : LocalDecl := { mutability := .mut, ty := calleeFnTy, debugName := none }
def safeFnPtrDecl : LocalDecl := { mutability := .mut, ty := safeFnPtrTy, debugName := none }

def witIndirectCallerBody : CapturedMir where
  defPath := "crate::indirect_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl, u8Decl, calleeFnDecl, safeFnPtrDecl]
  basicBlocks :=
    [ { statements := []
        terminator := mkTerm (.call (.copy ⟨2, .nil⟩) [] ⟨1, .nil⟩ (some 3) .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm (.call (.copy ⟨3, .nil⟩) [] ⟨1, .nil⟩ (some 3) .continue_)
        isCleanup := false }
    , { statements := []
        terminator := mkTerm (.call (.move ⟨3, .nil⟩) [] ⟨1, .nil⟩ (some 3) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]
  fnAbi := fnAbiU8
  layouts := emptyLayoutTable
  allocations := []

def witFnPtrVal : ProvenancePtr := { allocId := 1, offsetBytes := 0 }

def witFnEntrySafe : FnPtrEntry :=
  { allocId := 1
    defPath := "crate::callee"
    typeArgs := []
    fnSig := some (.fnPtr [] (.uint .u8) .safe .rust) }

def witFnEntryUnsafe : FnPtrEntry :=
  { allocId := 1
    defPath := "crate::callee"
    typeArgs := []
    fnSig := some (.fnPtr [] (.uint .u8) .unsafe_ .rust) }

def witFnPtrMachine : AnnealMachine :=
  Witness.witnessMachineOf Witness.witnessUninitAlloc

def witFnPtrMiriScalar : Miri.Memory.Scalar AnnealProv :=
  Miri.Memory.Scalar.fromPointer annealTargetDataLayout
    ⟨Miri.ABI.Size.ofBytes (Witness.witnessBaseAddr + UInt64.ofNat 0),
     .concrete Witness.witnessAllocId Witness.witnessTag⟩

def mkWitIndirectCallerAnneal
    (bbIdx : Nat) (slot2 slot3 : LocalSlot) (fnPtrs : List FnPtrEntry) : MachineState :=
  { frame := { blockIdx := bbIdx, stmtIdx := 0, locals := [.uninit, .uninit, slot2, slot3] }
    memory :=
      { callees := [witCalleeBody]
        fnPtrs := fnPtrs
        nextProtector := 1 } }

def mkWitIndirectCallerMiriFrame
    (bbIdx : Nat)
    (ls2 ls3 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody witIndirectCallerBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy u8Ty emptyLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate .uninit), none⟩, ls2, ls3]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨bbIdx, 0⟩ }

def mkWitIndirectCallerMiri
    (bbIdx : Nat)
    (ls2 ls3 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    AnnealStepState :=
  { stack := ⟨#[mkWitIndirectCallerMiriFrame bbIdx ls2 ls3]⟩
    machine := witFnPtrMachine }

theorem witIndirectCaller_rel
    (bbIdx : Nat) (slot2 slot3 : LocalSlot)
    (ls2 ls3 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
    (fnPtrs : List FnPtrEntry)
    (h2 : LocalRel witFnPtrMachine calleeFnDecl emptyLayoutTable slot2 ls2)
    (h3 : LocalRel witFnPtrMachine safeFnPtrDecl emptyLayoutTable slot3 ls3)
    (hno2 : ∀ mp, ls2.value ≠ .live (.indirect mp))
    (hno3 : ∀ mp, ls3.value ≠ .live (.indirect mp)) :
    MultiFrameStateRel witIndirectCallerBody
      (mkWitIndirectCallerAnneal bbIdx slot2 slot3 fnPtrs)
      (mkWitIndirectCallerMiri bbIdx ls2 ls3) := by
  have hfr :
      FrameRel witIndirectCallerBody witFnPtrMachine
        (mkWitIndirectCallerAnneal bbIdx slot2 slot3 fnPtrs).frame
        (mkWitIndirectCallerMiriFrame bbIdx ls2 ls3) := by
    refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
    rcases i with _ | ⟨_ | ⟨_ | ⟨_ | i⟩⟩⟩
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact h2
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact h3
    · cases hdecl
  have hlinks :
      CallerStackLinksRel witIndirectCallerBody witFnPtrMachine
        witIndirectCallerBody
        (mkWitIndirectCallerAnneal bbIdx slot2 slot3 fnPtrs).frame [] []
        [mkWitIndirectCallerMiriFrame bbIdx ls2 ls3] :=
    .root _ _ [] rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr
  have hdisj : MultiFrameAllocDisjoint (mkWitIndirectCallerMiri bbIdx ls2 ls3).stack.frames := by
    refine ⟨?_, ?_⟩
    · intro mf hmf i _ mp₁ _ _ _ _ hi _
      rcases List.mem_singleton.mp hmf with rfl
      rcases i with _ | ⟨_ | ⟨_ | ⟨_ | i⟩⟩⟩
      · cases hi
      · cases hi
      · injection hi with h; exact False.elim (hno2 mp₁ (congrArg Miri.Interpreter.LocalState.value h))
      · injection hi with h; exact False.elim (hno3 mp₁ (congrArg Miri.Interpreter.LocalState.value h))
      · cases hi
    · intro f₁ f₂ _ _ _ _ _ _ _ _ hne hf₁ hf₂ _ _
      rcases f₁ with _ | f₁ <;> rcases f₂ with _ | f₂
      · exact False.elim (hne rfl)
      · cases hf₂
      · cases hf₁
      · cases hf₁
  exact .mk _ rfl (fun _ => Or.inl rfl) (fun h => False.elim (h rfl))
    hlinks.toFrameStackRel hlinks hdisj
    ⟨by dsimp only [mkWitIndirectCallerAnneal]; decide,
     by dsimp only [mkWitIndirectCallerAnneal]; decide,
     rfl, rfl, rfl⟩
    (ActiveProtectorsValid.nil _) (Nat.zero_lt_succ 0)
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (BorrowTrackerStackRel.of_none _ _ _)

theorem witIndirectFnPtr_pre (fnPtrs : List FnPtrEntry) :
    IndirectFnPtrMovePre witIndirectCallerBody
      (mkWitIndirectCallerAnneal 2 .uninit (.init (.ptr witFnPtrVal 8)) fnPtrs)
      (mkWitIndirectCallerMiri 2
        ⟨.live (.immediate .uninit), none⟩
        ⟨.live (.immediate (.scalar witFnPtrMiriScalar)), none⟩)
      (mkWitIndirectCallerMiriFrame 2
        ⟨.live (.immediate .uninit), none⟩
        ⟨.live (.immediate (.scalar witFnPtrMiriScalar)), none⟩)
      [] 3 safeFnPtrDecl witFnPtrVal
      Witness.witnessAllocId Witness.witnessTag Witness.witnessBaseAddr where
  frames_eq := rfl
  fn_lt_af := by dsimp only [mkWitIndirectCallerAnneal]; decide
  fn_lt_mf := by dsimp only [mkWitIndirectCallerMiriFrame]; decide
  fn_decl := rfl
  fn_slot := rfl
  fn_mls := ⟨none, rfl, fun _ h => nomatch h⟩
  allocId_eq := rfl
  baseAddr_lookup := rfl
  offset_no_wrap := ⟨by decide, by decide⟩
  not_borrow := rfl
  deinit_rel :=
    witIndirectCaller_rel 2 .uninit .uninit
      ⟨.live (.immediate .uninit), none⟩
      ⟨.live (.immediate .uninit),
       some (translateTy safeFnPtrDecl.ty emptyLayoutTable)⟩
      fnPtrs
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
      (.immediate .uninit .uninit (some (translateTy safeFnPtrDecl.ty emptyLayoutTable))
        (fun _ h => (Option.some.inj h).symm) (Or.inl ⟨rfl, rfl⟩))
      (fun _ h => nomatch h)
      (fun _ h => nomatch h)

/-- **Witness (p)**:
1. `step_terminator_call_fnDef_local_simulation` (`bb0`): calling a non-constant
   ZST `FnDef` local `_2 = .init .unit` pushes `witCalleeBody` in lockstep
   (`StepRelMultiFrame`);
2. `step_terminator_call_fnPtr_dangling_or_uninit_ub_simulation` (`bb1`): calling
   an uninitialized `FnPtr` local `_3 = .uninit` faults with UB in both machines
   (`StepRelMultiFrame.ub`);
3. `step_terminator_call_indirect_fnPtr_move_simulation` (`bb2`, `witFnEntrySafe`):
   calling a valid provenance-bearing `FnPtr` local `_3 = .init (.ptr witFnPtrVal 8)`
   via `.move` deinitializes `_3` and pushes `witCalleeBody` in lockstep
   (`StepRelMultiFrame`);
4. `step_terminator_call_indirect_unsafe_to_safe_fnPtr_divergence` (`bb2`, `witFnEntryUnsafe`):
   calling an `unsafe fn() -> u8` entry through a safe `fn() -> u8` local faults
   with `.fail .ub` in Stage-1 (`safetyCompatible .unsafe_ .safe = false`), whereas
   `lean-miri` pushes `witCalleeBody` onto a 2-frame stack (`.ok true`). -/
theorem wit_lm4_1_nonConst_fnDef_and_indirect_fnPtr_call_and_safety_divergence :
    StepRelMultiFrame witIndirectCallerBody
      (mkWitIndirectCallerMiri 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
      (stepMirFn witIndirectCallerBody (mkWitIndirectCallerAnneal 0 (.init .unit) .uninit []))
      (Miri.Interpreter.Step.step
        (annealStepHooksForState witIndirectCallerBody
          (mkWitIndirectCallerAnneal 0 (.init .unit) .uninit []))
        () (mkWitIndirectCallerMiri 0 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)) ∧
    StepRelMultiFrame witIndirectCallerBody
      (mkWitIndirectCallerMiri 1 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)
      (stepMirFn witIndirectCallerBody (mkWitIndirectCallerAnneal 1 .uninit .uninit []))
      (Miri.Interpreter.Step.step
        (annealStepHooksForState witIndirectCallerBody
          (mkWitIndirectCallerAnneal 1 .uninit .uninit []))
        () (mkWitIndirectCallerMiri 1 ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩)) ∧
    StepRelMultiFrame witIndirectCallerBody
      (mkWitIndirectCallerMiri 2
        ⟨.live (.immediate .uninit), none⟩
        ⟨.live (.immediate (.scalar witFnPtrMiriScalar)), none⟩)
      (stepMirFn witIndirectCallerBody
        (mkWitIndirectCallerAnneal 2 .uninit (.init (.ptr witFnPtrVal 8)) [witFnEntrySafe]))
      (Miri.Interpreter.Step.step
        (annealStepHooksForState witIndirectCallerBody
          (mkWitIndirectCallerAnneal 2 .uninit (.init (.ptr witFnPtrVal 8)) [witFnEntrySafe]))
        () (mkWitIndirectCallerMiri 2
          ⟨.live (.immediate .uninit), none⟩
          ⟨.live (.immediate (.scalar witFnPtrMiriScalar)), none⟩)) ∧
    (stepMirFn witIndirectCallerBody
        (mkWitIndirectCallerAnneal 2 .uninit (.init (.ptr witFnPtrVal 8)) [witFnEntryUnsafe]) = .fail .ub ∧
      ∃ m' calleeMf,
        Miri.Interpreter.Step.step
          (annealStepHooksForState witIndirectCallerBody
            (mkWitIndirectCallerAnneal 2 .uninit (.init (.ptr witFnPtrVal 8)) [witFnEntryUnsafe]))
          () (mkWitIndirectCallerMiri 2
            ⟨.live (.immediate .uninit), none⟩
            ⟨.live (.immediate (.scalar witFnPtrMiriScalar)), none⟩) = (m', .ok true) ∧
        m'.stack.frames.size = 2 ∧
        m'.stack.frames.back? = some calleeMf ∧
        calleeMf.body = translateBody witCalleeBody ∧
        calleeMf.location = .mir ⟨0, 0⟩) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hstate0 :=
      witIndirectCaller_rel 0 (.init .unit) .uninit
        ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩ []
        (.immediate (.init .unit) .uninit none (fun _ h => nomatch h)
          (Or.inr ⟨.unit, rfl, .unit rfl⟩))
        (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
        (fun _ h => nomatch h) (fun _ h => nomatch h)
    exact step_terminator_call_fnDef_local_simulation hstate0
      (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.call (.copy ⟨2, .nil⟩) [] ⟨1, .nil⟩ (some 3) .continue_)
               isCleanup := false })
      (fnDecl := calleeFnDecl) (destDecl := u8Decl) (calleeBody := witCalleeBody)
      rfl rfl rfl rfl rfl rfl
      (by intro tf htf mls hmls mp hmp
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hmp)
      rfl rfl rfl rfl rfl
      (by intro tf htf
          apply CallerDestSlotWf.of_immediate
          intro mls hmls mp hmp
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hmp)
      (by intro tf htf mls hmls hdead
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hdead)
      (Or.inr rfl)
  · have hstate1 :=
      witIndirectCaller_rel 1 .uninit .uninit
        ⟨.live (.immediate .uninit), none⟩ ⟨.live (.immediate .uninit), none⟩ []
        (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
        (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
        (fun _ h => nomatch h) (fun _ h => nomatch h)
    exact step_terminator_call_fnPtr_dangling_or_uninit_ub_simulation hstate1
      (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.call (.copy ⟨3, .nil⟩) [] ⟨1, .nil⟩ (some 3) .continue_)
               isCleanup := false })
      (fnDecl := safeFnPtrDecl)
      rfl rfl rfl rfl rfl rfl
      (by intro tf htf mls hmls mp hmp
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hmp)
  · exact (step_terminator_call_indirect_fnPtr_move_simulation
      (witIndirectFnPtr_pre [witFnEntrySafe])
      (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.call (.move ⟨3, .nil⟩) [] ⟨1, .nil⟩ (some 3) .continue_)
               isCleanup := false })
      (destDecl := u8Decl)
      rfl rfl rfl rfl rfl rfl).2.2.2
      witFnEntrySafe witCalleeBody u8Decl []
      { statements := [], terminator := mkTerm .return_, isCleanup := false }
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by intro tf htf
          subst htf
          refine ⟨?_, ?_⟩
          · apply CallerDestSlotWf.of_immediate
            intro mls hmls mp hmp
            injection hmls with hm; subst hm; nomatch hmp
          · intro mls hmls hdead
            injection hmls with hm; subst hm; nomatch hdead)
      (Or.inl rfl)
  · exact step_terminator_call_indirect_unsafe_to_safe_fnPtr_divergence
      (witIndirectFnPtr_pre [witFnEntryUnsafe])
      (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.call (.move ⟨3, .nil⟩) [] ⟨1, .nil⟩ (some 3) .continue_)
               isCleanup := false })
      (destDecl := u8Decl)
      (fnEntry := witFnEntryUnsafe) (calleeBody := witCalleeBody)
      (retDecl := u8Decl) (restDecls := [])
      (calleeBb0 := { statements := [], terminator := mkTerm .return_, isCleanup := false })
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by intro tf htf
          subst htf
          refine ⟨?_, ?_⟩
          · apply CallerDestSlotWf.of_immediate
            intro mls hmls mp hmp
            injection hmls with hm; subst hm; nomatch hmp
          · intro mls hmls hdead
            injection hmls with hm; subst hm; nomatch hdead)

/-! ## (q) Nounwind Callee Unwinding: Stage-1 `FnAbi.canUnwind`-Blindness vs. Canonical `Call.initStackFrame` -/

/-- `fn() -> u8` function item type for the nounwind callee `"crate::nounwind_callee"`. -/
def noUnwCalleeFnTy : Ty := { kind := .fnDef "crate::nounwind_callee" [], layoutIdx := 0 }

/-- Constant operand referencing `"crate::nounwind_callee"`. -/
def noUnwCalleeFuncOp : MirAst.Operand :=
  .constant { ty := noUnwCalleeFnTy, val := .zeroSized }

/-- Callee `"crate::nounwind_callee"` whose `FnAbi` cannot unwind
(`canUnwind := false`), but whose entry block is a cleanup block that resumes
unwinding (`bb0` (cleanup): `UnwindResume`). -/
def witNoUnwCalleeBody : CapturedMir where
  defPath := "crate::nounwind_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl]
  basicBlocks :=
    [{ statements := [], terminator := mkTerm .unwindResume, isCleanup := true }]
  fnAbi := { fnAbiU8 with canUnwind := false }
  layouts := emptyLayoutTable
  allocations := []

/-- Root caller `"crate::nounwind_caller"`:
* `bb0`: `_1 = call crate::nounwind_callee() -> [return: bb1, unwind: cleanup bb2]`
* `bb1`: `return`
* `bb2` (cleanup): `UnwindResume` -/
def witNoUnwCallerBody : CapturedMir where
  defPath := "crate::nounwind_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl, u8Decl]
  basicBlocks :=
    [ { statements := []
        terminator := mkTerm (.call noUnwCalleeFuncOp [] ⟨1, .nil⟩ (some 1) (.cleanup 2))
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false }
    , { statements := [], terminator := mkTerm .unwindResume, isCleanup := true } ]
  fnAbi := fnAbiU8
  layouts := emptyLayoutTable
  allocations := []

def witNoUnwCallAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
    memory := { callees := [witNoUnwCalleeBody], nextProtector := 1 } }

def witNoUnwCallMiri : AnnealStepState :=
  { stack :=
      ⟨#[{ body := translateBody witNoUnwCallerBody
           bodyIdentity := .ofCanonicalIndex 0
           functionInstance := ⟨.Item 0, #[]⟩
           extra := ()
           returnContinuation := .stop false
           returnPlace :=
             .frameLocal 0 0 none (translateTy u8Ty emptyLayoutTable) (.ofAllocationToken 0)
           localsIdentity := .ofAllocationToken 0
           locals := #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate .uninit), none⟩]
           vaList := #[]
           trackCallerArg := none
           location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

/-- Return continuation of `m`'s top frame, if any. -/
def miriTopCont (m : AnnealStepState) : Option Miri.Interpreter.ReturnContinuation :=
  m.stack.frames.back?.map (·.returnContinuation)

/-- **Witness (q)**: genuine 2-step lockstep execution (kernel evaluation via
`decide`) of a call with `unwind = .cleanup bb2` to a callee whose `FnAbi`
cannot unwind (`canUnwind = false`), followed by the callee's `UnwindResume`:
1. Stage-1 `Trusted` ignores `FnAbi.canUnwind`: the pushed `SavedCallerFrame`
   keeps `returnUnwind = .cleanup 2`, and `UnwindResume` resumes the caller at
   its cleanup block `bb2` (`.step s₂`, `s₂.frame.blockIdx = 2`, empty call stack);
2. `lean-miri` (`annealPushCalleeFrameLM4_1`, like canonical `Call.initStackFrame`)
   pushes the callee with continuation `.goto (some 1) .Unreachable`, so the same
   `UnwindResume` faults with `.undefinedBehavior "unwinding past a frame that
   does not allow unwinding"`.
This is why `step_terminator_call_simulation` and its siblings require
`calleeBody.fnAbi.canUnwind = true ∨ unwind = .unreachable`. -/
theorem wit_lm4_1_nounwind_callee_unwind_divergence :
    ∃ s₁ s₂ : MachineState,
      stepMirFn witNoUnwCallerBody witNoUnwCallAnneal = .step s₁ ∧
      s₁.memory.callStack.map SavedCallerFrame.returnUnwind = [.cleanup 2] ∧
      stepMirFn witNoUnwCallerBody s₁ = .step s₂ ∧
      s₂.frame.blockIdx = 2 ∧
      s₂.memory.callStack = [] ∧
      (miriNextLM4_1 witNoUnwCallerBody witNoUnwCallAnneal witNoUnwCallMiri).map
          (fun m₁ => (miriTopCont m₁, miriStepUBMsgLM4_1 witNoUnwCallerBody s₁ m₁)) =
        some (some (.goto (some 1) .Unreachable),
          some "unwinding past a frame that does not allow unwinding") := by
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-! ## (r) `ReifyFnPointer` → `IndirectFnPtrMovePre` → Indirect `FnPtr` Call, `LayoutCompat` vs. `rigidTyEq` Divergence, & Linked Panic / Direct-Unwind Simulation -/

def witFnEntryU64 : FnPtrEntry :=
  { allocId := 1
    defPath := "crate::callee_u64"
    typeArgs := []
    fnSig := some (.fnPtr [] (.uint .u64) .safe .rust) }

def u64TyLM4 : Ty := { kind := .uint .u64, layoutIdx := 0 }
def u64DeclLM4 : LocalDecl := { mutability := .mut, ty := u64TyLM4, debugName := none }
def usizeTyLM4 : Ty := { kind := .uint .usize, layoutIdx := 0 }
def usizeDeclLM4 : LocalDecl := { mutability := .mut, ty := usizeTyLM4, debugName := none }
def safeFnPtrUsizeTy : Ty := { kind := .fnPtr [] (.uint .usize) .safe .rust, layoutIdx := 0 }
def safeFnPtrUsizeDecl : LocalDecl := { mutability := .mut, ty := safeFnPtrUsizeTy, debugName := none }

def u64LayoutLM4 : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def fnAbiU64 : FnAbi :=
  { args := []
    ret := { layout := u64LayoutLM4, mode := .direct }
    conv := .rust
    canUnwind := true }

def witU64CalleeBody : CapturedMir where
  defPath := "crate::callee_u64"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64DeclLM4]
  basicBlocks :=
    [{ statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

def witUsizeIndirectCallerBody : CapturedMir where
  defPath := "crate::usize_indirect_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [usizeDeclLM4, usizeDeclLM4, calleeFnDecl, safeFnPtrUsizeDecl]
  basicBlocks :=
    [ { statements := []
        terminator := mkTerm (.call (.move ⟨3, .nil⟩) [] ⟨1, .nil⟩ (some 1) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

def mkWitUsizeIndirectCallerAnneal (slot3 : LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit, .uninit, slot3] }
    memory :=
      { callees := [witU64CalleeBody]
        fnPtrs := [witFnEntryU64]
        nextProtector := 1 } }

abbrev witUsizeIndirectCallerAnneal : MachineState :=
  mkWitUsizeIndirectCallerAnneal (.init (.ptr witFnPtrVal 8))

def mkWitUsizeIndirectCallerMiriFrame
    (ls3 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody witUsizeIndirectCallerBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy usizeTyLM4 emptyLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals :=
      #[⟨.live (.immediate .uninit), none⟩,
        ⟨.live (.immediate .uninit), none⟩,
        ⟨.live (.immediate .uninit), none⟩,
        ls3]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def mkWitUsizeIndirectCallerMiri
    (ls3 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    AnnealStepState :=
  { stack := ⟨#[mkWitUsizeIndirectCallerMiriFrame ls3]⟩
    machine := witFnPtrMachine }

abbrev witUsizeIndirectCallerMiri : AnnealStepState :=
  mkWitUsizeIndirectCallerMiri ⟨.live (.immediate (.scalar witFnPtrMiriScalar)), none⟩

theorem witUsizeIndirectCaller_rel
    (slot3 : LocalSlot)
    (ls3 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
    (h3 : LocalRel witFnPtrMachine safeFnPtrUsizeDecl emptyLayoutTable slot3 ls3)
    (hno3 : ∀ mp, ls3.value ≠ .live (.indirect mp)) :
    MultiFrameStateRel witUsizeIndirectCallerBody
      (mkWitUsizeIndirectCallerAnneal slot3)
      (mkWitUsizeIndirectCallerMiri ls3) := by
  have hfr :
      FrameRel witUsizeIndirectCallerBody witFnPtrMachine
        (mkWitUsizeIndirectCallerAnneal slot3).frame
        (mkWitUsizeIndirectCallerMiriFrame ls3) := by
    refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
    rcases i with _ | ⟨_ | ⟨_ | ⟨_ | i⟩⟩⟩
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact h3
    · cases hdecl
  have hlinks :
      CallerStackLinksRel witUsizeIndirectCallerBody witFnPtrMachine
        witUsizeIndirectCallerBody
        (mkWitUsizeIndirectCallerAnneal slot3).frame [] []
        [mkWitUsizeIndirectCallerMiriFrame ls3] :=
    .root _ _ [] rfl ⟨translateTy usizeTyLM4 emptyLayoutTable, rfl⟩ hfr
  have hdisj : MultiFrameAllocDisjoint (mkWitUsizeIndirectCallerMiri ls3).stack.frames := by
    refine ⟨?_, ?_⟩
    · intro mf hmf i _ mp₁ _ _ _ _ hi _
      rcases List.mem_singleton.mp hmf with rfl
      rcases i with _ | ⟨_ | ⟨_ | ⟨_ | i⟩⟩⟩
      · cases hi
      · cases hi
      · cases hi
      · injection hi with h; exact False.elim (hno3 mp₁ (congrArg Miri.Interpreter.LocalState.value h))
      · cases hi
    · intro f₁ f₂ _ _ _ _ _ _ _ _ hne hf₁ hf₂ _ _
      rcases f₁ with _ | f₁ <;> rcases f₂ with _ | f₂
      · exact False.elim (hne rfl)
      · cases hf₂
      · cases hf₁
      · cases hf₁
  exact .mk _ rfl (fun _ => Or.inl rfl) (fun h => False.elim (h rfl))
    hlinks.toFrameStackRel hlinks hdisj
    ⟨by dsimp only [mkWitUsizeIndirectCallerAnneal]; decide,
     by dsimp only [mkWitUsizeIndirectCallerAnneal]; decide,
     rfl, rfl, rfl⟩
    (ActiveProtectorsValid.nil _) (Nat.zero_lt_succ 0)
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (BorrowTrackerStackRel.of_none _ _ _)

theorem witUsizeIndirectFnPtr_pre :
    IndirectFnPtrMovePre witUsizeIndirectCallerBody
      witUsizeIndirectCallerAnneal
      witUsizeIndirectCallerMiri
      (mkWitUsizeIndirectCallerMiriFrame ⟨.live (.immediate (.scalar witFnPtrMiriScalar)), none⟩)
      [] 3 safeFnPtrUsizeDecl witFnPtrVal
      Witness.witnessAllocId Witness.witnessTag Witness.witnessBaseAddr where
  frames_eq := rfl
  fn_lt_af := by dsimp only [witUsizeIndirectCallerAnneal, mkWitUsizeIndirectCallerAnneal]; decide
  fn_lt_mf := by dsimp only [mkWitUsizeIndirectCallerMiriFrame]; decide
  fn_decl := rfl
  fn_slot := rfl
  fn_mls := ⟨none, rfl, fun _ h => nomatch h⟩
  allocId_eq := rfl
  baseAddr_lookup := rfl
  offset_no_wrap := ⟨by decide, by decide⟩
  not_borrow := rfl
  deinit_rel :=
    witUsizeIndirectCaller_rel .uninit
      ⟨.live (.immediate .uninit),
       some (translateTy safeFnPtrUsizeDecl.ty emptyLayoutTable)⟩
      (.immediate .uninit .uninit (some (translateTy safeFnPtrUsizeDecl.ty emptyLayoutTable))
        (fun _ h => (Option.some.inj h).symm) (Or.inl ⟨rfl, rfl⟩))
      (fun _ h => nomatch h)

/-- Body exercising 2-step `MultiFrameStateRel` → `ReifyFnPointer` →
`IndirectFnPtrMovePre` → `TerminatorKind.call (.move ⟨3, .nil⟩)` →
`MultiFrameStateRel`:
* `bb0`:
  - `stmt 0`: `_3 = crate::callee as fn() -> u8 (PointerCoercion(ReifyFnPointer))`
  - `terminator`: `_1 = call move _3() -> [return: bb1, unwind: continue]`
* `bb1`: `return` -/
def witReifyCallerBody : CapturedMir where
  defPath := "crate::reify_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl, u8Decl, calleeFnDecl, safeFnPtrDecl]
  basicBlocks :=
    [ { statements :=
          [{ kind :=
               .assign ⟨3, .nil⟩
                 (.cast (.pointerCoercion "ReifyFnPointer")
                   calleeFuncOp
                   safeFnPtrTy)
             span := "" }]
        terminator := mkTerm (.call (.move ⟨3, .nil⟩) [] ⟨1, .nil⟩ (some 1) .continue_)
        isCleanup := false }
    , { statements := [], terminator := mkTerm .return_, isCleanup := false } ]
  fnAbi := fnAbiU8
  layouts := emptyLayoutTable
  allocations := []

def witReifyCallerAnneal0 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit, .uninit, .uninit] }
    memory :=
      { callees := [witCalleeBody]
        fnPtrs := []
        nextProtector := 1 } }

def witReifyCallerMiriFrame0 :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody witReifyCallerBody
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
        ⟨.live (.immediate .uninit), none⟩,
        ⟨.live (.immediate .uninit), none⟩]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def witReifyAllocId : Miri.Memory.AllocId :=
  ⟨UInt64.ofNat fnPtrAllocBase, by decide⟩

def witReifyFnPtrVal : ProvenancePtr :=
  { allocId := fnPtrAllocBase, offsetBytes := 0 }

def witReifyFnEntry : FnPtrEntry :=
  { allocId := fnPtrAllocBase
    defPath := "crate::callee"
    typeArgs := []
    fnSig := some (.fnPtr [] (.uint .u8) .safe .rust) }

def witReifyMachine : AnnealMachine :=
  { Witness.witnessMachineOf Witness.witnessUninitAlloc with
    addresses :=
      { (Witness.witnessMachineOf Witness.witnessUninitAlloc).addresses with
        baseAddr := #[⟨witReifyAllocId, Witness.witnessBaseAddr⟩] } }

def witReifyCallerMiri0 : AnnealStepState :=
  { stack := ⟨#[witReifyCallerMiriFrame0]⟩
    machine := witReifyMachine }

theorem witReifyCaller0_rel :
    MultiFrameStateRel witReifyCallerBody witReifyCallerAnneal0 witReifyCallerMiri0 := by
  have hfr :
      FrameRel witReifyCallerBody witReifyMachine
        witReifyCallerAnneal0.frame witReifyCallerMiriFrame0 := by
    refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
    rcases i with _ | ⟨_ | ⟨_ | ⟨_ | i⟩⟩⟩
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · cases hdecl
  have hlinks :
      CallerStackLinksRel witReifyCallerBody witReifyMachine
        witReifyCallerBody witReifyCallerAnneal0.frame [] [] [witReifyCallerMiriFrame0] :=
    .root _ _ [] rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr
  have hdisj : MultiFrameAllocDisjoint witReifyCallerMiri0.stack.frames := by
    refine ⟨?_, ?_⟩
    · intro mf hmf i _ _ _ _ _ _ hi _
      rcases List.mem_singleton.mp hmf with rfl
      rcases i with _ | ⟨_ | ⟨_ | ⟨_ | i⟩⟩⟩ <;> cases hi
    · intro f₁ f₂ _ _ _ _ _ _ _ _ hne hf₁ hf₂ _ _
      rcases f₁ with _ | f₁ <;> rcases f₂ with _ | f₂
      · exact False.elim (hne rfl)
      · cases hf₂
      · cases hf₁
      · cases hf₁
  exact .mk _ rfl (fun _ => Or.inl rfl) (fun h => False.elim (h rfl))
    hlinks.toFrameStackRel hlinks hdisj
    ⟨by decide, by decide, rfl, rfl, rfl⟩
    (ActiveProtectorsValid.nil _) (Nat.zero_lt_succ 0)
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (BorrowTrackerStackRel.of_none _ _ _)

/-- Linked `"core::panicking::panic"` body whose entry block is a cleanup block
that immediately executes `UnwindResume`. -/
def witLinkedPanicBody : CapturedMir where
  defPath := "core::panicking::panic"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl]
  basicBlocks :=
    [{ statements := [], terminator := mkTerm .unwindResume, isCleanup := true }]
  fnAbi := { fnAbiU8 with canUnwind := true }
  layouts := emptyLayoutTable
  allocations := []

def witLinkedPanicCallAnneal : MachineState :=
  { frame := { blockIdx := 2, stmtIdx := 0, locals := [.uninit, .uninit] }
    memory := { callees := [witLinkedPanicBody], nextProtector := 1 } }

theorem witLinkedPanicCall_rel :
    MultiFrameStateRel witAssertTermPanicBody witLinkedPanicCallAnneal
      (mkWitAssertTermPanicMiri 2 ⟨.live (.immediate .uninit), none⟩) := by
  have hfr :
      FrameRel witAssertTermPanicBody AnnealMachine.empty
        witLinkedPanicCallAnneal.frame
        (mkWitAssertTermPanicMiriFrame 2 ⟨.live (.immediate .uninit), none⟩) := by
    refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
    rcases i with _ | ⟨_ | i⟩
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · injection hdecl with hd; subst hd
      injection hslot with hs; subst hs
      injection hmls with hm; subst hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · cases hdecl
  have hlinks :
      CallerStackLinksRel witAssertTermPanicBody AnnealMachine.empty
        witAssertTermPanicBody witLinkedPanicCallAnneal.frame [] []
        [mkWitAssertTermPanicMiriFrame 2 ⟨.live (.immediate .uninit), none⟩] :=
    .root _ _ [] rfl ⟨translateTy u8Ty emptyLayoutTable, rfl⟩ hfr
  have hdisj :
      MultiFrameAllocDisjoint
        (mkWitAssertTermPanicMiri 2 ⟨.live (.immediate .uninit), none⟩).stack.frames := by
    refine ⟨?_, ?_⟩
    · intro mf hmf i _ _ _ _ _ _ hi _
      rcases List.mem_singleton.mp hmf with rfl
      rcases i with _ | ⟨_ | i⟩ <;> cases hi
    · intro f₁ f₂ _ _ _ _ _ _ _ _ hne hf₁ hf₂ _ _
      rcases f₁ with _ | f₁ <;> rcases f₂ with _ | f₂
      · exact False.elim (hne rfl)
      · cases hf₂
      · cases hf₁
      · cases hf₁
  exact .mk _ rfl (fun _ => Or.inl rfl) (fun h => False.elim (h rfl))
    hlinks.toFrameStackRel hlinks hdisj
    ⟨by decide, by decide, rfl, rfl, rfl⟩
    (ActiveProtectorsValid.nil _) (Nat.zero_lt_succ 0)
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (BorrowTrackerStackRel.of_none _ _ _)

/-- **Witness (r)**:
1. **2-step `MultiFrameStateRel` → `ReifyFnPointer` → `IndirectFnPtrMovePre` →
   Indirect `FnPtr` Call → `MultiFrameStateRel`**:
   starting from `witReifyCaller0_rel` (`MultiFrameStateRel witReifyCallerBody witReifyCallerAnneal0 witReifyCallerMiri0`),
   Step 1 (`step_stmt_assign_reifyFnPointer_to_indirectFnPtrMovePre_simulation`)
   interns `"crate::callee"` in `fnPtrs` and establishes `IndirectFnPtrMovePre`,
   and Step 2 (`step_terminator_call_indirect_fnPtr_move_simulation`) deinitializes
   `_3` and pushes `witCalleeBody` in lockstep (`StepRelMultiFrame`);
2. **Indirect `FnPtr` ABI mismatch UB (`fn() -> u64` called as `fn() -> u8`)**:
   both Stage-1 and `lean-miri` fault with UB in lockstep
   (`StepRelMultiFrame`);
3. **Indirect `FnPtr` `LayoutCompat` (`usize` vs. `u64`) divergence**
   (`step_terminator_call_indirect_layoutCompat_fnPtr_divergence`):
   calling `fn() -> u64` (`witFnEntryU64`) through `fn() -> usize` faults with
   `.fail .ub` in Stage-1 (`rigidTyEq (.uint .usize) (.uint .u64) = false`),
   while `lean-miri` (`annealRigidTyLayoutCompat (.uint .usize) (.uint .u64) = true`)
   pushes `witU64CalleeBody`;
4. **Canonical `Miri.Interpreter.FunctionPointers.Registry` bridge**:
   `((annealFnPtrRegistry [witFnEntrySafe]).extras.find? (·.1 == Witness.witnessAllocId)).map Prod.snd = some witFnEntrySafe`;
5. **Linked `"core::panicking::panic"` 2-step call + unwind simulation**
   (`step_terminator_call_linked_panic_unwind_simulation`) and **direct-unwind
   failed `Assert` & `UnwindTerminate` simulation**
   (`step_terminator_assert_failed_directUnwind_simulation`,
   `step_terminator_unwindTerminate_termination_abort_simulation`). -/
theorem wit_lm4_1_reifyFnPointer_chain_layoutCompat_and_directUnwind :
    (∃ s₁ m₁ topFrame₁ restMfs,
      stepMirFn witReifyCallerBody witReifyCallerAnneal0 = .step s₁ ∧
      Miri.Interpreter.Step.step
        (annealStepHooksForState witReifyCallerBody witReifyCallerAnneal0)
        () witReifyCallerMiri0 = (m₁, .ok true) ∧
      lookupFnPtr s₁.memory.fnPtrs fnPtrAllocBase = some witReifyFnEntry ∧
      IndirectFnPtrMovePre witReifyCallerBody s₁ m₁ topFrame₁ restMfs 3 safeFnPtrDecl
        witReifyFnPtrVal witReifyAllocId Miri.Memory.BorTag.one Witness.witnessBaseAddr ∧
      StepRelMultiFrame witReifyCallerBody m₁
        (stepMirFn witReifyCallerBody s₁)
        (Miri.Interpreter.Step.step
          (annealStepHooksForState witReifyCallerBody s₁) () m₁)) ∧
    StepRelMultiFrame witIndirectCallerBody
      (mkWitIndirectCallerMiri 2
        ⟨.live (.immediate .uninit), none⟩
        ⟨.live (.immediate (.scalar witFnPtrMiriScalar)), none⟩)
      (stepMirFn witIndirectCallerBody
        (mkWitIndirectCallerAnneal 2 .uninit (.init (.ptr witFnPtrVal 8)) [witFnEntryU64]))
      (Miri.Interpreter.Step.step
        (annealStepHooksForState witIndirectCallerBody
          (mkWitIndirectCallerAnneal 2 .uninit (.init (.ptr witFnPtrVal 8)) [witFnEntryU64]))
        () (mkWitIndirectCallerMiri 2
          ⟨.live (.immediate .uninit), none⟩
          ⟨.live (.immediate (.scalar witFnPtrMiriScalar)), none⟩)) ∧
    (stepMirFn witUsizeIndirectCallerBody witUsizeIndirectCallerAnneal = .fail .ub ∧
      ∃ m' calleeMf,
        Miri.Interpreter.Step.step
          (annealStepHooksForState witUsizeIndirectCallerBody witUsizeIndirectCallerAnneal)
          () witUsizeIndirectCallerMiri = (m', .ok true) ∧
        m'.stack.frames.size = 2 ∧
        m'.stack.frames.back? = some calleeMf ∧
        calleeMf.body = translateBody witU64CalleeBody ∧
        calleeMf.location = .mir ⟨0, 0⟩) ∧
    ((annealFnPtrRegistry [witFnEntrySafe]).extras.find? (·.1 == Witness.witnessAllocId)).map Prod.snd =
      some witFnEntrySafe ∧
    (StepRelMultiFrame witAssertTermPanicBody
      (mkWitAssertTermPanicMiri 2 ⟨.live (.immediate .uninit), none⟩)
      (stepMirFn witAssertTermPanicBody witLinkedPanicCallAnneal)
      (Miri.Interpreter.Step.step
        (annealStepHooksForState witAssertTermPanicBody witLinkedPanicCallAnneal)
        () (mkWitAssertTermPanicMiri 2 ⟨.live (.immediate .uninit), none⟩)) ∧
      ∃ s₁ m₁,
        stepMirFn witAssertTermPanicBody witLinkedPanicCallAnneal = .step s₁ ∧
        Miri.Interpreter.Step.step
          (annealStepHooksForState witAssertTermPanicBody witLinkedPanicCallAnneal)
          () (mkWitAssertTermPanicMiri 2 ⟨.live (.immediate .uninit), none⟩) = (m₁, .ok true) ∧
        MultiFrameStateRel witAssertTermPanicBody s₁ m₁ ∧
        StepRelMultiFrame witAssertTermPanicBody m₁
          (stepMirFn witAssertTermPanicBody s₁)
          (Miri.Interpreter.Step.step (annealStepHooksForState witAssertTermPanicBody s₁) () m₁)) ∧
    (stepMirFn witAssertTermPanicBody (mkWitAssertTermPanicAnneal 0 .uninit) = .retOutcome .abort ∧
      Miri.Interpreter.Step.step
        (annealStepHooksWithDirectUnwind witAssertTermPanicBody (mkWitAssertTermPanicAnneal 0 .uninit))
        () (mkWitAssertTermPanicMiri 0 ⟨.live (.immediate .uninit), none⟩) =
        (mkWitAssertTermPanicMiri 0 ⟨.live (.immediate .uninit), none⟩,
         .error (.termination (.abort "panic in a function that cannot unwind"))) ∧
      (Miri.Concurrency.TerminationInfo.abort "panic in a function that cannot unwind").report =
        .abnormalTermination ∧
      (Miri.Concurrency.TerminationInfo.abort "panic in a function that cannot unwind").isUbReport =
        false) ∧
    StepRelMultiFrame witAssertTermPanicBody
      (mkWitAssertTermPanicMiri 1
        ⟨.live (.immediate (.scalar (.fromScalarInt (.ofBool false)))), none⟩)
      (stepMirFn witAssertTermPanicBody
        (mkWitAssertTermPanicAnneal 1 (.init (.scalar (boolToScalar false)))))
      (Miri.Interpreter.Step.step
        (annealStepHooksWithDirectUnwind witAssertTermPanicBody
          (mkWitAssertTermPanicAnneal 1 (.init (.scalar (boolToScalar false)))))
        () (mkWitAssertTermPanicMiri 1
          ⟨.live (.immediate (.scalar (.fromScalarInt (.ofBool false)))), none⟩)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s₁, m₁, topFrame₁, restMfs, ha₁, hm₁, hblk₁, hstmt₁, hcal₁, hact₁, hfn₁, hpres₁, hpre₁⟩ :=
      step_stmt_assign_reifyFnPointer_to_indirectFnPtrMovePre_simulation
        witReifyCaller0_rel
        (fun _ h => nomatch h)
        (bb := (witReifyCallerBody.basicBlocks[0]))
        (fnIdx := 3) (fnDecl := safeFnPtrDecl)
        (defPath := "crate::callee") (span := "")
        (callerInputs := []) (callerOut := .uint .u8) (callerAbi := .rust)
        (allocId := fnPtrAllocBase) (mAllocId := witReifyAllocId)
        (baseAddr := Witness.witnessBaseAddr)
        rfl rfl rfl rfl rfl rfl rfl rfl
        (by intro tf htf mls hmls mp hmp
            injection htf with h; subst h
            injection hmls with hm; subst hm; nomatch hmp)
        (by intro h; nomatch h)
        rfl rfl rfl rfl
    have hbb₁ :
        get? (activeMirBody witReifyCallerBody s₁).basicBlocks s₁.frame.blockIdx =
          some (witReifyCallerBody.basicBlocks[0]) := by
      rw [hact₁, hblk₁]; rfl
    have hstmt_none₁ :
        get? (witReifyCallerBody.basicBlocks[0]).statements s₁.frame.stmtIdx = none := by
      rw [hstmt₁]; rfl
    have hstmt_len₁ :
        s₁.frame.stmtIdx = length (witReifyCallerBody.basicBlocks[0]).statements := by
      rw [hstmt₁]; rfl
    have hdest_decl₁ :
        get? (activeMirBody witReifyCallerBody s₁).localDecls 1 = some u8Decl := by
      rw [hact₁]; rfl
    obtain ⟨himm1, hlive1⟩ :=
      hpres₁ 1 (by
        intro tf htf
        injection htf with h; subst h
        refine ⟨?_, ?_⟩
        · intro mls hmls mp hmp
          injection hmls with hm; subst hm; nomatch hmp
        · intro mls hmls hdead
          injection hmls with hm; subst hm; nomatch hdead)
    have hsim₂ :=
      (step_terminator_call_indirect_fnPtr_move_simulation
        hpre₁
        (by rw [hact₁]; exact fun _ h => nomatch h)
        hbb₁ hstmt_none₁ hstmt_len₁ rfl rfl hdest_decl₁).2.2.2
        witReifyFnEntry witCalleeBody u8Decl []
        { statements := [], terminator := mkTerm .return_, isCleanup := false }
        rfl hfn₁ rfl rfl rfl
        (by rw [hcal₁]; rfl)
        rfl rfl rfl rfl
        (by intro tf htf
            subst htf
            exact ⟨CallerDestSlotWf.of_immediate
              ((himm1.cache_layout hpre₁.fn_lt_mf _).set_immediate _ .uninit),
              (hlive1.cache_layout hpre₁.fn_lt_mf _).set_immediate _ .uninit⟩)
        (Or.inl rfl)
    exact ⟨s₁, m₁, topFrame₁, restMfs, ha₁, hm₁, hfn₁, hpre₁, hsim₂⟩
  · exact (step_terminator_call_indirect_fnPtr_move_simulation
      (witIndirectFnPtr_pre [witFnEntryU64])
      (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.call (.move ⟨3, .nil⟩) [] ⟨1, .nil⟩ (some 3) .continue_)
               isCleanup := false })
      (destDecl := u8Decl)
      rfl rfl rfl rfl rfl rfl).2.2.1
      witFnEntryU64 rfl rfl rfl rfl rfl
  · exact step_terminator_call_indirect_layoutCompat_fnPtr_divergence
      witUsizeIndirectFnPtr_pre
      (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.call (.move ⟨3, .nil⟩) [] ⟨1, .nil⟩ (some 1) .continue_)
               isCleanup := false })
      (destDecl := usizeDeclLM4)
      (fnEntry := witFnEntryU64) (calleeBody := witU64CalleeBody)
      (retDecl := u64DeclLM4) (restDecls := [])
      (calleeBb0 := { statements := [], terminator := mkTerm .return_, isCleanup := false })
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by intro tf htf
          subst htf
          refine ⟨?_, ?_⟩
          · apply CallerDestSlotWf.of_immediate
            intro mls hmls mp hmp
            injection hmls with hm; subst hm; nomatch hmp
          · intro mls hmls hdead
            injection hmls with hm; subst hm; nomatch hdead)
  · exact annealFnPtrRegistry_singleton_find_eq witFnEntrySafe Witness.witnessAllocId rfl
  · exact step_terminator_call_linked_panic_unwind_simulation
      witLinkedPanicCall_rel
      (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.call panicFuncOp [] ⟨0, .nil⟩ none (.cleanup 0))
               isCleanup := false })
      (defPath := "core::panicking::panic")
      (panicBody := witLinkedPanicBody) (retDecl := u8Decl)
      (panicBb0 := { statements := [], terminator := mkTerm .unwindResume, isCleanup := true })
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun _ h => nomatch h)
      rfl
      (by intro tf htf
          apply CallerDestSlotWf.of_immediate
          intro mls hmls mp hmp
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hmp)
      (by intro tf htf mls hmls hdead
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hdead)
      (Or.inr ⟨0, rfl⟩)
  · exact step_terminator_unwindTerminate_termination_abort_simulation
      (witAssertTermPanic_rel 0 .uninit ⟨.live (.immediate .uninit), none⟩
        (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
        (fun _ h => nomatch h))
      (fun _ h => nomatch h)
      (bb := { statements := [], terminator := mkTerm .unwindTerminate, isCleanup := true })
      rfl rfl rfl rfl
  · have hstate_false :=
      witAssertTermPanic_rel 1 (.init (.scalar (boolToScalar false)))
        ⟨.live (.immediate (.scalar (.fromScalarInt (.ofBool false)))), none⟩
        (.immediate (.init (.scalar (boolToScalar false)))
          (.scalar (.fromScalarInt (.ofBool false))) none
          (fun _ h => nomatch h)
          (Or.inr ⟨.scalar (boolToScalar false), rfl,
            .scalar (boolToScalar false) (.ofBool false) (ScalarRel.of_boolToScalar false) rfl
              (fun _ => ⟨rfl, Or.inl rfl⟩) (fun h => nomatch h)⟩))
        (fun _ h => nomatch h)
    exact (step_terminator_assert_failed_directUnwind_simulation hstate_false
      (fun _ h => nomatch h)
      (bb := { statements := []
               terminator := mkTerm (.assert (.copy ⟨1, .nil⟩) true 2 (.cleanup 0))
               isCleanup := false })
      (condDecl := boolDecl)
      rfl rfl rfl rfl rfl rfl
      (by intro tf htf mls hmls mp hmp
          injection htf with h; subst h
          injection hmls with hm; subst hm; nomatch hmp)
      rfl (by decide)).1 0 rfl

end LeanMiriSpec.Correspondence.WitnessLM4_1
