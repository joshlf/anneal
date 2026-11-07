/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM1_4
import LeanMiriSpec.Correspondence.Witness

/-!
# Non-Vacuity Witnesses for the `LM-1.4` Correspondence

The `LM-1.4` theorems in `SimLM1_4` would hold vacuously if their premises could
never be met together. This module fixes the `Runtime(PostCleanup)` body
`lm14MoveBody`,
```text
bb0: StorageLive(_1); _1 = const 42_u8; PlaceMention(_1); _0 = move _1;
     StorageDead(_1); return
```
and the matching Anneal and `lean-miri` states before statement `k` once `_1`
holds `42_u8` (`lm14MoveAnneal k`, `lm14MoveMiri k`, related by
`lm14_stateRel`). It proves:

* `_0 = move _1` (statement 3) satisfies `WellTypedLM1_4Stmt`, so
  `evalOperand_move_simulation` applies (`lm14_move_stepRel`). Both machines
  take a normal step: Anneal moves `42_u8` into `_0` and leaves `_1`
  uninitialized (`lm14_move_anneal_step`), and `lean-miri` reaches a state
  related to that result (`lm14_move_steps`).
* `PlaceMention(_1)` (statement 2) steps in lockstep to the states before
  statement 3 (`lm14_placeMention_stepRel`, `lm14_placeMention_steps`).
* `forceAllocation` succeeds on the immediate local `_1`, moves it into a fresh
  stack allocation, and keeps `StateRel` (`lm14_forceAllocation_witness`).
  Kernel evaluation cannot run `reserveAllocId`, whose `KeyedArray` uses
  `Std.HashMap`, so the proof takes the reserved `AllocId` from
  `MemoryState.reserve_of_highWater` and writes the scalar using
  `freshStackAlloc_writeScalar_readScalar`.
* Once `forceAllocation` has moved `_1` into memory, `StorageLive(_1)`
  (statement 0) and `StorageDead(_1)` (statement 4) still step in lockstep, so
  the simulation covers `lean-miri` freeing the allocation
  (`lm14_storageLive_indirect_steps`, `lm14_storageDead_indirect_steps`).

The states before statement `k` are related for every `k`, although execution
from the start of `bb0` reaches only some of them; the witnesses need related
states, not reachable ones.
-/

namespace LeanMiriSpec.Correspondence.Witness

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ## 1. Body and related states -/

/-- `42_u8` as a `lean-miri` scalar. -/
def lm14Scalar42 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt8 42

/-- `lm14Scalar42` is related to Anneal's `42_u8`. -/
theorem lm14_scalarRel42 : ScalarRel ⟨42, 1⟩ lm14Scalar42 :=
  ⟨Or.inl rfl, by decide, rfl, rfl⟩

/-- `Runtime(PostCleanup)` MIR that moves a local into the return place:
```text
bb0: StorageLive(_1); _1 = const 42_u8; PlaceMention(_1); _0 = move _1;
     StorageDead(_1); return
``` -/
def lm14MoveBody : CapturedMir where
  defPath := "lm_1_4_witness::mv"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl, u8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.use (.constant (constU8 42)))),
        mkStmt (.placeMention (local_ 1)),
        mkStmt (.assign (local_ 0) (.use (.move (local_ 1)))),
        mkStmt (.storageDead 1)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi0
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal's state for `lm14MoveBody` before statement `k` of `bb0`, once
`StorageLive(_1); _1 = const 42_u8` has run: `_0` is uninitialized and
`_1 = 42_u8`. -/
def lm14MoveAnneal (k : Nat) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := k, locals := [.uninit, .init (.scalar ⟨42, 1⟩)] }
    memory := (initMachineState lm14MoveBody []).memory }

/-- Anneal's state after `_0 = move _1`: `_0 = 42_u8` and `_1` is
uninitialized. -/
def lm14MovedAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 4, locals := [.init (.scalar ⟨42, 1⟩), .uninit] }
    memory := (initMachineState lm14MoveBody []).memory }

/-- `lean-miri`'s root frame matching `lm14MoveAnneal k`: both locals are
immediate. -/
def lm14MoveMiriFrame (k : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm14MoveBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy u8Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[{ value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt lm14Scalar42))), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, k⟩ }

/-- `lean-miri`'s single-threaded state matching `lm14MoveAnneal k`. -/
def lm14MoveMiri (k : Nat) : AnnealStepState :=
  { stack := ⟨#[lm14MoveMiriFrame k]⟩, machine := AnnealMachine.empty }

/-- `StateRel` holds before every statement `k` once `_1` holds `42_u8`. -/
theorem lm14_stateRel (k : Nat) :
    StateRel lm14MoveBody (lm14MoveAnneal k) (lm14MoveMiri k) := by
  refine StateRel.mk (lm14MoveMiriFrame k) rfl rfl ⟨translateTy u8Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i j mplace_i mplace_j lay_i lay_j hneq hi hj
      revert hi
      match i with
      | 0 => rintro ⟨⟩
      | 1 => rintro ⟨⟩
      | _ + 2 => rintro ⟨⟩)
  refine
    { body_eq := rfl
      location_eq := rfl
      af_locals_len := rfl
      mf_locals_size := rfl
      locals_rel := ?_ }
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = u8Decl := by simpa [lm14MoveBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm14MoveAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm14MoveMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = u8Decl := by simpa [lm14MoveBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 1⟩) := by simpa [lm14MoveAnneal, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt lm14Scalar42))), layout := none } :=
      by simpa [lm14MoveMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ none (fun _ h => nomatch h)
      (Or.inr ⟨_, rfl, .scalar _ _ lm14_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | n + 2 =>
    simp [lm14MoveBody, get?] at hdecl

/-- `lm14MoveBody` is a `Runtime(PostCleanup)` body, not an `other` phase. -/
theorem lm14_phase : ∀ p, lm14MoveBody.phase ≠ .other p := by
  intro p h
  cases h

private theorem lm14_frame_eq {k : Nat}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : (lm14MoveMiri k).stack.frames = #[topFrame]) : topFrame = lm14MoveMiriFrame k := by
  simp only [lm14MoveMiri, List.toArray, Array.mk.injEq, List.cons.injEq, and_true] at h
  exact h.symm

/-! ## 2. `_0 = move _1` -/

/-- `_0 = move _1` satisfies `WellTypedLM1_4Stmt` in the root frame of
`lm14MoveMiri 3`. -/
theorem lm14_move_wellTyped
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (h : (lm14MoveMiri 3).stack.frames = #[topFrame]) :
    WellTypedLM1_4Stmt lm14MoveBody topFrame
      ⟨.assign ⟨0, .nil⟩ (.use (.move ⟨1, .nil⟩)), "lm-1.1-witness"⟩ := by
  obtain rfl := lm14_frame_eq h
  refine .assignMove 0 1 u8Decl u8Decl _ rfl rfl rfl (by decide) ?_ ?_
  · intro mls hmls mp hv
    simp only [lm14MoveMiriFrame, List.getElem?_toArray, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.some.injEq] at hmls
    subst hmls
    cases hv
  · intro mls hmls mp hv
    simp only [lm14MoveMiriFrame, List.getElem?_toArray, List.getElem?_cons_zero,
      Option.some.injEq] at hmls
    subst hmls
    cases hv

/-- `evalOperand_move_simulation` applies to `_0 = move _1`. -/
theorem lm14_move_stepRel :
    StepRel lm14MoveBody (lm14MoveMiri 3)
      (stepMirFn lm14MoveBody (lm14MoveAnneal 3))
      (Miri.Interpreter.Step.step (annealStepHooks lm14MoveBody.localDecls lm14MoveBody.layouts) ()
        (lm14MoveMiri 3)) :=
  evalOperand_move_simulation (lm14_stateRel 3) lm14_phase rfl rfl lm14_move_wellTyped

/-- Anneal executes `_0 = move _1` normally: `42_u8` moves into `_0`, and `_1`
becomes uninitialized. -/
theorem lm14_move_anneal_step :
    stepMirFn lm14MoveBody (lm14MoveAnneal 3) = .step lm14MovedAnneal := rfl

/-- `lean-miri` also executes `_0 = move _1` normally, reaching a state related
to `lm14MovedAnneal`. -/
theorem lm14_move_steps :
    ∃ m', Miri.Interpreter.Step.step
        (annealStepHooks lm14MoveBody.localDecls lm14MoveBody.layouts) () (lm14MoveMiri 3) =
        (m', .ok true) ∧
      StateRel lm14MoveBody lm14MovedAnneal m' := by
  have h := lm14_move_stepRel
  rw [lm14_move_anneal_step] at h
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm14MoveBody.localDecls lm14MoveBody.layouts) () (lm14MoveMiri 3) = r at h ⊢
  cases h with
  | step s' m' hrel => exact ⟨m', rfl, hrel⟩

/-! ## 3. `PlaceMention(_1)` -/

/-- `PlaceMention(_1)` satisfies `WellTypedLM1_4Stmt` in the root frame of
`lm14MoveMiri 2`. -/
theorem lm14_placeMention_wellTyped
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (h : (lm14MoveMiri 2).stack.frames = #[topFrame]) :
    WellTypedLM1_4Stmt lm14MoveBody topFrame ⟨.placeMention ⟨1, .nil⟩, "lm-1.1-witness"⟩ := by
  obtain rfl := lm14_frame_eq h
  refine .placeMention 1 u8Decl _ rfl ?_
  intro mls hmls hv
  simp only [lm14MoveMiriFrame, List.getElem?_toArray, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.some.injEq] at hmls
  subst hmls
  cases hv

/-- `step_placeMention_simulation` applies to `PlaceMention(_1)`. -/
theorem lm14_placeMention_stepRel :
    StepRel lm14MoveBody (lm14MoveMiri 2)
      (stepMirFn lm14MoveBody (lm14MoveAnneal 2))
      (Miri.Interpreter.Step.step (annealStepHooks lm14MoveBody.localDecls lm14MoveBody.layouts) ()
        (lm14MoveMiri 2)) :=
  step_placeMention_simulation (lm14_stateRel 2) lm14_phase rfl rfl lm14_placeMention_wellTyped

/-- Both machines execute `PlaceMention(_1)` normally: Anneal reaches
`lm14MoveAnneal 3`, and `lean-miri` reaches a state related to it. -/
theorem lm14_placeMention_steps :
    stepMirFn lm14MoveBody (lm14MoveAnneal 2) = .step (lm14MoveAnneal 3) ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks lm14MoveBody.localDecls lm14MoveBody.layouts) () (lm14MoveMiri 2) =
          (m', .ok true) ∧
        StateRel lm14MoveBody (lm14MoveAnneal 3) m' := by
  have hstep : stepMirFn lm14MoveBody (lm14MoveAnneal 2) = .step (lm14MoveAnneal 3) := rfl
  refine ⟨hstep, ?_⟩
  have h := lm14_placeMention_stepRel
  rw [hstep] at h
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm14MoveBody.localDecls lm14MoveBody.layouts) () (lm14MoveMiri 2) = r at h ⊢
  cases h with
  | step s' m' hrel => exact ⟨m', rfl, hrel⟩

/-! ## 4. `forceAllocation` promotes an immediate local -/

/-- Forward counterpart of `annealPlaceHooks_allocateStack_inv`. -/
private theorem lm14_allocateStack_ok {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState} {layout : Miri.Interpreter.LocalLayout}
    {allocation : Miri.Memory.Allocation AnnealProv Unit} {mem' : AnnealMemory}
    {id : Miri.Memory.AllocId}
    (htry : Miri.Memory.Allocation.tryNew layout.layout.size layout.layout.align.abi .Uninit
      annealZeroedStorage = .ok allocation)
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id)) :
    (annealPlaceHooks ld ly).allocateStack () layout m =
      .ok ⟨stackAllocPlace id, layout⟩
        { m with machine := stackAllocMachine m.machine mem' id (allocation.withExtra none) } := by
  simp only [annealPlaceHooks, htry, hres, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, set, MonadStateOf.set, EStateM.set, pure, EStateM.pure]
  rfl

/-- Forward counterpart of
`annealPlaceHooks_writeMemoryNoValidate_fresh_inv`. -/
private theorem lm14_writeMemoryNoValidate_ok {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState} {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    {a0 alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {layout : Miri.Interpreter.LocalLayout} {s : Miri.Memory.Scalar AnnealProv}
    (hfresh : mem'.live.any (fun entry => entry.1 == id) = false)
    (hw : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO s.size) s a0 = .ok () alloc') :
    (annealPlaceHooks ld ly).writeMemoryNoValidate () (.scalar s) ⟨stackAllocPlace id, layout⟩
        { m with machine := stackAllocMachine m.machine mem' id a0 } =
      .ok () { m with machine := stackAllocMachine m.machine mem' id alloc' } := by
  have hbase := lookupBaseAddr_stackAllocMachine_self m.machine mem' id a0
  have hidx := findIdx?_push_fresh mem'.live id
    ({ kind := .stack, allocation := a0 } : Miri.Memory.LocalAllocation AnnealProv
      (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind) hfresh
  have hlive : (stackAllocMachine m.machine mem' id a0).memory.live =
      mem'.live.push (id, ⟨.stack, a0⟩) := rfl
  have hoff : Miri.ABI.Size.ofBytes
      ((Miri.ABI.Size.ofBytes (annealStackBaseAddr id)).bytes - annealStackBaseAddr id) =
      Miri.ABI.Size.ZERO := by
    simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
  simp only [annealPlaceHooks]
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, stackAllocPlace,
    Option.bind, Miri.Memory.Provenance.getAllocId, hbase, hlive, hidx,
    Array.getElem?_push_size, hoff, hw, pure, EStateM.pure, set, MonadStateOf.set, EStateM.set,
    array_push_set!_size]
  rfl

/-- `forceAllocation` succeeds on the immediate local `_1` of `lm14MoveMiri k`.
The do-block unfolds as in `forceAllocation_preserves_StateRel`, with each hook
leaf discharged forward. -/
private theorem lm14_forceAllocation_ok (k : Nat) :
    ∃ (mplace : Miri.Interpreter.MPlaceTy AnnealProv) (m' : AnnealStepState),
      Miri.Interpreter.forceAllocation
          (annealPlaceHooks lm14MoveBody.localDecls lm14MoveBody.layouts) ()
          ⟨.local 0 1 none (lm14MoveMiriFrame k).localsIdentity, translateTy u8Ty⟩
          (lm14MoveMiri k) = .ok mplace m' := by
  have hframes : (lm14MoveMiri k).stack.frames = #[lm14MoveMiriFrame k] := rfl
  have hlt : 1 < (lm14MoveMiriFrame k).locals.size := by simp [lm14MoveMiriFrame]
  have hdecl : get? lm14MoveBody.localDecls 1 = some u8Decl := rfl
  have hcache : ∀ l, ((lm14MoveMiriFrame k).locals[1]'hlt).layout = some l →
      l = translateTy u8Decl.ty lm14MoveBody.layouts := by
    intro l h
    cases h
  have hgo : (lm14MoveMiriFrame k).getLocalOperand 1 =
      .ok (.immediate (.scalar (.fromScalarInt lm14Scalar42))) := rfl
  -- The empty memory meets the premises of `reserve_of_highWater`.
  obtain ⟨mem', hres⟩ := Miri.Memory.MemoryState.reserve_of_highWater
    (Miri.Memory.MemoryState.empty : AnnealMemory) rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hfresh := (reserveAllocId_ok_live hres).2
  rw [← (reserveAllocId_ok_live hres).1] at hfresh
  obtain ⟨allocation, htry0, -⟩ :=
    Miri.Memory.Allocation.tryNew_replicate_full (P := AnnealProv) (translateSizeBytes 1)
      ⟨0⟩ 1 rfl rfl
  have htry : Miri.Memory.Allocation.tryNew
      (translateSizeBytes (⟨42, 1⟩ : MirAst.ScalarInt).sizeBytes) ⟨0⟩ .Uninit
      annealZeroedStorage = .ok allocation := htry0
  obtain ⟨alloc', hw, -⟩ := freshStackAlloc_writeScalar_readScalar lm14_scalarRel42 htry
  have htryL : Miri.Memory.Allocation.tryNew
      (translateTy u8Decl.ty lm14MoveBody.layouts).layout.size
      (translateTy u8Decl.ty lm14MoveBody.layouts).layout.align.abi .Uninit
      annealZeroedStorage = .ok allocation := htry0
  have hlt' : 1 < (cacheFrameLocalLayout (lm14MoveMiriFrame k) 1 hlt
      (translateTy u8Decl.ty lm14MoveBody.layouts)).locals.size := by
    rw [cacheFrameLocalLayout_size]; exact hlt
  have hval' : ((cacheFrameLocalLayout (lm14MoveMiriFrame k) 1 hlt
      (translateTy u8Decl.ty lm14MoveBody.layouts)).locals[1]'hlt').value =
      .live (.immediate (.scalar (.fromScalarInt lm14Scalar42))) := by
    simp [cacheFrameLocalLayout, lm14MoveMiriFrame]
  have hsized : (translateTy u8Decl.ty lm14MoveBody.layouts).layout.isSized = true := by decide
  unfold Miri.Interpreter.forceAllocation
  simp only [Miri.Interpreter.requireCurrent_eq,
    Miri.Interpreter.checkLocalIdentity_debugOff (annealPlaceHooks _ _) _ rfl,
    bind, EStateM.bind, annealPlaceHooks_frameIndex_eq hframes]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
    annealPlaceHooks_getFrame_eq hframes]
  rw [hgo, Miri.Interpreter.stackLift_ok]
  simp only [pure, EStateM.pure]
  rw [EStateM.bind_apply_ok (placeLayoutOfLocal_eq hframes hlt hdecl hcache)]
  simp only [hsized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [EStateM.bind_apply_ok (lm14_allocateStack_ok htryL hres)]
  rw [EStateM.bind_apply_ok (lm14_writeMemoryNoValidate_ok
    (m := { lm14MoveMiri k with stack := ⟨#[cacheFrameLocalLayout (lm14MoveMiriFrame k) 1 hlt
      (translateTy u8Decl.ty lm14MoveBody.layouts)]⟩ })
    (s := .fromScalarInt lm14Scalar42) hfresh hw)]
  simp only [EStateM.bind, pure, EStateM.pure, annealPlaceHooks_afterLocalMovedToMemory_eq,
    annealPlaceHooks_getFrame_mk, frame_setLocalOperand_live hlt' hval',
    Miri.Interpreter.stackLift_ok, annealPlaceHooks_setFrame_mk]
  exact ⟨_, _, rfl⟩

/-- `forceAllocation` succeeds on the immediate local `_1 = 42_u8` of
`lm14MoveMiri k`. Afterwards `_1` is memory-backed at exactly the returned
place, and the result is still related to the unchanged Anneal state
`lm14MoveAnneal k` by `StateRel` (`forceAllocation_preserves_StateRel`). -/
theorem lm14_forceAllocation_witness (k : Nat) :
    ∃ (mplace : Miri.Interpreter.MPlaceTy AnnealProv) (m' : AnnealStepState),
      Miri.Interpreter.forceAllocation
          (annealPlaceHooks lm14MoveBody.localDecls lm14MoveBody.layouts) ()
          ⟨.local 0 1 none (lm14MoveMiriFrame k).localsIdentity, translateTy u8Ty⟩
          (lm14MoveMiri k) = .ok mplace m' ∧
      (∃ tf' lay', m'.stack.frames = #[tf'] ∧
        tf'.locals[1]? = some ⟨.live (.indirect mplace.mplace), lay'⟩) ∧
      StateRel lm14MoveBody (lm14MoveAnneal k) m' := by
  obtain ⟨mplace, m', hforce⟩ := lm14_forceAllocation_ok k
  obtain ⟨hrel, hloc⟩ := forceAllocation_preserves_StateRel (lm14_stateRel k) hforce
  exact ⟨mplace, m', hforce, hloc 0 1 _ rfl, hrel⟩

/-! ## 5. Storage statements on a memory-backed local -/

/-- Anneal's state after `StorageLive(_1)` runs in `lm14MoveAnneal 0`: `_1` is
live and uninitialized. -/
def lm14LiveAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 1, locals := [.uninit, .uninit] }
    memory := (initMachineState lm14MoveBody []).memory }

/-- Anneal's state after `StorageDead(_1)` runs in `lm14MoveAnneal 4`: `_1` is
dead. -/
def lm14DeadAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 5, locals := [.uninit, .dead] }
    memory := (initMachineState lm14MoveBody []).memory }

/-- `StorageLive(_1)` (statement 0) after `forceAllocation` has moved `_1` into
memory: by `step_storageLive_simulation`, `lean-miri` frees the allocation,
steps normally, and stays related to Anneal's `lm14LiveAnneal`. -/
theorem lm14_storageLive_indirect_steps :
    ∃ (m : AnnealStepState) (mp : Miri.Interpreter.MemPlace AnnealProv)
      (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (lay : Option Miri.Interpreter.LocalLayout),
      m.stack.frames = #[tf] ∧ tf.locals[1]? = some ⟨.live (.indirect mp), lay⟩ ∧
      StateRel lm14MoveBody (lm14MoveAnneal 0) m ∧
      stepMirFn lm14MoveBody (lm14MoveAnneal 0) = .step lm14LiveAnneal ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks lm14MoveBody.localDecls lm14MoveBody.layouts) () m =
          (m', .ok true) ∧
        StateRel lm14MoveBody lm14LiveAnneal m' := by
  obtain ⟨mplace, m, -, ⟨tf, lay, hframes, hloc⟩, hrel⟩ := lm14_forceAllocation_witness 0
  have hstep : stepMirFn lm14MoveBody (lm14MoveAnneal 0) = .step lm14LiveAnneal := rfl
  have h := step_storageLive_simulation hrel lm14_phase rfl rfl
    (fun _ _ => .storageLive 1 u8Decl _ rfl)
  rw [hstep] at h
  refine ⟨m, mplace.mplace, tf, lay, hframes, hloc, hrel, hstep, ?_⟩
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm14MoveBody.localDecls lm14MoveBody.layouts) () m = r at h ⊢
  cases h with
  | step s' m' hrel' => exact ⟨m', rfl, hrel'⟩

/-- `StorageDead(_1)` (statement 4) after `forceAllocation` has moved `_1` into
memory: by `step_storageDead_simulation`, `lean-miri` frees the allocation,
steps normally, and stays related to Anneal's `lm14DeadAnneal`. -/
theorem lm14_storageDead_indirect_steps :
    ∃ (m : AnnealStepState) (mp : Miri.Interpreter.MemPlace AnnealProv)
      (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (lay : Option Miri.Interpreter.LocalLayout),
      m.stack.frames = #[tf] ∧ tf.locals[1]? = some ⟨.live (.indirect mp), lay⟩ ∧
      StateRel lm14MoveBody (lm14MoveAnneal 4) m ∧
      stepMirFn lm14MoveBody (lm14MoveAnneal 4) = .step lm14DeadAnneal ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks lm14MoveBody.localDecls lm14MoveBody.layouts) () m =
          (m', .ok true) ∧
        StateRel lm14MoveBody lm14DeadAnneal m' := by
  obtain ⟨mplace, m, -, ⟨tf, lay, hframes, hloc⟩, hrel⟩ := lm14_forceAllocation_witness 4
  have hstep : stepMirFn lm14MoveBody (lm14MoveAnneal 4) = .step lm14DeadAnneal := rfl
  have h := step_storageDead_simulation hrel lm14_phase rfl rfl
    (fun _ _ => .storageDead 1 u8Decl _ rfl (by decide))
  rw [hstep] at h
  refine ⟨m, mplace.mplace, tf, lay, hframes, hloc, hrel, hstep, ?_⟩
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm14MoveBody.localDecls lm14MoveBody.layouts) () m = r at h ⊢
  cases h with
  | step s' m' hrel' => exact ⟨m', rfl, hrel'⟩

end LeanMiriSpec.Correspondence.Witness
