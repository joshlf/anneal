/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM3_2
import LeanMiriSpec.Correspondence.WitLM3_1

/-!
# Witnesses for the `LM-3.2` Correspondence

Concrete, kernel-checked instances of the `LM-3.2` theorems on the body
`lm32RefBody`:

```text
bb0: StorageLive(_1); StorageLive(_2);
     _1 = const 42_u64;
     _2 = &_1;
     _0 = copy *_2;
     StorageDead(_2); StorageDead(_1); return
```

1. **`wit_lm3_2_ref_step`**: `evalRvalue_ref_simulation` applies to `_2 = &_1`
   from pointer-free `StateRel` states; both machines take the step
   (`lean-miri` promoting `_1` into a stack allocation) to `StateRelLM3_2`-related
   states with a non-empty `allocMap`.
2. **`wit_lm3_2_validity_visitor_runs`**: the vendored
   `ValidityVisitor.validatePlace`, instantiated by `annealValidityHooks`, runs
   end to end: it accepts `true` and rejects the byte `2` at `bool`, accepts
   and rejects code points at `char`, rejects every value of `!`, and accepts
   a reference into a live allocation while rejecting the same reference once
   the allocation is freed.
-/

namespace LeanMiriSpec.Correspondence.Witness

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ## 1. `_2 = &_1` -/

/-- `&u64`. -/
def refU64Ty : Ty := { kind := .ref .not (.uint .u64), layoutIdx := 0 }

/-- Local declaration of type `&u64`. -/
def refU64Decl : LocalDecl := { mutability := .mut, ty := refU64Ty, debugName := none }

/-- `Runtime(PostCleanup)` MIR body that borrows the immediate scalar local
`_1 = 42_u64` as `_2 = &_1` and reads it back through the reference. -/
def lm32RefBody : CapturedMir where
  defPath := "lm_3_2_witness::ref_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, refU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 1) (.use (.constant (constU64 42)))),
        mkStmt (.assign (local_ 2) (.ref .shared (local_ 1))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 2)))),
        mkStmt (.storageDead 2),
        mkStmt (.storageDead 1)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal state before statement 3 (`_2 = &_1`) of `lm32RefBody`. -/
def lm32RefAnnealPre : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 3
        locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit] }
    memory := (initMachineState lm32RefBody []).memory }

/-- `lean-miri` root frame matching `lm32RefAnnealPre`. -/
def lm32RefMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm32RefBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy u64Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
        layout := some (translateTy u64Ty) },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 3⟩ }

/-- `lean-miri` state matching `lm32RefAnnealPre`. -/
def lm32RefMiriPre : AnnealStepState :=
  { stack := ⟨#[lm32RefMiriFramePre]⟩, machine := AnnealMachine.empty }

/-- `StateRel` holds between `lm32RefAnnealPre` and `lm32RefMiriPre`. -/
theorem lm32Ref_stateRel_pre :
    StateRel lm32RefBody lm32RefAnnealPre lm32RefMiriPre := by
  refine StateRel.mk lm32RefMiriFramePre rfl rfl ⟨translateTy u64Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i j mplace_i mplace_j lay_i lay_j hneq hi hj
      revert hi
      match i with
      | 0 => rintro ⟨⟩
      | 1 => rintro ⟨⟩
      | 2 => rintro ⟨⟩
      | _ + 3 => rintro ⟨⟩)
  refine
    { body_eq := rfl
      location_eq := rfl
      af_locals_len := rfl
      mf_locals_size := rfl
      locals_rel := ?_ }
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = u64Decl := by simpa [lm32RefBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm32RefAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm32RefMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = u64Decl := by simpa [lm32RefBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by
      simpa [lm32RefAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
          layout := some (translateTy u64Ty) } := by
      simpa [lm32RefMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | 2 =>
    have hd : decl = refU64Decl := by simpa [lm32RefBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm32RefAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm32RefMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | n + 3 =>
    simp [lm32RefBody, get?] at hdecl

/-- `_1` and `_2` are immediate in `lm32RefMiriPre`. -/
theorem lm32Ref_immediate_pre :
    ∀ topFrame, lm32RefMiriPre.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame 2 ∧ IsImmediateFrameLocal topFrame 1 := by
  intro topFrame h
  injection h with h₁
  injection h₁ with h₂
  subst h₂
  refine ⟨?_, ?_⟩ <;> intro mls hmls mp hmp <;>
    simp [lm32RefMiriFramePre] at hmls <;> subst hmls <;> cases hmp

/-- **`wit_lm3_2_ref_step`**: `evalRvalue_ref_simulation` applies to statement
3 (`_2 = &_1`) of `lm32RefBody` from the pointer-free states of
`lm32Ref_stateRel_pre`. Both machines take the step (`lean-miri` moving `_1`
into the fresh allocation `lm31AllocId1`), and the resulting states are
related by `StateRelLM3_2` under the shared-borrow entry `(tag 1, _1,
lm31AllocId1)`. -/
theorem wit_lm3_2_ref_step :
    ∃ (s' : MachineState) (m' : AnnealStepState),
      stepMirFn lm32RefBody lm32RefAnnealPre = .step s' ∧
      Miri.Interpreter.Step.step
          (annealStepHooks lm32RefBody.localDecls lm32RefBody.layouts) ()
          lm32RefMiriPre = (m', .ok true) ∧
      StateRelLM3_2 lm32RefBody s' m'
        [refAllocMapEntry lm32RefBody.localDecls lm32RefBody.layouts .shared 1 1
          lm31AllocId1] := by
  have hsim := evalRvalue_ref_simulation (body := lm32RefBody)
    (s := lm32RefAnnealPre) (m := lm32RefMiriPre) lm32Ref_stateRel_pre.toLM3_1.toLM3_2
    (by intro p h; cases h) (dstIdx := 2) (targetIdx := 1) (bk := .shared)
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    lm32Ref_immediate_pre AllocIdSupplyReady.empty
  have hstep : (match stepMirFn lm32RefBody lm32RefAnnealPre with
      | .tau (.running _) => true
      | _ => false) = true := by decide
  generalize hA : stepMirFn lm32RefBody lm32RefAnnealPre = aRes at hsim hstep
  generalize hres : Miri.Interpreter.Step.step
    (annealStepHooks lm32RefBody.localDecls lm32RefBody.layouts) ()
    lm32RefMiriPre = res at hsim
  cases hsim with
  | step s' m' hrel =>
    have htag : lm32RefAnnealPre.memory.nextTag = 1 := by decide
    have hid : (⟨lm32RefMiriPre.machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag, hid] at hrel
    exact ⟨s', m', rfl, rfl, hrel⟩
  | retRoot _ _ _ _ _ _ _ _ _ => simp [MirStepNode.retNormal] at hstep
  | ub _ _ => simp [MirStepNode.fail] at hstep

/-! ## 2. The Vendored Validity Visitor, End to End -/

/-- A one-local root frame holding the immediate `v`, for running the
validity visitor on a concrete place. -/
def lm32ValidityFrame (v : Miri.Interpreter.Immediate AnnealProv) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm32RefBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy u64Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[{ value := .live (.immediate v), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- The state whose only frame is `lm32ValidityFrame v`, with no allocations. -/
def lm32ValidityState (v : Miri.Interpreter.Immediate AnnealProv) : AnnealStepState :=
  { stack := ⟨#[lm32ValidityFrame v]⟩, machine := AnnealMachine.empty }

/-- Run `ValidityVisitor.validatePlace` (non-recursive, without reset) under
`annealValidityHooks` on local `_0` of `lm32ValidityState v` at type `ty`. -/
def lm32Validate (ty : Ty) (v : Miri.Interpreter.Immediate AnnealProv) :
    EStateM.Result Miri.Interpreter.StepError AnnealStepState Unit :=
  Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks emptyLayoutTable) ty 4
    ⟨.local 0 0 none (.ofAllocationToken 0), translateTy ty⟩ false false
    (lm32ValidityState v)

/-- `char` as an Anneal type. -/
def charTyLM32 : Ty := { kind := .char, layoutIdx := 0 }

/-- `bool` as an Anneal type. -/
def boolTyLM32 : Ty := { kind := .bool, layoutIdx := 0 }

/-- `!` as an Anneal type. -/
def neverTyLM32 : Ty := { kind := .never, layoutIdx := 0 }

/-- **`wit_lm3_2_validity_visitor_runs`**: the vendored validity visitor
(`ValidityVisitor.validatePlace`, `visit`, `primitive`, `checkSafe`), run
under `annealValidityHooks`, returns exactly the verdict of Anneal's typed
invariants (`AnnealScalarValid`, `decodeValueFromBytes`, and reference
dereferenceability):

* `bool`: `1` is valid, the byte `2` is undefined behavior;
* `char`: `U+0041` is valid, the surrogate `0xD800` is undefined behavior;
* `!`: every value, even an uninitialized one, is undefined behavior;
* `&u64`: a reference into an allocation that is not live (the state of a
  pointee after `StorageDead`) and the null reference are undefined
  behavior. -/
theorem wit_lm3_2_validity_visitor_runs :
    lm32Validate boolTyLM32 (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 1))) =
      .ok () (lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 1)))) ∧
    (∃ msg, lm32Validate boolTyLM32 (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 2))) =
      .error (.undefinedBehavior msg)
        (lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 2))))) ∧
    lm32Validate charTyLM32 (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 0x41))) =
      .ok () (lm32ValidityState
        (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 0x41)))) ∧
    (∃ msg, lm32Validate charTyLM32
        (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 0xD800))) =
      .error (.undefinedBehavior msg)
        (lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 0xD800))))) ∧
    (∃ msg, lm32Validate neverTyLM32 .uninit =
      .error (.undefinedBehavior msg) (lm32ValidityState .uninit)) ∧
    (∃ msg, lm32Validate refU64Ty
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
            .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩)) =
      .error (.undefinedBehavior msg)
        (lm32ValidityState (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
            .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩)))) ∧
    (∃ msg, lm32Validate refU64Ty (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0))) =
      .error (.undefinedBehavior msg)
        (lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0))))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · exact ⟨_, by with_unfolding_all rfl⟩
  · with_unfolding_all rfl
  · exact ⟨_, by with_unfolding_all rfl⟩
  · exact ⟨_, by with_unfolding_all rfl⟩
  · exact ⟨_, by with_unfolding_all rfl⟩
  · exact ⟨_, by with_unfolding_all rfl⟩

end LeanMiriSpec.Correspondence.Witness
