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

1. **`wit_lm3_2_ref_step` & `wit_lm3_2_ref_deref_read_storageDead_real_steps`**:
   `evalRvalue_ref_simulation`, `step_safeRef_deref_read_simulation_explicit`,
   and `step_storageDead_lm3_2_simulation` execute `lm32RefBody` (`_2 = &_1` ->
   `_0 = copy *_2` -> `StorageDead(_2)` -> `StorageDead(_1)`) from pointer-free
   `StateRel` states through `StateRelLM3_2`-related states at every step,
   reading `42_u64` into `_0` and freeing `lm31AllocId1` on `StorageDead(_1)`.
2. **`wit_lm3_2_validity_visitor_runs` &
   `wit_lm3_2_recursive_ref_pointee_validity`**: the vendored
   `ValidityVisitor.validatePlace`, instantiated by `annealValidityHooks`, runs
   end to end both shallowly (`recursive = false`) and recursively through
   `RefTracking` (`recursive = true`), distinguishing shallow reference
   dereferenceability from deep pointee initialization and `bool` validity.
3. **`wit_lm3_2_mut_ref_move_write_read_reborrow_real_steps`**: 5-step execution
   of `&mut _1` -> `_3 = move _2` -> `*_3 = 99_u64` -> `_0 = copy *_3` ->
   `_4 = &*_3` across `evalRvalue_ref_simulation`, `step_safeRef_use_simulation`,
   `step_safeRef_deref_write_simulation_explicit`,
   `step_safeRef_deref_read_simulation_explicit`, and
   `evalRvalue_reborrow_safeRef_simulation`.
4. **`wit_lm3_2_safeRef_dangling_reborrow_and_rawPtr_int_divergences`**:
   concrete real-step witnesses for both
   `evalRvalue_reborrow_safeRef_dangling_divergence` (`&*_2` after
   `StorageDead(_1)`: Anneal steps while `Step.step` fails with
   `"dereferencing a dangling reference"`) and
   `evalRvalue_reborrow_rawPtr_int_divergence` (`&*_1` on an integer-valued raw
   pointer: Anneal fails with UB while `Step.step` steps).
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

/-! ## 3. Multi-Step Real-Step Chains (`&_1`, `&mut _1`, `move`, `*_r`, `&*_r`, `StorageDead`) -/

/-- Decidable check that local `idx` in `st`'s top frame is not `.indirect`. -/
def checkImmediateInTopFrame (st : AnnealStepState) (idx : Nat) : Bool :=
  match st.stack.frames[0]? with
  | some tf =>
    match tf.locals[idx]? with
    | some mls =>
      match mls.value with
      | .live (.indirect _) => false
      | _ => true
    | none => true
  | none => false

/-- Soundness of `checkImmediateInTopFrame` for `IsImmediateFrameLocal`. -/
theorem isImmediate_of_checkImmediateInTopFrame {st : AnnealStepState} {idx : Nat}
    (hchk : checkImmediateInTopFrame st idx = true) :
    ∀ topFrame, st.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame idx := by
  intro topFrame hframes mls hmls mp hmp
  have hf0 : st.stack.frames[0]? = some topFrame := by rw [hframes]; rfl
  unfold checkImmediateInTopFrame at hchk
  rw [hf0] at hchk
  dsimp only [] at hchk
  rw [hmls] at hchk
  dsimp only [] at hchk
  rw [hmp] at hchk
  cases hchk

private def mkWitStateLM32 (body : CapturedMir) (stmtIdx : Nat) (locals : List LocalSlot)
    (borrows : List BorrowEntry) (nextTag : Nat) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := stmtIdx, locals := locals }
    memory := { (initMachineState body []).memory with
                  borrows := borrows, nextTag := nextTag } }

private theorem stepRelLM3_2_of_anneal_step
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {s' : MachineState}
    (hsim : StepRelLM3_2 body m allocMap aRes mRes)
    (ha : aRes = .step s') :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_2 body s' m' allocMap := by
  cases hsim with
  | step s₁ m' hrel =>
    injection ha with htau
    injection htau with hs
    subst hs
    exact ⟨m', rfl, hrel⟩
  | retRoot _ _ _ _ _ _ _ _ _ => cases ha
  | ub _ _ => cases ha

private theorem constU64_wellTypedLM32 (body : CapturedMir)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hcan : n < scalarModulus 8) :
    WellTypedScalarOperand body tf (.constant (constU64 n)) u64Ty :=
  .constScalar (constU64 n) ⟨n, 8⟩ rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hcan rfl (fun h => nomatch h) (fun h => nomatch h)

private theorem ptrVal_of_some_initLM32 {p q : ProvenancePtr}
    (h : some (LocalSlot.init (.ptr p 8)) = some (LocalSlot.init (.ptr q 8))) : q = p := by
  injection h with h₁; injection h₁ with h₂; injection h₂ with h₃ _; exact h₃.symm

private theorem step_ref_preserves_ne
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    (hstate : StateRel body s m)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {bk : BorrowKind} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (htgt_ty : IsPrimScalarTy targetDecl.ty)
    (hne : dstIdx ≠ targetIdx)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame targetIdx)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    ∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, k ≠ targetIdx → IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_dst, himm_tgt⟩ := himm tf hframes
  obtain ⟨_, mls_d, _, hlt_d, _, hmls_d, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.layout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hfra : FrameRel body m.machine s.frame tfa := hfr.cache_local_layout hdecl_dst hlt_d
  obtain ⟨_, mls_t, _, hlt_t, _, hmls_t, hmls_t_eq, hloc_t⟩ := hfra.lookup_local hdecl_tgt
  have hcache_t : ∀ l, (tfa.locals[targetIdx]'hlt_t).layout = some l →
      l = translateTy targetDecl.ty body.layouts := by
    rw [hmls_t_eq]; exact hloc_t.layout_eq
  have htgt_eval := annealEvalPlace_unprojected (m := { m with stack := ⟨#[tfa]⟩ }) rfl hlt_t
    hdecl_tgt hcache_t
  let tfb := cacheFrameLocalLayout tfa targetIdx hlt_t (translateTy targetDecl.ty body.layouts)
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
          (.Ref .Erased (translateBorrowKind bk) ⟨targetIdx, #[]⟩) ⟨dstIdx, #[]⟩) m := rfl
  have hval_tb : (tfb.locals[targetIdx]'(by rw [cacheFrameLocalLayout_size]; exact hlt_t)).value =
      mls_t.value := by
    simp [tfb, cacheFrameLocalLayout, hmls_t_eq]
  cases hloc_t with
  | indirect _ mp _ _ _ _ =>
    exact absurd rfl (himm_tgt.cache_layout hlt_d _ _ hmls_t mp)
  | dead _ _ =>
    have hforce := annealForceAllocation_dead_eq (ld := body.localDecls) (ly := body.layouts)
      (m := { m with stack := ⟨#[tfb]⟩ }) rfl
      (by rw [cacheFrameLocalLayout_size]; exact hlt_t) hval_tb
      (translateTy targetDecl.ty body.layouts)
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "address of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [evalRvalueIntoPlace_ref_force_error (region := .Erased)
        (borrow := translateBorrowKind bk) hdst_eval htgt_eval hforce]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err] at hstep
    cases hstep
  | immediate _ imm _ _ hval =>
    have hlt_tb : targetIdx < tfb.locals.size := by
      rw [cacheFrameLocalLayout_size]; exact hlt_t
    have hlay_tb : (tfb.locals[targetIdx]'hlt_tb).layout =
        some (translateTy targetDecl.ty body.layouts) := by
      simp [tfb, cacheFrameLocalLayout]
    obtain ⟨hsized, allocation, htry⟩ := htgt_ty.layout_ok (layouts := body.layouts)
    obtain ⟨mem', hres⟩ := hsupply.reserve_eq
    let freshId : Miri.Memory.AllocId := ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩
    obtain ⟨alloc', hfill⟩ :
        ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
          (imm = .uninit ∧ alloc' = allocation.withExtra none) ∨
          ∃ sc, imm = .scalar sc ∧
            Miri.Memory.Allocation.writeScalar annealTargetDataLayout
              (Miri.Memory.allocRange Miri.ABI.Size.ZERO sc.size) sc
              (allocation.withExtra none) = .ok () alloc' := by
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · exact ⟨allocation.withExtra none, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨sc, msc, rfl, rfl, hrel, hsz, _, _⟩ := himmRel.of_primitive_scalar htgt_ty
        have htry' : Miri.Memory.Allocation.tryNew (translateSizeBytes sc.sizeBytes)
            (translateTy targetDecl.ty body.layouts).layout.align.abi .Uninit
            annealZeroedStorage = .ok allocation := hsz ▸ htry
        obtain ⟨alloc'', hw'', -⟩ := freshStackAlloc_writeScalar_readScalar hrel htry'
        exact ⟨alloc'', Or.inr ⟨_, rfl, hw''⟩⟩
    have hforce₀ := forceAllocation_promote_eq (m := { m with stack := ⟨#[tfb]⟩ }) rfl hdecl_tgt
      hlt_tb hlay_tb hval_tb hsized htry hres hfill
    have hforce : annealForceAllocation body.localDecls body.layouts
        ⟨.local 0 targetIdx none tf.localsIdentity, translateTy targetDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } =
        .ok (stackAllocPlace freshId)
          { stack := ⟨#[{ tfb with
              locals := tfb.locals.set targetIdx
                { tfb.locals[targetIdx]'hlt_tb with
                  value := .live (.indirect (stackAllocPlace freshId)) }
                hlt_tb }]⟩
            machine := stackAllocMachine m.machine mem' freshId alloc' } := by
      unfold annealForceAllocation; erw [hforce₀]
    have hrv := evalRvalueIntoPlace_ref_ok (region := .Erased)
      (borrow := translateBorrowKind bk) hdst_eval htgt_eval hforce (stackAllocPlace_toRef freshId)
    let tfc : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
      { tfb with
        locals := tfb.locals.set targetIdx
          { tfb.locals[targetIdx]'hlt_tb with
            value := .live (.indirect (stackAllocPlace freshId)) }
          hlt_tb }
    let machc := stackAllocMachine m.machine mem' freshId alloc'
    have hdc_eq : tfc.locals[dstIdx]? =
        some { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } := by
      simp only [tfc, tfb, tfa, cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hne), Array.getElem?_set_ne _ (Ne.symm hne),
        Array.getElem?_set_self, hmls_d_eq]
    obtain ⟨hlt_dc, -⟩ := Array.getElem?_eq_some_iff.mp hdc_eq
    have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_eq
    cases hloc_d with
    | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst _ hmls_d mp)
    | dead _ _ =>
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩) m =
          (⟨⟨#[tfc]⟩, machc⟩, .error (.undefinedBehavior "write to dead local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        rw [hrv, annealWriteImmediate_dead (m := ⟨⟨#[tfc]⟩, machc⟩) (id0 := tf.localsIdentity)
          rfl hget_dc]
      rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err] at hstep
      cases hstep
    | immediate _ _ _ _ _ =>
      have hw := annealWriteImmediate_live
        (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr freshId),
            .concrete freshId Miri.Memory.BorTag.one⟩))
        (m := ⟨⟨#[tfc]⟩, machc⟩) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dc hget_dc
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩) m =
          ({ (⟨⟨#[tfc]⟩, machc⟩ : AnnealStepState) with
              stack := ⟨#[{ tfc with
                locals := tfc.locals.set dstIdx
                  { tfc.locals[dstIdx]'hlt_dc with
                    value := .live (.immediate (.scalar
                      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr freshId),
                          .concrete freshId Miri.Memory.BorTag.one⟩))) }
                  hlt_dc }]⟩ },
            .ok ()) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
      rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
        hfr.location_eq] at hstep
      injection hstep with hm' _
      subst hm'
      intro tf₀ tf' htf₀ htf' k hk_ne hk mls' hmls' mp hmp
      rw [hframes] at htf₀
      injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
      injection htf' with h₁; injection h₁ with h₁'; subst h₁'
      dsimp only [] at hmls'
      rw [Array.getElem?_set] at hmls'
      by_cases hdk : dstIdx = k
      · subst hdk
        simp only [↓reduceIte, Option.some.injEq] at hmls'
        rw [← hmls'] at hmp; cases hmp
      · simp only [hdk, ↓reduceIte, tfc] at hmls'
        rw [Array.getElem?_set_ne _ (Ne.symm hk_ne)] at hmls'
        exact ((hk.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)).cache_layout hlt_t
          (translateTy targetDecl.ty body.layouts)) mls' hmls' mp hmp

private theorem step_storageDead_lm3_2_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne0 : loc ≠ 0)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    ∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls, _, hlt_mf, _, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hlive : LocalAllocLive m.machine.memory (tf.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m =
      ({ stack := ⟨#[{ tf with
            locals := tf.locals.set loc
              { tf.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (tf.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
    exact annealStepHooks_storageDead_any_eq hframes hlt_mf hne0 hlive
  rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq] at hstep
  injection hstep with hm' _
  subst hm'
  intro tf₀ tf' htf₀ htf' k hk mls' hmls' mp hmp
  rw [hframes] at htf₀
  injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
  injection htf' with h₁; injection h₁ with h₁'; subst h₁'
  dsimp only [] at hmls'
  rw [Array.getElem?_set] at hmls'
  by_cases hlk : loc = k
  · subst hlk; simp only [↓reduceIte, Option.some.injEq] at hmls'; rw [← hmls'] at hmp; cases hmp
  · simp only [hlk, ↓reduceIte] at hmls'; exact hk mls' hmls' mp hmp

private theorem step_safeRef_move_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl : LocalDecl} {srcMut : Mutability} {srcPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .ref srcMut srcPointee)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    ∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_dst, himm_src⟩ := himm tf hframes
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨dstIdx, .nil⟩ (.move ⟨srcIdx, .nil⟩) span m
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_move : translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ := rfl
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨_, mls_s, _, hlt_sa, _, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx :=
    himm_src.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  have himm_d_tfa : IsImmediateFrameLocal tfa dstIdx :=
    himm_dst.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by
    rw [cacheFrameLocalLayout_size]; exact hlt_sa
  let tf_mid := deinitFrameLocal tfb srcIdx hlt_sb
  have himm_d_mid : IsImmediateFrameLocal tf_mid dstIdx :=
    (himm_d_tfa.cache_layout hlt_sa (translateTy srcDecl.ty body.layouts)).deinit_local hlt_sb
  have hfinish_imm : ∀ (newImm : Miri.Interpreter.Immediate AnnealProv),
      Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate newImm
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tf_mid]⟩ } →
      ∀ tf₀ tf', m.stack.frames = #[tf₀] → m'.stack.frames = #[tf'] →
        ∀ k, IsImmediateFrameLocal tf₀ k → IsImmediateFrameLocal tf' k := by
    intro newImm hm_w
    have hlt_dm : dstIdx < tf_mid.locals.size := by
      simp only [tf_mid, deinitFrameLocal, Array.size_set, tfb, tfa, cacheFrameLocalLayout_size]
      exact hlt_d
    rcases hdm : tf_mid.locals[dstIdx]'hlt_dm with ⟨vd, ld⟩
    have hdm_opt : tf_mid.locals[dstIdx]? = some ⟨vd, ld⟩ := by
      rw [Array.getElem?_eq_getElem hlt_dm, hdm]
    have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_opt
    cases vd with
    | dead =>
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
          ({ m with stack := ⟨#[tf_mid]⟩ },
            .error (.undefinedBehavior "write to dead local")) := by
        rw [hm_w]; unfold Miri.Interpreter.runRvalue
        rw [annealWriteImmediate_dead (m := { m with stack := ⟨#[tf_mid]⟩ })
          (id0 := tf.localsIdentity) rfl hget_dm]
      rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        at hstep
      cases hstep
    | live opd =>
      cases opd with
      | indirect mp => exact absurd rfl (himm_d_mid _ hdm_opt mp)
      | immediate oldImm =>
        have hw_ok := annealWriteImmediate_live (val := newImm)
          (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
          (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dm hget_dm
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
            ({ m with stack := ⟨#[{ tf_mid with
                locals := tf_mid.locals.set dstIdx
                  { tf_mid.locals[dstIdx]'hlt_dm with value := .live (.immediate newImm) }
                  hlt_dm }]⟩ }, .ok ()) := by
          rw [hm_w]; unfold Miri.Interpreter.runRvalue; rw [hw_ok]
        have hloc_mid : tf_mid.location = tf.location := rfl
        rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
          (hloc_mid.trans hfr.location_eq)] at hstep
        injection hstep with hm' _
        subst hm'
        intro tf₀ tf' htf₀ htf' k hk mls' hmls' mp hmp
        rw [hframes] at htf₀
        injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
        injection htf' with h₁; injection h₁ with h₁'; subst h₁'
        dsimp only [] at hmls'
        rw [Array.getElem?_set] at hmls'
        by_cases hdk : dstIdx = k
        · subst hdk; simp only [↓reduceIte, Option.some.injEq] at hmls'
          rw [← hmls'] at hmp; cases hmp
        · simp only [hdk, ↓reduceIte] at hmls'
          exact (((hk.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb)
            mls' hmls' mp hmp
  rcases hloc_s.ref_immediate_cases hsrc_ty (himm_s_tfa mls_s hmls_s) with
    ⟨_, hms_dead⟩ | ⟨_, hms_un⟩ | ⟨_, msc_s, _, _, _, hms_sc⟩ | ⟨_, mptr, _, _, hms_ptr⟩
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_dead; subst hms_dead; rfl
    have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      at hstep
    cases hstep
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_un; subst hms_un; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
        ({ m with stack := ⟨#[tf_mid]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      at hstep
    cases hstep
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc_s))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_sc; subst hms_sc; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
    exact hfinish_imm (.scalar (.fromScalarInt msc_s)) (by
      rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl)
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_ptr; subst hms_ptr; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
    exact hfinish_imm (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)) (by
      rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl)

private theorem step_safeRef_deref_write_const_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {bb : BasicBlockData} {refIdx : Local} {c : ConstOperand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use (.constant c)), span⟩)
    {refDecl : LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hval_prim : IsPrimScalarTy c.ty)
    (hval_kind : c.ty.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame (.constant c) c.ty)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal e tgtDecl,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
        tgtDecl.ty.kind = pointeeKind)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    ∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  have himm_r := himm_ref tf hframes
  have hop_tf := hop tf hframes
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨refIdx, .cons .deref .nil⟩ (.constant c) span m
  obtain ⟨slot_r, mls_r, _, hlt_r, hslot_r, hmls_r, hmls_r_eq, hloc_r⟩ :=
    hfr.lookup_local hdecl_ref
  have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
    hloc_r.cachedLayout_eq
  let tfa := cacheFrameLocalLayout tf refIdx hlt_r (translateTy refDecl.ty body.layouts)
  have hstate_a : StateRelLM3_2 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_ref hlt_r
  have hop_tfa : WellTypedScalarOperand body tfa (.constant c) c.ty :=
    hop_tf.of_cacheFrameLocalLayout refIdx hlt_r (translateTy refDecl.ty body.layouts)
  have hpt_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 } := by
    rcases hval_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact Or.inl (hval_kind ▸ hk)
    · exact Or.inr (Or.inl (hval_kind ▸ hk))
    · exact Or.inr (Or.inr (Or.inl ⟨it, hval_kind ▸ hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ut, hval_kind ▸ hk⟩))
  have hlay0_eq : translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts =
      translateTy c.ty body.layouts := by
    have h1 := hval_prim.translateTy_layoutIdx body.layouts
    rw [hval_kind] at h1; exact h1
  rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
    ⟨_, hmr_dead⟩ | ⟨_, hmr_un⟩ | ⟨sc_r, msc_r, _, hsz8_r, hrel_r, hmr_sc⟩ |
    ⟨ptrVal, mptr, hsr_ptr, hptrRel, hmr_ptr⟩
  · have hmls_r' : tf.locals[refIdx]'hlt_r = ⟨.dead, mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_dead; subst hmr_dead; rfl
    have hdst_err := annealEvalPlace_deref_dead hframes hlt_r hdecl_ref hmls_r' hcache_r
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use (.constant c)), span⟩) m =
        ({ m with stack := ⟨#[tfa]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hdst_err]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err] at hstep
    cases hstep
  · have hmls_r' : tf.locals[refIdx]'hlt_r = ⟨.live (.immediate .uninit), mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_un; subst hmr_un; rfl
    have hdst_live := annealEvalPlace_deref_live hframes hlt_r hdecl_ref hmls_r' hcache_r
    have hder_err := annealDerefOperandToMemPlace_safeRef_uninit (ly := body.layouts)
      hdecl_ref href_ty hpt_prim (translateTy refDecl.ty body.layouts) { m with stack := ⟨#[tfa]⟩ }
    have hdst_err : annealEvalPlace body.localDecls body.layouts
        (translatePlace ⟨refIdx, .cons .deref .nil⟩) m =
        .error (.undefinedBehavior "read of uninitialized local") { m with stack := ⟨#[tfa]⟩ } := by
      rw [hdst_live, EStateM.bind_eq_error hder_err]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use (.constant c)), span⟩) m =
        ({ m with stack := ⟨#[tfa]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hdst_err]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err] at hstep
    cases hstep
  · have hmls_r' : tf.locals[refIdx]'hlt_r =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc_r))), mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_sc; subst hmr_sc; rfl
    have hdst_live := annealEvalPlace_deref_live hframes hlt_r hdecl_ref hmls_r' hcache_r
    have hsc_chk := annealDerefOperandToMemPlace_safeRef_scalarInt (ly := body.layouts)
      hdecl_ref href_ty hpt_prim hrel_r hsz8_r (translateTy refDecl.ty body.layouts)
      { m with stack := ⟨#[tfa]⟩ }
    obtain ⟨msg, hdst_err⟩ : ∃ msg, annealEvalPlace body.localDecls body.layouts
        (translatePlace ⟨refIdx, .cons .deref .nil⟩) m =
        .error (.undefinedBehavior msg) { m with stack := ⟨#[tfa]⟩ } := by
      by_cases h0 : sc_r.bits = 0
      · exact ⟨_, by rw [hdst_live, EStateM.bind_eq_error (hsc_chk.1 h0)]⟩
      · exact ⟨_, by rw [hdst_live, EStateM.bind_eq_error (hsc_chk.2 h0)]⟩
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use (.constant c)), span⟩) m =
        ({ m with stack := ⟨#[tfa]⟩ }, .error (.undefinedBehavior msg)) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hdst_err]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err] at hstep
    cases hstep
  · subst hsr_ptr
    have hmls_r' : tf.locals[refIdx]'hlt_r =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
    have hdst_live := annealEvalPlace_deref_live hframes hlt_r hdecl_ref hmls_r' hcache_r
    obtain ⟨_, borTag, hprov_eq, hid_lt, _, hmptr_off, ⟨e, he, htag, rfl⟩⟩ := id hptrRel
    obtain ⟨tgtDecl, hdecl_tgt, htgt_prim⟩ := halloc.target_decl e he
    obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
    obtain ⟨slot_t, _, _, _, hslot_t, _, _, _⟩ := hfr.lookup_local hdecl_tgt
    by_cases ht_dead : slot_t = .dead
    · have hdead_t : get? s.frame.locals e.localIdx = some .dead :=
        hslot_t.trans (congrArg some ht_dead)
      have hder_err := annealDerefOperandToMemPlace_safeRef_ptr_dead hstate hdecl_ref href_ty
        hpt_prim hptrRel he htag hdead_t (translateTy refDecl.ty body.layouts)
        (st := { m with stack := ⟨#[tfa]⟩ }) rfl
      have hdst_err : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨refIdx, .cons .deref .nil⟩) m =
          .error (.undefinedBehavior "dereferencing a dangling reference")
            { m with stack := ⟨#[tfa]⟩ } := by
        rw [hdst_live, EStateM.bind_eq_error hder_err]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use (.constant c)), span⟩) m =
          ({ m with stack := ⟨#[tfa]⟩ },
            .error (.undefinedBehavior "dereferencing a dangling reference")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hdst_err]
      rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        at hstep
      cases hstep
    · have hs_not_dead : get? s.frame.locals e.localIdx ≠ some .dead := by
        rw [hslot_t]; exact fun h => ht_dead (Option.some.inj h)
      obtain ⟨hoff0, _, htgt_kind⟩ :=
        hlive_ref ptrVal e tgtDecl hslot_r he htag hdecl_tgt hs_not_dead
      have hkind_all : ∀ d, get? body.localDecls e.localIdx = some d → d.ty.kind = pointeeKind := by
        intro d hd; rw [hdecl_tgt] at hd; injection hd with hd_eq; subst hd_eq; exact htgt_kind
      have hder_ok := annealDerefOperandToMemPlace_safeRef_ptr_live hstate hdecl_ref href_ty
        hpt_prim hprov_eq hmptr_off he hoff0 hs_not_dead hkind_all
        (translateTy refDecl.ty body.layouts) (st := { m with stack := ⟨#[tfa]⟩ }) rfl
      rw [hlay0_eq] at hder_ok
      have hdst_ok : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨refIdx, .cons .deref .nil⟩) m =
          .ok ⟨.memory ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              some (.concrete e.allocId borTag)⟩, .none, none⟩,
            translateTy c.ty body.layouts⟩ { m with stack := ⟨#[tfa]⟩ } := by
        rw [hdst_live, EStateM.bind_eq_ok hder_ok]; rfl
      rcases evalOperand_scalar_lm3_2_simulation hstate_a rfl hop_tfa hval_prim
          (some (translateTy c.ty body.layouts)) with
        ⟨m_op, msg_op, _, hm_op_ub⟩ | ⟨sc, msc, tf', _, hm_op_ok, hstate_tf', himm_sc, _, hvals_eq⟩
      · have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use (.constant c)), span⟩) m =
            (m_op, .error (.undefinedBehavior msg_op)) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_ok]; dsimp only []
          have hassoc : ∀ (f : Miri.Interpreter.RvalueImmTy AnnealProv →
              Miri.Interpreter.RvalueM AnnealStepState Unit) st,
              ((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
                (some (translateTy c.ty body.layouts)) >>= fun opv =>
                annealReadImmediate opv >>= f) st) =
              (((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
                (some (translateTy c.ty body.layouts)) >>= annealReadImmediate) >>= f) st) := by
            intro f st; simp only [Bind.bind, EStateM.bind]; cases annealEvalOperand
              body.localDecls body.layouts (translateOperand (.constant c))
              (some (translateTy c.ty body.layouts)) st <;> rfl
          rw [hassoc, EStateM.bind_eq_error hm_op_ub]
        rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
          at hstep
        cases hstep
      · rcases id hstate_tf' with ⟨tf₀', hframes_tf', _, _, hfr_tf', _, _, _, _, _, halloc_tf', _⟩
        injection hframes_tf' with h1_tf; injection h1_tf with h2_tf; subst h2_tf
        obtain ⟨hlive_sync, _⟩ := halloc_tf'.local_alloc_sync tf' rfl e he
        have htr_tgt : translateTy tgtDecl.ty body.layouts = translateTy c.ty body.layouts := by
          rw [← htgt_prim.translateTy_layoutIdx body.layouts,
            ← hval_prim.translateTy_layoutIdx body.layouts, htgt_kind, hval_kind]
        obtain ⟨_, _, hshape_fn⟩ := hlive_sync slot_t hslot_t ht_dead
        obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hshape_fn tgtDecl hdecl_tgt
        obtain ⟨sc', msc', hsc_eq, hmsc_eq, hrel_sc, hsz_sc, hbool_val, hchar_val⟩ :=
          himm_sc.of_primitive_scalar hval_prim
        injection hsc_eq with hsc_eq'; subst hsc_eq'
        have hmsc_eq' : msc = msc' := by
          injection hmsc_eq with h1; unfold Miri.Memory.Scalar.fromScalarInt at h1
          injection h1 with h2; injection h2
        subst hmsc_eq'
        have hshape_sc : StackScalarAllocShape (translateSizeBytes sc.sizeBytes)
            localAlloc.allocation := by
          rw [← hsz_sc, ← htr_tgt]; exact hshape_la
        obtain ⟨alloc', hw_alloc, -⟩ := hshape_sc.writeScalar_readScalar hrel_sc
        have hmsc_sz : msc.size = (translateTy c.ty body.layouts).layout.size := by
          rw [hrel_sc.size_eq, ← hsz_sc]
        have hw_alloc_lay : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy c.ty body.layouts).layout.size)
            (.fromScalarInt msc) localAlloc.allocation = .ok () alloc' := by
          rw [← hmsc_sz]; exact hw_alloc
        have hval_sc : annealValidateScalarForTyId (translateTy c.ty body.layouts).ty
            (.fromScalarInt msc) = true :=
          annealValidateScalarForTyId_of_scalarRel hval_prim hrel_sc hbool_val hchar_val
        have hw_m := annealWriteMemoryPlace_zero_offset_scalar_ok hval_prim hid_lt hbase hfind_la
          hshape_la.mutability_eq (htr_tgt ▸ hshape_la.byteSize_eq) hmsc_sz hval_sc hw_alloc_lay
          (borTag := borTag) (st := { m with stack := ⟨#[tf']⟩ })
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use (.constant c)), span⟩) m =
            ({ stack := ⟨#[tf']⟩
               machine := { m.machine with
                 memory := { m.machine.memory with
                   live := (m.machine.memory.live.filter (fun x => x.1 != e.allocId)).push
                     (e.allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_ok]; dsimp only []
          have hassoc : ∀ (f : Miri.Interpreter.RvalueImmTy AnnealProv →
              Miri.Interpreter.RvalueM AnnealStepState Unit) st,
              ((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
                (some (translateTy c.ty body.layouts)) >>= fun opv =>
                annealReadImmediate opv >>= f) st) =
              (((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
                (some (translateTy c.ty body.layouts)) >>= annealReadImmediate) >>= f) st) := by
            intro f st; simp only [Bind.bind, EStateM.bind]; cases annealEvalOperand
              body.localDecls body.layouts (translateOperand (.constant c))
              (some (translateTy c.ty body.layouts)) st <;> rfl
          rw [hassoc, EStateM.bind_eq_ok hm_op_ok, annealWriteImmediate_memory_eq rfl, hw_m]
        rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok
          rfl hfr_tf'.location_eq] at hstep
        injection hstep with hm' _
        subst hm'
        intro tf₀ tf_out htf₀ htf_out k hk mls' hmls' mp hmp
        rw [hframes] at htf₀
        injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
        injection htf_out with h₁; injection h₁ with h₁'; subst h₁'
        have hv_eq := hvals_eq k
        have hm' : (tf'.locals[k]?).map Miri.Interpreter.LocalState.value = some mls'.value := by
          dsimp only [] at hmls'; rw [hmls']; rfl
        rw [hm'] at hv_eq
        cases hta : tfa.locals[k]? with
        | none => rw [hta] at hv_eq; cases hv_eq
        | some mls_a =>
          rw [hta] at hv_eq
          injection hv_eq with hv_eq'
          exact (hk.cache_layout hlt_r _) mls_a hta mp (hv_eq'.symm.trans hmp)

private theorem annealReadImmediate_indirect_prim_eq₃
    {ty : Ty} {ly : LayoutTable} (hprim : IsPrimScalarTy ty)
    (mp : Miri.Interpreter.MemPlace AnnealProv) :
    annealReadImmediate ⟨.indirect mp, translateTy ty ly⟩ =
      annealReadMemoryPlace mp (translateTy ty ly) := by
  have hf : (translateTy ty ly).layout.fields = .Primitive := by
    rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
      (try cases it) <;> (try cases ut) <;>
      (unfold translateTy; rw [hk]; rfl)
  funext st
  unfold annealReadImmediate
  dsimp only
  rw [hf]

private theorem step_safeRef_deref_read_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl refDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal, get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ allocMap, e.tag = ptrVal.tag →
        get? s.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, get? body.localDecls e.localIdx = some decl →
            decl.ty.kind = dstDecl.ty.kind))
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    ∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨himm_dst, himm_ref⟩ := himm tf hframes
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨dstIdx, .nil⟩ (opKind ⟨refIdx, .cons .deref .nil⟩) span m
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  rw [htr_dst] at hm_stmt
  obtain ⟨_, mls_d, _, hlt_d, _, hmls_d, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hfra := hstate_a.frame_rel_singleton rfl
  obtain ⟨_, mls_r, _, hlt_ra, hslot_r, hmls_r, hmls_r_eq, hloc_r⟩ :=
    hfra.lookup_local hdecl_ref
  have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
    hloc_r.cachedLayout_eq
  have himm_ra : ∀ mp, mls_r.value ≠ .live (.indirect mp) :=
    himm_ref.cache_layout hlt_d _ mls_r hmls_r
  have hprim0 : IsPrimScalarTy { kind := dstDecl.ty.kind, layoutIdx := 0 } := by
    rcases hdst_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
    · exact Or.inr (Or.inr (Or.inl ⟨it, hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ut, hk⟩))
  have hlay0_eq : translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts =
      translateTy dstDecl.ty body.layouts :=
    hdst_prim.translateTy_layoutIdx body.layouts
  let tfb := cacheFrameLocalLayout tfa refIdx hlt_ra (translateTy refDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_ref hlt_ra
  have hfrb := hstate_b.frame_rel_singleton rfl
  have hop_deref_dead : ∀ (hmls_r' : tfa.locals[refIdx]'hlt_ra = ⟨.dead, mls_r.layout⟩),
      annealEvalOperand body.localDecls body.layouts
        (translateOperand (opKind ⟨refIdx, .cons .deref .nil⟩))
        (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
        .error (.undefinedBehavior "read of dead local") { m with stack := ⟨#[tfb]⟩ } := by
    intro hmls_r'
    rcases hopKind with rfl | rfl
    · exact annealEvalOperand_deref_dead (m := { m with stack := ⟨#[tfa]⟩ })
        (Or.inl rfl) rfl hlt_ra hdecl_ref hmls_r' hcache_r
    · exact annealEvalOperand_deref_dead (m := { m with stack := ⟨#[tfa]⟩ })
        (Or.inr rfl) rfl hlt_ra hdecl_ref hmls_r' hcache_r
  have hop_deref_live : ∀ imm
      (hmls_r' : tfa.locals[refIdx]'hlt_ra = ⟨.live (.immediate imm), mls_r.layout⟩),
      annealEvalOperand body.localDecls body.layouts
        (translateOperand (opKind ⟨refIdx, .cons .deref .nil⟩))
        (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
        (annealDerefOperandToMemPlace body.localDecls body.layouts refIdx (.immediate imm)
          (translateTy refDecl.ty body.layouts) >>= fun (mp, lay) => pure ⟨.indirect mp, lay⟩)
          { m with stack := ⟨#[tfb]⟩ } := by
    intro imm hmls_r'
    rcases hopKind with rfl | rfl
    · exact annealEvalOperand_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        (Or.inl rfl) rfl hlt_ra hdecl_ref hmls_r' hcache_r
    · exact annealEvalOperand_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        (Or.inr rfl) rfl hlt_ra hdecl_ref hmls_r' hcache_r
  rcases hloc_r.ref_immediate_cases href_ty himm_ra with
    ⟨_, hmr_dead⟩ | ⟨_, hmr_un⟩ | ⟨sc_r, msc_r, _, hsz8_r, hrel_r, hmr_sc⟩ |
    ⟨ptrVal, mptr, hsr_ptr, hptrRel, hmr_ptr⟩
  · have hmls_r' : tfa.locals[refIdx]'hlt_ra = ⟨.dead, mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_dead; subst hmr_dead; rfl
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
        m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error (hop_deref_dead hmls_r')]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      at hstep
    cases hstep
  · have hmls_r' : tfa.locals[refIdx]'hlt_ra = ⟨.live (.immediate .uninit), mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_un; subst hmr_un; rfl
    have hder_un := annealDerefOperandToMemPlace_safeRef_uninit (ly := body.layouts)
      hdecl_ref href_ty hprim0 (translateTy refDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
    have hop_un : annealEvalOperand body.localDecls body.layouts
        (translateOperand (opKind ⟨refIdx, .cons .deref .nil⟩))
        (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
        .error (.undefinedBehavior "read of uninitialized local") { m with stack := ⟨#[tfb]⟩ } := by
      rw [hop_deref_live .uninit hmls_r', EStateM.bind_eq_error hder_un]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
        m =
        ({ m with stack := ⟨#[tfb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hop_un]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      at hstep
    cases hstep
  · have hmls_r' : tfa.locals[refIdx]'hlt_ra =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc_r))), mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_sc; subst hmr_sc; rfl
    have hsc_chk := annealDerefOperandToMemPlace_safeRef_scalarInt (ly := body.layouts)
      hdecl_ref href_ty hprim0 hrel_r hsz8_r (translateTy refDecl.ty body.layouts)
      { m with stack := ⟨#[tfb]⟩ }
    obtain ⟨msg, hop_err⟩ : ∃ msg, annealEvalOperand body.localDecls body.layouts
        (translateOperand (opKind ⟨refIdx, .cons .deref .nil⟩))
        (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
        .error (.undefinedBehavior msg) { m with stack := ⟨#[tfb]⟩ } := by
      by_cases h0 : sc_r.bits = 0
      · exact ⟨_, by rw [hop_deref_live _ hmls_r', EStateM.bind_eq_error (hsc_chk.1 h0)]⟩
      · exact ⟨_, by rw [hop_deref_live _ hmls_r', EStateM.bind_eq_error (hsc_chk.2 h0)]⟩
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
        m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior msg)) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hop_err]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      at hstep
    cases hstep
  · subst hsr_ptr
    have hmls_r' : tfa.locals[refIdx]'hlt_ra =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
    have hop_ptr := hop_deref_live _ hmls_r'
    obtain ⟨_, borTag, hprov_eq, hid_lt, _, hmptr_off, ⟨e, he, htag, rfl⟩⟩ := id hptrRel
    obtain ⟨tgtDecl, hdecl_tgt, htgt_prim⟩ := halloc.target_decl e he
    obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
    obtain ⟨_, _, _, halloc_a⟩ : ∃ a b c, AllocMapRel body s { m with stack := ⟨#[tfa]⟩ } allocMap := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc_a, _⟩ := id hstate_a
      exact ⟨(), (), (), halloc_a⟩
    obtain ⟨slot_t, mls_t, _, _, hslot_t, hmls_t, _, hloc_t⟩ := hfra.lookup_local hdecl_tgt
    obtain ⟨hlive_e, _⟩ := halloc_a.local_alloc_sync tfa rfl e he
    by_cases ht_dead : slot_t = .dead
    · subst ht_dead
      have hder_err := annealDerefOperandToMemPlace_safeRef_ptr_dead hstate hdecl_ref href_ty
        hprim0 hptrRel he htag hslot_t (translateTy refDecl.ty body.layouts)
        (st := { m with stack := ⟨#[tfb]⟩ }) rfl
      have hop_err : annealEvalOperand body.localDecls body.layouts
          (translateOperand (opKind ⟨refIdx, .cons .deref .nil⟩))
          (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
          .error (.undefinedBehavior "dereferencing a dangling reference")
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hop_ptr, EStateM.bind_eq_error hder_err]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
          m =
          ({ m with stack := ⟨#[tfb]⟩ },
            .error (.undefinedBehavior "dereferencing a dangling reference")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hop_err]
      rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        at hstep
      cases hstep
    · have ht_ne_some_dead : get? s.frame.locals e.localIdx ≠ some .dead := by
        rw [hslot_t]; intro h; exact ht_dead (Option.some.inj h)
      obtain ⟨hoff0, _, hkind_tgt⟩ := hlive_ref ptrVal hslot_r e he htag ht_ne_some_dead
      have htgt_kind_eq : tgtDecl.ty.kind = dstDecl.ty.kind := hkind_tgt tgtDecl hdecl_tgt
      have htr_tgt : translateTy tgtDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
        rw [← htgt_prim.translateTy_layoutIdx body.layouts, htgt_kind_eq, hlay0_eq]
      obtain ⟨⟨lay_t, hlay_t⟩, hsc_t, hshape_f⟩ := hlive_e slot_t hslot_t ht_dead
      obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hshape_f tgtDecl hdecl_tgt
      rw [htr_tgt] at hshape_la
      obtain ⟨_, _, _, _, _, hnz_sz⟩ := hdst_prim.size_align_ok body.layouts
      have hder_ok := annealDerefOperandToMemPlace_safeRef_ptr_live hstate hdecl_ref href_ty
        hprim0 hprov_eq hmptr_off he hoff0 ht_ne_some_dead hkind_tgt
        (translateTy refDecl.ty body.layouts) (st := { m with stack := ⟨#[tfb]⟩ }) rfl
      rw [hlay0_eq] at hder_ok
      have hop_ok : annealEvalOperand body.localDecls body.layouts
          (translateOperand (opKind ⟨refIdx, .cons .deref .nil⟩))
          (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              some (.concrete e.allocId borTag)⟩, .none, none⟩,
            translateTy dstDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } := by
        rw [hop_ptr, EStateM.bind_eq_ok hder_ok]; rfl
      have hread_eq := annealReadMemoryPlace_zero_offset_eq hdst_prim hid_lt hbase hfind_la
        hshape_la.1 (borTag := borTag) (st := { m with stack := ⟨#[tfb]⟩ })
      rw [hlay_t] at hmls_t
      have hmls_t_eq' : mls_t = ⟨.live (.indirect (stackAllocPlace e.allocId)), lay_t⟩ :=
        Option.some.inj hmls_t.symm
      have hloc_t_1 : LocalRelLM3_1 m.machine allocMap tgtDecl body.layouts slot_t mls_t := by
        rw [hmls_t_eq'] at hloc_t ⊢
        exact hloc_t.indirect_base
      obtain ⟨hun_la', hsc_la'⟩ := hloc_t_1.indirect_stackAllocPlace_spec hmls_t_eq' hbase
        hfind_la (halloc_a.live_key_unique e he) (htr_tgt ▸ hnz_sz)
      cases hs_t : slot_t with
      | dead => exact absurd hs_t ht_dead
      | uninit =>
        have hun_la : localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO
              (translateTy dstDecl.ty body.layouts).layout.size) ≠ .ok (.ok ()) := by
          rw [← htr_tgt]; exact hun_la' hs_t
        obtain ⟨_, hread_err⟩ := hshape_la.uninit_readScalar_err hun_la false
        have hread_m : annealReadMemoryPlace
            ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              some (.concrete e.allocId borTag)⟩, .none, none⟩
            (translateTy dstDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ } =
            .error (.undefinedBehavior "read of uninitialized memory")
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hread_eq, hread_err]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt
              ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
            m =
            ({ m with stack := ⟨#[tfb]⟩ },
              .error (.undefinedBehavior "read of uninitialized memory")) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_ok]
          rw [annealReadImmediate_indirect_prim_eq₃ hdst_prim]
          rw [EStateM.bind_eq_error hread_m]
        rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
          at hstep
        cases hstep
      | init v_t =>
        obtain ⟨sc_t, rfl⟩ := hsc_t v_t hs_t
        have hsc_la := hsc_la' sc_t hs_t
        rw [htr_tgt] at hsc_la
        obtain ⟨_, hbool_t, hchar_t, msc_t, hrel_t, hread_ok⟩ := hsc_la
        have hrd_ne : refIdx ≠ dstIdx := by
          intro hrd; subst hrd
          rw [hdecl_dst] at hdecl_ref
          injection hdecl_ref with hd_eq; subst hd_eq
          rcases hdst_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;>
            rw [hk] at href_ty <;> cases href_ty
        have hlt_db : dstIdx < tfb.locals.size := by
          simp only [tfb, tfa, cacheFrameLocalLayout_size]; exact hlt_d
        have hdb_get : tfb.locals[dstIdx]? =
            some { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } := by
          simp only [tfb, tfa, cacheFrameLocalLayout]
          rw [Array.getElem?_set_ne _ hrd_ne, Array.getElem?_set_self, hmls_d_eq]
        have hdb_elem : tfb.locals[dstIdx]'hlt_db =
            { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } :=
          Option.some.inj ((Array.getElem?_eq_getElem hlt_db).symm.trans hdb_get)
        have hd_Lay : (tfb.locals[dstIdx]'hlt_db).layout =
            some (translateTy dstDecl.ty body.layouts) := by rw [hdb_elem]
        have hd_Val : (tfb.locals[dstIdx]'hlt_db).value = mls_d.value := by rw [hdb_elem]
        have hval_t : annealValidateScalarForTyId (translateTy dstDecl.ty body.layouts).ty
            (.fromScalarInt msc_t) = true :=
          annealValidateScalarForTyId_of_scalarRel hdst_prim hrel_t
            (fun hb => hbool_t (htgt_kind_eq.trans hb))
            (fun hc => hchar_t (htgt_kind_eq.trans hc))
        have hread_m : annealReadMemoryPlace
            ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              some (.concrete e.allocId borTag)⟩, .none, none⟩
            (translateTy dstDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ } =
            .ok ⟨.scalar (.fromScalarInt msc_t), translateTy dstDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hread_eq, hread_ok]; dsimp only []; rw [hval_t]; rfl
        rcases hloc_d with hloc_d_1 | ⟨_, _, _, _, _, _, hty_ref, _⟩
        rotate_left
        · exfalso
          rcases hdst_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;>
            rw [hk] at hty_ref <;> cases hty_ref
        cases hloc_d_1 with
        | rawPtr _ _ _ _ _ _ hty_raw _ =>
          exfalso
          rcases hdst_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;>
            rw [hk] at hty_raw <;> cases hty_raw
        | base hloc_d_b =>
          cases hloc_d_b with
          | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst _ hmls_d mp)
          | dead _ _ =>
            have hdb_dead : tfb.locals[dstIdx]? =
                some ⟨.dead, some (translateTy dstDecl.ty body.layouts)⟩ := by
              rw [Array.getElem?_eq_getElem hlt_db]
              rcases hls : tfb.locals[dstIdx]'hlt_db with ⟨v0, l0⟩
              rw [hls] at hd_Val hd_Lay
              dsimp only at hd_Val hd_Lay
              rw [hd_Val, hd_Lay]
            have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_dead
            have hm_err : Miri.Interpreter.Step.evalStatement
                (annealStepHooks body.localDecls body.layouts) ()
                (translateStmt
                  ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
                m =
                ({ m with stack := ⟨#[tfb]⟩ },
                  .error (.undefinedBehavior "write to dead local")) := by
              rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
              rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_ok]
              rw [annealReadImmediate_indirect_prim_eq₃ hdst_prim]
              rw [EStateM.bind_eq_ok hread_m,
                annealWriteImmediate_dead (m := { m with stack := ⟨#[tfb]⟩ })
                  (id0 := tf.localsIdentity) rfl hget_db]
            rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb
              hstmt hm_err] at hstep
            cases hstep
          | immediate _ oldImm _ _ _ =>
            have hdb_eq : tfb.locals[dstIdx]? =
                some ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ :=
              hdb_get
            have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_eq
            have hw_ok := annealWriteImmediate_live
              (val := .scalar (.fromScalarInt msc_t))
              (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
              (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
            have hm_ok : Miri.Interpreter.Step.evalStatement
                (annealStepHooks body.localDecls body.layouts) ()
                (translateStmt
                  ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
                m =
                ({ m with stack := ⟨#[{ tfb with
                    locals := tfb.locals.set dstIdx
                      { tfb.locals[dstIdx]'hlt_db with
                        value := .live (.immediate (.scalar (.fromScalarInt msc_t))) }
                      hlt_db }]⟩ },
                  .ok ()) := by
              rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
              rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_ok]
              rw [annealReadImmediate_indirect_prim_eq₃ hdst_prim]
              rw [EStateM.bind_eq_ok hread_m, hw_ok]
            rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok
              rfl hfrb.location_eq] at hstep
            injection hstep with hm' _
            subst hm'
            intro tf₀ tf' htf₀ htf' k hk mls' hmls' mp hmp
            rw [hframes] at htf₀
            injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
            injection htf' with h₁; injection h₁ with h₁'; subst h₁'
            dsimp only [] at hmls'
            rw [Array.getElem?_set] at hmls'
            by_cases hdk : dstIdx = k
            · subst hdk; simp only [↓reduceIte, Option.some.injEq] at hmls'
              rw [← hmls'] at hmp; cases hmp
            · simp only [hdk, ↓reduceIte] at hmls'
              exact ((hk.cache_layout hlt_d _).cache_layout hlt_ra _) mls' hmls' mp hmp

private theorem u64Local_value_of_stateRelLM3_2
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {n : Nat} {msc : Miri.Memory.ScalarInt}
    (hdecl0 : get? body.localDecls 0 = some u64Decl)
    (hslot0 : get? s.frame.locals 0 = some (.init (.scalar ⟨n, 8⟩)))
    (himm0 : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf 0)
    (hrel_sc : ScalarRel ⟨n, 8⟩ msc) :
    (m.stack.frames[0]?.bind (fun tf => (tf.locals[0]?).map Miri.Interpreter.LocalState.value)) =
      some (.live (.immediate (.scalar (.fromScalarInt msc)))) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have hf0 : m.stack.frames[0]? = some tf := by rw [hframes]; rfl
  rw [hf0]; dsimp only [Option.bind]
  obtain ⟨slot₀, mls₀, _, _, hs₀, hmls₀, _, hloc₀⟩ := hfr.lookup_local hdecl0
  rw [hslot0] at hs₀; injection hs₀ with hs₀'; subst hs₀'
  rw [hmls₀]
  cases hloc₀ with
  | lm3_1 h1 =>
    cases h1 with
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm0 tf hframes _ hmls₀ mp)
      | immediate _ imm _ _ hval =>
        rcases hval with ⟨h, _⟩ | ⟨v, hv, himmRel⟩
        · cases h
        · injection hv with hv'; subst hv'
          obtain ⟨sc', msc', hsc_eq, hmsc_eq, hrel', _, _, _⟩ :=
            himmRel.of_primitive_scalar (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
          injection hsc_eq with hsc'; subst hsc'
          have hm_eq : msc' = msc := by
            rcases msc' with ⟨d₁, sz₁⟩; rcases msc with ⟨d₂, sz₂⟩
            have hd := hrel'.data_eq.trans hrel_sc.data_eq.symm
            have hsz := hrel'.size_eq.trans hrel_sc.size_eq.symm
            subst hd hsz; rfl
          subst hm_eq hmsc_eq; rfl

/-- **`wit_lm3_2_ref_deref_read_storageDead_real_steps`**:
Full 4-step real-step execution of `lm32RefBody` (`_2 = &_1` -> `_0 = copy *_2`
-> `StorageDead(_2)` -> `StorageDead(_1)`) from `lm32Ref_stateRel_pre`,
preserving `StateRelLM3_2` at every step, reading `42_u64` into `_0` in both
machines, and freeing `lm31AllocId1` on `StorageDead(_1)`. -/
theorem wit_lm3_2_ref_deref_read_storageDead_real_steps :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState),
      let hooks := annealStepHooks lm32RefBody.localDecls lm32RefBody.layouts
      let entry := refAllocMapEntry lm32RefBody.localDecls lm32RefBody.layouts .shared 1 1
        lm31AllocId1
      stepMirFn lm32RefBody lm32RefAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm32RefMiriPre = (m₁, .ok true) ∧
      StateRelLM3_2 lm32RefBody s₁ m₁ [entry] ∧
      stepMirFn lm32RefBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2 lm32RefBody s₂ m₂ [entry] ∧
      get? s₂.frame.locals 0 = some (.init (.scalar ⟨42, 8⟩)) ∧
      (m₂.stack.frames[0]?.bind (fun tf => (tf.locals[0]?).map Miri.Interpreter.LocalState.value)) =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar42)))) ∧
      stepMirFn lm32RefBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_2 lm32RefBody s₃ m₃ [entry] ∧
      stepMirFn lm32RefBody s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_2 lm32RefBody s₄ m₄ [entry] ∧
      m₄.machine.memory.live.find? (fun x => x.1 == lm31AllocId1) = none := by
  have hphase : ∀ p, lm32RefBody.phase ≠ .other p := fun _ h => nomatch h
  let hooks := annealStepHooks lm32RefBody.localDecls lm32RefBody.layouts
  let entry := refAllocMapEntry lm32RefBody.localDecls lm32RefBody.layouts .shared 1 1 lm31AllocId1
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let borSh := [entry.toBorrowEntry]
  -- Step 1: `_2 = &_1`
  let s₁ := mkWitStateLM32 lm32RefBody 4 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr1] borSh 2
  have hs₁ : stepMirFn lm32RefBody lm32RefAnnealPre = .step s₁ := rfl
  obtain ⟨s₁', m₁, hs₁', hm₁, hrel₁⟩ := wit_lm3_2_ref_step
  have hs₁_eq : s₁' = s₁ := by
    rw [hs₁] at hs₁'; injection hs₁' with h; injection h with h'; exact h'.symm
  subst hs₁_eq
  have himm₀_all : ∀ tf, lm32RefMiriPre.stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
    intro tf h k mls hmls mp hmp
    injection h with h₁; injection h₁ with h₂; subst h₂
    match k with
    | 0 | 1 | 2 => simp [lm32RefMiriFramePre] at hmls; subst hmls; cases hmp
    | _ + 3 => simp [lm32RefMiriFramePre] at hmls
  have himm₁_step := step_ref_preserves_ne lm32Ref_stateRel_pre rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) lm32Ref_immediate_pre
    AllocIdSupplyReady.empty hm₁
  have himm₁_ne1 : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm₁_step lm32RefMiriFramePre tf rfl htf k hne (himm₀_all _ rfl k)
  -- Step 2: `_0 = copy *_2`
  let s₂ := mkWitStateLM32 lm32RefBody 5
    [.init (.scalar ⟨42, 8⟩), .init (.scalar ⟨42, 8⟩), .init ptr1] borSh 2
  have hs₂ : stepMirFn lm32RefBody s₁ = .step s₂ := rfl
  have hsim₂ := step_safeRef_deref_read_simulation_explicit hrel₁ hphase (Or.inl rfl)
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    (fun tf htf => ⟨himm₁_ne1 tf htf 0 (by decide), himm₁_ne1 tf htf 2 (by decide)⟩)
    (fun ptrVal hp e he _ _ => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_initLM32 hp
      cases he with
      | tail _ h => cases h
      | head _ =>
        subst hp'
        refine ⟨rfl, (fun h => nomatch h), fun decl hdecl => ?_⟩
        dsimp only [entry, refAllocMapEntry] at hdecl
        have h0 : get? lm32RefBody.localDecls 1 = some u64Decl := rfl
        rw [h0] at hdecl; injection hdecl with hd; subst hd; rfl)
  have hnext₂ : derefReadNextAllocMap s₁.frame.locals [entry] 2 = [entry] := rfl
  rw [hnext₂] at hsim₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_2_of_anneal_step hsim₂ hs₂
  have himm₂_step := step_safeRef_deref_read_preserves hrel₁ (Or.inl rfl)
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    (fun tf htf => ⟨himm₁_ne1 tf htf 0 (by decide), himm₁_ne1 tf htf 2 (by decide)⟩)
    (fun ptrVal hp e he _ _ => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_initLM32 hp
      cases he with
      | tail _ h => cases h
      | head _ =>
        subst hp'
        refine ⟨rfl, (fun h => nomatch h), fun decl hdecl => ?_⟩
        dsimp only [entry, refAllocMapEntry] at hdecl
        have h0 : get? lm32RefBody.localDecls 1 = some u64Decl := rfl
        rw [h0] at hdecl; injection hdecl with hd; subst hd; rfl)
    hm₂
  have hm₂_val :
      (m₂.stack.frames[0]?.bind (fun tf => (tf.locals[0]?).map Miri.Interpreter.LocalState.value)) =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar42)))) := by
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact u64Local_value_of_stateRelLM3_2 hrel₂ rfl rfl
      (fun tf₂ htf₂ => himm₂_step tf₁ tf₂ htf₁ htf₂ 0 (himm₁_ne1 tf₁ htf₁ 0 (by decide)))
      lm31_scalarRel42
  -- Step 3: `StorageDead(_2)`
  let s₃ := mkWitStateLM32 lm32RefBody 6
    [.init (.scalar ⟨42, 8⟩), .init (.scalar ⟨42, 8⟩), .dead] borSh 2
  have hs₃ : stepMirFn lm32RefBody s₂ = .step s₃ := rfl
  have hsim₃ := step_storageDead_lm3_2_simulation hrel₂ hphase rfl rfl rfl (by decide)
  obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_2_of_anneal_step hsim₃ hs₃
  -- Step 4: `StorageDead(_1)`
  let s₄ := mkWitStateLM32 lm32RefBody 7
    [.init (.scalar ⟨42, 8⟩), .dead, .dead] borSh 2
  have hs₄ : stepMirFn lm32RefBody s₃ = .step s₄ := rfl
  have hsim₄ := step_storageDead_lm3_2_simulation hrel₃ hphase rfl rfl rfl (by decide)
  obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_2_of_anneal_step hsim₄ hs₄
  have hm₄_dead : m₄.machine.memory.live.find? (fun x => x.1 == lm31AllocId1) = none := by
    obtain ⟨tf₄, hframes₄, _, _, _, _, _, _, _, _, halloc₄, _⟩ := id hrel₄
    exact (halloc₄.local_alloc_sync tf₄ hframes₄ entry (List.Mem.head _)).2 rfl
  exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, rfl, hm₂_val, hs₃, hm₃, hrel₃, hs₄, hm₄, hrel₄, hm₄_dead⟩

/-- `&mut u64`. -/
def refMutU64Ty : Ty := { kind := .ref .mut (.uint .u64), layoutIdx := 0 }

/-- Local declaration of type `&mut u64`. -/
def refMutU64Decl : LocalDecl := { mutability := .mut, ty := refMutU64Ty, debugName := none }

/-- `Runtime(PostCleanup)` MIR body exercising `&mut _1`, `move _2`, `*_3 = 99`,
`_0 = copy *_3`, and safe-reference reborrow `_4 = &*_3`:
```text
bb0: _2 = &mut _1;
     _3 = move _2;
     *_3 = const 99_u64;
     _0 = copy *_3;
     _4 = &*_3;
     return
``` -/
def lm32MutRefChainBody : CapturedMir where
  defPath := "lm_3_2_witness::mut_ref_move_write_read_reborrow"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, refMutU64Decl, refMutU64Decl, refU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
        mkStmt (.assign (local_ 3) (.use (.move (local_ 2)))),
        mkStmt (.assign (derefLocal 3) (.use (.constant (constU64 99)))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 3)))),
        mkStmt (.assign (local_ 4) (.ref .shared (derefLocal 3)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal pre-state for `lm32MutRefChainBody` at statement 0 (`_2 = &mut _1`). -/
def lm32MutRefChainAnnealPre : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit, .uninit] }
    memory := (initMachineState lm32MutRefChainBody []).memory }

/-- `lean-miri` root frame matching `lm32MutRefChainAnnealPre`. -/
def lm32MutRefChainMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm32MutRefChainBody
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
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- `lean-miri` state matching `lm32MutRefChainAnnealPre`. -/
def lm32MutRefChainMiriPre : AnnealStepState :=
  { stack := ⟨#[lm32MutRefChainMiriFramePre]⟩, machine := AnnealMachine.empty }

/-- `StateRel` holds between `lm32MutRefChainAnnealPre` and `lm32MutRefChainMiriPre`. -/
theorem lm32MutRefChain_stateRel_pre :
    StateRel lm32MutRefChainBody lm32MutRefChainAnnealPre lm32MutRefChainMiriPre := by
  refine StateRel.mk lm32MutRefChainMiriFramePre rfl rfl ⟨translateTy u64Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i j mplace_i mplace_j lay_i lay_j _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | 4 => rintro ⟨⟩
      | _ + 5 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = u64Decl := by simpa [lm32MutRefChainBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm32MutRefChainAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm32MutRefChainMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = u64Decl := by simpa [lm32MutRefChainBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by
      simpa [lm32MutRefChainAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
          layout := some (translateTy u64Ty) } := by
      simpa [lm32MutRefChainMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | 2 =>
    have hd : decl = refMutU64Decl := by simpa [lm32MutRefChainBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm32MutRefChainAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm32MutRefChainMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 3 =>
    have hd : decl = refMutU64Decl := by simpa [lm32MutRefChainBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm32MutRefChainAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm32MutRefChainMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 4 =>
    have hd : decl = refU64Decl := by simpa [lm32MutRefChainBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm32MutRefChainAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm32MutRefChainMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 5 =>
    simp [lm32MutRefChainBody, get?] at hdecl

/-- **`wit_lm3_2_mut_ref_move_write_read_reborrow_real_steps`**:
5-step execution of `lm32MutRefChainBody` through both `stepMirFn` and
`Miri.Interpreter.Step.step`:
1. `_2 = &mut _1` (`evalRvalue_ref_simulation`),
2. `_3 = move _2` (`step_safeRef_use_simulation`, deinitializing `_2`),
3. `*_3 = const 99_u64` (`step_safeRef_deref_write_simulation_explicit`),
4. `_0 = copy *_3` (`step_safeRef_deref_read_simulation_explicit`, yielding `99_u64`),
5. `_4 = &*_3` (`evalRvalue_reborrow_safeRef_simulation`, creating a shared
   reborrow of `lm31AllocId1` at tag `2`). -/
theorem wit_lm3_2_mut_ref_move_write_read_reborrow_real_steps :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
      (tf₅ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let hooks := annealStepHooks lm32MutRefChainBody.localDecls lm32MutRefChainBody.layouts
      let entry := refAllocMapEntry lm32MutRefChainBody.localDecls lm32MutRefChainBody.layouts
        (.mut false) 1 1 lm31AllocId1
      stepMirFn lm32MutRefChainBody lm32MutRefChainAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm32MutRefChainMiriPre = (m₁, .ok true) ∧
      StateRelLM3_2 lm32MutRefChainBody s₁ m₁ [entry] ∧
      stepMirFn lm32MutRefChainBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2 lm32MutRefChainBody s₂ m₂ [entry] ∧
      get? s₂.frame.locals 2 = some .uninit ∧
      stepMirFn lm32MutRefChainBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_2 lm32MutRefChainBody s₃ m₃ [entry] ∧
      stepMirFn lm32MutRefChainBody s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_2 lm32MutRefChainBody s₄ m₄ [entry] ∧
      get? s₄.frame.locals 0 = some (.init (.scalar ⟨99, 8⟩)) ∧
      (m₄.stack.frames[0]?.bind (fun tf => (tf.locals[0]?).map Miri.Interpreter.LocalState.value)) =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar99)))) ∧
      stepMirFn lm32MutRefChainBody s₄ = .step s₅ ∧
      get? s₅.frame.locals 4 = some (.init (.ptr { allocId := 2, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      m₅.stack.frames = #[tf₅] ∧
      (tf₅.locals[4]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
              .concrete lm31AllocId1 borTag⟩)))) := by
  have hphase : ∀ p, lm32MutRefChainBody.phase ≠ .other p := fun _ h => nomatch h
  let hooks := annealStepHooks lm32MutRefChainBody.localDecls lm32MutRefChainBody.layouts
  let entry := refAllocMapEntry lm32MutRefChainBody.localDecls lm32MutRefChainBody.layouts
    (.mut false) 1 1 lm31AllocId1
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let borAct := [entry.toBorrowEntry]
  have himm₀_all : ∀ tf, lm32MutRefChainMiriPre.stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
    intro tf h k mls hmls mp hmp
    injection h with h₁; injection h₁ with h₂; subst h₂
    match k with
    | 0 | 1 | 2 | 3 | 4 => simp [lm32MutRefChainMiriFramePre] at hmls; subst hmls; cases hmp
    | _ + 5 => simp [lm32MutRefChainMiriFramePre] at hmls
  -- Step 1: `_2 = &mut _1`
  let s₁ := mkWitStateLM32 lm32MutRefChainBody 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr1, .uninit, .uninit] borAct 2
  have hs₁ : stepMirFn lm32MutRefChainBody lm32MutRefChainAnnealPre = .step s₁ := rfl
  have hsim₁ := evalRvalue_ref_simulation lm32MutRefChain_stateRel_pre.toLM3_1.toLM3_2 hphase
    (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀_all tf htf 2, himm₀_all tf htf 1⟩)
    AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
  have himm₁_step := step_ref_preserves_ne lm32MutRefChain_stateRel_pre
    (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
    rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀_all tf htf 2, himm₀_all tf htf 1⟩)
    AllocIdSupplyReady.empty hm₁
  have himm₁_ne1 : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm₁_step lm32MutRefChainMiriFramePre tf rfl htf k hne (himm₀_all _ rfl k)
  -- Step 2: `_3 = move _2`
  let s₂ := mkWitStateLM32 lm32MutRefChainBody 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr1, .uninit] borAct 2
  have hs₂ : stepMirFn lm32MutRefChainBody s₁ = .step s₂ := rfl
  have himm₁_32 : ∀ tf, m₁.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 3 ∧ IsImmediateFrameLocal tf 2 :=
    fun tf htf => ⟨himm₁_ne1 tf htf 3 (by decide), himm₁_ne1 tf htf 2 (by decide)⟩
  have hsim₂ := step_safeRef_use_simulation hrel₁ hphase (Or.inr rfl)
    rfl rfl rfl rfl rfl rfl himm₁_32
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_2_of_anneal_step hsim₂ hs₂
  have himm₂_step := step_safeRef_move_preserves hrel₁ rfl rfl rfl rfl rfl himm₁_32 hm₂
  have himm₂_ne1 : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf₂ htf₂ k hne
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁_ne1 tf₁ htf₁ k hne)
  -- Step 3: `*_3 = const 99_u64`
  let s₃ := mkWitStateLM32 lm32MutRefChainBody 3
    [.uninit, .init (.scalar ⟨99, 8⟩), .uninit, .init ptr1, .uninit] borAct 2
  have hs₃ : stepMirFn lm32MutRefChainBody s₂ = .step s₃ := rfl
  have himm₂_3 : ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf 3 :=
    fun tf htf => himm₂_ne1 tf htf 3 (by decide)
  have hlive₃ : ∀ ptrVal e tgtDecl,
      get? s₂.frame.locals 3 = some (.init (.ptr ptrVal 8)) →
      e ∈ [entry] → e.tag = ptrVal.tag →
      get? lm32MutRefChainBody.localDecls e.localIdx = some tgtDecl →
      get? s₂.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
        tgtDecl.ty.kind = u64Ty.kind := by
    intro ptrVal e tgtDecl hp he _ htgt _
    have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_initLM32 hp
    cases he with
    | tail _ h => cases h
    | head _ =>
      dsimp only [entry, refAllocMapEntry] at htgt
      have h0 : get? lm32MutRefChainBody.localDecls 1 = some u64Decl := rfl
      rw [h0] at htgt
      have hd : tgtDecl = u64Decl := Option.some.inj htgt.symm
      subst hp' hd
      exact ⟨rfl, Or.inl rfl, rfl⟩
  have hsim₃ := step_safeRef_deref_write_simulation_explicit hrel₂ hphase rfl rfl
    rfl rfl (valTy := u64Ty) (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
    (fun tf _ => constU64_wellTypedLM32 lm32MutRefChainBody tf 99 (by decide))
    himm₂_3 hlive₃
  change StepRelLM3_2 lm32MutRefChainBody m₂ [entry]
    (stepMirFn lm32MutRefChainBody s₂)
    (Miri.Interpreter.Step.step hooks () m₂) at hsim₃
  obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_2_of_anneal_step hsim₃ hs₃
  have himm₃_step := step_safeRef_deref_write_const_preserves hrel₂ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
    (fun tf _ => constU64_wellTypedLM32 lm32MutRefChainBody tf 99 (by decide))
    himm₂_3 hlive₃ hm₃
  have himm₃_ne1 : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf₃ htf₃ k hne
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂_ne1 tf₂ htf₂ k hne)
  -- Step 4: `_0 = copy *_3`
  let s₄ := mkWitStateLM32 lm32MutRefChainBody 4
    [.init (.scalar ⟨99, 8⟩), .init (.scalar ⟨99, 8⟩), .uninit, .init ptr1, .uninit] borAct 2
  have hs₄ : stepMirFn lm32MutRefChainBody s₃ = .step s₄ := rfl
  have himm₃_03 : ∀ tf, m₃.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 ∧ IsImmediateFrameLocal tf 3 :=
    fun tf htf => ⟨himm₃_ne1 tf htf 0 (by decide), himm₃_ne1 tf htf 3 (by decide)⟩
  have hlive₄ : ∀ ptrVal, get? s₃.frame.locals 3 = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ [entry], e.tag = ptrVal.tag →
        get? s₃.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, get? lm32MutRefChainBody.localDecls e.localIdx = some decl →
            decl.ty.kind = u64Decl.ty.kind) := by
    intro ptrVal hp e he _ _
    have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_initLM32 hp
    cases he with
    | tail _ h => cases h
    | head _ =>
      subst hp'
      refine ⟨rfl, (fun h => nomatch h), fun decl hdecl => ?_⟩
      dsimp only [entry, refAllocMapEntry] at hdecl
      have h0 : get? lm32MutRefChainBody.localDecls 1 = some u64Decl := rfl
      rw [h0] at hdecl; injection hdecl with hd; subst hd; rfl
  have hsim₄ := step_safeRef_deref_read_simulation_explicit hrel₃ hphase (Or.inl rfl)
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₃_03 hlive₄
  change StepRelLM3_2 lm32MutRefChainBody m₃ [entry]
    (stepMirFn lm32MutRefChainBody s₃)
    (Miri.Interpreter.Step.step hooks () m₃) at hsim₄
  obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_2_of_anneal_step hsim₄ hs₄
  have himm₄_step := step_safeRef_deref_read_preserves hrel₃ (Or.inl rfl)
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₃_03 hlive₄ hm₄
  have himm₄_ne1 : ∀ tf, m₄.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf₄ htf₄ k hne
    obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃_ne1 tf₃ htf₃ k hne)
  have hm₄_val :
      (m₄.stack.frames[0]?.bind (fun tf => (tf.locals[0]?).map Miri.Interpreter.LocalState.value)) =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar99)))) :=
    u64Local_value_of_stateRelLM3_2 hrel₄ rfl rfl
      (fun tf htf => himm₄_ne1 tf htf 0 (by decide)) lm31_scalarRel99
  -- Step 5: `_4 = &*_3`
  have himm₄_43 : ∀ tf, m₄.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 4 ∧ IsImmediateFrameLocal tf 3 :=
    fun tf htf => ⟨himm₄_ne1 tf htf 4 (by decide), himm₄_ne1 tf htf 3 (by decide)⟩
  have hreb := evalRvalue_reborrow_safeRef_simulation hrel₄ hphase
    (dstIdx := 4) (refIdx := 3) (bk := .shared)
    rfl rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₄_43
    (fun ptrVal e hp he _ => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_initLM32 hp
      cases he with
      | tail _ h => cases h
      | head _ =>
        subst hp'
        refine ⟨(fun h => nomatch h), rfl, (fun h => nomatch h),
          (fun ⟨_, hne⟩ => hne rfl), fun d hd => ?_⟩
        dsimp only [entry, refAllocMapEntry] at hd
        have h0 : get? lm32MutRefChainBody.localDecls 1 = some u64Decl := rfl
        rw [h0] at hd; injection hd with hd'; subst hd'; rfl)
  obtain ⟨⟨s₅, hs₅, hloc₅⟩, m₅, tf₅, borTag, hm₅, htf₅, _, hval₅⟩ :=
    hreb.2 { allocId := 1, offsetBytes := 0 } entry rfl (List.Mem.head _) rfl (fun h => nomatch h)
  exact ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, tf₅, borTag,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, rfl, hs₃, hm₃, hrel₃, hs₄, hm₄, hrel₄, rfl, hm₄_val,
    hs₅, hloc₅, hm₅, htf₅, hval₅⟩

/-! ## 4. Concrete Real-Step Reborrow Divergences & Recursive Pointee Validity -/

/-- `Runtime(PostCleanup)` MIR body exercising safe-reference dangling reborrow
after `StorageDead(_1)`:
```text
bb0: _2 = &_1;
     StorageDead(_1);
     _3 = &*_2;
     return
``` -/
def lm32DanglingReborrowBody : CapturedMir where
  defPath := "lm_3_2_witness::safe_ref_dangling_reborrow"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, refU64Decl, refU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.ref .shared (local_ 1))),
        mkStmt (.storageDead 1),
        mkStmt (.assign (local_ 3) (.ref .shared (derefLocal 2)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal pre-state for `lm32DanglingReborrowBody` at statement 0 (`_2 = &_1`). -/
def lm32DanglingReborrowAnnealPre : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit] }
    memory := (initMachineState lm32DanglingReborrowBody []).memory }

/-- `lean-miri` root frame matching `lm32DanglingReborrowAnnealPre`. -/
def lm32DanglingReborrowMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm32DanglingReborrowBody
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
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- `lean-miri` state matching `lm32DanglingReborrowAnnealPre`. -/
def lm32DanglingReborrowMiriPre : AnnealStepState :=
  { stack := ⟨#[lm32DanglingReborrowMiriFramePre]⟩, machine := AnnealMachine.empty }

/-- `StateRel` holds between `lm32DanglingReborrowAnnealPre` and `lm32DanglingReborrowMiriPre`. -/
theorem lm32DanglingReborrow_stateRel_pre :
    StateRel lm32DanglingReborrowBody lm32DanglingReborrowAnnealPre lm32DanglingReborrowMiriPre := by
  refine StateRel.mk lm32DanglingReborrowMiriFramePre rfl rfl ⟨translateTy u64Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i j mplace_i mplace_j lay_i lay_j _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 => rintro ⟨⟩
      | _ + 4 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = u64Decl := by simpa [lm32DanglingReborrowBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm32DanglingReborrowAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm32DanglingReborrowMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = u64Decl := by simpa [lm32DanglingReborrowBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by
      simpa [lm32DanglingReborrowAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
          layout := some (translateTy u64Ty) } := by
      simpa [lm32DanglingReborrowMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | 2 =>
    have hd : decl = refU64Decl := by simpa [lm32DanglingReborrowBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm32DanglingReborrowAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm32DanglingReborrowMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 3 =>
    have hd : decl = refU64Decl := by simpa [lm32DanglingReborrowBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm32DanglingReborrowAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm32DanglingReborrowMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 4 =>
    simp [lm32DanglingReborrowBody, get?] at hdecl

/-- `Runtime(PostCleanup)` MIR body exercising `&*_1` on an integer-valued raw
pointer `_1 : *const u64`. -/
def lm32RawPtrIntReborrowBody : CapturedMir where
  defPath := "lm_3_2_witness::raw_ptr_int_reborrow"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU64Decl, refU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.ref .shared (derefLocal 1)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal pre-state for `lm32RawPtrIntReborrowBody`: `_1` holds `0` as an
integer scalar without provenance. -/
def lm32RawPtrIntReborrowAnnealPre : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨0, 8⟩), .uninit] }
    memory := (initMachineState lm32RawPtrIntReborrowBody []).memory }

/-- `lean-miri` root frame matching `lm32RawPtrIntReborrowAnnealPre`. -/
def lm32RawPtrIntReborrowMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm32RawPtrIntReborrowBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy u64Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0)))),
        layout := some (translateTy rawPtrConstU64Ty) },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- `lean-miri` state matching `lm32RawPtrIntReborrowAnnealPre`. -/
def lm32RawPtrIntReborrowMiriPre : AnnealStepState :=
  { stack := ⟨#[lm32RawPtrIntReborrowMiriFramePre]⟩, machine := AnnealMachine.empty }

/-- `StateRel` holds between `lm32RawPtrIntReborrowAnnealPre` and
`lm32RawPtrIntReborrowMiriPre`. -/
theorem lm32RawPtrIntReborrow_stateRel_pre :
    StateRel lm32RawPtrIntReborrowBody
      lm32RawPtrIntReborrowAnnealPre lm32RawPtrIntReborrowMiriPre := by
  refine StateRel.mk lm32RawPtrIntReborrowMiriFramePre rfl rfl ⟨translateTy u64Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i j mplace_i mplace_j lay_i lay_j _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 => rintro ⟨⟩
      | _ + 3 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = u64Decl := by simpa [lm32RawPtrIntReborrowBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm32RawPtrIntReborrowAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm32RawPtrIntReborrowMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = rawPtrConstU64Decl := by
      simpa [lm32RawPtrIntReborrowBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨0, 8⟩) := by
      simpa [lm32RawPtrIntReborrowAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0)))),
          layout := some (translateTy rawPtrConstU64Ty) } := by
      simpa [lm32RawPtrIntReborrowMiriFramePre] using hmls.symm
    subst hd hs hm
    have hrel0 : ScalarRel ⟨0, 8⟩ (Miri.Memory.ScalarInt.ofUInt64 0) :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
    exact .immediate _ _ (some (translateTy rawPtrConstU64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ hrel0 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | 2 =>
    have hd : decl = refU64Decl := by simpa [lm32RawPtrIntReborrowBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm32RawPtrIntReborrowAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm32RawPtrIntReborrowMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 3 =>
    simp [lm32RawPtrIntReborrowBody, get?] at hdecl

/-- **`wit_lm3_2_safeRef_dangling_reborrow_and_rawPtr_int_divergences`**:
1. **Dangling safe-reference reborrow**: from pointer-free `StateRel`, `_2 = &_1`
   and `StorageDead(_1)` step in lockstep to `StateRelLM3_2`-related states
   `(s₂, m₂)`, after which `_3 = &*_2` steps in Anneal (`stepMirFn`) while
   `Miri.Interpreter.Step.step` immediately fails with
   `undefinedBehavior "dereferencing a dangling reference"`
   (`evalRvalue_reborrow_safeRef_dangling_divergence`).
2. **Integer-scalar raw-pointer reborrow**: from pointer-free `StateRel` where
   `_1 : *const u64` holds `0` without provenance, `_2 = &*_1` fails with UB in
   Anneal (`stepMirFn`) while `Miri.Interpreter.Step.step` steps and writes a
   provenance-less scalar into `_2`
   (`evalRvalue_reborrow_rawPtr_int_divergence`). -/
theorem wit_lm3_2_safeRef_dangling_reborrow_and_rawPtr_int_divergences :
    (∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let hooks := annealStepHooks lm32DanglingReborrowBody.localDecls
        lm32DanglingReborrowBody.layouts
      let entry := refAllocMapEntry lm32DanglingReborrowBody.localDecls
        lm32DanglingReborrowBody.layouts .shared 1 1 lm31AllocId1
      stepMirFn lm32DanglingReborrowBody lm32DanglingReborrowAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm32DanglingReborrowMiriPre = (m₁, .ok true) ∧
      StateRelLM3_2 lm32DanglingReborrowBody s₁ m₁ [entry] ∧
      stepMirFn lm32DanglingReborrowBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2 lm32DanglingReborrowBody s₂ m₂ [entry] ∧
      stepMirFn lm32DanglingReborrowBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "dereferencing a dangling reference"))) ∧
    (stepMirFn lm32RawPtrIntReborrowBody lm32RawPtrIntReborrowAnnealPre = MirStepNode.fail .ub ∧
      ∃ m' tf',
        Miri.Interpreter.Step.step
          (annealStepHooks lm32RawPtrIntReborrowBody.localDecls lm32RawPtrIntReborrowBody.layouts)
          () lm32RawPtrIntReborrowMiriPre = (m', .ok true) ∧
        m'.stack.frames = #[tf'] ∧
        (tf'.locals[2]?).map Miri.Interpreter.LocalState.value =
          some (.live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0)))))) := by
  refine ⟨?_, ?_⟩
  · have hphase : ∀ p, lm32DanglingReborrowBody.phase ≠ .other p := fun _ h => nomatch h
    let entry := refAllocMapEntry lm32DanglingReborrowBody.localDecls
      lm32DanglingReborrowBody.layouts .shared 1 1 lm31AllocId1
    let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let borSh := [entry.toBorrowEntry]
    have himm₀_all : ∀ tf, lm32DanglingReborrowMiriPre.stack.frames = #[tf] →
        ∀ k, IsImmediateFrameLocal tf k := by
      intro tf h k mls hmls mp hmp
      injection h with h₁; injection h₁ with h₂; subst h₂
      match k with
      | 0 | 1 | 2 | 3 => simp [lm32DanglingReborrowMiriFramePre] at hmls; subst hmls; cases hmp
      | _ + 4 => simp [lm32DanglingReborrowMiriFramePre] at hmls
    let s₁ := mkWitStateLM32 lm32DanglingReborrowBody 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr1, .uninit] borSh 2
    have hs₁ : stepMirFn lm32DanglingReborrowBody lm32DanglingReborrowAnnealPre = .step s₁ := rfl
    have hsim₁ := evalRvalue_ref_simulation lm32DanglingReborrow_stateRel_pre.toLM3_1.toLM3_2
      hphase (dstIdx := 2) (targetIdx := 1) (bk := .shared)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀_all tf htf 2, himm₀_all tf htf 1⟩)
      AllocIdSupplyReady.empty
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
    have himm₁_step := step_ref_preserves_ne lm32DanglingReborrow_stateRel_pre
      (dstIdx := 2) (targetIdx := 1) (bk := .shared)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀_all tf htf 2, himm₀_all tf htf 1⟩)
      AllocIdSupplyReady.empty hm₁
    have himm₁_ne1 : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
      fun tf htf k hne =>
        himm₁_step lm32DanglingReborrowMiriFramePre tf rfl htf k hne (himm₀_all _ rfl k)
    let s₂ := mkWitStateLM32 lm32DanglingReborrowBody 2
      [.uninit, .dead, .init ptr1, .uninit] borSh 2
    have hs₂ : stepMirFn lm32DanglingReborrowBody s₁ = .step s₂ := rfl
    have hsim₂ := step_storageDead_lm3_2_simulation hrel₁ hphase rfl rfl rfl (by decide)
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_2_of_anneal_step hsim₂ hs₂
    have himm₂_step := step_storageDead_lm3_2_preserves hrel₁ rfl rfl rfl (by decide) hm₂
    have himm₂_2 : ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 := by
      intro tf₂ htf₂
      obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm₂_step tf₁ tf₂ htf₁ htf₂ 2 (himm₁_ne1 tf₁ htf₁ 2 (by decide))
    obtain ⟨⟨s₃, hs₃, _⟩, m₃, hm₃⟩ := evalRvalue_reborrow_safeRef_dangling_divergence
      hrel₂ hphase (dstIdx := 3) (refIdx := 2) (bk := .shared)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₂_2
      (fun h => nomatch h) (ptrVal := { allocId := 1, offsetBytes := 0 }) rfl
      (e := entry) (List.Mem.head _) rfl
      ⟨(fun h => nomatch h), (fun ⟨_, hne⟩ => hne rfl)⟩ rfl
    exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃⟩
  · have hphase : ∀ p, lm32RawPtrIntReborrowBody.phase ≠ .other p := fun _ h => nomatch h
    obtain ⟨hub, m', tf', msc, hrel_sc, _, hm', htf', hval'⟩ :=
      evalRvalue_reborrow_rawPtr_int_divergence
        lm32RawPtrIntReborrow_stateRel_pre.toLM3_1.toLM3_2 hphase
        (dstIdx := 2) (ptrIdx := 1) (bk := .shared)
        rfl rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
        (fun tf htf =>
          ⟨isImmediate_of_checkImmediateInTopFrame (by with_unfolding_all rfl) tf htf,
           isImmediate_of_checkImmediateInTopFrame (by with_unfolding_all rfl) tf htf⟩)
        (fun h => nomatch h) (sc := ⟨0, 8⟩) rfl
    have hrel0 : ScalarRel ⟨0, 8⟩ (Miri.Memory.ScalarInt.ofUInt64 0) :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
    have hmsc_eq : msc = Miri.Memory.ScalarInt.ofUInt64 0 := by
      rcases msc with ⟨d, sz⟩
      have hd : d = (Miri.Memory.ScalarInt.ofUInt64 0).data := hrel_sc.data_eq.trans hrel0.data_eq.symm
      have hsz : sz = (Miri.Memory.ScalarInt.ofUInt64 0).size := hrel_sc.size_eq.trans hrel0.size_eq.symm
      subst hd hsz
      rfl
    subst hmsc_eq
    exact ⟨hub, m', tf', hm', htf', hval'⟩

/-- `&bool` as an Anneal type. -/
def refBoolTyLM32 : Ty := { kind := .ref .not .bool, layoutIdx := 0 }

/-- 1-byte stack allocation at `lm31AllocId1` holding either `.Uninit` (`none`)
or an initialized byte `some b`. -/
def lm32BoolPointeeAlloc? (optByte : Option UInt8) :
    Except Miri.Memory.AllocError
      (Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :=
  let res : Except Miri.Memory.AllocError (Miri.Memory.Allocation AnnealProv Unit) :=
    match optByte with
    | none =>
      Miri.Memory.Allocation.tryNew (Miri.ABI.Size.ofBytes 1) Miri.ABI.Align.ONE .Uninit
        (fun _ _ => some #[0])
    | some b =>
      Miri.Memory.Allocation.fromBytes #[b] Miri.ABI.Align.ONE .Mut
  res.map (fun alloc => alloc.withExtra none)

/-- Concrete `AnnealStepState` whose root local `_0` holds a live `&bool`
reference into `alloc` at `lm31AllocId1`. -/
def lm32RefBoolValidityState
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    AnnealStepState :=
  let refImm : Miri.Interpreter.Immediate AnnealProv :=
    .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
        .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩)
  { stack := ⟨#[lm32ValidityFrame refImm]⟩
    machine := mkSingleAllocMachine lm31AllocId1 alloc }

/-- Construct `lm32BoolPointeeAlloc? optByte` and run shallow (`recursive = false`,
`reset = false`) `ValidityVisitor.validatePlace` on local `_0 : &bool`. -/
def lm32RunValidateRefBoolShallow (optByte : Option UInt8) :
    Except Miri.Memory.AllocError (Except Miri.Interpreter.StepError Unit) := do
  let alloc ← lm32BoolPointeeAlloc? optByte
  match Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks emptyLayoutTable)
      refBoolTyLM32 4 ⟨.local 0 0 none (.ofAllocationToken 0), translateTy refBoolTyLM32⟩
      false false (lm32RefBoolValidityState alloc) with
  | .ok () _ => .ok (.ok ())
  | .error err _ => .ok (.error err)

/-- Construct `lm32BoolPointeeAlloc? optByte` and execute the recursive
`RefTracking` root + child pointee validation pass of
`ValidityVisitor.validatePlace` (`ValidityVisitor.visit` on root `_0 : &bool`
with `refTracking := some .empty`, `RefTracking.next`, and child
`ValidityVisitor.visit` on `⟨.memory key.mplace, key.layout⟩`; `validatePlace`
wraps its outer `while` worklist in `partial` `Lean.Loop.forIn`, whereas each
fuel-bounded `visit` + `RefTracking.next` step reduces directly in the Lean
kernel). Returns `true` when the `RefTracking` worklist is drained after
validating the pointee. -/
def lm32RunVisitRefBoolRecursive (optByte : Option UInt8) :
    Except Miri.Memory.AllocError (Except Miri.Interpreter.StepError Bool) := do
  let alloc ← lm32BoolPointeeAlloc? optByte
  let hooks := annealValidityHooks emptyLayoutTable
  let rootPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 0 none (.ofAllocationToken 0), translateTy refBoolTyLM32⟩
  let rootSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
    { path := ⟨"", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
      refTracking := some .empty, dataBytes := none }
  let stepAction : Miri.Interpreter.ValidityVisitor.M AnnealStepState Bool := do
    let s1 ← Miri.Interpreter.ValidityVisitor.visit hooks refBoolTyLM32 4 rootSession rootPlace
    match s1.refTracking.bind Miri.Memory.Validity.RefTracking.next with
    | none => throw (.invalidProgram "expected tracked pointee")
    | some ((key, path), tracking) =>
      let childSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
        { path := path, flags := ⟨false, true⟩, ctfeMode := none,
          refTracking := none, dataBytes := none }
      let child : Miri.Interpreter.RuntimePlace AnnealProv := ⟨.memory key.mplace, key.layout⟩
      let _ ← Miri.Interpreter.ValidityVisitor.visit hooks refBoolTyLM32 4 childSession child
      pure tracking.todo.isEmpty
  match stepAction (lm32RefBoolValidityState alloc) with
  | .ok drained _ => .ok (.ok drained)
  | .error err _ => .ok (.error err)

/-- **`wit_lm3_2_recursive_ref_pointee_validity`**:
Running the vendored `ValidityVisitor` on a live `&bool` reference distinguishes
shallow dereferenceability (`recursive = false`) from recursive `RefTracking`
pointee validation (`refTracking := some .empty` -> `RefTracking.next` -> child
`visit`):
1. Uninitialized pointee byte (`none`): shallow `validatePlace` succeeds
   (`.ok (.ok ())`), whereas recursive pointee validation fails with
   `undefinedBehavior "read of uninitialized memory"`;
2. Invalid `bool` pointee byte (`some 2`): shallow `validatePlace` succeeds
   (`.ok (.ok ())`), whereas recursive pointee validation fails with
   `undefinedBehavior`;
3. Valid `bool` pointee byte (`some 1`): recursive pointee validation succeeds
   and drains the `RefTracking` worklist (`.ok (.ok true)`). -/
theorem wit_lm3_2_recursive_ref_pointee_validity :
    lm32RunValidateRefBoolShallow none = .ok (.ok ()) ∧
    lm32RunVisitRefBoolRecursive none =
      .ok (.error (.undefinedBehavior "read of uninitialized memory")) ∧
    lm32RunValidateRefBoolShallow (some 2) = .ok (.ok ()) ∧
    (∃ msg, lm32RunVisitRefBoolRecursive (some 2) = .ok (.error (.undefinedBehavior msg))) ∧
    lm32RunVisitRefBoolRecursive (some 1) = .ok (.ok true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · exact ⟨_, by with_unfolding_all rfl⟩
  · with_unfolding_all rfl

end LeanMiriSpec.Correspondence.Witness
