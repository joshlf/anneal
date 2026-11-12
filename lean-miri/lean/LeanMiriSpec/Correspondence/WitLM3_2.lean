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
   `evalRvalue_reborrow_safeRef_dangling_simulation` (`&*_2` after
   `StorageDead(_1)`: undefined behavior in BOTH machines, `lean-miri` failing
   with `"dereferencing a dangling reference"`) and
   `evalRvalue_reborrow_rawPtr_int_divergence` (`&*_1` on an integer-valued raw
   pointer: Anneal fails with UB while `Step.step` steps).
5. **`wit_lm3_2_ref_never_and_enum_discriminant_validity`,
   `wit_lm3_2_invalid_bool_deref_read_ub_real_steps`, and
   `wit_lm3_2_reborrow_tree_write_and_parent_read_real_steps`** (Section 6):
   `&!` validation failing even on a live stack pointer, zero-variant and
   `u8`-tagged enum discriminant validation against `decodeValueFromBytes`, the
   invalid-`bool` deref-read UB in both machines on real steps, and a 5-step Tree Borrows
   child-write/parent-read chain driven through the `StateRelLM3_2Tree`
   simulations.
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

private theorem step_safeRef_deref_read_machine_and_preserves
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
    m'.machine = m.machine ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) := by
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
            refine ⟨rfl, ?_⟩
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
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k :=
  (step_safeRef_deref_read_machine_and_preserves hstate hopKind hbb hstmt hdecl_dst hdecl_ref
    href_ty hdst_prim himm hlive_ref hstep).2

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
      StateRelLM3_2 lm32RefBody s₄ m₄ [{ entry with perm := .disabled }] ∧
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
  let entryDis : AllocMapEntry := { entry with perm := .disabled }
  let s₄ := mkWitStateLM32 lm32RefBody 7
    [.init (.scalar ⟨42, 8⟩), .dead, .dead] [entryDis.toBorrowEntry] 2
  have hs₄ : stepMirFn lm32RefBody s₃ = .step s₄ := rfl
  have hsim₄ := step_storageDead_lm3_2_simulation hrel₃ hphase rfl rfl rfl (by decide)
  obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_2_of_anneal_step hsim₄ hs₄
  change StateRelLM3_2 lm32RefBody s₄ m₄ [entryDis] at hrel₄
  have hm₄_dead : m₄.machine.memory.live.find? (fun x => x.1 == lm31AllocId1) = none := by
    obtain ⟨tf₄, hframes₄, _, _, _, _, _, _, _, _, halloc₄, _⟩ := id hrel₄
    exact (halloc₄.local_alloc_sync tf₄ hframes₄ entryDis (List.Mem.head _)).2 rfl
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
1. `_2 = &mut _1` (`evalRvalue_ref_simulation`), creating the `.reserved`
   borrow `entry`,
2. `_3 = move _2` (`step_safeRef_use_simulation`, deinitializing `_2`),
3. `*_3 = const 99_u64` (`step_safeRef_deref_write_simulation_explicit`), whose
   child write activates `entry` to `.active`,
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
      StateRelLM3_2 lm32MutRefChainBody s₃ m₃ [{ entry with perm := .active }] ∧
      stepMirFn lm32MutRefChainBody s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_2 lm32MutRefChainBody s₄ m₄ [{ entry with perm := .active }] ∧
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
  let entryAct : AllocMapEntry := { entry with perm := .active }
  let borActW := [entryAct.toBorrowEntry]
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
    [.uninit, .init (.scalar ⟨99, 8⟩), .uninit, .init ptr1, .uninit] borActW 2
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
      exact ⟨rfl, Or.inr rfl, rfl⟩
  have hsim₃ := step_safeRef_deref_write_simulation_explicit hrel₂ hphase rfl rfl
    rfl rfl (valTy := u64Ty) (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
    (fun tf _ => constU64_wellTypedLM32 lm32MutRefChainBody tf 99 (by decide))
    himm₂_3 hlive₃
  change StepRelLM3_2 lm32MutRefChainBody m₂ [entryAct]
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
    [.init (.scalar ⟨99, 8⟩), .init (.scalar ⟨99, 8⟩), .uninit, .init ptr1, .uninit] borActW 2
  have hs₄ : stepMirFn lm32MutRefChainBody s₃ = .step s₄ := rfl
  have himm₃_03 : ∀ tf, m₃.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 ∧ IsImmediateFrameLocal tf 3 :=
    fun tf htf => ⟨himm₃_ne1 tf htf 0 (by decide), himm₃_ne1 tf htf 3 (by decide)⟩
  have hlive₄ : ∀ ptrVal, get? s₃.frame.locals 3 = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ [entryAct], e.tag = ptrVal.tag →
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
      dsimp only [entryAct, entry, refAllocMapEntry] at hdecl
      have h0 : get? lm32MutRefChainBody.localDecls 1 = some u64Decl := rfl
      rw [h0] at hdecl; injection hdecl with hd; subst hd; rfl
  have hsim₄ := step_safeRef_deref_read_simulation_explicit hrel₃ hphase (Or.inl rfl)
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₃_03 hlive₄
  change StepRelLM3_2 lm32MutRefChainBody m₃ [entryAct]
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
        refine ⟨(fun h => nomatch h), (fun h => nomatch h), rfl, (fun h => nomatch h),
          (fun ⟨_, hne⟩ => hne rfl), fun d hd => ?_⟩
        dsimp only [entryAct, entry, refAllocMapEntry] at hd
        have h0 : get? lm32MutRefChainBody.localDecls 1 = some u64Decl := rfl
        rw [h0] at hd; injection hd with hd'; subst hd'; rfl)
  obtain ⟨⟨s₅, hs₅, hloc₅⟩, m₅, tf₅, borTag, hm₅, htf₅, _, hval₅⟩ :=
    hreb.2 { allocId := 1, offsetBytes := 0 } entryAct rfl (List.Mem.head _) rfl
      (fun h => nomatch h)
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
1. **Dangling safe-reference reborrow (now a UB simulation)**: from pointer-free
   `StateRel`, `_2 = &_1` and `StorageDead(_1)` step in lockstep to
   `StateRelLM3_2`-related states `(s₂, m₂)`, after which `_3 = &*_2` raises
   undefined behavior in BOTH Anneal (`stepMirFn`, `MirStepNode.fail .ub`) and
   `Miri.Interpreter.Step.step`
   (`undefinedBehavior "dereferencing a dangling reference"`,
   `evalRvalue_reborrow_safeRef_dangling_simulation`).
2. **Integer-scalar raw-pointer reborrow (genuine divergence)**: from
   pointer-free `StateRel` where `_1 : *const u64` holds `0` without provenance,
   `_2 = &*_1` fails with UB in Anneal (`stepMirFn`) while
   `Miri.Interpreter.Step.step` steps and writes a provenance-less scalar into
   `_2` (`evalRvalue_reborrow_rawPtr_int_divergence`). -/
theorem wit_lm3_2_safeRef_dangling_reborrow_and_rawPtr_int_divergences :
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let hooks := annealStepHooks lm32DanglingReborrowBody.localDecls
        lm32DanglingReborrowBody.layouts
      let entry := refAllocMapEntry lm32DanglingReborrowBody.localDecls
        lm32DanglingReborrowBody.layouts .shared 1 1 lm31AllocId1
      stepMirFn lm32DanglingReborrowBody lm32DanglingReborrowAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm32DanglingReborrowMiriPre = (m₁, .ok true) ∧
      StateRelLM3_2 lm32DanglingReborrowBody s₁ m₁ [entry] ∧
      stepMirFn lm32DanglingReborrowBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2 lm32DanglingReborrowBody s₂ m₂ [{ entry with perm := .disabled }] ∧
      stepMirFn lm32DanglingReborrowBody s₂ = .fail .ub ∧
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
    let entryDis : AllocMapEntry := { entry with perm := .disabled }
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
      [.uninit, .dead, .init ptr1, .uninit] [entryDis.toBorrowEntry] 2
    have hs₂ : stepMirFn lm32DanglingReborrowBody s₁ = .step s₂ := rfl
    have hsim₂ := step_storageDead_lm3_2_simulation hrel₁ hphase rfl rfl rfl (by decide)
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_2_of_anneal_step hsim₂ hs₂
    change StateRelLM3_2 lm32DanglingReborrowBody s₂ m₂ [entryDis] at hrel₂
    have himm₂_step := step_storageDead_lm3_2_preserves hrel₁ rfl rfl rfl (by decide) hm₂
    have himm₂_2 : ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 := by
      intro tf₂ htf₂
      obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm₂_step tf₁ tf₂ htf₁ htf₂ 2 (himm₁_ne1 tf₁ htf₁ 2 (by decide))
    obtain ⟨_, hs₃, m₃, hm₃⟩ := evalRvalue_reborrow_safeRef_dangling_simulation
      hrel₂ hphase (dstIdx := 3) (refIdx := 2) (bk := .shared)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₂_2
      (fun h => nomatch h) (ptrVal := { allocId := 1, offsetBytes := 0 }) rfl
      (e := entryDis) (List.Mem.head _) rfl rfl
    exact ⟨s₁, s₂, m₁, m₂, m₃, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃⟩
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

/-! ## 5. Pass B2 Validity, OOB/Misaligned UB Simulations, Permission Divergences, PlaceMention, and Unified Trace Witnesses -/

/-- `&()` as an Anneal type. -/
def refUnitTyLM32 : Ty := { kind := .ref .not (.tuple .nil), layoutIdx := 0 }

/-- Local declaration of type `&()`. -/
def refUnitDeclLM32 : LocalDecl := { mutability := .mut, ty := refUnitTyLM32, debugName := none }

/-- `u8` as an Anneal type. -/
def u8TyLM32 : Ty := { kind := .uint .u8, layoutIdx := 0 }

/-- Local declaration of type `u8`. -/
def u8DeclLM32 : LocalDecl := { mutability := .mut, ty := u8TyLM32, debugName := none }

/-- `u16` as an Anneal type. -/
def u16TyLM32 : Ty := { kind := .uint .u16, layoutIdx := 0 }

/-- Local declaration of type `u16`. -/
def u16DeclLM32 : LocalDecl := { mutability := .mut, ty := u16TyLM32, debugName := none }

/-- `&mut u16` as an Anneal type. -/
def refMutU16TyLM32 : Ty := { kind := .ref .mut (.uint .u16), layoutIdx := 0 }

/-- Local declaration of type `&mut u16`. -/
def refMutU16DeclLM32 : LocalDecl :=
  { mutability := .mut, ty := refMutU16TyLM32, debugName := none }

/-- Constant `u16` operand. -/
def constU16LM32 (n : Nat) : ConstOperand :=
  { ty := u16TyLM32, val := .scalar (.int ⟨n, 2⟩) }

/-- Misalignment record for a `u16` (`align = 2`) reference at byte offset `1`
inside `lm31AllocId1` (`has = 1`, `required = 2`). -/
def lm32MisalignU16At1 : Miri.Memory.Misalignment :=
  ⟨Miri.ABI.Align.ONE, (translateTy u16TyLM32 emptyLayoutTable).layout.align.abi⟩

/-- Shared 4-local Anneal pre-state for Pass `B2` witnesses. -/
def mkPre4AnnealLM32 (b : CapturedMir) (slot₁ : LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, slot₁, .uninit, .uninit] }
    memory := (initMachineState b []).memory }

/-- Shared 4-local `lean-miri` frame pre-state for Pass `B2` witnesses. -/
def mkPre4MiriFrameLM32 (b : CapturedMir) (retTy : Ty)
    (mls₁ : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody b
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy retTy b.layouts) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      mls₁,
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- Shared 4-local `lean-miri` step state for Pass `B2` witnesses. -/
def mkPre4MiriLM32 (b : CapturedMir) (retTy : Ty)
    (mls₁ : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    AnnealStepState :=
  { stack := ⟨#[mkPre4MiriFrameLM32 b retTy mls₁]⟩, machine := AnnealMachine.empty }

private theorem mkPre4_stateRel_and_imm
    (b : CapturedMir) (d0 d1 d2 d3 : LocalDecl)
    (hdecls : b.localDecls = [d0, d1, d2, d3])
    (slot₁ : LocalSlot)
    (mls₁ : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
    (hnoind₁ : ∀ mp, mls₁.value ≠ .live (.indirect mp))
    (hrel₁ : LocalRel AnnealMachine.empty d1 b.layouts slot₁ mls₁) :
    StateRel b (mkPre4AnnealLM32 b slot₁) (mkPre4MiriLM32 b d0.ty mls₁) ∧
    (∀ tf, (mkPre4MiriLM32 b d0.ty mls₁).stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k) := by
  have himm_all : ∀ tf, (mkPre4MiriLM32 b d0.ty mls₁).stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
    intro tf h k mls hmls mp hmp
    injection h with h₁; injection h₁ with h₂; subst h₂
    match k with
    | 0 | 2 | 3 => simp [mkPre4MiriFrameLM32] at hmls; subst hmls; cases hmp
    | 1 => simp [mkPre4MiriFrameLM32] at hmls; subst hmls; exact hnoind₁ mp hmp
    | _ + 4 => simp [mkPre4MiriFrameLM32] at hmls
  refine ⟨?_, himm_all⟩
  refine StateRel.mk (mkPre4MiriFrameLM32 b d0.ty mls₁) rfl rfl ⟨translateTy d0.ty b.layouts, rfl⟩
    ?_ rfl rfl rfl rfl rfl
    (MemoryAllocDisjoint.of_no_indirect _ (himm_all _ rfl))
  refine ⟨rfl, rfl, by simp [mkPre4AnnealLM32, hdecls], by simp [mkPre4MiriFrameLM32, hdecls], ?_⟩
  intro i decl slot mls hdecl hslot hmls
  rw [hdecls] at hdecl
  match i with
  | 0 =>
    have hd : decl = d0 := by simpa [get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [mkPre4AnnealLM32, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [mkPre4MiriFrameLM32] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = d1 := by simpa [get?] using hdecl.symm
    have hs : slot = slot₁ := by simpa [mkPre4AnnealLM32, get?] using hslot.symm
    have hm : mls = mls₁ := by simpa [mkPre4MiriFrameLM32] using hmls.symm
    subst hd hs hm
    exact hrel₁
  | 2 =>
    have hd : decl = d2 := by simpa [get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [mkPre4AnnealLM32, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [mkPre4MiriFrameLM32] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 3 =>
    have hd : decl = d3 := by simpa [get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [mkPre4AnnealLM32, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [mkPre4MiriFrameLM32] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 4 =>
    simp [get?] at hdecl

private theorem lm32_misalign_u16_at_1 :
    annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 1))
      (translateTy u16TyLM32 emptyLayoutTable).layout.align.abi =
      .ok (some lm32MisalignU16At1) := by
  with_unfolding_all rfl

/-- **`wit_lm3_2_unit_zst_and_misaligned_ref_validity`**:
1. **Zero-sized `&()` validation (`validatePlace_ref_unit_zst_simulation`)**:
   - Null `&()` (`0_u64`) and non-null integer `&()` (`1_u64`, e.g.
     `NonNull::<()>::dangling().as_ref()`): `0_u64` fails with
     `"validation: null or maybe-null safe pointer"`, while `1_u64` succeeds
     (`.ok ()`) without provenance or a backing allocation;
   - Stack-pointer `&()` after `_2 = &_1; StorageDead(_1)`: both steps run in
     lockstep to `StateRelLM3_2`-related states `(s₂, m₂)`, and `validatePlace`
     on `_2 : &()` succeeds (`.ok () m₂`) despite `lm31AllocId1` being dead.
2. **Misaligned `&mut u16` validation (`validatePlace_ref_misaligned_simulation`)**:
   After promoting `_1 : u64` (`8` bytes) at `lm31AllocId1` and storing an
   in-bounds misaligned `&mut u16` pointer at `offsetBytes = 1` (`1 + 2 ≤ 8`)
   in `_3` under `StateRelLM3_2`, `validatePlace` rejects `_3` with
   `classifyPointerAlignmentError ⟨"", #[]⟩ (.reference true) lm32MisalignU16At1`. -/
theorem wit_lm3_2_unit_zst_and_misaligned_ref_validity :
    (∃ (b : CapturedMir) (s₀ s₁ : MachineState) (m₀ m₁ : AnnealStepState)
        (tf₀ tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
        (_ : 1 < tf₀.locals.size) (_ : 1 < tf₁.locals.size),
      StateRel b s₀ m₀ ∧ m₀.stack.frames = #[tf₀] ∧
      get? s₀.frame.locals 1 = some (.init (.scalar ⟨0, 8⟩)) ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
        refUnitTyLM32 4
        ⟨.local 0 1 none tf₀.localsIdentity, translateTy refUnitTyLM32 b.layouts⟩
        false false m₀ =
        .error (.undefinedBehavior "validation: null or maybe-null safe pointer") m₀ ∧
      StateRel b s₁ m₁ ∧ m₁.stack.frames = #[tf₁] ∧
      get? s₁.frame.locals 1 = some (.init (.scalar ⟨1, 8⟩)) ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
        refUnitTyLM32 4
        ⟨.local 0 1 none tf₁.localsIdentity, translateTy refUnitTyLM32 b.layouts⟩
        false false m₁ = .ok () m₁) ∧
    (∃ (b : CapturedMir) (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
        (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
            layout := some (translateTy u64Ty) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2 b s₂ m₂ [{ entry with perm := .disabled }] ∧
      m₂.stack.frames = #[tf₂] ∧
      get? s₂.frame.locals 1 = some .dead ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
        refUnitTyLM32 4
        ⟨.local 0 2 none tf₂.localsIdentity, translateTy refUnitTyLM32 b.layouts⟩
        false false m₂ = .ok () m₂) ∧
    (∃ (b : CapturedMir) (s_mis : MachineState) (m_mis : AnnealStepState)
        (tf_mis : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
      StateRelLM3_2 b s_mis m_mis [entry] ∧
      m_mis.stack.frames = #[tf_mis] ∧
      get? s_mis.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 1 } 8)) ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
        refMutU16TyLM32 4
        ⟨.local 0 3 none tf_mis.localsIdentity, translateTy refMutU16TyLM32 b.layouts⟩
        false false m_mis =
      .error (Miri.Interpreter.ValidityVisitor.classifyPointerAlignmentError
        ⟨"", #[]⟩ (.reference true) lm32MisalignU16At1) m_mis) := by
  refine ⟨?_, ?_, ?_⟩
  · let b : CapturedMir :=
      { defPath := "lm_3_2_witness::unit_zst_scalar"
        phase := .runtimePostCleanup, role := .subject, argCount := 0
        localDecls := [u64Decl, refUnitDeclLM32, u64Decl, u64Decl]
        basicBlocks := [{ statements := [], terminator := mkTerm .return_, isCleanup := false }]
        fnAbi := fnAbiU64, layouts := emptyLayoutTable, allocations := [] }
    have hrel_sc0 : ScalarRel ⟨0, 8⟩ (Miri.Memory.ScalarInt.ofUInt64 0) :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
    have hrel_sc1 : ScalarRel ⟨1, 8⟩ (Miri.Memory.ScalarInt.ofUInt64 1) :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
    let mls0 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
      { value := .live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0)))),
        layout := some (translateTy refUnitTyLM32) }
    let mls1 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
      { value := .live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 1)))),
        layout := some (translateTy refUnitTyLM32) }
    obtain ⟨hs0, _⟩ := mkPre4_stateRel_and_imm b u64Decl refUnitDeclLM32 u64Decl u64Decl rfl
      (.init (.scalar ⟨0, 8⟩)) mls0 (fun _ h => nomatch h)
      (.immediate _ _ (some (translateTy refUnitTyLM32)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ hrel_sc0 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
    obtain ⟨hs1, _⟩ := mkPre4_stateRel_and_imm b u64Decl refUnitDeclLM32 u64Decl u64Decl rfl
      (.init (.scalar ⟨1, 8⟩)) mls1 (fun _ h => nomatch h)
      (.immediate _ _ (some (translateTy refUnitTyLM32)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ hrel_sc1 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
    have hlt0 : 1 < (mkPre4MiriFrameLM32 b u64Ty mls0).locals.size := by decide
    have hlt1 : 1 < (mkPre4MiriFrameLM32 b u64Ty mls1).locals.size := by decide
    have hv0 := ((validatePlace_ref_unit_zst_simulation hs0.toLM3_1.toLM3_2 rfl hlt0
      (refTy := refUnitTyLM32) (refMut := .not) rfl 3).1 hrel_sc0 rfl (by decide) rfl).1 rfl
    have hv1 := ((validatePlace_ref_unit_zst_simulation hs1.toLM3_1.toLM3_2 rfl hlt1
      (refTy := refUnitTyLM32) (refMut := .not) rfl 3).1 hrel_sc1 rfl (by decide) rfl).2
      (by decide)
    exact ⟨b, _, _, _, _, _, _, hlt0, hlt1, hs0, rfl, rfl, hv0, hs1, rfl, rfl, hv1⟩
  · let b : CapturedMir :=
      { defPath := "lm_3_2_witness::unit_zst_dangling"
        phase := .runtimePostCleanup, role := .subject, argCount := 0
        localDecls := [u64Decl, u64Decl, refUnitDeclLM32, u64Decl]
        basicBlocks := [
          { statements := [
              mkStmt (.assign (local_ 2) (.ref .shared (local_ 1))),
              mkStmt (.storageDead 1)],
            terminator := mkTerm .return_, isCleanup := false }]
        fnAbi := fnAbiU64, layouts := emptyLayoutTable, allocations := [] }
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let mls42 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
      { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
        layout := some (translateTy u64Ty) }
    obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b u64Decl u64Decl refUnitDeclLM32 u64Decl rfl
      (.init (.scalar ⟨42, 8⟩)) mls42 (fun _ h => nomatch h)
      (.immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
    let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1
    let entryDis : AllocMapEntry := { entry with perm := .disabled }
    let s₁ := mkWitStateLM32 b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
      [entry.toBorrowEntry] 2
    have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ := rfl
    have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
      (dstIdx := 2) (targetIdx := 1) (bk := .shared)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
    have himm₁_step := step_ref_preserves_ne hrel₀ (dstIdx := 2) (targetIdx := 1) (bk := .shared)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    let s₂ := mkWitStateLM32 b 2
      [.uninit, .dead, .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
      [entryDis.toBorrowEntry] 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    have hsim₂ := step_storageDead_lm3_2_simulation hrel₁ hphase rfl rfl rfl (by decide)
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_2_of_anneal_step hsim₂ hs₂
    change StateRelLM3_2 b s₂ m₂ [entryDis] at hrel₂
    have himm₂_step := step_storageDead_lm3_2_preserves hrel₁ rfl rfl rfl (by decide) hm₂
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    obtain ⟨tf₂, htf₂, _, _, hfr₂, _⟩ := id hrel₂
    have himm₂_2 : IsImmediateFrameLocal tf₂ 2 :=
      himm₂_step tf₁ tf₂ htf₁ htf₂ 2
        (himm₁_step _ tf₁ rfl htf₁ 2 (by decide) (himm₀ _ rfl 2))
    obtain ⟨slot₂, mls₂, _, hlt₂, hslot₂, hmls₂, hmls₂_eq, hloc₂⟩ :=
      hfr₂.lookup_local (idx := 2) (decl := refUnitDeclLM32) rfl
    have hs₂_eq : slot₂ = .init (.ptr { allocId := 1, offsetBytes := 0 } 8) :=
      Option.some.inj hslot₂.symm
    subst hs₂_eq
    rcases hloc₂.ref_immediate_cases (mutability := .not) (pointeeKind := .tuple .nil) rfl
        (himm₂_2 mls₂ hmls₂) with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨p', mptr, hp_eq, hptrRel, hm_ptr⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv; injection hv with hp _; subst hp
      have hval₂ : (tf₂.locals[2]'hlt₂).value =
          .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))) := by
        rw [hmls₂_eq, hm_ptr]
      have hval_ok := (validatePlace_ref_unit_zst_simulation hrel₂ htf₂ hlt₂
        (refTy := refUnitTyLM32) (refMut := .not) rfl 3).2 (e := entryDis) hptrRel (List.Mem.head _) rfl hval₂
      exact ⟨b, s₁, s₂, m₁, m₂, tf₂, hs₁, hm₁, hs₂, hm₂, hrel₂, htf₂, rfl, hval_ok⟩
  · let b : CapturedMir :=
      { defPath := "lm_3_2_witness::misalign_ref_validity"
        phase := .runtimePostCleanup, role := .subject, argCount := 0
        localDecls := [u16DeclLM32, u64Decl, refMutU64Decl, refMutU16DeclLM32]
        basicBlocks := [
          { statements := [
              mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
              mkStmt .nop],
            terminator := mkTerm .return_, isCleanup := false }]
        fnAbi := fnAbiU64, layouts := emptyLayoutTable, allocations := [] }
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let mls42 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
      { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
        layout := some (translateTy u64Ty) }
    obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b u16DeclLM32 u64Decl refMutU64Decl
      refMutU16DeclLM32 rfl (.init (.scalar ⟨42, 8⟩)) mls42 (fun _ h => nomatch h)
      (.immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
    let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
    let s₁ := mkWitStateLM32 b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
      [entry.toBorrowEntry] 2
    have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ := rfl
    have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
      (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
    have himm₁_step := step_ref_preserves_ne hrel₀ (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    obtain ⟨tf₁, htf₁, _, _, hfr₁, _⟩ := id hrel₁
    have himm₁_3 : IsImmediateFrameLocal tf₁ 3 :=
      himm₁_step _ tf₁ rfl htf₁ 3 (by decide) (himm₀ _ rfl 3)
    obtain ⟨slot₃, mls₃, _, hlt₃, hslot₃, hmls₃, hmls₃_eq, hloc₃⟩ :=
      hfr₁.lookup_local (idx := 3) (decl := refMutU16DeclLM32) rfl
    have hs₃_eq : slot₃ = .uninit := Option.some.inj hslot₃.symm
    subst hs₃_eq
    rcases hloc₃.ref_immediate_cases (mutability := .mut) (pointeeKind := .uint .u16) rfl
        (himm₁_3 mls₃ hmls₃) with
      ⟨h, _⟩ | ⟨_, hm_un⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩
    · cases h
    · have hval₃_old : (tf₁.locals[3]'hlt₃).value = .live (.immediate .uninit) := by
        rw [hmls₃_eq, hm_un]
      let p_mis : ProvenancePtr := { allocId := 1, offsetBytes := 1 }
      let mptr_mis : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 1),
          .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩
      have hptr_mis : PtrRel [entry] p_mis mptr_mis :=
        ⟨lm31AllocId1, Miri.Memory.BorTag.one, rfl, by decide, by decide, rfl,
          entry, List.Mem.head _, rfl, rfl⟩
      have hnew₃ : LocalRelLM3_2 m₁.machine ([entry].map id) refMutU16DeclLM32 b.layouts
          (.init (.ptr p_mis 8))
          { tf₁.locals[3]'hlt₃ with
            value := .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr_mis))) } := by
        rw [List.map_id]
        exact .ref p_mis mptr_mis _ .mut (.uint .u16)
          (by rw [hmls₃_eq]; exact hloc₃.cachedLayout_eq) rfl hptr_mis
      have hrel_mis := hrel₁.advance_write_immediate_perm_map htf₁ id
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (dstIdx := 3) (dstDecl := refMutU16DeclLM32) rfl
        (fun e he => by cases he with | head => decide | tail _ h => nomatch h)
        hval₃_old hnew₃ rfl rfl rfl rfl (by rw [List.map_id]; rfl) rfl
      rw [List.map_id] at hrel_mis
      let tf_mis : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
        { { tf₁ with
            locals := tf₁.locals.set 3
              { tf₁.locals[3]'hlt₃ with
                value := .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr_mis))) }
              hlt₃ } with
          location := .mir ⟨0, 2⟩ }
      have hlt₃' : 3 < tf_mis.locals.size := by
        dsimp only [tf_mis]; rw [Array.size_set]; exact hlt₃
      have hval₃_new : (tf_mis.locals[3]'hlt₃').value =
          .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr_mis))) := by
        dsimp only [tf_mis]; rw [Array.getElem_set_self]
      have hverr := validatePlace_ref_misaligned_simulation hrel_mis rfl hlt₃'
        (pointeeTy := u16TyLM32) (Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩)))
        (refTy := refMutU16TyLM32) (refMut := .mut) rfl hptr_mis (List.Mem.head _) rfl
        (allocDecl := u64Decl) rfl (slot := .init (.scalar ⟨42, 8⟩)) rfl (by simp) (by decide)
        lm32_misalign_u16_at_1 hval₃_new 3
      exact ⟨b, _, _, tf_mis, hrel_mis, rfl, rfl, hverr⟩
    · cases h
    · cases h

/-- **`wit_lm3_2_oob_and_misaligned_deref_ub_simulations`**:
Concrete instances of all four safe-reference OOB and misaligned dereference
read/write UB simulations, in each of which BOTH machines raise undefined
behavior:
1. `step_safeRef_deref_read_oob_simulation` (`_1 : u8`, `_2 : &mut u64`,
   `_0 = copy *_2`);
2. `step_safeRef_deref_write_oob_simulation` (`_1 : u8`, `_2 : &mut u64`,
   `*_2 = 99_u64`);
3. `step_safeRef_deref_read_misaligned_simulation` (`_1 : u64`, `_3 : &mut u16`
   at offset `1`, `_0 = copy *_3`);
4. `step_safeRef_deref_write_misaligned_simulation` (`_1 : u64`, `_3 : &mut u16`
   at offset `1`, `*_3 = 7_u16`). -/
theorem wit_lm3_2_oob_and_misaligned_deref_ub_simulations :
    (∃ (b : CapturedMir) (s₁ : MachineState) (m₁ m₂ : AnnealStepState),
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨7, 1⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 7)))),
            layout := some (translateTy u8TyLM32) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.undefinedBehavior "dereferencing a dangling reference"))) ∧
    (∃ (b : CapturedMir) (s₁ : MachineState) (m₁ m₂ : AnnealStepState),
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨7, 1⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 7)))),
            layout := some (translateTy u8TyLM32) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.undefinedBehavior "dereferencing a dangling reference"))) ∧
    (∃ (b : CapturedMir) (s_mis : MachineState) (m_mis m_out : AnnealStepState),
      let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
      StateRelLM3_2 b s_mis m_mis [entry] ∧
      stepMirFn b s_mis = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m_mis =
        (m_out, .error (.undefinedBehavior "dereferencing an unaligned reference"))) ∧
    (∃ (b : CapturedMir) (s_mis : MachineState) (m_mis m_out : AnnealStepState),
      let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
      StateRelLM3_2 b s_mis m_mis [entry] ∧
      stepMirFn b s_mis = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m_mis =
        (m_out, .error (.undefinedBehavior "dereferencing an unaligned reference"))) := by
  have hrel7 : ScalarRel ⟨7, 1⟩ (Miri.Memory.ScalarInt.ofUInt8 7) :=
    ⟨Or.inl rfl, by decide, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) OOB safe-ref deref read (`_1 : u8` = 1 byte, `_2 : &mut u64` = 8 bytes)
    let b : CapturedMir :=
      { defPath := "lm_3_2_witness::oob_deref_read"
        phase := .runtimePostCleanup, role := .subject, argCount := 0
        localDecls := [u64Decl, u8DeclLM32, refMutU64Decl, u64Decl]
        basicBlocks := [
          { statements := [
              mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
              mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 2))))],
            terminator := mkTerm .return_, isCleanup := false }]
        fnAbi := fnAbiU64, layouts := emptyLayoutTable, allocations := [] }
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let mls7 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
      { value := .live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 7)))),
        layout := some (translateTy u8TyLM32) }
    obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b u64Decl u8DeclLM32 refMutU64Decl u64Decl rfl
      (.init (.scalar ⟨7, 1⟩)) mls7 (fun _ h => nomatch h)
      (.immediate _ _ (some (translateTy u8TyLM32)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ hrel7 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
    let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
    let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let s₁ := mkWitStateLM32 b 1 [.uninit, .init (.scalar ⟨7, 1⟩), .init ptr1, .uninit]
      [entry.toBorrowEntry] 2
    have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨7, 1⟩))) = .step s₁ := rfl
    have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
      (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
    have himm₁_step := step_ref_preserves_ne hrel₀ (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    have himm₁_2 : ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 :=
      fun tf htf => himm₁_step _ tf rfl htf 2 (by decide) (himm₀ _ rfl 2)
    obtain ⟨_, hs₂, m₂, hm₂⟩ := step_safeRef_deref_read_oob_simulation hrel₁ hphase
      (Or.inl rfl) rfl rfl (dstDecl := u64Decl) (refDecl := refMutU64Decl) (allocDecl := u8DeclLM32)
      rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₁_2
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (e := entry) (sc := ⟨7, 1⟩)
      rfl (List.Mem.head _) rfl (fun h => nomatch h) rfl rfl (by decide) (fun h => nomatch h)
    exact ⟨b, s₁, m₁, m₂, hs₁, hm₁, hs₂, hm₂⟩
  · -- (2) OOB safe-ref deref write (`_1 : u8` = 1 byte, `_2 : &mut u64` = 8 bytes)
    let b : CapturedMir :=
      { defPath := "lm_3_2_witness::oob_deref_write"
        phase := .runtimePostCleanup, role := .subject, argCount := 0
        localDecls := [u64Decl, u8DeclLM32, refMutU64Decl, u64Decl]
        basicBlocks := [
          { statements := [
              mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
              mkStmt (.assign (derefLocal 2) (.use (.constant (constU64 99))))],
            terminator := mkTerm .return_, isCleanup := false }]
        fnAbi := fnAbiU64, layouts := emptyLayoutTable, allocations := [] }
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let mls7 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
      { value := .live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 7)))),
        layout := some (translateTy u8TyLM32) }
    obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b u64Decl u8DeclLM32 refMutU64Decl u64Decl rfl
      (.init (.scalar ⟨7, 1⟩)) mls7 (fun _ h => nomatch h)
      (.immediate _ _ (some (translateTy u8TyLM32)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ hrel7 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
    let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
    let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let s₁ := mkWitStateLM32 b 1 [.uninit, .init (.scalar ⟨7, 1⟩), .init ptr1, .uninit]
      [entry.toBorrowEntry] 2
    have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨7, 1⟩))) = .step s₁ := rfl
    have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
      (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
    have himm₁_step := step_ref_preserves_ne hrel₀ (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    have himm₁_2 : ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 :=
      fun tf htf => himm₁_step _ tf rfl htf 2 (by decide) (himm₀ _ rfl 2)
    obtain ⟨_, hs₂, m₂, hm₂⟩ := step_safeRef_deref_write_oob_simulation hrel₁ hphase
      rfl rfl (refDecl := refMutU64Decl) (allocDecl := u8DeclLM32) (valTy := u64Ty)
      rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
      (fun tf _ => constU64_wellTypedLM32 b tf 99 (by decide)) himm₁_2
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (e := entry) (sc := ⟨99, 8⟩)
      rfl rfl (List.Mem.head _) rfl (Or.inr rfl) rfl rfl (fun h => nomatch h) (by decide)
    exact ⟨b, s₁, m₁, m₂, hs₁, hm₁, hs₂, hm₂⟩
  · -- (3) Misaligned safe-ref deref read (`_1 : u64`, `_3 : &mut u16` at offset 1, `_0 = copy *_3`)
    let b : CapturedMir :=
      { defPath := "lm_3_2_witness::misalign_deref_read"
        phase := .runtimePostCleanup, role := .subject, argCount := 0
        localDecls := [u16DeclLM32, u64Decl, refMutU64Decl, refMutU16DeclLM32]
        basicBlocks := [
          { statements := [
              mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
              mkStmt .nop,
              mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 3))))],
            terminator := mkTerm .return_, isCleanup := false }]
        fnAbi := fnAbiU64, layouts := emptyLayoutTable, allocations := [] }
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let mls42 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
      { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
        layout := some (translateTy u64Ty) }
    obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b u16DeclLM32 u64Decl refMutU64Decl
      refMutU16DeclLM32 rfl (.init (.scalar ⟨42, 8⟩)) mls42 (fun _ h => nomatch h)
      (.immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
    let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
    let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let s₁ := mkWitStateLM32 b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr1, .uninit]
      [entry.toBorrowEntry] 2
    have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ := rfl
    have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
      (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
    have himm₁_step := step_ref_preserves_ne hrel₀ (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    obtain ⟨tf₁, htf₁, _, _, hfr₁, _⟩ := id hrel₁
    have himm₁_3 : IsImmediateFrameLocal tf₁ 3 :=
      himm₁_step _ tf₁ rfl htf₁ 3 (by decide) (himm₀ _ rfl 3)
    obtain ⟨slot₃, mls₃, _, hlt₃, hslot₃, hmls₃, hmls₃_eq, hloc₃⟩ :=
      hfr₁.lookup_local (idx := 3) (decl := refMutU16DeclLM32) rfl
    have hs₃_eq : slot₃ = .uninit := Option.some.inj hslot₃.symm
    subst hs₃_eq
    rcases hloc₃.ref_immediate_cases (mutability := .mut) (pointeeKind := .uint .u16) rfl
        (himm₁_3 mls₃ hmls₃) with
      ⟨h, _⟩ | ⟨_, hm_un⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩
    · cases h
    · have hval₃_old : (tf₁.locals[3]'hlt₃).value = .live (.immediate .uninit) := by
        rw [hmls₃_eq, hm_un]
      let p_mis : ProvenancePtr := { allocId := 1, offsetBytes := 1 }
      let mptr_mis : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 1),
          .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩
      have hptr_mis : PtrRel [entry] p_mis mptr_mis :=
        ⟨lm31AllocId1, Miri.Memory.BorTag.one, rfl, by decide, by decide, rfl,
          entry, List.Mem.head _, rfl, rfl⟩
      have hnew₃ : LocalRelLM3_2 m₁.machine ([entry].map id) refMutU16DeclLM32 b.layouts
          (.init (.ptr p_mis 8))
          { tf₁.locals[3]'hlt₃ with
            value := .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr_mis))) } := by
        rw [List.map_id]
        exact .ref p_mis mptr_mis _ .mut (.uint .u16)
          (by rw [hmls₃_eq]; exact hloc₃.cachedLayout_eq) rfl hptr_mis
      have hrel_mis := hrel₁.advance_write_immediate_perm_map htf₁ id
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (dstIdx := 3) (dstDecl := refMutU16DeclLM32) rfl
        (fun e he => by cases he with | head => decide | tail _ h => nomatch h)
        hval₃_old hnew₃ rfl rfl rfl rfl (by rw [List.map_id]; rfl) rfl
      rw [List.map_id] at hrel_mis
      let tf_mis : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
        { { tf₁ with
            locals := tf₁.locals.set 3
              { tf₁.locals[3]'hlt₃ with
                value := .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr_mis))) }
              hlt₃ } with
          location := .mir ⟨0, 2⟩ }
      have himm_mis_3 : ∀ tf, ({ m₁ with stack := ⟨#[tf_mis]⟩ } : AnnealStepState).stack.frames = #[tf] →
          IsImmediateFrameLocal tf 3 := by
        intro tf htf mls hmls mp hmp
        injection htf with h₁; injection h₁ with h₂; subst h₂
        dsimp only [tf_mis] at hmls
        rw [Array.getElem?_set_self] at hmls
        injection hmls with hmls'
        rw [← hmls'] at hmp
        cases hmp
      obtain ⟨_, hs_out, m_out, hm_out⟩ :=
        step_safeRef_deref_read_misaligned_simulation hrel_mis hphase (Or.inl rfl) rfl rfl
          (dstDecl := u16DeclLM32) (refDecl := refMutU16DeclLM32) (allocDecl := u64Decl)
          rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩))) himm_mis_3
          (ptrVal := p_mis) (e := entry) (sc := ⟨42, 8⟩)
          rfl (List.Mem.head _) rfl (fun h => nomatch h) rfl rfl (by decide) lm32_misalign_u16_at_1
          (fun h => nomatch h)
      exact ⟨b, _, _, m_out, hrel_mis, hs_out, hm_out⟩
    · cases h
    · cases h
  · -- (4) Misaligned safe-ref deref write (`_1 : u64`, `_3 : &mut u16` at offset 1, `*_3 = 7_u16`)
    let b : CapturedMir :=
      { defPath := "lm_3_2_witness::misalign_deref_write"
        phase := .runtimePostCleanup, role := .subject, argCount := 0
        localDecls := [u16DeclLM32, u64Decl, refMutU64Decl, refMutU16DeclLM32]
        basicBlocks := [
          { statements := [
              mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
              mkStmt .nop,
              mkStmt (.assign (derefLocal 3) (.use (.constant (constU16LM32 7))))],
            terminator := mkTerm .return_, isCleanup := false }]
        fnAbi := fnAbiU64, layouts := emptyLayoutTable, allocations := [] }
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let mls42 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
      { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
        layout := some (translateTy u64Ty) }
    obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b u16DeclLM32 u64Decl refMutU64Decl
      refMutU16DeclLM32 rfl (.init (.scalar ⟨42, 8⟩)) mls42 (fun _ h => nomatch h)
      (.immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
    let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
    let s₁ := mkWitStateLM32 b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
      [entry.toBorrowEntry] 2
    have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ := rfl
    have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
      (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
    have himm₁_step := step_ref_preserves_ne hrel₀ (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    obtain ⟨tf₁, htf₁, _, _, hfr₁, _⟩ := id hrel₁
    have himm₁_3 : IsImmediateFrameLocal tf₁ 3 :=
      himm₁_step _ tf₁ rfl htf₁ 3 (by decide) (himm₀ _ rfl 3)
    obtain ⟨slot₃, mls₃, _, hlt₃, hslot₃, hmls₃, hmls₃_eq, hloc₃⟩ :=
      hfr₁.lookup_local (idx := 3) (decl := refMutU16DeclLM32) rfl
    have hs₃_eq : slot₃ = .uninit := Option.some.inj hslot₃.symm
    subst hs₃_eq
    rcases hloc₃.ref_immediate_cases (mutability := .mut) (pointeeKind := .uint .u16) rfl
        (himm₁_3 mls₃ hmls₃) with
      ⟨h, _⟩ | ⟨_, hm_un⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩
    · cases h
    · have hval₃_old : (tf₁.locals[3]'hlt₃).value = .live (.immediate .uninit) := by
        rw [hmls₃_eq, hm_un]
      let p_mis : ProvenancePtr := { allocId := 1, offsetBytes := 1 }
      let mptr_mis : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 1),
          .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩
      have hptr_mis : PtrRel [entry] p_mis mptr_mis :=
        ⟨lm31AllocId1, Miri.Memory.BorTag.one, rfl, by decide, by decide, rfl,
          entry, List.Mem.head _, rfl, rfl⟩
      have hnew₃ : LocalRelLM3_2 m₁.machine ([entry].map id) refMutU16DeclLM32 b.layouts
          (.init (.ptr p_mis 8))
          { tf₁.locals[3]'hlt₃ with
            value := .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr_mis))) } := by
        rw [List.map_id]
        exact .ref p_mis mptr_mis _ .mut (.uint .u16)
          (by rw [hmls₃_eq]; exact hloc₃.cachedLayout_eq) rfl hptr_mis
      have hrel_mis := hrel₁.advance_write_immediate_perm_map htf₁ id
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (dstIdx := 3) (dstDecl := refMutU16DeclLM32) rfl
        (fun e he => by cases he with | head => decide | tail _ h => nomatch h)
        hval₃_old hnew₃ rfl rfl rfl rfl (by rw [List.map_id]; rfl) rfl
      rw [List.map_id] at hrel_mis
      let tf_mis : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
        { { tf₁ with
            locals := tf₁.locals.set 3
              { tf₁.locals[3]'hlt₃ with
                value := .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr_mis))) }
              hlt₃ } with
          location := .mir ⟨0, 2⟩ }
      have himm_mis_3 : ∀ tf, ({ m₁ with stack := ⟨#[tf_mis]⟩ } : AnnealStepState).stack.frames = #[tf] →
          IsImmediateFrameLocal tf 3 := by
        intro tf htf mls hmls mp hmp
        injection htf with h₁; injection h₁ with h₂; subst h₂
        dsimp only [tf_mis] at hmls
        rw [Array.getElem?_set_self] at hmls
        injection hmls with hmls'
        rw [← hmls'] at hmp
        cases hmp
      have hop_u16 : ∀ tf, WellTypedScalarOperand b tf (.constant (constU16LM32 7)) u16TyLM32 :=
        fun _ => .constScalar (constU16LM32 7) ⟨7, 2⟩ rfl (Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩)))
          (Or.inr (Or.inl rfl)) (by decide) rfl (fun h => nomatch h) (fun h => nomatch h)
      obtain ⟨_, hs_out, m_out, hm_out⟩ :=
        step_safeRef_deref_write_misaligned_simulation hrel_mis hphase rfl rfl
          (refDecl := refMutU16DeclLM32) (allocDecl := u64Decl) (valTy := u16TyLM32)
          rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩))) (fun tf _ => hop_u16 tf) himm_mis_3
          (ptrVal := p_mis) (e := entry) (sc := ⟨7, 2⟩)
          rfl rfl (List.Mem.head _) rfl (Or.inr rfl) rfl rfl (by simp) (by decide)
          lm32_misalign_u16_at_1
      exact ⟨b, _, _, m_out, hrel_mis, hs_out, hm_out⟩
    · cases h
    · cases h

private theorem allocId_eq_one_of_lt_two {a : Miri.Memory.AllocId}
    (hlt : a.value.toNat < 2) : a = lm31AllocId1 := by
  rcases a with ⟨av, hanz⟩
  dsimp only at hlt
  have hne0 : av.toNat ≠ 0 := fun hz => hanz (by rw [← @UInt64.ofNat_toNat av, hz]; rfl)
  have hv1 : av.toNat = 1 := by omega
  have hav1 : av = 1 := by rw [← @UInt64.ofNat_toNat av, hv1]; rfl
  subst hav1
  rfl

private theorem immediate_of_nextAllocId_two
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hnext2 : m.machine.memory.nextAllocId = 2)
    {e : AllocMapEntry} (he : e ∈ allocMap) (ha1 : e.allocId = lm31AllocId1)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (k : Nat) (hne : get? s.frame.locals e.localIdx = some .dead ∨ k ≠ e.localIdx) :
    IsImmediateFrameLocal tf k := by
  intro mls hmls mp hmp
  obtain ⟨tf₀, hframes₀, _, _, hfr, _, _, _, _, _, halloc, hdisj⟩ := id hstate
  rw [hframes] at hframes₀; injection hframes₀ with h0; injection h0 with htf; subst htf
  have hmls_ind : tf.locals[k]? = some ⟨.live (.indirect mp), mls.layout⟩ := by
    rw [hmls]; rcases mls with ⟨v0, l0⟩; dsimp only at hmp; subst hmp; rfl
  obtain ⟨a, la, hprov_a, hl_a⟩ := hfr.indirect_allocId hmls_ind
  have ha_lt2 : a.value.toNat < 2 := by
    have hlt := hsupply.live (a, la) (Array.mem_toList_iff.mp hl_a)
    rw [hnext2] at hlt
    exact hlt
  have ha_eq : a = lm31AllocId1 := allocId_eq_one_of_lt_two ha_lt2
  subst ha_eq
  have hnot_dead : get? s.frame.locals e.localIdx ≠ some .dead := by
    intro hdead
    have hfind_none := (halloc.local_alloc_sync tf hframes e he).2 hdead
    rw [ha1] at hfind_none
    have hfalse := Array.find?_eq_none.mp hfind_none (lm31AllocId1, la)
      (Array.mem_toList_iff.mp hl_a)
    simp at hfalse
  rcases hne with hdead | hk_ne
  · exact hnot_dead hdead
  · obtain ⟨tgtDecl, hdecl_e, _⟩ := halloc.target_decl e he
    obtain ⟨slot_e, _, _, _, hslot_e, _, _, _⟩ := hfr.lookup_local hdecl_e
    have hs_ne : slot_e ≠ .dead := fun hd => hnot_dead (hslot_e.trans (congrArg some hd))
    obtain ⟨⟨lay_e, hlay_e⟩, _, _⟩ :=
      (halloc.local_alloc_sync tf hframes e he).1 slot_e hslot_e hs_ne
    rw [ha1] at hlay_e
    have hprov_e : (stackAllocPlace lm31AllocId1).ptr.provenance.bind
        Miri.Memory.Provenance.getAllocId = some lm31AllocId1 := rfl
    exact hdisj k e.localIdx mp (stackAllocPlace lm31AllocId1) mls.layout lay_e hk_ne
      hmls_ind hlay_e (hprov_a.trans hprov_e.symm)

private theorem step_ref_supply_two
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
    (hm_empty : m.machine = AnnealMachine.empty)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    AllocIdSupplyReady m'.machine.memory ∧ m'.machine.memory.nextAllocId = 2 := by
  have hsupply : AllocIdSupplyReady m.machine.memory := hm_empty ▸ AllocIdSupplyReady.empty
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
      obtain ⟨hsup', hnext', _⟩ := hsupply.of_stackAllocMachine
        (by rw [hm_empty]; decide) (by rw [hm_empty]; intro h; cases h) hres alloc'
      exact ⟨hsup', by rw [hnext', hm_empty]; rfl⟩

private theorem step_storageDead_supply
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne0 : loc ≠ 0)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hnext2 : m.machine.memory.nextAllocId = 2)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    AllocIdSupplyReady m'.machine.memory ∧ m'.machine.memory.nextAllocId = 2 := by
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
  refine ⟨hsupply.of_deallocLocalMemory _, ?_⟩
  cases hval : (tf.locals[loc]'hlt_mf).value with
  | dead => exact hnext2
  | live op =>
    cases op with
    | immediate _ => exact hnext2
    | indirect mp =>
      dsimp only [deallocLocalMemory]
      cases mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId <;> exact hnext2

private theorem step_placeMention_local_machine_eq
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.placeMention ⟨loc, .nil⟩, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine = m.machine := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls, _, hlt_mf, _, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hcache : ∀ l, (tf.locals[loc]'hlt_mf).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls_eq]; exact hloc.cachedLayout_eq
  have hm := evalStatement_placeMention_eq (span := span) hframes hlt_mf hdecl hcache
  rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq] at hstep
  injection hstep with hm' _
  subst hm'
  rfl

private theorem step_placeMention_safeRef_deref_machine_eq
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {bb : BasicBlockData} {refIdx : Local} {refDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    (hptr : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag) (hoff0 : ptrVal.offsetBytes = 0)
    (hlive_t : get? s.frame.locals e.localIdx ≠ some .dead)
    (htgt_kind : ∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
      tgtDecl.ty.kind = pointeeKind)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine = m.machine := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  have himm_r := himm_ref tf hframes
  obtain ⟨slot_r, mls_r, _, hlt_r, hslot_r, hmls_r, hmls_r_eq, hloc_r⟩ :=
    hfr.lookup_local hdecl_ref
  have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
    hloc_r.cachedLayout_eq
  have hsr_eq : slot_r = .init (.ptr ptrVal 8) := Option.some.inj (hslot_r.symm.trans hptr)
  subst hsr_eq
  rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmr_ptr⟩
  · cases h
  · cases h
  · cases h
  · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
    obtain ⟨id₀, borTag, hprov_eq, _, _, hmptr_off, ⟨e', he', htag', _⟩⟩ := hptrRel
    have he_eq : e' = e :=
      mem_eq_of_map_nodup halloc.tags_nodup he' he (htag'.trans htag.symm)
    subst e'; subst id₀
    have hmls_ptr : tf.locals[refIdx]'hlt_r =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
    have hlive_ev := annealEvalPlace_deref_live hframes hlt_r hdecl_ref hmls_ptr hcache_r
    have hder_ptr := annealDerefOperandToMemPlace_safeRef_ptr_live hstate hdecl_ref href_ty
      hpk_prim hprov_eq hmptr_off he hoff0 hlive_t htgt_kind
      (translateTy refDecl.ty body.layouts)
      (st := { m with stack := ⟨#[cacheFrameLocalLayout tf refIdx hlt_r
          (translateTy refDecl.ty body.layouts)]⟩ }) rfl
    have hm_ok : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩) m =
        ({ m with stack := ⟨#[cacheFrameLocalLayout tf refIdx hlt_r
            (translateTy refDecl.ty body.layouts)]⟩ }, .ok ()) := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt translateStmtKind annealStepHooks
      dsimp only [Miri.Interpreter.runRvalue]; rw [hlive_ev, EStateM.bind_eq_ok hder_ptr]; rfl
    rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
      hfr.location_eq] at hstep
    injection hstep with hm' _
    subst hm'
    rfl

private theorem step_safeRef_deref_write_const_supply
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
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag) (hoff0 : ptrVal.offsetBytes = 0)
    (hlive_t : get? s.frame.locals e.localIdx ≠ some .dead)
    (htgt_kind : ∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
      tgtDecl.ty.kind = pointeeKind)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hnext2 : m.machine.memory.nextAllocId = 2)
    (ha1 : e.allocId = lm31AllocId1)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    AllocIdSupplyReady m'.machine.memory ∧ m'.machine.memory.nextAllocId = 2 := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  have himm_r := himm_ref tf hframes
  have hop_tf := hop tf hframes
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨refIdx, .cons .deref .nil⟩ (.constant c) span m
  obtain ⟨slot_r, mls_r, _, hlt_r, hslot_rf, hmls_r, hmls_r_eq, hloc_r⟩ :=
    hfr.lookup_local hdecl_ref
  have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
    hloc_r.cachedLayout_eq
  let tfa := cacheFrameLocalLayout tf refIdx hlt_r (translateTy refDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_ref hlt_r
  have hop_tfa := hop_tf.of_cacheFrameLocalLayout refIdx hlt_r (translateTy refDecl.ty body.layouts)
  have hpt_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 } := by
    rcases hval_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact Or.inl (hval_kind ▸ hk)
    · exact Or.inr (Or.inl (hval_kind ▸ hk))
    · exact Or.inr (Or.inr (Or.inl ⟨it, hval_kind ▸ hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ut, hval_kind ▸ hk⟩))
  have hlay0_eq : translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts =
      translateTy c.ty body.layouts := by
    have h1 := hval_prim.translateTy_layoutIdx body.layouts; rw [hval_kind] at h1; exact h1
  have hsr_eq : slot_r = .init (.ptr ptrVal 8) := Option.some.inj (hslot_rf.symm.trans hslot_r)
  subst hsr_eq
  rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmr_ptr⟩
  · cases h
  · cases h
  · cases h
  · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
    have hmls_r' : tf.locals[refIdx]'hlt_r =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
    have hdst_live := annealEvalPlace_deref_live hframes hlt_r hdecl_ref hmls_r' hcache_r
    obtain ⟨id₀, borTag, hprov_eq, hid_lt, _, hmptr_off, ⟨e', he', htag', _⟩⟩ := id hptrRel
    have he_eq : e' = e :=
      mem_eq_of_map_nodup halloc.tags_nodup he' he (htag'.trans htag.symm)
    subst e'; subst id₀
    obtain ⟨tgtDecl, hdecl_tgt, htgt_prim⟩ := halloc.target_decl e he
    obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
    obtain ⟨slot_t, _, _, _, hslot_t, _, _, _⟩ := hfr.lookup_local hdecl_tgt
    have ht_ne : slot_t ≠ .dead := fun hd => hlive_t (hslot_t.trans (congrArg some hd))
    have hder_ok := annealDerefOperandToMemPlace_safeRef_ptr_live hstate hdecl_ref href_ty
      hpt_prim hprov_eq hmptr_off he hoff0 hlive_t htgt_kind
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
      ⟨m_op, msg_op, _, hm_op_ub⟩ | ⟨sc, msc, tf', _, hm_op_ok, hstate_tf', himm_sc, _, _⟩
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
          ← hval_prim.translateTy_layoutIdx body.layouts, htgt_kind tgtDecl hdecl_tgt, hval_kind]
      obtain ⟨_, _, hshape_fn⟩ := hlive_sync slot_t hslot_t ht_ne
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
      refine ⟨hsupply.of_setLive ?_ _, hnext2⟩
      rw [ha1, hnext2]; decide

private theorem step_safeRef_use_machine_eq
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {bb : BasicBlockData} {dstIdx srcIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl : LocalDecl} {srcMut dstMut : Mutability} {srcPointee dstPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .ref srcMut srcPointee)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    {p : ProvenancePtr}
    (hslot_src : get? s.frame.locals srcIdx = some (.init (.ptr p 8)))
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine = m.machine := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_dst, himm_src⟩ := himm tf hframes
  obtain ⟨slot_d, mls_d, _, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, hlt_af_s, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    (hstate_a.frame_rel_singleton rfl).lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa := himm_src.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  have himm_d_tfa := himm_dst.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have himm_d_tfb := himm_d_tfa.cache_layout hlt_sa (translateTy srcDecl.ty body.layouts)
  have himm_s_tfb := himm_s_tfa.cache_layout hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hss_eq : slot_s = .init (.ptr p 8) := Option.some.inj (hslot_s.symm.trans hslot_src)
  subst hss_eq
  rcases hloc_s.ref_immediate_cases hsrc_ty (himm_s_tfa mls_s hmls_s) with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨p', mptr, hp_eq, _, hms_ptr⟩
  · cases h
  · cases h
  · cases h
  · injection hp_eq with hv_eq; injection hv_eq with hp_eq'; subst hp_eq'
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_ptr; subst hms_ptr; rfl
    have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
      ⟨dstIdx, .nil⟩ (opKind ⟨srcIdx, .nil⟩) span m
    have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
    obtain ⟨tf_mid, s_mid, hstate_mid, himm_d_mid, hlive_mid, hloc_mid, hm_w⟩ :
        ∃ (tf_mid : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
          (s_mid : MachineState),
          StateRelLM3_2 body s_mid { m with stack := ⟨#[tf_mid]⟩ } allocMap ∧
          IsImmediateFrameLocal tf_mid dstIdx ∧
          get? s_mid.frame.locals dstIdx ≠ some .dead ∧
          tf_mid.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ ∧
          Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨srcIdx, .nil⟩)), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
            { m with stack := ⟨#[tf_mid]⟩ } := by
      rcases hopKind with rfl | rfl
      · have htr_copy : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
        have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
          (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
        refine ⟨tfb, s, hstate_b, himm_d_tfb, hdst_live,
          (hstate_b.frame_rel_singleton rfl).location_eq, ?_⟩
        rw [hm_stmt, htr_dst, htr_copy]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
      · have htr_move : translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ := rfl
        have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
          (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
        have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hslot_src
          (by simp) himm_s_tfb hlt_sb
        have hlive_mid : get? (s.frame.locals.set srcIdx .uninit) dstIdx ≠ some .dead := by
          rw [get?_eq_getElem?, List.getElem?_set]
          by_cases h_eq : srcIdx = dstIdx
          · subst h_eq; simp [hlt_af_s]
          · simp only [h_eq, ↓reduceIte, ← get?_eq_getElem?]; exact hdst_live
        refine ⟨deinitFrameLocal tfb srcIdx hlt_sb,
          { s with frame := { s.frame with locals := s.frame.locals.set srcIdx .uninit } },
          hstate_mid, himm_d_tfb.deinit_local hlt_sb, hlive_mid,
          (hstate_mid.frame_rel_singleton rfl).location_eq, ?_⟩
        rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
    obtain ⟨slot_dm, mls_dm, _, hlt_dm, hslot_dm, hmls_dm, _, hloc_dm⟩ :=
      (hstate_mid.frame_rel_singleton rfl).lookup_local hdecl_dst
    have hsdm_ne : slot_dm ≠ .dead := fun hd => hlive_mid (hslot_dm.trans (congrArg some hd))
    obtain ⟨oldImm, hmd_imm⟩ : ∃ oldImm, mls_dm.value = .live (.immediate oldImm) := by
      rcases hloc_dm.ref_immediate_cases hdst_ty (himm_d_mid mls_dm hmls_dm) with
        ⟨rfl, _⟩ | ⟨_, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
      · exact absurd rfl hsdm_ne
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    have hdm_live : tf_mid.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_dm.layout⟩ := by
      rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
    have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_live
    have hw_ok := annealWriteImmediate_live
      (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
      (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
      (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dm hget_dm
    have hm_ok : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨srcIdx, .nil⟩)), span⟩) m =
        ({ m with stack := ⟨#[{ tf_mid with
            locals := tf_mid.locals.set dstIdx
              { tf_mid.locals[dstIdx]'hlt_dm with
                value := .live (.immediate
                  (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) }
              hlt_dm }]⟩ }, .ok ()) := by
      rw [hm_w]; unfold Miri.Interpreter.runRvalue; rw [hw_ok]
    rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
      hloc_mid] at hstep
    injection hstep with hm' _
    subst hm'
    rfl

private theorem step_direct_write_promoted_const_supply
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.constant c)), span⟩)
    {dstDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hval_kind : c.ty.kind = dstDecl.ty.kind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame (.constant c) c.ty)
    {e₀ : AllocMapEntry} (he₀ : e₀ ∈ allocMap) (he₀_loc : e₀.localIdx = dstIdx)
    (ha1 : e₀.allocId = lm31AllocId1)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hnext2 : m.machine.memory.nextAllocId = 2)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    AllocIdSupplyReady m'.machine.memory ∧ m'.machine.memory.nextAllocId = 2 := by
  cases he₀_loc
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have hop_tf := hop tf hframes
  have hval_prim : IsPrimScalarTy c.ty := by
    rcases hdst_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact Or.inl (hval_kind.trans hk)
    · exact Or.inr (Or.inl (hval_kind.trans hk))
    · exact Or.inr (Or.inr (Or.inl ⟨it, hval_kind.trans hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ut, hval_kind.trans hk⟩))
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨e₀.localIdx, .nil⟩ (.constant c) span m
  have htr_dst : translatePlace ⟨e₀.localIdx, .nil⟩ = ⟨e₀.localIdx, #[]⟩ := rfl
  obtain ⟨slot_d, mls_d, _, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[e₀.localIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf e₀.localIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hop_tfa := hop_tf.of_cacheFrameLocalLayout e₀.localIdx hlt_d
    (translateTy dstDecl.ty body.layouts)
  rcases evalOperand_scalar_lm3_2_simulation hstate_a rfl hop_tfa hval_prim
      (some (translateTy dstDecl.ty body.layouts)) with
    ⟨m_op, msg_op, _, hm_op_ub⟩ |
    ⟨sc, msc, tf', _, hm_op_ok, hstate_tf', himm_sc, _, htf'_preserve⟩
  · have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use (.constant c)), span⟩) m =
        (m_op, .error (.undefinedBehavior msg_op)) := by
      rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval]; dsimp only []
      have hassoc : ∀ (f : Miri.Interpreter.RvalueImmTy AnnealProv →
          Miri.Interpreter.RvalueM AnnealStepState Unit) st,
          ((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
            (some (translateTy dstDecl.ty body.layouts)) >>= fun opv =>
            annealReadImmediate opv >>= f) st) =
          (((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
            (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>= f) st) := by
        intro f st; simp only [Bind.bind, EStateM.bind]; cases annealEvalOperand
          body.localDecls body.layouts (translateOperand (.constant c))
          (some (translateTy dstDecl.ty body.layouts)) st <;> rfl
      rw [hassoc, EStateM.bind_eq_error hm_op_ub]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      at hstep
    cases hstep
  · obtain ⟨tf₀', hframes_tf', _, _, hfr_tf', _, _, _, _, _, halloc_tf', _⟩ := id hstate_tf'
    injection hframes_tf' with h₁; injection h₁ with htf'; subst htf'
    obtain ⟨_, mls_dc, _, _, _, hmls_dc, _, _⟩ := hfr_tf'.lookup_local hdecl_dst
    have hd_tfa : (tfa.locals[e₀.localIdx]?).map Miri.Interpreter.LocalState.value =
        some mls_d.value := by
      simp [tfa, cacheFrameLocalLayout, Array.getElem?_set_self, hmls_d_eq]
    have hd_Val : mls_dc.value = mls_d.value := by
      have hp := htf'_preserve e₀.localIdx; rw [hd_tfa, hmls_dc] at hp; injection hp
    by_cases hsd_dead : slot_d = .dead
    · subst hsd_dead
      have hmd_dead : mls_d.value = .dead := by
        cases hloc_d with
        | lm3_1 h1 =>
          cases h1 with
          | base hb =>
            cases hb with
            | dead _ _ => rfl
            | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
            | indirect _ _ _ _ hne _ => exact absurd rfl hne
      have hdc_dead : tf'.locals[e₀.localIdx]? = some ⟨.dead, mls_dc.layout⟩ := by
        rw [hmls_dc]; rcases mls_dc with ⟨vd, ld⟩; dsimp only at hd_Val; rw [hd_Val, hmd_dead]
      have hget_dc := frame_getLocal_of_getElem? tf' e₀.localIdx _ hdc_dead
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use (.constant c)), span⟩) m =
          ({ m with stack := ⟨#[tf']⟩ }, .error (.undefinedBehavior "write to dead local")) := by
        rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; dsimp only []
        have hassoc : ∀ (f : Miri.Interpreter.RvalueImmTy AnnealProv →
            Miri.Interpreter.RvalueM AnnealStepState Unit) st,
            ((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
               (some (translateTy dstDecl.ty body.layouts)) >>= fun opv =>
              annealReadImmediate opv >>= f) st) =
            (((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
               (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>= f) st) := by
          intro f st; simp only [Bind.bind, EStateM.bind]; cases annealEvalOperand
            body.localDecls body.layouts (translateOperand (.constant c))
            (some (translateTy dstDecl.ty body.layouts)) st <;> rfl
        rw [hassoc, EStateM.bind_eq_ok hm_op_ok,
          annealWriteImmediate_dead (m := { m with stack := ⟨#[tf']⟩ }) (id0 := tf.localsIdentity)
            rfl hget_dc]
      rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        at hstep
      cases hstep
    · obtain ⟨⟨lay_e, hlay_e⟩, _, hsh_e⟩ :=
        (halloc_tf'.local_alloc_sync tf' rfl e₀ he₀).1 slot_d hslot_d hsd_dead
      obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh_e dstDecl hdecl_dst
      obtain ⟨hid_lt, _, hbase_e⟩ := halloc_tf'.base_addr_valid e₀ he₀
      obtain ⟨sc', msc', hsc_eq, hmsc_eq, hrel_sc, hsz_sc, hbool_val, hchar_val⟩ :=
        (himm_sc.of_ty_kind_eq hval_prim hval_kind).of_primitive_scalar hdst_prim
      injection hsc_eq with hsc'; subst hsc'
      have hmsc' : msc = msc' := by
        injection hmsc_eq with h1; unfold Miri.Memory.Scalar.fromScalarInt at h1
        injection h1 with h2; injection h2
      subst hmsc'
      have hshape_sc : StackScalarAllocShape (translateSizeBytes sc.sizeBytes)
          localAlloc.allocation := hsz_sc ▸ hshape_la
      obtain ⟨alloc', hw_alloc, -⟩ := hshape_sc.writeScalar_readScalar hrel_sc
      have hmsc_sz : msc.size = (translateTy dstDecl.ty body.layouts).layout.size := by
        rw [hrel_sc.size_eq, ← hsz_sc]
      have hw_alloc_lay : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy dstDecl.ty body.layouts).layout.size)
          (.fromScalarInt msc) localAlloc.allocation = .ok () alloc' := by
        rw [← hmsc_sz]; exact hw_alloc
      have hval_sc : annealValidateScalarForTyId (translateTy dstDecl.ty body.layouts).ty
          (.fromScalarInt msc) = true :=
        annealValidateScalarForTyId_of_scalarRel hdst_prim hrel_sc hbool_val hchar_val
      have hget_dc := frame_getLocal_of_getElem? tf' e₀.localIdx _ hlay_e
      have hw_ind := annealWriteImmediate_indirect
        (val := .scalar (.fromScalarInt msc))
        (m := { m with stack := ⟨#[tf']⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hget_dc
      have hw_m := annealWriteMemoryPlace_zero_offset_scalar_ok hdst_prim hid_lt hbase_e hfind_la
        hshape_la.mutability_eq hshape_la.byteSize_eq hmsc_sz hval_sc hw_alloc_lay
        (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tf']⟩ })
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use (.constant c)), span⟩) m =
          ({ stack := ⟨#[tf']⟩
             machine := { m.machine with
               memory := { m.machine.memory with
                 live := (m.machine.memory.live.filter (fun x => x.1 != e₀.allocId)).push
                   (e₀.allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
        rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; dsimp only []
        have hassoc : ∀ (f : Miri.Interpreter.RvalueImmTy AnnealProv →
            Miri.Interpreter.RvalueM AnnealStepState Unit) st,
            ((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
              (some (translateTy dstDecl.ty body.layouts)) >>= fun opv =>
              annealReadImmediate opv >>= f) st) =
            (((annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
              (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>= f) st) := by
          intro f st; simp only [Bind.bind, EStateM.bind]; cases annealEvalOperand
            body.localDecls body.layouts (translateOperand (.constant c))
            (some (translateTy dstDecl.ty body.layouts)) st <;> rfl
        rw [hassoc, EStateM.bind_eq_ok hm_op_ok, hw_ind, stackAllocPlace, hw_m]
      rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
        hfr_tf'.location_eq] at hstep
      injection hstep with hm' _
      subst hm'
      refine ⟨hsupply.of_setLive ?_ _, hnext2⟩
      rw [ha1, hnext2]; decide

/-- **`wit_lm3_2_dangling_copy_move_and_perm_divergences_real_steps`**:
1. **Dangling safe-reference `copy` AND `move` post-step destination validity
   (`step_safeRef_use_dangling_post_validity_divergence`)**:
   `_2 = &_1 -> StorageDead(_1) -> _3 = copy _2 -> _0 = move _2` steps in
   lockstep to `StateRelLM3_2` at every step while `ValidityVisitor.validatePlace`
   rejects the newly written dangling destination (`_3` after `copy`, `_0` after
   `move`) with `"validation: encountered a dangling reference (use-after-free)"`.
2. **Tree Borrows permission divergences (`LM-3.2` hook-free `annealStepHooks` vs
   `LM-3.3` `BorrowTree` in `SimLM3_3.lean`)**:
   - `_2 = &_1 -> *_2 = 99_u64` (`step_safeRef_deref_write_perm_divergence`; cf.
     `sim_lm3_3_child_write_step` and `sim_lm3_3_interpreter_deref_write_step`);
   - `_2 = &_1 -> _3 = &mut *_2` (`evalRvalue_reborrow_safeRef_perm_divergence`; cf.
     `sim_lm3_3_retag_ref_step` and `sim_lm3_3_interpreter_reborrow_step`);
   - `_2 = &mut _1 -> _1 = 77_u64 -> _0 = copy *_2`
     (`step_direct_write_promoted_lm3_2_simulation` disabling `entry.perm` +
     `step_safeRef_deref_read_disabled_divergence`; cf. `sim_lm3_3_child_read_step`
     and `sim_lm3_3_interpreter_deref_read_step`). -/
theorem wit_lm3_2_dangling_copy_move_and_perm_divergences_real_steps :
    (∃ (b : CapturedMir) (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState)
        (tf₃ tf₄ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b refU64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
            layout := some (translateTy u64Ty) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_2 b s₃ m₃ [{ entry with perm := .disabled }] ∧
      m₃.stack.frames = #[tf₃] ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
        refU64Ty 4 ⟨.local 0 3 none tf₃.localsIdentity, translateTy refU64Ty b.layouts⟩
        false false m₃ =
        .error (.undefinedBehavior
          "validation: encountered a dangling reference (use-after-free)") m₃ ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_2 b s₄ m₄ [{ entry with perm := .disabled }] ∧
      m₄.stack.frames = #[tf₄] ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
        refU64Ty 4 ⟨.local 0 0 none tf₄.localsIdentity, translateTy refU64Ty b.layouts⟩
        false false m₄ =
        .error (.undefinedBehavior
          "validation: encountered a dangling reference (use-after-free)") m₄) ∧
    (∃ (b : CapturedMir) (s₁ : MachineState) (m₁ m₂ : AnnealStepState),
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
            layout := some (translateTy u64Ty) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true)) ∧
    (∃ (b : CapturedMir) (s₁ : MachineState) (m₁ m₂ : AnnealStepState),
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
            layout := some (translateTy u64Ty) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true)) ∧
    (∃ (b : CapturedMir) (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState)
        (tf₃ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
        (msc : Miri.Memory.ScalarInt),
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
            layout := some (translateTy u64Ty) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2 b s₂ m₂ [{ entry with perm := .disabled }] ∧
      stepMirFn b s₂ = .fail .ub ∧
      ScalarRel ⟨77, 8⟩ msc ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      m₃.stack.frames = #[tf₃] ∧
      (tf₃.locals[0]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc))))) := by
  let mls42 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
    { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
      layout := some (translateTy u64Ty) }
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) Dangling copy + move post-validity
    let b : CapturedMir :=
      { defPath := "lm_3_2_witness::dangling_copy_move"
        phase := .runtimePostCleanup, role := .subject, argCount := 0
        localDecls := [refU64Decl, u64Decl, refU64Decl, refU64Decl]
        basicBlocks := [
          { statements := [
              mkStmt (.assign (local_ 2) (.ref .shared (local_ 1))),
              mkStmt (.storageDead 1),
              mkStmt (.assign (local_ 3) (.use (.copy (local_ 2)))),
              mkStmt (.assign (local_ 0) (.use (.move (local_ 2))))],
            terminator := mkTerm .return_, isCleanup := false }]
        fnAbi := fnAbiU64, layouts := emptyLayoutTable, allocations := [] }
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b refU64Decl u64Decl refU64Decl refU64Decl rfl
      (.init (.scalar ⟨42, 8⟩)) mls42 (fun _ h => nomatch h)
      (.immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
    let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1
    let entryDis : AllocMapEntry := { entry with perm := .disabled }
    let p0 : ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    let s₁ := mkWitStateLM32 b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr p0 8), .uninit]
      [entry.toBorrowEntry] 2
    have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ := rfl
    have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
      (dstIdx := 2) (targetIdx := 1) (bk := .shared)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
    obtain ⟨hsup₁, hnext₁⟩ := step_ref_supply_two hrel₀ (dstIdx := 2) (targetIdx := 1) (bk := .shared)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) rfl hm₁
    let s₂ := mkWitStateLM32 b 2 [.uninit, .dead, .init (.ptr p0 8), .uninit]
      [entryDis.toBorrowEntry] 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    have hsim₂ := step_storageDead_lm3_2_simulation hrel₁ hphase rfl rfl rfl (by decide)
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_2_of_anneal_step hsim₂ hs₂
    change StateRelLM3_2 b s₂ m₂ [entryDis] at hrel₂
    obtain ⟨hsup₂, hnext₂⟩ := step_storageDead_supply hrel₁ rfl rfl rfl (by decide) hsup₁ hnext₁ hm₂
    have himm₂ : ∀ tf, m₂.stack.frames = #[tf] →
        IsImmediateFrameLocal tf 3 ∧ IsImmediateFrameLocal tf 2 :=
      fun tf htf =>
        ⟨immediate_of_nextAllocId_two hrel₂ hsup₂ hnext₂ (List.Mem.head _) rfl htf 3 (Or.inl rfl),
         immediate_of_nextAllocId_two hrel₂ hsup₂ hnext₂ (List.Mem.head _) rfl htf 2 (Or.inl rfl)⟩
    obtain ⟨s₃', m₃, tf₃, hs₃', hm₃, hrel₃, htf₃, _, _, hv₃⟩ :=
      step_safeRef_use_dangling_post_validity_divergence hrel₂ hphase (Or.inl rfl) rfl rfl
        (dstDecl := refU64Decl) (srcDecl := refU64Decl) (targetDecl := u64Decl)
        rfl rfl rfl rfl himm₂ (p := p0) (e := entryDis) rfl (fun h => nomatch h) (List.Mem.head _) rfl rfl rfl
    let s₃ := mkWitStateLM32 b 3 [.uninit, .dead, .init (.ptr p0 8), .init (.ptr p0 8)]
      [entryDis.toBorrowEntry] 2
    have hs₃_eq : s₃' = s₃ := by
      have hs₃_step : stepMirFn b s₂ = .step s₃ := rfl
      rw [hs₃_step] at hs₃'; injection hs₃' with h; injection h with h'; exact h'.symm
    subst hs₃_eq
    have hmach₃ := step_safeRef_use_machine_eq hrel₂ (Or.inl rfl) rfl rfl
      (dstDecl := refU64Decl) (srcDecl := refU64Decl) rfl rfl rfl rfl himm₂
      (p := p0) rfl (fun h => nomatch h) hm₃
    have hsup₃ : AllocIdSupplyReady m₃.machine.memory := hmach₃ ▸ hsup₂
    have hnext₃ : m₃.machine.memory.nextAllocId = 2 := hmach₃ ▸ hnext₂
    have himm₃ : ∀ tf, m₃.stack.frames = #[tf] →
        IsImmediateFrameLocal tf 0 ∧ IsImmediateFrameLocal tf 2 :=
      fun tf htf =>
        ⟨immediate_of_nextAllocId_two hrel₃ hsup₃ hnext₃ (List.Mem.head _) rfl htf 0 (Or.inl rfl),
         immediate_of_nextAllocId_two hrel₃ hsup₃ hnext₃ (List.Mem.head _) rfl htf 2 (Or.inl rfl)⟩
    obtain ⟨s₄, m₄, tf₄, hs₄, hm₄, hrel₄, htf₄, _, _, hv₄⟩ :=
      step_safeRef_use_dangling_post_validity_divergence hrel₃ hphase (Or.inr rfl) rfl rfl
        (dstDecl := refU64Decl) (srcDecl := refU64Decl) (targetDecl := u64Decl)
        rfl rfl rfl rfl himm₃ (p := p0) (e := entryDis) rfl (fun h => nomatch h) (List.Mem.head _) rfl rfl rfl
    exact ⟨b, s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, tf₃, tf₄,
      hs₁, hm₁, hs₂, hm₂, hs₃', hm₃, hrel₃, htf₃, hv₃ 3, hs₄, hm₄, hrel₄, htf₄, hv₄ 3⟩
  · -- (2a) `_2 = &_1 -> *_2 = 99_u64` (`step_safeRef_deref_write_perm_divergence`)
    let b : CapturedMir :=
      { defPath := "lm_3_2_witness::perm_write_frozen"
        phase := .runtimePostCleanup, role := .subject, argCount := 0
        localDecls := [u64Decl, u64Decl, refU64Decl, u64Decl]
        basicBlocks := [
          { statements := [
              mkStmt (.assign (local_ 2) (.ref .shared (local_ 1))),
              mkStmt (.assign (derefLocal 2) (.use (.constant (constU64 99))))],
            terminator := mkTerm .return_, isCleanup := false }]
        fnAbi := fnAbiU64, layouts := emptyLayoutTable, allocations := [] }
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b u64Decl u64Decl refU64Decl u64Decl rfl
      (.init (.scalar ⟨42, 8⟩)) mls42 (fun _ h => nomatch h)
      (.immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
    let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1
    let s₁ := mkWitStateLM32 b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
      [entry.toBorrowEntry] 2
    have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ := rfl
    have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
      (dstIdx := 2) (targetIdx := 1) (bk := .shared)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
    obtain ⟨hsup₁, hnext₁⟩ := step_ref_supply_two hrel₀ (dstIdx := 2) (targetIdx := 1) (bk := .shared)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) rfl hm₁
    have himm₁_2 : ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 :=
      fun tf htf =>
        immediate_of_nextAllocId_two hrel₁ hsup₁ hnext₁ (List.Mem.head _) rfl htf 2
          (Or.inr (by decide))
    obtain ⟨hub, m₂, _, _, _, _, hm₂, _, _⟩ :=
      step_safeRef_deref_write_perm_divergence hrel₁ hphase rfl rfl
        (refDecl := refU64Decl) (valTy := u64Ty) rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
        (fun tf _ => constU64_wellTypedLM32 b tf 99 (by decide)) himm₁_2
        (ptrVal := { allocId := 1, offsetBytes := 0 }) (e := entry) (sc := ⟨99, 8⟩)
        rfl rfl (List.Mem.head _) rfl rfl (Or.inl rfl) (fun h => nomatch h)
        (fun d hd => by injection hd with hd'; subst hd'; rfl)
    exact ⟨b, s₁, m₁, m₂, hs₁, hm₁, hub, hm₂⟩
  · -- (2b) `_2 = &_1 -> _3 = &mut *_2` (`evalRvalue_reborrow_safeRef_perm_divergence`)
    let b : CapturedMir :=
      { defPath := "lm_3_2_witness::perm_reborrow_frozen"
        phase := .runtimePostCleanup, role := .subject, argCount := 0
        localDecls := [u64Decl, u64Decl, refU64Decl, refMutU64Decl]
        basicBlocks := [
          { statements := [
              mkStmt (.assign (local_ 2) (.ref .shared (local_ 1))),
              mkStmt (.assign (local_ 3) (.ref (.mut false) (derefLocal 2)))],
            terminator := mkTerm .return_, isCleanup := false }]
        fnAbi := fnAbiU64, layouts := emptyLayoutTable, allocations := [] }
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b u64Decl u64Decl refU64Decl refMutU64Decl rfl
      (.init (.scalar ⟨42, 8⟩)) mls42 (fun _ h => nomatch h)
      (.immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
    let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1
    let s₁ := mkWitStateLM32 b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
      [entry.toBorrowEntry] 2
    have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ := rfl
    have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
      (dstIdx := 2) (targetIdx := 1) (bk := .shared)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
    obtain ⟨hsup₁, hnext₁⟩ := step_ref_supply_two hrel₀ (dstIdx := 2) (targetIdx := 1) (bk := .shared)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) rfl hm₁
    have himm₁ : ∀ tf, m₁.stack.frames = #[tf] →
        IsImmediateFrameLocal tf 3 ∧ IsImmediateFrameLocal tf 2 :=
      fun tf htf =>
        ⟨immediate_of_nextAllocId_two hrel₁ hsup₁ hnext₁ (List.Mem.head _) rfl htf 3 (Or.inr (by decide)),
         immediate_of_nextAllocId_two hrel₁ hsup₁ hnext₁ (List.Mem.head _) rfl htf 2 (Or.inr (by decide))⟩
    obtain ⟨hub, m₂, _, _, hm₂, _, _⟩ :=
      evalRvalue_reborrow_safeRef_perm_divergence hrel₁ hphase rfl rfl
        (dstDecl := refMutU64Decl) (refDecl := refU64Decl) rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₁
        (ptrVal := { allocId := 1, offsetBytes := 0 }) (e := entry)
        rfl (List.Mem.head _) rfl rfl (Or.inr ⟨rfl, fun h => nomatch h⟩) (fun h => nomatch h)
        (fun d hd => by injection hd with hd'; subst hd'; rfl) (fun h => nomatch h)
    exact ⟨b, s₁, m₁, m₂, hs₁, hm₁, hub, hm₂⟩
  · -- (2c) `_2 = &mut _1 -> _1 = 77_u64 -> _0 = copy *_2` (`step_safeRef_deref_read_disabled_divergence`)
    let b : CapturedMir :=
      { defPath := "lm_3_2_witness::perm_read_disabled"
        phase := .runtimePostCleanup, role := .subject, argCount := 0
        localDecls := [u64Decl, u64Decl, refMutU64Decl, u64Decl]
        basicBlocks := [
          { statements := [
              mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
              mkStmt (.assign (local_ 1) (.use (.constant (constU64 77)))),
              mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 2))))],
            terminator := mkTerm .return_, isCleanup := false }]
        fnAbi := fnAbiU64, layouts := emptyLayoutTable, allocations := [] }
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b u64Decl u64Decl refMutU64Decl u64Decl rfl
      (.init (.scalar ⟨42, 8⟩)) mls42 (fun _ h => nomatch h)
      (.immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
    let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
    let entryDis : AllocMapEntry := { entry with perm := .disabled }
    let s₁ := mkWitStateLM32 b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
      [entry.toBorrowEntry] 2
    have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ := rfl
    have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
      (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
    obtain ⟨hsup₁, hnext₁⟩ := step_ref_supply_two hrel₀ (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) rfl hm₁
    let s₂ := mkWitStateLM32 b 2
      [.uninit, .init (.scalar ⟨77, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
      [entryDis.toBorrowEntry] 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    have hsim₂ := step_direct_write_promoted_lm3_2_simulation hrel₁ hphase rfl rfl
      (dstDecl := u64Decl) (valTy := u64Ty) rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
      (fun tf _ => constU64_wellTypedLM32 b tf 77 (by decide)) ⟨entry, List.Mem.head _, rfl⟩
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_2_of_anneal_step hsim₂ hs₂
    change StateRelLM3_2 b s₂ m₂ [entryDis] at hrel₂
    obtain ⟨hsup₂, hnext₂⟩ := step_direct_write_promoted_const_supply hrel₁ rfl rfl
      (dstDecl := u64Decl) rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
      (fun tf _ => constU64_wellTypedLM32 b tf 77 (by decide)) (List.Mem.head _) rfl rfl
      hsup₁ hnext₁ hm₂
    have himm₂ : ∀ tf, m₂.stack.frames = #[tf] →
        IsImmediateFrameLocal tf 0 ∧ IsImmediateFrameLocal tf 2 :=
      fun tf htf =>
        ⟨immediate_of_nextAllocId_two hrel₂ hsup₂ hnext₂ (List.Mem.head _) rfl htf 0 (Or.inr (by decide)),
         immediate_of_nextAllocId_two hrel₂ hsup₂ hnext₂ (List.Mem.head _) rfl htf 2 (Or.inr (by decide))⟩
    obtain ⟨hub, m₃, tf₃, msc, hrel_sc, hm₃, htf₃, hval₃⟩ :=
      step_safeRef_deref_read_disabled_divergence hrel₂ hphase (Or.inl rfl) rfl rfl
        (dstDecl := u64Decl) (refDecl := refMutU64Decl) rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₂
        (ptrVal := { allocId := 1, offsetBytes := 0 }) (e := entryDis) (sc := ⟨77, 8⟩)
        rfl (List.Mem.head _) rfl rfl rfl rfl
        (fun d hd => by injection hd with hd'; subst hd'; rfl) (fun h => nomatch h)
    exact ⟨b, s₁, s₂, m₁, m₂, m₃, tf₃, msc, hs₁, hm₁, hs₂, hm₂, hrel₂, hub, hrel_sc, hm₃, htf₃, hval₃⟩

private theorem stepObsRelLM3_2_of_anneal_step
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {s' : MachineState}
    (hsim : StepObsRelLM3_2 body m allocMap aRes mRes)
    (ha : aRes = .step s') :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_2 body s' m' allocMap := by
  generalize ha_eq : aRes = aNode at hsim
  cases hsim with
  | emitStep obs s₁ m' hrel =>
    rw [ha] at ha_eq
    cases obs with
    | silent =>
      injection ha_eq with hrun
      injection hrun with hs
      subst hs
      exact ⟨m', rfl, hrel⟩
    | event _ => cases ha_eq
  | retRoot _ _ _ _ _ _ _ _ _ =>
    rw [ha] at ha_eq
    cases ha_eq
  | ub _ _ =>
    rw [ha] at ha_eq
    cases ha_eq

private theorem allocMap_eq_singleton_of_nextAllocId_two
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} {e : AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hbor : s.memory.borrows = [e.toBorrowEntry])
    (ha1 : e.allocId = lm31AllocId1)
    (hnext2 : m.machine.memory.nextAllocId = 2) :
    allocMap = [e] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hbor_eq, halloc, _⟩ := id hstate
  rw [hbor] at hbor_eq
  cases allocMap with
  | nil => cases hbor_eq
  | cons e' rest =>
    cases rest with
    | cons _ _ =>
      injection hbor_eq with _ hnil
      cases hnil
    | nil =>
      injection hbor_eq with hbe _
      have hid_lt2 : e'.allocId.value.toNat < 2 := by
        have h := (halloc.base_addr_valid e' (List.Mem.head _)).2.1
        rw [hnext2] at h
        exact h
      have hid_eq : e'.allocId = lm31AllocId1 := allocId_eq_one_of_lt_two hid_lt2
      have ht : e'.tag = e.tag := congrArg BorrowEntry.tag hbe.symm
      have hl : e'.localIdx = e.localIdx := congrArg BorrowEntry.targetLocal hbe.symm
      have hp : e'.perm = e.perm := congrArg BorrowEntry.perm hbe.symm
      rcases e' with ⟨t', l', a', p'⟩
      rcases e with ⟨t, l, a, p⟩
      dsimp only at ht hl hp hid_eq ha1
      subst ht hl hp hid_eq ha1
      rfl

/-- **`wit_lm3_2_placeMention_and_unified_return_ref_real_steps`**:
1. **End-to-end 6-step unified `step_mir_lm3_2_state_simulation` trace returning
   `_0 : &u64`**:
   ```text
   bb0: _2 = &mut _1;         -- `_1` initially `.uninit`!
        PlaceMention(_2);
        PlaceMention(*_2);    -- lockstep even while `*_2` is `.uninit`!
        *_2 = const 55_u64;
        _0 = move _2;         -- `&mut u64 -> &u64` move into `_0`
        return                -- root-frame `Return` of safe reference `&u64`!
   ```
   Every single transition (`5` statements + `return` terminator) is driven
   through `step_mir_lm3_2_state_simulation`, ending with `StepObsRelLM3_2.retNormal_rel`
   establishing `ImmediateRelLM3_2` on the returned safe reference.
2. **`PlaceMention(*_2)` divergence (`step_placeMention_safeRef_deref_divergence`)**:
   `_2 = &_1 -> StorageDead(_1) -> PlaceMention(*_2)` steps in Anneal while
   `lean-miri` raises `.error (.undefinedBehavior msg)`. -/
theorem wit_lm3_2_placeMention_and_unified_return_ref_real_steps :
    (∃ (b : CapturedMir) (s₁ s₂ s₃ s₄ s₅ : MachineState)
        (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
        (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
      stepMirFn b (mkPre4AnnealLM32 b .uninit) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b refU64Ty { value := .live (.immediate .uninit), layout := none }) =
        (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      stepMirFn b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_2 b s₅ m₅ [{ entry with perm := .active }] ∧
      (∃ am, StepObsRelLM3_2 b m₅ am (stepMirFn b s₅) (Miri.Interpreter.Step.step hooks () m₅)) ∧
      stepMirFn b s₅ = .retNormal (.ptr { allocId := 1, offsetBytes := 0 } 8) s₅.memory ∧
      Miri.Interpreter.Step.step hooks () m₅ = ({ m₅ with stack := ⟨#[]⟩ }, .ok true) ∧
      get? b.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m₅ = (m₅, .ok (.immediate imm0)) ∧
      ImmediateRelLM3_2 [{ entry with perm := .active }] decl0.ty b.layouts
        (.ptr { allocId := 1, offsetBytes := 0 } 8) imm0) ∧
    (∃ (b : CapturedMir) (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState) (msg : String),
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
            layout := some (translateTy u64Ty) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step (advanceStmt s₂ s₂.frame.locals) ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .error (.undefinedBehavior msg))) := by
  refine ⟨?_, ?_⟩
  · -- (1) Unified 6-step trace returning `_0 : &u64`
    let b : CapturedMir :=
      { defPath := "lm_3_2_witness::unified_return_ref"
        phase := .runtimePostCleanup, role := .subject, argCount := 0
        localDecls := [refU64Decl, u64Decl, refMutU64Decl, u64Decl]
        basicBlocks := [
          { statements := [
              mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
              mkStmt (.placeMention (local_ 2)),
              mkStmt (.placeMention (derefLocal 2)),
              mkStmt (.assign (derefLocal 2) (.use (.constant (constU64 55)))),
              mkStmt (.assign (local_ 0) (.use (.move (local_ 2))))],
            terminator := mkTerm .return_, isCleanup := false }]
        fnAbi := fnAbiU64, layouts := emptyLayoutTable, allocations := [] }
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let mlsUninit : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
      { value := .live (.immediate .uninit), layout := none }
    obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b refU64Decl u64Decl refMutU64Decl u64Decl rfl
      .uninit mlsUninit (fun _ h => nomatch h)
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
    let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
    let p0 : ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    let borMut := [entry.toBorrowEntry]
    let entryAct : AllocMapEntry := { entry with perm := .active }
    let borMutW := [entryAct.toBorrowEntry]
    -- Step 1 (`stmtIdx = 0`): `_2 = &mut _1`
    let s₁ := mkWitStateLM32 b 1 [.uninit, .uninit, .init (.ptr p0 8), .uninit] borMut 2
    have hs₁ : stepMirFn b (mkPre4AnnealLM32 b .uninit) = .step s₁ := rfl
    have hwt₁ : WellTypedLM3_2StateStmt b (mkPre4AnnealLM32 b .uninit)
        (mkPre4MiriLM32 b refU64Ty mlsUninit) []
        (mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1)))) :=
      WellTypedLM3_2StateStmt.refAddrOf (body := b) (s := mkPre4AnnealLM32 b .uninit)
        (m := mkPre4MiriLM32 b refU64Ty mlsUninit) (allocMap := [])
        2 1 (.mut false) refMutU64Decl u64Decl .mut (.uint .u64) _
        rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
        (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩)
    obtain ⟨am₁, hobs₁⟩ := step_mir_lm3_2_state_simulation hrel₀.toLM3_1.toLM3_2 hphase rfl
      (Or.inl ⟨_, rfl, hwt₁⟩) (by exact AllocIdSupplyReady.empty)
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepObsRelLM3_2_of_anneal_step hobs₁ hs₁
    obtain ⟨hsup₁, hnext₁⟩ := step_ref_supply_two hrel₀ rfl rfl
      (dstDecl := refMutU64Decl) (targetDecl := u64Decl) rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) rfl hm₁
    have ham₁ := allocMap_eq_singleton_of_nextAllocId_two hrel₁ rfl rfl hnext₁
    subst ham₁
    -- Step 2 (`stmtIdx = 1`): `PlaceMention(_2)`
    let s₂ := mkWitStateLM32 b 2 [.uninit, .uninit, .init (.ptr p0 8), .uninit] borMut 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    have hwt₂ : WellTypedLM3_2StateStmt b s₁ m₁ [entry] (mkStmt (.placeMention (local_ 2))) :=
      WellTypedLM3_2StateStmt.placeMentionLocal (body := b) (s := s₁) (m := m₁)
        (allocMap := [entry]) 2 refMutU64Decl _ rfl (fun h => nomatch h)
    obtain ⟨am₂, hobs₂⟩ := step_mir_lm3_2_state_simulation hrel₁ hphase rfl
      (Or.inl ⟨_, rfl, hwt₂⟩) hsup₁
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepObsRelLM3_2_of_anneal_step hobs₂ hs₂
    have hmach₂ := step_placeMention_local_machine_eq hrel₁ rfl rfl (decl := refMutU64Decl) rfl hm₂
    have hsup₂ : AllocIdSupplyReady m₂.machine.memory := hmach₂ ▸ hsup₁
    have hnext₂ : m₂.machine.memory.nextAllocId = 2 := by rw [hmach₂]; exact hnext₁
    have ham₂ := allocMap_eq_singleton_of_nextAllocId_two hrel₂ rfl rfl hnext₂
    subst ham₂
    -- Step 3 (`stmtIdx = 2`): `PlaceMention(*_2)` (while `*_2` is `.uninit`!)
    let s₃ := mkWitStateLM32 b 3 [.uninit, .uninit, .init (.ptr p0 8), .uninit] borMut 2
    have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
    have himm₂_2 : ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 :=
      fun tf htf => immediate_of_nextAllocId_two hrel₂ hsup₂ hnext₂
        (List.Mem.head _) rfl htf 2 (Or.inr (by decide))
    have hwt₃ : WellTypedLM3_2StateStmt b s₂ m₂ [entry] (mkStmt (.placeMention (derefLocal 2))) :=
      WellTypedLM3_2StateStmt.placeMentionSafeRefDeref (body := b) (s := s₂) (m := m₂)
        (allocMap := [entry]) 2 refMutU64Decl .mut (.uint .u64) _
        rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₂_2
        (Or.inr ⟨p0, entry, rfl, List.Mem.head _, rfl, rfl,
          (fun h => nomatch h),
          fun d hd => by injection hd with hd'; subst hd'; rfl⟩)
    obtain ⟨am₃, hobs₃⟩ := step_mir_lm3_2_state_simulation hrel₂ hphase rfl
      (Or.inl ⟨_, rfl, hwt₃⟩) hsup₂
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepObsRelLM3_2_of_anneal_step hobs₃ hs₃
    have hmach₃ := step_placeMention_safeRef_deref_machine_eq hrel₂ rfl rfl
      (refDecl := refMutU64Decl) rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₂_2
      rfl (List.Mem.head _) rfl rfl (fun h => nomatch h)
      (fun d hd => by injection hd with hd'; subst hd'; rfl) hm₃
    have hsup₃ : AllocIdSupplyReady m₃.machine.memory := hmach₃ ▸ hsup₂
    have hnext₃ : m₃.machine.memory.nextAllocId = 2 := by rw [hmach₃]; exact hnext₂
    have ham₃ := allocMap_eq_singleton_of_nextAllocId_two hrel₃ rfl rfl hnext₃
    subst ham₃
    -- Step 4 (`stmtIdx = 3`): `*_2 = const 55_u64`
    let s₄ := mkWitStateLM32 b 4 [.uninit, .init (.scalar ⟨55, 8⟩), .init (.ptr p0 8), .uninit] borMutW 2
    have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
    have himm₃_2 : ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 :=
      fun tf htf => immediate_of_nextAllocId_two hrel₃ hsup₃ hnext₃
        (List.Mem.head _) rfl htf 2 (Or.inr (by decide))
    have hwt₄ : WellTypedLM3_2StateStmt b s₃ m₃ [entry]
        (mkStmt (.assign (derefLocal 2) (.use (.constant (constU64 55))))) :=
      WellTypedLM3_2StateStmt.safeRefDerefWrite (body := b) (s := s₃) (m := m₃)
        (allocMap := [entry]) 2 (.constant (constU64 55)) refMutU64Decl .mut (.uint .u64) u64Ty _
        rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
        (fun tf _ => constU64_wellTypedLM32 b tf 55 (by decide)) himm₃_2
        (fun pv e td hpv he _ htd _ => by
          have hpv_eq := ptrVal_of_some_initLM32 hpv
          subst hpv_eq
          cases he with
          | head =>
            injection htd with htd'
            subst htd'
            exact ⟨rfl, Or.inr rfl, rfl⟩
          | tail _ h => nomatch h)
    obtain ⟨am₄, hobs₄⟩ := step_mir_lm3_2_state_simulation hrel₃ hphase rfl
      (Or.inl ⟨_, rfl, hwt₄⟩) hsup₃
    obtain ⟨m₄, hm₄, hrel₄⟩ := stepObsRelLM3_2_of_anneal_step hobs₄ hs₄
    obtain ⟨hsup₄, hnext₄⟩ := step_safeRef_deref_write_const_supply hrel₃ rfl rfl
      (refDecl := refMutU64Decl) rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
      (fun tf _ => constU64_wellTypedLM32 b tf 55 (by decide)) himm₃_2
      rfl (List.Mem.head _) rfl rfl (fun h => nomatch h)
      (fun d hd => by injection hd with hd'; subst hd'; rfl) hsup₃ hnext₃ rfl hm₄
    have ham₄ := allocMap_eq_singleton_of_nextAllocId_two hrel₄ rfl rfl hnext₄
    subst ham₄
    -- Step 5 (`stmtIdx = 4`): `_0 = move _2` (`&mut u64 -> &u64`)
    let s₅ := mkWitStateLM32 b 5 [.init (.ptr p0 8), .init (.scalar ⟨55, 8⟩), .uninit, .uninit] borMutW 2
    have hs₅ : stepMirFn b s₄ = .step s₅ := rfl
    have himm₄_02 : ∀ tf, m₄.stack.frames = #[tf] →
        IsImmediateFrameLocal tf 0 ∧ IsImmediateFrameLocal tf 2 :=
      fun tf htf =>
        ⟨immediate_of_nextAllocId_two hrel₄ hsup₄ hnext₄ (List.Mem.head _) rfl htf 0 (Or.inr (by decide)),
         immediate_of_nextAllocId_two hrel₄ hsup₄ hnext₄ (List.Mem.head _) rfl htf 2 (Or.inr (by decide))⟩
    have hwt₅ : WellTypedLM3_2StateStmt b s₄ m₄ [entryAct]
        (mkStmt (.assign (local_ 0) (.use (.move (local_ 2))))) :=
      WellTypedLM3_2StateStmt.safeRefUse (body := b) (s := s₄) (m := m₄) (allocMap := [entryAct])
        0 2 MirAst.Operand.move refU64Decl refMutU64Decl .mut .not (.uint .u64) (.uint .u64) _
        (Or.inr rfl) rfl rfl rfl rfl himm₄_02
    obtain ⟨am₅, hobs₅⟩ := step_mir_lm3_2_state_simulation hrel₄ hphase rfl
      (Or.inl ⟨_, rfl, hwt₅⟩) hsup₄
    obtain ⟨m₅, hm₅, hrel₅⟩ := stepObsRelLM3_2_of_anneal_step hobs₅ hs₅
    have hmach₅ := step_safeRef_use_machine_eq hrel₄ (Or.inr rfl) rfl rfl
      (dstDecl := refU64Decl) (srcDecl := refMutU64Decl) rfl rfl rfl rfl himm₄_02
      rfl (fun h => nomatch h) hm₅
    have hsup₅ : AllocIdSupplyReady m₅.machine.memory := hmach₅ ▸ hsup₄
    have hnext₅ : m₅.machine.memory.nextAllocId = 2 := by rw [hmach₅]; exact hnext₄
    have ham₅ := allocMap_eq_singleton_of_nextAllocId_two hrel₅ rfl rfl hnext₅
    subst ham₅
    -- Step 6 (`stmtIdx = 5`): root-frame `return` terminator returning `_0 : &u64`
    have hs₆ : stepMirFn b s₅ = .retNormal (.ptr p0 8) s₅.memory := rfl
    have himm₅_0 : ∀ tf, m₅.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 :=
      fun tf htf => immediate_of_nextAllocId_two hrel₅ hsup₅ hnext₅
        (List.Mem.head _) rfl htf 0 (Or.inr (by decide))
    have hwt₆ : WellTypedLM3_2StateTerminator b m₅
        { statements := [
            mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
            mkStmt (.placeMention (local_ 2)),
            mkStmt (.placeMention (derefLocal 2)),
            mkStmt (.assign (derefLocal 2) (.use (.constant (constU64 55)))),
            mkStmt (.assign (local_ 0) (.use (.move (local_ 2))))],
          terminator := mkTerm .return_, isCleanup := false } := by
      exact .return_ refU64Decl rfl rfl rfl (by decide) himm₅_0
    have hobs₆_uni := step_mir_lm3_2_state_simulation hrel₅ hphase rfl
      (Or.inr ⟨rfl, rfl, hwt₆⟩) hsup₅
    have hobs₆ := step_terminator_lm3_2_state_simulation hrel₅ hphase rfl rfl rfl hwt₆
    rw [hs₆] at hobs₆
    obtain ⟨decl0, imm0, hdecl0, hretOp, himmRel0, hm₆⟩ := hobs₆.retNormal_rel
    exact ⟨b, s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, decl0, imm0,
      hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hs₅, hm₅, hrel₅,
      hobs₆_uni, hs₆, hm₆, hdecl0, hretOp, himmRel0⟩
  · -- (2) `PlaceMention(*_2)` divergence on dangling safe reference
    let b : CapturedMir :=
      { defPath := "lm_3_2_witness::place_mention_deref_div"
        phase := .runtimePostCleanup, role := .subject, argCount := 0
        localDecls := [u64Decl, u64Decl, refU64Decl, u64Decl]
        basicBlocks := [
          { statements := [
              mkStmt (.assign (local_ 2) (.ref .shared (local_ 1))),
              mkStmt (.storageDead 1),
              mkStmt (.placeMention (derefLocal 2))],
            terminator := mkTerm .return_, isCleanup := false }]
        fnAbi := fnAbiU64, layouts := emptyLayoutTable, allocations := [] }
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let mls42 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
      { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
        layout := some (translateTy u64Ty) }
    obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b u64Decl u64Decl refU64Decl u64Decl rfl
      (.init (.scalar ⟨42, 8⟩)) mls42 (fun _ h => nomatch h)
      (.immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
    let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1
    let entryDis : AllocMapEntry := { entry with perm := .disabled }
    let p0 : ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    let s₁ := mkWitStateLM32 b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr p0 8), .uninit]
      [entry.toBorrowEntry] 2
    have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ := rfl
    have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
      (dstIdx := 2) (targetIdx := 1) (bk := .shared)
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
    obtain ⟨hsup₁, hnext₁⟩ := step_ref_supply_two hrel₀ rfl rfl
      (dstDecl := refU64Decl) (targetDecl := u64Decl) rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) rfl hm₁
    let s₂ := mkWitStateLM32 b 2 [.uninit, .dead, .init (.ptr p0 8), .uninit]
      [entryDis.toBorrowEntry] 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    have hsim₂ := step_storageDead_lm3_2_simulation hrel₁ hphase rfl rfl rfl (by decide)
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_2_of_anneal_step hsim₂ hs₂
    change StateRelLM3_2 b s₂ m₂ [entryDis] at hrel₂
    obtain ⟨hsup₂, hnext₂⟩ := step_storageDead_supply hrel₁ rfl rfl (decl := u64Decl) rfl
      (by decide) hsup₁ hnext₁ hm₂
    have himm₂_2 : ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 :=
      fun tf htf => immediate_of_nextAllocId_two hrel₂ hsup₂ hnext₂
        (List.Mem.head _) rfl htf 2 (Or.inl rfl)
    obtain ⟨hs₃, m₃, msg, hm₃⟩ := step_placeMention_safeRef_deref_divergence hrel₂ hphase rfl rfl
      (refDecl := refU64Decl) rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₂_2
      (Or.inr (Or.inl ⟨p0, entryDis, rfl, List.Mem.head _, rfl, rfl⟩))
    exact ⟨b, s₁, s₂, m₁, m₂, m₃, msg, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃⟩

/-! ## 6. `&!` and Enum Validity, Invalid-`bool` Reads, and Tree Borrows Reborrow Chains -/

/-- `lean-miri` local state of a `u64` local holding `42`. -/
def lm32Mls42 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
  { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42)))
    layout := some (translateTy u64Ty) }

/-- `&!` as an Anneal type. -/
def refNeverTyLM32 : Ty := { kind := .ref .not .never, layoutIdx := 0 }

/-- Local declaration of type `&!`. -/
def refNeverDeclLM32 : LocalDecl :=
  { mutability := .mut, ty := refNeverTyLM32, debugName := none }

/-- `Runtime(PostCleanup)` MIR body that stores a reference to the live `u64`
local `_1` in `_2 : &!`:
```text
bb0: _2 = &_1;
     return
``` -/
def lm32RefNeverBody : CapturedMir where
  defPath := "lm_3_2_witness::ref_never"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, refNeverDeclLM32, u64Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 2) (.ref .shared (local_ 1)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Layout of the zero-variant `enum Void {}`: zero-sized and uninhabited. -/
def lm32VoidLayout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .arbitrary .nil .nil, variants := .empty, isUninhabited := true }

/-- Valid tag range `0..=1` of `lm32Tag2Layout`. -/
def lm32Tag2Range : WrappingRange := { start := 0, end_ := 1 }

/-- Layout of the fieldless `#[repr(u8)] enum Tag2 { A = 0, B = 1 }`: a 1-byte
`u8` tag at offset `0` whose valid range `0..=1` covers exactly its two
variants. -/
def lm32Tag2Layout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 },
    backendRepr := .scalar (.initialized (.int 8 false) lm32Tag2Range),
    fields := .arbitrary [{ bytes := 0 }] [0],
    variants := .multiple (.initialized (.int 8 false) lm32Tag2Range) 0
      [.arbitrary .nil .nil, .arbitrary .nil .nil],
    isUninhabited := false }

/-- Layout table holding `enum Void {}` (index `0`) and `Tag2` (index `1`). -/
def lm32EnumLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [lm32VoidLayout, lm32Tag2Layout] }

/-- `enum Void {}` as an Anneal type. -/
def voidTyLM32 : Ty := { kind := .adt "lm_3_2_witness::Void" .nil, layoutIdx := 0 }

/-- `Tag2` as an Anneal type. -/
def tag2TyLM32 : Ty := { kind := .adt "lm_3_2_witness::Tag2" .nil, layoutIdx := 1 }

/-- Run `ValidityVisitor.validatePlace` (non-recursive, without reset) under
`annealValidityHooks lm32EnumLayouts` on local `_0 : Tag2` of
`lm32ValidityState v`. -/
def lm32ValidateTag2 (v : Miri.Interpreter.Immediate AnnealProv) :
    EStateM.Result Miri.Interpreter.StepError AnnealStepState Unit :=
  Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks lm32EnumLayouts)
    tag2TyLM32 4
    ⟨.local 0 0 none (.ofAllocationToken 0), translateTy tag2TyLM32 lm32EnumLayouts⟩ false false
    (lm32ValidityState v)

private theorem lm32Tag2_fieldless :
    ∀ v < ([.arbitrary .nil .nil, .arbitrary .nil .nil] : List FieldsShape).length,
      get? ([.arbitrary .nil .nil, .arbitrary .nil .nil] : List FieldsShape) v =
        some (.arbitrary .nil .nil) := by
  intro v hv
  match v, hv with
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, hv => exact absurd hv (by simp)

/-- **`wit_lm3_2_ref_never_and_enum_discriminant_validity`**:
1. **`&!` (`validatePlace_ref_never_always_ub`)**: in `lm32RefNeverBody`, the
   uninitialized `_2 : &!` of the pre-state fails validation; after `_2 = &_1`
   steps in lockstep to `StateRelLM3_2`-related states, `_2 : &!` holds a live,
   aligned, dereferenceable stack pointer and still fails validation with
   undefined behavior, because no value of type `&!` is valid.
2. **`enum Void {}` (`validatePlace_zero_variant_enum_simulation`)**: every place
   of type `Void` fails `validatePlace` with
   `"validation: zero-variant enum value"`, and every byte sequence fails
   `decodeValueFromBytes` at type `Void`.
3. **`#[repr(u8)] enum Tag2 { A = 0, B = 1 }`
   (`validatePlace_enum_discriminant_simulation`)**: the tag byte `0` passes
   `validatePlace` and decodes to variant `0`, while the tag byte `2` (outside
   the valid range `0..=1`) fails `validatePlace` with
   `"InvalidTag(outside valid range)"` and fails `decodeValueFromBytes`. -/
theorem wit_lm3_2_ref_never_and_enum_discriminant_validity :
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState)
        (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
        (msg₀ msg₁ : String),
      let b := lm32RefNeverBody
      let m₀ := mkPre4MiriLM32 b u64Ty lm32Mls42
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
          refNeverTyLM32 4
          ⟨.local 0 2 none (.ofAllocationToken 0), translateTy refNeverTyLM32 b.layouts⟩
          false false m₀ =
        .error (.undefinedBehavior msg₀) m₀ ∧
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m₀ =
        (m₁, .ok true) ∧
      StateRelLM3_2 b s₁ m₁ [refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1] ∧
      get? s₁.frame.locals 2 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      m₁.stack.frames = #[tf₁] ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
          refNeverTyLM32 4
          ⟨.local 0 2 none tf₁.localsIdentity, translateTy refNeverTyLM32 b.layouts⟩
          false false m₁ =
        .error (.undefinedBehavior msg₁) m₁) ∧
    (∀ (place : Miri.Interpreter.RuntimePlace AnnealProv) (m : AnnealStepState),
      place.layout = translateTy voidTyLM32 lm32EnumLayouts →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks lm32EnumLayouts)
          voidTyLM32 4 place false false m =
        .error (.undefinedBehavior "validation: zero-variant enum value") m) ∧
    (∀ bytes, decodeValueFromBytes 4 lm32EnumLayouts voidTyLM32 bytes = none) ∧
    lm32ValidateTag2 (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 0))) =
      .ok () (lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 0)))) ∧
    decodeValueFromBytes 4 lm32EnumLayouts tag2TyLM32 [.init (UInt8.ofNat 0) none] =
      some (.aggregate 0 .nil) ∧
    lm32ValidateTag2 (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 2))) =
      .error (.undefinedBehavior "InvalidTag(outside valid range)")
        (lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 2)))) ∧
    decodeValueFromBytes 4 lm32EnumLayouts tag2TyLM32 [.init (UInt8.ofNat 2) none] = none := by
  have hrel0 : ScalarRel ⟨0, 1⟩ (Miri.Memory.ScalarInt.ofUInt8 0) :=
    ⟨Or.inl rfl, by decide, rfl, rfl⟩
  have hrel2 : ScalarRel ⟨2, 1⟩ (Miri.Memory.ScalarInt.ofUInt8 2) :=
    ⟨Or.inl rfl, by decide, rfl, rfl⟩
  have hvoid := validatePlace_zero_variant_enum_simulation lm32EnumLayouts
    (enumTy := voidTyLM32) (defPath := "lm_3_2_witness::Void") (args := .nil) rfl (by decide)
    (tl := lm32VoidLayout) rfl rfl rfl 3
  have htag0 := validatePlace_enum_discriminant_simulation lm32EnumLayouts
    (enumTy := tag2TyLM32) (defPath := "lm_3_2_witness::Tag2") (args := .nil) rfl (by decide)
    (tl := lm32Tag2Layout) rfl (validRange := lm32Tag2Range) (by decide) (by decide)
    (variantShapes := [.arbitrary .nil .nil, .arbitrary .nil .nil]) rfl rfl rfl rfl
    lm32Tag2_fieldless 2 3
    (m := lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 0))))
    (tf := lm32ValidityFrame (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 0))))
    rfl (idx := 0) (by decide)
  have htag2 := validatePlace_enum_discriminant_simulation lm32EnumLayouts
    (enumTy := tag2TyLM32) (defPath := "lm_3_2_witness::Tag2") (args := .nil) rfl (by decide)
    (tl := lm32Tag2Layout) rfl (validRange := lm32Tag2Range) (by decide) (by decide)
    (variantShapes := [.arbitrary .nil .nil, .arbitrary .nil .nil]) rfl rfl rfl rfl
    lm32Tag2_fieldless 2 3
    (m := lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 2))))
    (tf := lm32ValidityFrame (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 2))))
    rfl (idx := 0) (by decide)
  obtain ⟨hv0, hd0⟩ := (htag0.2.2 hrel0 rfl rfl).2.2.1 (by decide) (by decide)
  obtain ⟨hv2, hd2⟩ := (htag2.2.2 hrel2 rfl rfl).1 (by decide)
  refine ⟨?_, hvoid.1, hvoid.2 3, hv0, hd0, hv2, hd2⟩
  -- (1) `&!`: uninitialized, then a live stack pointer after `_2 = &_1`
  let b := lm32RefNeverBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hu64 : IsPrimScalarTy u64Ty := Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))
  obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b u64Decl u64Decl refNeverDeclLM32 u64Decl
    rfl (.init (.scalar ⟨42, 8⟩)) lm32Mls42 (fun _ h => nomatch h)
    (.immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
  obtain ⟨msg₀, hv₀⟩ := validatePlace_ref_never_always_ub hrel₀.toLM3_1.toLM3_2 rfl
    (refIdx := 2) (decl := refNeverDeclLM32) rfl (refMut := .not) rfl (himm₀ _ rfl 2) 3
  let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1
  let s₁ := mkWitStateLM32 b 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ := rfl
  have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
    (dstIdx := 2) (targetIdx := 1) (bk := .shared)
    rfl rfl rfl rfl rfl hu64 (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
  have himm₁_step := step_ref_preserves_ne hrel₀ (dstIdx := 2) (targetIdx := 1) (bk := .shared)
    rfl rfl rfl rfl hu64 (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
  obtain ⟨msg₁, hv₁⟩ := validatePlace_ref_never_always_ub hrel₁ htf₁
    (refIdx := 2) (decl := refNeverDeclLM32) rfl (refMut := .not) rfl
    (himm₁_step _ tf₁ rfl htf₁ 2 (by decide) (himm₀ _ rfl 2)) 3
  exact ⟨s₁, m₁, tf₁, msg₀, msg₁, hv₀, hs₁, hm₁, hrel₁, rfl, htf₁, hv₁⟩

/-- Local declaration of type `bool`. -/
def boolDeclLM32 : LocalDecl := { mutability := .mut, ty := boolTyLM32, debugName := none }

/-- Local declaration of type `&bool`. -/
def refBoolDeclLM32 : LocalDecl :=
  { mutability := .mut, ty := refBoolTyLM32, debugName := none }

/-- `lean-miri` local state of a `u8` local holding the byte `2`. -/
def lm32MlsU8Two : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
  { value := .live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 2))))
    layout := some (translateTy u8TyLM32) }

/-- `Runtime(PostCleanup)` MIR body that reads the byte `2` of `_1 : u8` as a
`bool` through `_2 : &bool` and returns it:
```text
bb0: _2 = &_1;
     _0 = copy *_2;
     return
``` -/
def lm32InvalidBoolReadBody : CapturedMir where
  defPath := "lm_3_2_witness::invalid_bool_deref_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDeclLM32, u8DeclLM32, refBoolDeclLM32, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.ref .shared (local_ 1))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_2_invalid_bool_deref_read_ub_real_steps`**: a real-step instance of
`step_safeRef_deref_read_invalid_scalar_simulation` on `lm32InvalidBoolReadBody`,
starting from pointer-free `StateRel` states in which `_1 : u8` holds `2`:
1. `_2 = &_1` steps in lockstep (`evalRvalue_ref_simulation`) to
   `StateRelLM3_2`-related states with `_2` pointing at `_1`;
2. `_0 = copy *_2` raises undefined behavior in BOTH machines: Anneal re-validates
   the byte read at type `bool` and fails with `MirStepNode.fail .ub`, and
   `lean-miri` rejects the typed load with `"reading invalid value"`. -/
theorem wit_lm3_2_invalid_bool_deref_read_ub_real_steps :
    ∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := lm32InvalidBoolReadBody
      let hooks := annealStepHooks b.localDecls b.layouts
      ¬ AnnealScalarValid boolTyLM32 ⟨2, 1⟩ ∧
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨2, 1⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkPre4MiriLM32 b boolTyLM32 lm32MlsU8Two) =
        (m₁, .ok true) ∧
      StateRelLM3_2 b s₁ m₁ [refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1] ∧
      get? s₁.frame.locals 2 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.undefinedBehavior "reading invalid value")) := by
  let b := lm32InvalidBoolReadBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hu8 : IsPrimScalarTy u8TyLM32 := Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))
  have hrel2 : ScalarRel ⟨2, 1⟩ (Miri.Memory.ScalarInt.ofUInt8 2) :=
    ⟨Or.inl rfl, by decide, rfl, rfl⟩
  have hinvalid : ¬ AnnealScalarValid boolTyLM32 ⟨2, 1⟩ := fun ⟨hb, _⟩ => by
    rcases hb rfl with h | h <;> exact absurd h (by decide)
  obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b boolDeclLM32 u8DeclLM32 refBoolDeclLM32
    u64Decl rfl (.init (.scalar ⟨2, 1⟩)) lm32MlsU8Two (fun _ h => nomatch h)
    (.immediate _ _ (some (translateTy u8TyLM32)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ hrel2 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
  let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1
  let p0 : ProvenancePtr := { allocId := 1, offsetBytes := 0 }
  -- Step 1 (`stmtIdx = 0`): `_2 = &_1`
  let s₁ := mkWitStateLM32 b 1 [.uninit, .init (.scalar ⟨2, 1⟩), .init (.ptr p0 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨2, 1⟩))) = .step s₁ := rfl
  have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
    (dstIdx := 2) (targetIdx := 1) (bk := .shared)
    rfl rfl rfl rfl rfl hu8 (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
  have himm₁_step := step_ref_preserves_ne hrel₀ (dstIdx := 2) (targetIdx := 1) (bk := .shared)
    rfl rfl rfl rfl hu8 (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁_2 : ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 :=
    fun tf htf => himm₁_step _ tf rfl htf 2 (by decide) (himm₀ _ rfl 2)
  -- Step 2 (`stmtIdx = 1`): `_0 = copy *_2` both reject with UB
  obtain ⟨_, hs₂, m₂, hm₂⟩ := step_safeRef_deref_read_invalid_scalar_simulation hrel₁
    hphase (Or.inl rfl) rfl rfl (dstDecl := boolDeclLM32) (refDecl := refBoolDeclLM32)
    (allocDecl := u8DeclLM32) rfl rfl rfl (Or.inl rfl) himm₁_2
    (ptrVal := p0) (e := entry) (sc := ⟨2, 1⟩)
    rfl (List.Mem.head _) rfl rfl (fun h => nomatch h) rfl rfl rfl hinvalid (fun h => nomatch h)
  exact ⟨s₁, m₁, m₂, hinvalid, hs₁, hm₁, hrel₁, rfl, hs₂, hm₂⟩

private theorem stepRelLM3_2Tree_of_anneal_step
    {body : CapturedMir} {m : AnnealStepState} {treeMap : List ReborrowMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {s' : MachineState}
    (hsim : StepRelLM3_2Tree body m treeMap aRes mRes)
    (ha : aRes = .step s') :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_2Tree body s' m' treeMap := by
  cases hsim with
  | step s₁ m' _ hrel =>
    injection ha with htau
    injection htau with hs
    subst hs
    exact ⟨m', rfl, hrel⟩
  | retRoot _ _ _ _ _ _ _ _ _ _ => cases ha
  | ub _ _ _ => cases ha

private theorem stepRelLM3_2Tree_retNormal
    {body : CapturedMir} {m : AnnealStepState} {treeMap : List ReborrowMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {retVal : Value} {mem' : Memory}
    (hsim : StepRelLM3_2Tree body m treeMap aRes mRes)
    (ha : aRes = .retNormal retVal mem') :
    ∃ decl0 imm0,
      get? body.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) ∧
      ImmediateRelLM3_2 (treeMap.map ReborrowMapEntry.toAllocMapEntry) decl0.ty body.layouts
        retVal imm0 ∧
      mRes = ({ m with stack := ⟨#[]⟩ }, .ok true) := by
  cases hsim with
  | step _ _ _ _ => cases ha
  | retRoot _ decl0 rv imm0 mm _ hdecl hop himm hm' =>
    injection ha with h₁
    injection h₁ with h₂
    injection h₂ with hrv hmem
    subst hrv hmem hm'
    exact ⟨decl0, imm0, hdecl, hop, himm, rfl⟩
  | ub _ _ _ => cases ha

/-- Root Tree Borrows entry for `&mut _1` (tag `1`, no parent). -/
def lm32TreeRoot (perm : TreeBorrowPerm) : ReborrowMapEntry :=
  { tag := 1, localIdx := 1, allocId := lm31AllocId1, perm := perm }

/-- Child Tree Borrows entry for the reborrow `&mut *_2` (tag `2`, parent tag
`1`). -/
def lm32TreeChild (perm : TreeBorrowPerm) : ReborrowMapEntry :=
  { tag := 2, localIdx := 1, allocId := lm31AllocId1, perm := perm, parentTag := some 1 }

/-- `Runtime(PostCleanup)` MIR body that writes through a child reborrow and
then reads through its parent:
```text
bb0: _2 = &mut _1;
     _3 = &mut *_2;
     *_3 = const 99_u64;
     _0 = copy *_2;
     return
``` -/
def lm32ReborrowTreeBody : CapturedMir where
  defPath := "lm_3_2_witness::reborrow_tree_write_parent_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, refMutU64Decl, refMutU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
        mkStmt (.assign (local_ 3) (.ref (.mut false) (derefLocal 2))),
        mkStmt (.assign (derefLocal 3) (.use (.constant (constU64 99)))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_2_reborrow_tree_write_and_parent_read_real_steps`**: a 5-step
execution of `lm32ReborrowTreeBody` in which every transition is driven through
the `StateRelLM3_2Tree` simulations of Section 9, tracking the Tree Borrows
hierarchy (`BorrowEntry.parentTag`) in `s.memory.borrows`:
1. `_2 = &mut _1` (`evalRvalue_ref_simulation`, `StateRelLM3_2.toTree`): root
   tag `1` is `.reserved`;
2. `_3 = &mut *_2` (`step_reborrow_safeRef_tree_simulation_explicit`): child
   tag `2` with `parentTag = some 1` is `.reserved`, and the root stays
   `.reserved`;
3. `*_3 = const 99_u64` (`step_safeRef_deref_write_tree_simulation`): the child
   write activates tag `2` and its ancestor tag `1` to `.active`;
4. `_0 = copy *_2` (`step_safeRef_deref_read_tree_simulation`): the parent read
   yields `99_u64`, freezes the child tag `2`, and keeps tag `1` `.active`;
5. `return` (`step_terminator_goto_return_tree_simulation`): both machines
   return `99_u64` with `ImmediateRelLM3_2`-related return values. -/
theorem wit_lm3_2_reborrow_tree_write_and_parent_read_real_steps :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState)
        (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      let b := lm32ReborrowTreeBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkPre4MiriLM32 b u64Ty lm32Mls42) =
        (m₁, .ok true) ∧
      StateRelLM3_2Tree b s₁ m₁ [lm32TreeRoot .reserved] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2Tree b s₂ m₂ [lm32TreeChild .reserved, lm32TreeRoot .reserved] ∧
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 2, offsetBytes := 0 } 8)) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_2Tree b s₃ m₃ [lm32TreeChild .active, lm32TreeRoot .active] ∧
      get? s₃.frame.locals 1 = some (.init (.scalar ⟨99, 8⟩)) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_2Tree b s₄ m₄ [lm32TreeChild .frozen, lm32TreeRoot .active] ∧
      get? s₄.frame.locals 0 = some (.init (.scalar ⟨99, 8⟩)) ∧
      stepMirFn b s₄ = .retNormal (.scalar ⟨99, 8⟩) s₄.memory ∧
      Miri.Interpreter.Step.step hooks () m₄ = ({ m₄ with stack := ⟨#[]⟩ }, .ok true) ∧
      get? b.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m₄ = (m₄, .ok (.immediate imm0)) ∧
      ImmediateRelLM3_2
        ([lm32TreeChild .frozen, lm32TreeRoot .active].map ReborrowMapEntry.toAllocMapEntry)
        decl0.ty b.layouts (.scalar ⟨99, 8⟩) imm0 := by
  let b := lm32ReborrowTreeBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hu64 : IsPrimScalarTy u64Ty := Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))
  obtain ⟨hrel₀, himm₀⟩ := mkPre4_stateRel_and_imm b u64Decl u64Decl refMutU64Decl refMutU64Decl
    rfl (.init (.scalar ⟨42, 8⟩)) lm32Mls42 (fun _ h => nomatch h)
    (.immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
  let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
  let p1 : ProvenancePtr := { allocId := 1, offsetBytes := 0 }
  let p2 : ProvenancePtr := { allocId := 2, offsetBytes := 0 }
  -- Step 1 (`stmtIdx = 0`): `_2 = &mut _1`
  let s₁ := mkWitStateLM32 b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr p1 8), .uninit]
    [entry.toBorrowEntry] 2
  have hs₁ : stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ := rfl
  have hsim₁ := evalRvalue_ref_simulation hrel₀.toLM3_1.toLM3_2 hphase
    (dstIdx := 2) (targetIdx := 1) (bk := .mut false)
    rfl rfl rfl rfl rfl hu64 (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_2_of_anneal_step hsim₁ hs₁
  obtain ⟨hsup₁, hnext₁⟩ := step_ref_supply_two hrel₀ rfl rfl
    (dstDecl := refMutU64Decl) (targetDecl := u64Decl) rfl rfl hu64 (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) rfl hm₁
  have himm₁_step := step_ref_preserves_ne hrel₀ (dstIdx := 2) (targetIdx := 1)
    (bk := .mut false) rfl rfl rfl rfl hu64 (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm₁_step _ tf rfl htf k hne (himm₀ _ rfl k)
  have htree₁ : StateRelLM3_2Tree b s₁ m₁ [lm32TreeRoot .reserved] := hrel₁.toTree
  -- Step 2 (`stmtIdx = 1`): `_3 = &mut *_2` (child tag `2`, parent tag `1`)
  let s₂ := mkWitStateLM32 b 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr p1 8), .init (.ptr p2 8)]
    [(lm32TreeChild .reserved).toBorrowEntry, (lm32TreeRoot .reserved).toBorrowEntry] 3
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have hlive₂ : ∀ (ptrVal : ProvenancePtr) (e : ReborrowMapEntry),
      get? s₁.frame.locals 2 = some (.init (.ptr ptrVal 8)) →
      e ∈ [lm32TreeRoot .reserved] → e.tag = ptrVal.tag →
      get? s₁.frame.locals e.localIdx ≠ some .dead ∧
      get? s₁.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
      ¬(e.perm = .frozen ∧ BorrowKind.mut false ≠ .shared) ∧
      (∀ tgtDecl, get? b.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = .uint .u64) := by
    intro ptrVal e hp he _
    have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_initLM32 hp
    subst hp'
    cases he with
    | tail _ h => cases h
    | head _ =>
      exact ⟨(fun h => nomatch h), (fun h => nomatch h), rfl, (fun h => nomatch h),
        (fun ⟨h, _⟩ => nomatch h),
        (fun d hd => by injection hd with hd'; subst hd'; rfl)⟩
  have hanc₂ : ∀ (ptrVal : ProvenancePtr) (e : ReborrowMapEntry),
      get? s₁.frame.locals 2 = some (.init (.ptr ptrVal 8)) →
      e ∈ [lm32TreeRoot .reserved] → e.tag = ptrVal.tag →
      treeBorrowAncestorsChildAccessUB .read s₁.memory.borrows e.parentTag = false := by
    intro ptrVal e _ he _
    cases he with
    | tail _ h => cases h
    | head _ => rfl
  have himm₁_32 : ∀ tf, m₁.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 3 ∧ IsImmediateFrameLocal tf 2 :=
    fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩
  have hsim₂ := step_reborrow_safeRef_tree_simulation_explicit htree₁ hphase
    (dstIdx := 3) (refIdx := 2) (bk := .mut false) rfl rfl rfl rfl rfl rfl hu64 himm₁_32 hlive₂
    hanc₂
  obtain ⟨m₂, hm₂, htree₂⟩ := stepRelLM3_2Tree_of_anneal_step hsim₂ hs₂
  have htree₂' : StateRelLM3_2Tree b s₂ m₂ [lm32TreeChild .reserved, lm32TreeRoot .reserved] :=
    htree₂
  have hflat₂ := evalRvalue_reborrow_safeRef_simulation htree₁.erased_rel hphase
    (dstIdx := 3) (refIdx := 2) (bk := .mut false) rfl rfl rfl rfl rfl rfl hu64 himm₁_32
    (fun ptrVal e' hget he' htag' => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      exact hlive₂ ptrVal e hget he htag')
  obtain ⟨_, m₂', _, _, hm₂', _, hmach₂', _⟩ :=
    hflat₂.2 p1 (lm32TreeRoot .reserved).toAllocMapEntry rfl (List.Mem.head _) rfl
      (fun h => nomatch h)
  have hm₂_eq : m₂' = m₂ := by
    have h := hm₂'.symm.trans hm₂
    injection h
  have hmach₂ : m₂.machine = m₁.machine := hm₂_eq ▸ hmach₂'
  have hsup₂ : AllocIdSupplyReady m₂.machine.memory := hmach₂ ▸ hsup₁
  have hnext₂ : m₂.machine.memory.nextAllocId = 2 := by rw [hmach₂]; exact hnext₁
  -- Step 3 (`stmtIdx = 2`): `*_3 = const 99_u64` (child write)
  let s₃ := mkWitStateLM32 b 3
    [.uninit, .init (.scalar ⟨99, 8⟩), .init (.ptr p1 8), .init (.ptr p2 8)]
    [(lm32TreeChild .active).toBorrowEntry, (lm32TreeRoot .active).toBorrowEntry] 3
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  have himm₂_3 : ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf 3 :=
    fun tf htf => immediate_of_nextAllocId_two htree₂'.erased_rel hsup₂ hnext₂
      (List.Mem.head _) rfl htf 3 (Or.inr (by decide))
  have hsim₃ := step_safeRef_deref_write_tree_simulation htree₂' hphase
    (refIdx := 3) (op := .constant (constU64 99)) rfl rfl (refDecl := refMutU64Decl) rfl rfl
    (valTy := u64Ty) hu64 rfl (fun tf _ => constU64_wellTypedLM32 b tf 99 (by decide)) himm₂_3
    (fun ptrVal e tgtDecl hp he htag htgt _ => by
      have hp' : ptrVal = { allocId := 2, offsetBytes := 0 } := ptrVal_of_some_initLM32 hp
      subst hp'
      cases he with
      | head _ =>
        injection htgt with hd
        subst hd
        exact ⟨rfl, Or.inr rfl, rfl⟩
      | tail _ h =>
        cases h with
        | head _ => exact absurd htag (by decide)
        | tail _ h' => cases h')
    (fun ptrVal e hp he htag => by
      have hp' : ptrVal = { allocId := 2, offsetBytes := 0 } := ptrVal_of_some_initLM32 hp
      subst hp'
      cases he with
      | head _ => rfl
      | tail _ h =>
        cases h with
        | head _ => exact absurd htag (by decide)
        | tail _ h' => cases h')
  obtain ⟨m₃, hm₃, htree₃⟩ := stepRelLM3_2Tree_of_anneal_step hsim₃ hs₃
  have htree₃' : StateRelLM3_2Tree b s₃ m₃ [lm32TreeChild .active, lm32TreeRoot .active] :=
    htree₃
  obtain ⟨hsup₃, hnext₃⟩ := step_safeRef_deref_write_const_supply htree₂'.erased_rel rfl rfl
    (refDecl := refMutU64Decl) rfl rfl hu64 rfl
    (fun tf _ => constU64_wellTypedLM32 b tf 99 (by decide)) himm₂_3
    (ptrVal := p2) (e := (lm32TreeChild .reserved).toAllocMapEntry)
    rfl (List.Mem.head _) rfl rfl (fun h => nomatch h)
    (fun d hd => by injection hd with hd'; subst hd'; rfl) hsup₂ hnext₂ rfl hm₃
  -- Step 4 (`stmtIdx = 3`): `_0 = copy *_2` (parent read)
  let s₄ := mkWitStateLM32 b 4
    [.init (.scalar ⟨99, 8⟩), .init (.scalar ⟨99, 8⟩), .init (.ptr p1 8), .init (.ptr p2 8)]
    [(lm32TreeChild .frozen).toBorrowEntry, (lm32TreeRoot .active).toBorrowEntry] 3
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => immediate_of_nextAllocId_two htree₃'.erased_rel hsup₃ hnext₃
      (List.Mem.head _) rfl htf k (Or.inr hne)
  have himm₃_02 : ∀ tf, m₃.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 ∧ IsImmediateFrameLocal tf 2 :=
    fun tf htf => ⟨himm₃ tf htf 0 (by decide), himm₃ tf htf 2 (by decide)⟩
  have hlive₄ : ∀ (ptrVal : ProvenancePtr), get? s₃.frame.locals 2 = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ [lm32TreeChild .active, lm32TreeRoot .active], e.tag = ptrVal.tag →
        get? s₃.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, get? b.localDecls e.localIdx = some decl →
            decl.ty.kind = u64Decl.ty.kind) := by
    intro ptrVal hp e he htag _
    have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_initLM32 hp
    subst hp'
    cases he with
    | head _ => exact absurd htag (by decide)
    | tail _ h =>
      cases h with
      | head _ =>
        exact ⟨rfl, (fun h => nomatch h), (fun d hd => by injection hd with hd'; subst hd'; rfl)⟩
      | tail _ h' => cases h'
  have hanc₄ : ∀ (ptrVal : ProvenancePtr), get? s₃.frame.locals 2 = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ [lm32TreeChild .active, lm32TreeRoot .active], e.tag = ptrVal.tag →
        treeBorrowAncestorsChildAccessUB .read s₃.memory.borrows e.parentTag = false := by
    intro ptrVal hp e he htag
    have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_initLM32 hp
    subst hp'
    cases he with
    | head _ => exact absurd htag (by decide)
    | tail _ h =>
      cases h with
      | head _ => rfl
      | tail _ h' => cases h'
  have hsim₄ := step_safeRef_deref_read_tree_simulation htree₃' hphase (Or.inl rfl) rfl rfl
    (dstDecl := u64Decl) (refDecl := refMutU64Decl) rfl rfl rfl hu64 himm₃_02 hlive₄ hanc₄
  obtain ⟨m₄, hm₄, htree₄⟩ := stepRelLM3_2Tree_of_anneal_step hsim₄ hs₄
  have htree₄' : StateRelLM3_2Tree b s₄ m₄ [lm32TreeChild .frozen, lm32TreeRoot .active] :=
    htree₄
  have himm₄_step := step_safeRef_deref_read_preserves htree₃'.erased_rel (Or.inl rfl) rfl rfl
    (dstDecl := u64Decl) (refDecl := refMutU64Decl) rfl rfl rfl hu64 himm₃_02
    (fun ptrVal hget e' he' htag' hdead => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      exact hlive₄ ptrVal hget e he htag' hdead) hm₄
  obtain ⟨tf₃, htf₃, _⟩ := id htree₃'.erased_rel
  have himm₄_0 : ∀ tf, m₄.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 :=
    fun tf htf => himm₄_step tf₃ tf htf₃ htf 0 (himm₃ tf₃ htf₃ 0 (by decide))
  -- Step 5 (`stmtIdx = 4`): root-frame `return` of `_0 = 99_u64`
  have hs₅ : stepMirFn b s₄ = .retNormal (.scalar ⟨99, 8⟩) s₄.memory := rfl
  have hsim₅ := step_terminator_goto_return_tree_simulation htree₄' hphase rfl rfl rfl
    (.return_ u64Decl rfl rfl rfl (by decide) himm₄_0) (Or.inr (Or.inl rfl))
  obtain ⟨decl0, imm0, hdecl0, hret0, himmRel0, hm₅⟩ := stepRelLM3_2Tree_retNormal hsim₅ hs₅
  exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, decl0, imm0, hs₁, hm₁, htree₁, hs₂, hm₂, htree₂', rfl,
    hs₃, hm₃, htree₃', rfl, hs₄, hm₄, htree₄', rfl, hs₅, hm₅, hdecl0, hret0, himmRel0⟩

/-- `Runtime(PostCleanup)` MIR body exercising `evalRvalue_reborrow_uninit_target_divergence`:
1. `_2 = &raw const _1` on live, uninitialized `_1 : u64`;
2. `_3 = &*_2`: reborrowing through a raw pointer whose stack target `_1` is
   live but `.uninit` faults with `MirStepNode.fail .ub` in Anneal while
   `lean-miri`'s `Rvalue.Ref` + shallow `ValidityVisitor` steps cleanly. -/
def lm32UninitTargetReborrowBody : CapturedMir where
  defPath := "lm_3_2_witness::uninit_target_reborrow"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl, refU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3) (.ref .shared (derefLocal 2)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal pre-state for `lm32UninitTargetReborrowBody`: all four locals start `.uninit`. -/
def lm32UninitTargetReborrowAnnealPre : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .uninit, .uninit, .uninit] }
    memory := (initMachineState lm32UninitTargetReborrowBody []).memory }

/-- `lean-miri` root frame matching `lm32UninitTargetReborrowAnnealPre`. -/
def lm32UninitTargetReborrowMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm32UninitTargetReborrowBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy u64Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- `lean-miri` state matching `lm32UninitTargetReborrowAnnealPre`. -/
def lm32UninitTargetReborrowMiriPre : AnnealStepState :=
  { stack := ⟨#[lm32UninitTargetReborrowMiriFramePre]⟩, machine := AnnealMachine.empty }

/-- `StateRel` holds between `lm32UninitTargetReborrowAnnealPre` and
`lm32UninitTargetReborrowMiriPre`. -/
theorem lm32UninitTargetReborrow_stateRel_pre :
    StateRel lm32UninitTargetReborrowBody
      lm32UninitTargetReborrowAnnealPre lm32UninitTargetReborrowMiriPre := by
  refine StateRel.mk lm32UninitTargetReborrowMiriFramePre rfl rfl ⟨translateTy u64Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | _ + 4 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i _ slot mls hdecl hslot hmls
  match i with
  | 0 | 1 | 2 | 3 =>
    have hs : slot = .uninit := by simpa [lm32UninitTargetReborrowAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm32UninitTargetReborrowMiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 4 =>
    simp [lm32UninitTargetReborrowBody, get?] at hdecl

private theorem stepRelLM3_1_of_anneal_stepLM32
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {s' : MachineState}
    (hsim : StepRelLM3_1 body m allocMap aRes mRes)
    (ha : aRes = .step s') :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_1 body s' m' allocMap := by
  cases hsim with
  | step s₁ m' hrel =>
    injection ha with htau
    injection htau with hs
    subst hs
    exact ⟨m', rfl, hrel⟩
  | retRoot _ _ _ _ _ _ _ _ _ => cases ha
  | ub _ _ => cases ha

/-- **`wit_lm3_2_reborrow_uninit_target_divergence`**:
Concrete end-to-end non-vacuity witness for
`evalRvalue_reborrow_uninit_target_divergence` starting from pointer-free `StateRel`:
1. `_2 = &raw const _1` promotes live `.uninit` `_1 : u64` to `lm31AllocId1` in
   lockstep (`StateRelLM3_2`);
2. `_3 = &*_2` faults with `MirStepNode.fail .ub` in Anneal (`stepMirFn`, which
   requires `get? locals targetLocal = some (.init _)`) while `lean-miri`
   (`Miri.Interpreter.Step.step` under `annealStepHooks`) steps to `(m₂, .ok true)`,
   writes a tagged pointer into `_3`, and passes shallow `annealValidityAccessCheck`
   on the 8-byte uninitialized allocation (contrast recursive `RefTracking` pointee
   validation in `wit_lm3_2_recursive_ref_pointee_validity`, which rejects the
   uninitialized pointee, and `sim_lm3_3_interpreter_reborrow_step` in `SimLM3_3.lean`,
   which establishes 3-way lockstep whenever the target local is initialized). -/
theorem wit_lm3_2_reborrow_uninit_target_divergence :
    ∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let hooks := annealStepHooks lm32UninitTargetReborrowBody.localDecls
        lm32UninitTargetReborrowBody.layouts
      let entry := rawPtrAllocMapEntry lm32UninitTargetReborrowBody.localDecls
        lm32UninitTargetReborrowBody.layouts .not 1 1 lm31AllocId1
      stepMirFn lm32UninitTargetReborrowBody lm32UninitTargetReborrowAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm32UninitTargetReborrowMiriPre = (m₁, .ok true) ∧
      StateRelLM3_2 lm32UninitTargetReborrowBody s₁ m₁ [entry] ∧
      stepMirFn lm32UninitTargetReborrowBody s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
              .concrete lm31AllocId1 borTag⟩)))) ∧
      annealValidityAccessCheck m₂.machine
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
          some (.concrete lm31AllocId1 borTag)⟩
        (translateTy u64Ty lm32UninitTargetReborrowBody.layouts).layout.size = .ok () := by
  have hphase : ∀ p, lm32UninitTargetReborrowBody.phase ≠ .other p := fun _ h => nomatch h
  have himm₀_all : ∀ tf, lm32UninitTargetReborrowMiriPre.stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
    intro tf h k mls hmls mp hmp
    injection h with h₁; injection h₁ with h₂; subst h₂
    match k with
    | 0 | 1 | 2 | 3 => simp [lm32UninitTargetReborrowMiriFramePre] at hmls; subst hmls; cases hmp
    | _ + 4 => simp [lm32UninitTargetReborrowMiriFramePre] at hmls
  let entry := rawPtrAllocMapEntry lm32UninitTargetReborrowBody.localDecls
    lm32UninitTargetReborrowBody.layouts .not 1 1 lm31AllocId1
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let bor := [rawPtrBorrowEntry lm32UninitTargetReborrowBody.localDecls
    lm32UninitTargetReborrowBody.layouts .not 1 1]
  -- Step 1: `_2 = &raw const _1`
  let s₁ := mkWitStateLM32 lm32UninitTargetReborrowBody 1
    [.uninit, .uninit, .init ptr0, .uninit] bor 2
  have hs₁ : stepMirFn lm32UninitTargetReborrowBody lm32UninitTargetReborrowAnnealPre =
      .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation lm32UninitTargetReborrow_stateRel_pre hphase
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀_all tf htf 2, himm₀_all tf htf 1⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, hrel₁_raw⟩ := stepRelLM3_1_of_anneal_stepLM32 hsim₁ hs₁
  have htag₀ : lm32UninitTargetReborrowAnnealPre.memory.nextTag = 1 := rfl
  have hid₀ : (⟨lm32UninitTargetReborrowMiriPre.machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁_raw
  have hrel₁ : StateRelLM3_2 lm32UninitTargetReborrowBody s₁ m₁ [entry] := hrel₁_raw.toLM3_2
  obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne
    lm32UninitTargetReborrow_stateRel_pre rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀_all tf htf 2, himm₀_all tf htf 1⟩)
    AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne =>
      himm₁_step _ tf₁ rfl htf₁ k hne (himm₀_all _ rfl k)
  -- Step 2: `_3 = &*_2` -> UB in Anneal, `.ok true` in Miri
  obtain ⟨hs₂, m₂, tf₂, borTag, hm₂, htf₂, hloc₃, hval₂⟩ :=
    evalRvalue_reborrow_uninit_target_divergence hrel₁ hphase rfl rfl
      (dstDecl := refU64Decl) (ptrDecl := rawPtrConstU64Decl)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
      (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
      (fun _ h => by dsimp [s₁, mkWitStateLM32, get?, ptr0] at h; nomatch h)
      (fun ptrVal e hp he _ => by
        have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_initLM32 hp
        cases he with
        | tail _ h => cases h
        | head _ =>
          subst hp'
          exact ⟨rfl, (fun h => nomatch h), (fun ⟨_, h⟩ => h rfl)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (e := entry) (targetDecl := u64Decl)
      rfl (.head _) rfl rfl (by rintro ⟨⟩) rfl
  exact ⟨s₁, m₁, m₂, tf₂, borTag, hs₁, hm₁, hrel₁, hs₂, hm₂, htf₂, hloc₃, hval₂⟩

/-! ## 7. Unified Multi-Block `step_mir_lm3_2_tree_state_simulation` Witness Across 3-Level Reborrow Hierarchies, `SwitchInt`, `Assert`, and Safe-Reference `Return` -/

private def mkWitLocStateLM32 (body : CapturedMir) (blockIdx stmtIdx : Nat)
    (locals : List LocalSlot) (borrows : List BorrowEntry) (nextTag : Nat) : MachineState :=
  { frame := { blockIdx := blockIdx, stmtIdx := stmtIdx, locals := locals }
    memory := { (initMachineState body []).memory with
                  borrows := borrows, nextTag := nextTag } }

/-- Shared 6-local Anneal pre-state for `lm32ComposedTreeBody`. -/
def mkPre6AnnealLM32 (b : CapturedMir) (slot₁ : LocalSlot) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0,
        locals := [.uninit, slot₁, .uninit, .uninit, .uninit, .uninit] }
    memory := (initMachineState b []).memory }

/-- Shared 6-local `lean-miri` frame pre-state for `lm32ComposedTreeBody`. -/
def mkPre6MiriFrameLM32 (b : CapturedMir) (retTy : Ty)
    (mls₁ : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody b
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy retTy b.layouts) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      mls₁,
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- Shared 6-local `lean-miri` step state for `lm32ComposedTreeBody`. -/
def mkPre6MiriLM32 (b : CapturedMir) (retTy : Ty)
    (mls₁ : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    AnnealStepState :=
  { stack := ⟨#[mkPre6MiriFrameLM32 b retTy mls₁]⟩, machine := AnnealMachine.empty }

private theorem mkPre6_stateRel_and_imm
    (b : CapturedMir) (d0 d1 d2 d3 d4 d5 : LocalDecl)
    (hdecls : b.localDecls = [d0, d1, d2, d3, d4, d5])
    (slot₁ : LocalSlot)
    (mls₁ : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
    (hnoind₁ : ∀ mp, mls₁.value ≠ .live (.indirect mp))
    (hrel₁ : LocalRel AnnealMachine.empty d1 b.layouts slot₁ mls₁) :
    StateRel b (mkPre6AnnealLM32 b slot₁) (mkPre6MiriLM32 b d0.ty mls₁) ∧
    (∀ tf, (mkPre6MiriLM32 b d0.ty mls₁).stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k) := by
  have himm_all : ∀ tf, (mkPre6MiriLM32 b d0.ty mls₁).stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
    intro tf h k mls hmls mp hmp
    injection h with h₁; injection h₁ with h₂; subst h₂
    match k with
    | 0 | 2 | 3 | 4 | 5 => simp [mkPre6MiriFrameLM32] at hmls; subst hmls; cases hmp
    | 1 => simp [mkPre6MiriFrameLM32] at hmls; subst hmls; exact hnoind₁ mp hmp
    | _ + 6 => simp [mkPre6MiriFrameLM32] at hmls
  refine ⟨?_, himm_all⟩
  refine StateRel.mk (mkPre6MiriFrameLM32 b d0.ty mls₁) rfl rfl ⟨translateTy d0.ty b.layouts, rfl⟩
    ?_ rfl rfl rfl rfl rfl
    (MemoryAllocDisjoint.of_no_indirect _ (himm_all _ rfl))
  refine ⟨rfl, rfl, by simp [mkPre6AnnealLM32, hdecls], by simp [mkPre6MiriFrameLM32, hdecls], ?_⟩
  intro i decl slot mls hdecl hslot hmls
  rw [hdecls] at hdecl
  match i with
  | 0 =>
    have hd : decl = d0 := by simpa [get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [mkPre6AnnealLM32, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [mkPre6MiriFrameLM32] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = d1 := by simpa [get?] using hdecl.symm
    have hs : slot = slot₁ := by simpa [mkPre6AnnealLM32, get?] using hslot.symm
    have hm : mls = mls₁ := by simpa [mkPre6MiriFrameLM32] using hmls.symm
    subst hd hs hm
    exact hrel₁
  | 2 =>
    have hd : decl = d2 := by simpa [get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [mkPre6AnnealLM32, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [mkPre6MiriFrameLM32] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 3 =>
    have hd : decl = d3 := by simpa [get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [mkPre6AnnealLM32, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [mkPre6MiriFrameLM32] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 4 =>
    have hd : decl = d4 := by simpa [get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [mkPre6AnnealLM32, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [mkPre6MiriFrameLM32] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 5 =>
    have hd : decl = d5 := by simpa [get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [mkPre6AnnealLM32, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [mkPre6MiriFrameLM32] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 6 =>
    simp [get?] at hdecl

private theorem stepObsRelLM3_2Tree_of_anneal_step
    {body : CapturedMir} {m : AnnealStepState} {treeMap : List ReborrowMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {s' : MachineState}
    (hsim : StepObsRelLM3_2Tree body m treeMap aRes mRes)
    (ha : aRes = .step s') :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_2Tree body s' m' treeMap := by
  generalize ha_eq : aRes = aNode at hsim
  cases hsim with
  | emitStep obs s₁ m' hrel =>
    rw [ha] at ha_eq
    cases obs with
    | silent =>
      injection ha_eq with hrun
      injection hrun with hs
      subst hs
      exact ⟨m', rfl, hrel⟩
    | event _ => cases ha_eq
  | retRoot _ _ _ _ _ _ _ _ hm' => rw [ha] at ha_eq; cases ha_eq
  | ub _ _ => rw [ha] at ha_eq; cases ha_eq

private theorem stepObsRelLM3_2Tree_of_anneal_emitEvent
    {body : CapturedMir} {m : AnnealStepState} {treeMap : List ReborrowMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {tag : Nat} {s' : MachineState}
    (hsim : StepObsRelLM3_2Tree body m treeMap aRes mRes)
    (ha : aRes = .emitStep (.event tag) s') :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_2Tree body s' m' treeMap := by
  generalize ha_eq : aRes = aNode at hsim
  cases hsim with
  | emitStep obs s₁ m' hrel =>
    rw [ha] at ha_eq
    cases obs with
    | silent => cases ha_eq
    | event _ =>
      injection ha_eq with _ h2
      have hfun := congrFun h2 PUnit.unit
      injection hfun with hs
      subst hs
      exact ⟨m', rfl, hrel⟩
  | retRoot _ _ _ _ _ _ _ _ _ => rw [ha] at ha_eq; cases ha_eq
  | ub _ _ => rw [ha] at ha_eq; cases ha_eq

private theorem treeMap_eq_of_toBorrowEntry_eq
    {treeMap expected : List ReborrowMapEntry}
    (hta1 : ∀ e' ∈ treeMap, e'.allocId = lm31AllocId1)
    (ha1 : ∀ e ∈ expected, e.allocId = lm31AllocId1)
    (hmap : treeMap.map ReborrowMapEntry.toBorrowEntry =
      expected.map ReborrowMapEntry.toBorrowEntry) :
    treeMap = expected := by
  induction treeMap generalizing expected with
  | nil =>
    cases expected with
    | nil => rfl
    | cons _ _ => cases hmap
  | cons e' rest ih =>
    cases expected with
    | nil => cases hmap
    | cons e rest_exp =>
      injection hmap with hbe hrest
      have he'_a1 := hta1 e' (List.Mem.head _)
      have he_a1 := ha1 e (List.Mem.head _)
      have htl := ih (fun x hx => hta1 x (List.Mem.tail _ hx))
        (fun x hx => ha1 x (List.Mem.tail _ hx)) hrest
      subst htl
      have ht : e'.tag = e.tag := congrArg BorrowEntry.tag hbe
      have hl : e'.localIdx = e.localIdx := congrArg BorrowEntry.targetLocal hbe
      have hp : e'.perm = e.perm := congrArg BorrowEntry.perm hbe
      have hpar : e'.parentTag = e.parentTag := congrArg BorrowEntry.parentTag hbe
      rcases e' with ⟨t', l', a', p', par'⟩
      rcases e with ⟨t, l, a, p, par⟩
      dsimp only at ht hl hp hpar he'_a1 he_a1
      subst ht hl hp hpar he'_a1 he_a1
      rfl

private theorem treeMap_eq_of_borrows_and_nextAllocId_two
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap expected : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hbor : s.memory.borrows = expected.map ReborrowMapEntry.toBorrowEntry)
    (ha1 : ∀ e ∈ expected, e.allocId = lm31AllocId1)
    (hnext2 : m.machine.memory.nextAllocId = 2) :
    treeMap = expected := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc, _⟩ := id htree.erased_rel
  refine treeMap_eq_of_toBorrowEntry_eq (fun e' he' => ?_) ha1 (htree.borrows_eq.symm.trans hbor)
  have hlt := (halloc.base_addr_valid e'.toAllocMapEntry (List.mem_map_of_mem he')).2.1
  rw [hnext2] at hlt
  exact allocId_eq_one_of_lt_two hlt

/-- Constant `true : bool` operand for `Assert` terminator witnesses. -/
def constBoolTrueLM32 : ConstOperand :=
  { ty := boolTyLM32, val := .scalar (.int ⟨1, 1⟩) }

private theorem constBoolTrue_wellTypedLM32 (body : CapturedMir)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (hlay : body.layouts = emptyLayoutTable) :
    WellTypedScalarOperand body tf (.constant constBoolTrueLM32) boolTyLM32 :=
  .constScalar constBoolTrueLM32 ⟨1, 1⟩ rfl (Or.inl rfl) (Or.inl rfl) (by decide)
    (by rw [hlay]; rfl) (fun _ => ⟨rfl, Or.inr rfl⟩) (fun h => nomatch h)

private theorem step_terminator_switchInt_u64_machine_eq
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {bb : BasicBlockData} {discr : MirAst.Operand} {targets : SwitchTargets}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hterm : bb.terminator.kind = .switchInt discr targets)
    (hdiscr : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf discr u64Ty)
    (hcases : SwitchCasesFit u64Ty targets)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine = m.machine := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  rw [miri_step_at_terminator hframes hfr.body_eq hfr.location_eq hbb hstmt_none] at hstep
  have hm_term : translateTerminator bb.terminator =
      { sourceInfo := defaultSourceInfo,
        kind := .SwitchInt (translateOperand discr) (translateSwitchTargets targets) } := by
    unfold translateTerminator; rw [hterm]; rfl
  rw [hm_term] at hstep
  have hprim : IsPrimScalarTy u64Ty := Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))
  have hty : u64Ty.kind = .bool ∨ (∃ k, u64Ty.kind = .int k) ∨ (∃ k, u64Ty.kind = .uint k) :=
    Or.inr (Or.inr ⟨.u64, rfl⟩)
  have hdisc_eq : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
      (translateOperand discr) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperand body.localDecls body.layouts (translateOperand discr) none >>=
          annealReadImmediate) m := rfl
  rcases evalOperand_scalar_lm3_2_simulation hstate hframes (hdiscr tf hframes) hprim none with
    ⟨m_e, msg, _, hm_ub⟩ | ⟨sc, msc, tf', _, hm_ok, _, himm, _, _⟩
  · have hdisc : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
        (translateOperand discr) m = (m_e, .error (.undefinedBehavior msg)) := by
      rw [hdisc_eq]; unfold Miri.Interpreter.runRvalue; rw [hm_ub]
    rw [evalTerminator_switchInt_error _ () _ _ _ m m_e _ hdisc] at hstep
    cases hstep
  · obtain ⟨sc₀, msc₀, hsc_eq, hmsc_eq, hrel, hsz, _, _⟩ := himm.of_primitive_scalar hprim
    injection hsc_eq with hsc_eq'; subst hsc_eq'
    have hmsc_eq' : msc = msc₀ := by cases hmsc_eq; rfl
    subst hmsc_eq'
    have hdisc : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
        (translateOperand discr) m =
        ({ m with stack := ⟨#[tf']⟩ },
          .ok ⟨.scalar (.fromScalarInt msc), translateTy u64Ty body.layouts⟩) := by
      rw [hdisc_eq]; unfold Miri.Interpreter.runRvalue; rw [hm_ok]
    obtain ⟨hwsz, hwvalid⟩ := boolOrInt_translateTy_size hty body.layouts
    have hwidth : sc.sizeBytes = boolOrIntByteWidth u64Ty :=
      translateSizeBytes_inj hrel.validBytes hwvalid (by rw [← hsz, hwsz])
    have hsz_ty : sc.sizeBytes = match u64Ty.kind with
        | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc.sizeBytes := by
      rw [hwidth]; rfl
    have hcmp : ∀ v b, (v, b) ∈ targets.branches →
        (annealTerminatorHooks body.localDecls body.layouts).compareSwitchCase ()
          ⟨.scalar (.fromScalarInt msc), translateTy u64Ty body.layouts⟩ v
          { m with stack := ⟨#[tf']⟩ } =
        ({ m with stack := ⟨#[tf']⟩ }, .ok (Nat.beq sc.bits v)) := by
      intro v b hmem
      obtain ⟨hlt, hcase_bool⟩ := hcases v b hmem
      rw [← hwidth] at hlt
      exact compareSwitchCase_simulation hrel body.localDecls body.layouts u64Ty hty hsz_ty
        (fun h => nomatch h) v hlt hcase_bool _
    rw [evalTerminator_switchInt_ok _ () _ _ _ m _ _ sc.bits hdisc hcmp] at hstep
    unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation at hstep
    rw [stack_currentFrame?_singleton _ tf' rfl] at hstep
    dsimp only [Except.map] at hstep
    try split at hstep
    all_goals first | (injection hstep with hm' _; subst hm'; rfl) | cases hstep

private theorem step_terminator_assert_constTrue_machine_eq
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {bb : BasicBlockData} {target : BasicBlockIdx}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hterm : bb.terminator.kind = .assert (.constant constBoolTrueLM32) true target .unreachable)
    (hlay : body.layouts = emptyLayoutTable)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine = m.machine := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  rw [miri_step_at_terminator hframes hfr.body_eq hfr.location_eq hbb hstmt_none] at hstep
  have hm_term : translateTerminator bb.terminator =
      { sourceInfo := defaultSourceInfo,
        kind := .Assert (translateOperand (.constant constBoolTrueLM32)) true
          (.BoundsCheck (translateOperand (.constant constBoolTrueLM32))
            (translateOperand (.constant constBoolTrueLM32)))
          target .Unreachable } := by
    unfold translateTerminator; rw [hterm]; rfl
  rw [hm_term] at hstep
  dsimp only [Miri.Interpreter.ControlFlow.evalTerminator] at hstep
  rcases evalOperand_scalar_lm3_2_simulation hstate hframes
      (constBoolTrue_wellTypedLM32 body tf hlay) (Or.inl rfl) none with
    ⟨_, _, ha_ub, _⟩ | ⟨sc, msc, tf', ha_ok, hm_ok, _, himm, _, _⟩
  · cases ha_ub
  · obtain ⟨sc₀, msc₀, hsc_eq, hmsc_eq, hsc_rel, _, _, _⟩ := himm.of_primitive_scalar (Or.inl rfl)
    injection hsc_eq with hsc_eq'; subst hsc_eq'
    have hmsc_eq' : msc = msc₀ := by cases hmsc_eq; rfl
    subst hmsc_eq'
    have hsc1 : sc = ⟨1, 1⟩ := by cases ha_ok; rfl
    subst hsc1
    have htoB : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBool = .ok true := by
      have hsz := hsc_rel.size_eq
      have hdat := hsc_rel.data_eq
      rcases msc with ⟨d, s_sz⟩
      dsimp only at hsz hdat; subst hsz hdat
      with_unfolding_all rfl
    have hread_ok : (annealTerminatorHooks body.localDecls body.layouts).readAssertCondition ()
        (translateOperand (.constant constBoolTrueLM32)) m =
        ({ m with stack := ⟨#[tf']⟩ }, .ok true) := by
      dsimp only [annealTerminatorHooks, Miri.Interpreter.TerminatorHooks.readAssertCondition]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_assoc_apply, EStateM.bind_eq_ok hm_ok]
      dsimp only [Miri.Interpreter.Immediate.toScalar, bind, EStateM.bind, pure, EStateM.pure]
      rw [htoB]; rfl
    have h8 := readAssertCondition_to_8 hread_ok
    simp only [h8] at hstep
    dsimp only [Id.run, bind, Except.bind, pure, Except.pure,
      Miri.Interpreter.TerminatorHooks.ignoreOptionalOverflowChecks,
      Miri.Interpreter.ControlFlow.isOptionalOverflowCheck] at hstep
    have hbeq_t : (true == true) = true := rfl
    simp only [Bool.and_false, Bool.false_or, hbeq_t, ↓reduceIte] at hstep
    unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation at hstep
    rw [stack_currentFrame?_singleton _ tf' rfl] at hstep
    dsimp only [Except.map] at hstep
    try split at hstep
    all_goals first | (injection hstep with hm' _; subst hm'; rfl) | cases hstep

/-- Grandchild Tree Borrows entry for `&*_3` (tag `3`, parent tag `2`). -/
def lm32TreeGrandchild (perm : TreeBorrowPerm) : ReborrowMapEntry :=
  { tag := 3, localIdx := 1, allocId := lm31AllocId1, perm := perm, parentTag := some 2 }

/-- Multi-block `Runtime(PostCleanup)` MIR body exercising 3-level parent -> child ->
grandchild Tree Borrows reborrows, child write activating ancestor, root read
freezing child descendant, `SwitchInt`, `Assert`, safe-ref `move`, and root-frame
safe-ref `return`:
```text
bb0: _2 = &mut _1;
     _3 = &mut *_2;
     *_3 = const 99_u64;
     _4 = &*_3;
     _5 = copy *_2;
     switchInt(copy _5) -> [99: bb1, otherwise: bb2]
bb1: assert(const true == true) -> [success: bb2, unwind: unreachable]
bb2: _0 = move _4;
     return
``` -/
def lm32ComposedTreeBody : CapturedMir where
  defPath := "lm_3_2_witness::composed_tree_state_sim"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [refU64Decl, u64Decl, refMutU64Decl, refMutU64Decl, refU64Decl, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
        mkStmt (.assign (local_ 3) (.ref (.mut false) (derefLocal 2))),
        mkStmt (.assign (derefLocal 3) (.use (.constant (constU64 99)))),
        mkStmt (.assign (local_ 4) (.ref .shared (derefLocal 3))),
        mkStmt (.assign (local_ 5) (.use (.copy (derefLocal 2))))],
      terminator := mkTerm (.switchInt (.copy (local_ 5)) { branches := [(99, 1)], otherwise := 2 }),
      isCleanup := false },
    { statements := [],
      terminator := mkTerm (.assert (.constant constBoolTrueLM32) true 2 .unreachable),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.move (local_ 4))))],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_2_composed_tree_state_simulation_real_steps`**: end-to-end 9-step
multi-block execution of `lm32ComposedTreeBody` driven at **every single step**
through the unified `step_mir_lm3_2_tree_state_simulation` theorem across a
3-level parent -> child -> grandchild Tree Borrows hierarchy (`tag 1` -> `tag 2`
-> `tag 3`), `SwitchInt`, `Assert`, safe-ref `move`, and safe-ref root `return`:
1. `bb0[0]`: `_2 = &mut _1` (`[root(.reserved)]`);
2. `bb0[1]`: `_3 = &mut *_2` (`[child(.reserved), root(.reserved)]`);
3. `bb0[2]`: `*_3 = const 99_u64` (activates child and ancestor:
   `[child(.active), root(.active)]`);
4. `bb0[3]`: `_4 = &*_3` (`[grandchild(.frozen), child(.active), root(.active)]`);
5. `bb0[4]`: `_5 = copy *_2` (root read yields `99_u64` and freezes child:
   `[grandchild(.frozen), child(.frozen), root(.active)]`);
6. `bb0` `SwitchInt(copy _5)` -> emits `MirObs.event 99` and branches to `bb1`;
7. `bb1` `Assert(const true == true)` -> jumps to `bb2`;
8. `bb2[0]`: `_0 = move _4` -> moves grandchild `&u64` (`tag 3`) into `_0`;
9. `bb2` `return` -> returns `.ptr { allocId := 3, offsetBytes := 0 } 8` in
   lockstep with `ImmediateRelLM3_2` across the 3-level `treeMap`. -/
theorem wit_lm3_2_composed_tree_state_simulation_real_steps :
    ∃ (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ : MachineState)
      (m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ : AnnealStepState)
      (decl0 : LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      let b := lm32ComposedTreeBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let finalTree :=
        [lm32TreeGrandchild .frozen, lm32TreeChild .frozen, lm32TreeRoot .active]
      stepMirFn b (mkPre6AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkPre6MiriLM32 b refU64Ty lm32Mls42) =
        (m₁, .ok true) ∧
      StateRelLM3_2Tree b s₁ m₁ [lm32TreeRoot .reserved] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2Tree b s₂ m₂ [lm32TreeChild .reserved, lm32TreeRoot .reserved] ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_2Tree b s₃ m₃ [lm32TreeChild .active, lm32TreeRoot .active] ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_2Tree b s₄ m₄
        [lm32TreeGrandchild .frozen, lm32TreeChild .active, lm32TreeRoot .active] ∧
      stepMirFn b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_2Tree b s₅ m₅ finalTree ∧
      stepMirFn b s₅ = .emitStep (.event 99) s₆ ∧
      Miri.Interpreter.Step.step hooks () m₅ = (m₆, .ok true) ∧
      StateRelLM3_2Tree b s₆ m₆ finalTree ∧
      s₆.frame.blockIdx = 1 ∧
      stepMirFn b s₆ = .step s₇ ∧
      Miri.Interpreter.Step.step hooks () m₆ = (m₇, .ok true) ∧
      StateRelLM3_2Tree b s₇ m₇ finalTree ∧
      s₇.frame.blockIdx = 2 ∧
      stepMirFn b s₇ = .step s₈ ∧
      Miri.Interpreter.Step.step hooks () m₇ = (m₈, .ok true) ∧
      StateRelLM3_2Tree b s₈ m₈ finalTree ∧
      (∃ tm, StepObsRelLM3_2Tree b m₈ tm (stepMirFn b s₈) (Miri.Interpreter.Step.step hooks () m₈)) ∧
      stepMirFn b s₈ = .retNormal (.ptr { allocId := 3, offsetBytes := 0 } 8) s₈.memory ∧
      Miri.Interpreter.Step.step hooks () m₈ = ({ m₈ with stack := ⟨#[]⟩ }, .ok true) ∧
      get? b.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m₈ = (m₈, .ok (.immediate imm0)) ∧
      ImmediateRelLM3_2 (finalTree.map ReborrowMapEntry.toAllocMapEntry)
        decl0.ty b.layouts (.ptr { allocId := 3, offsetBytes := 0 } 8) imm0 := by
  let b := lm32ComposedTreeBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hu64 : IsPrimScalarTy u64Ty := Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))
  obtain ⟨hrel₀, himm₀⟩ := mkPre6_stateRel_and_imm b refU64Decl u64Decl refMutU64Decl
    refMutU64Decl refU64Decl u64Decl rfl (.init (.scalar ⟨42, 8⟩)) lm32Mls42
    (fun _ h => nomatch h)
    (.immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
  have htree₀ : StateRelLM3_2Tree b (mkPre6AnnealLM32 b (.init (.scalar ⟨42, 8⟩)))
      (mkPre6MiriLM32 b refU64Ty lm32Mls42) [] := hrel₀.toLM3_1.toLM3_2.toTree
  let p1 : ProvenancePtr := { allocId := 1, offsetBytes := 0 }
  let p2 : ProvenancePtr := { allocId := 2, offsetBytes := 0 }
  let p3 : ProvenancePtr := { allocId := 3, offsetBytes := 0 }
  -- Step 1 (`bb0[0]`): `_2 = &mut _1`
  let s₁ := mkWitLocStateLM32 b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr p1 8), .uninit, .uninit, .uninit]
    [(lm32TreeRoot .reserved).toBorrowEntry] 2
  have hs₁ : stepMirFn b (mkPre6AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ := rfl
  have hwt₁ : WellTypedLM3_2TreeStateStmt b (mkPre6AnnealLM32 b (.init (.scalar ⟨42, 8⟩)))
      (mkPre6MiriLM32 b refU64Ty lm32Mls42) []
      (mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1)))) :=
    .refAddrOf 2 1 (.mut false) refMutU64Decl u64Decl .mut (.uint .u64) _
      rfl rfl rfl hu64 (by decide) (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩)
  obtain ⟨tm₁, hobs₁⟩ := step_mir_lm3_2_tree_state_simulation htree₀ hphase rfl
    (Or.inl ⟨_, rfl, hwt₁⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, htree₁⟩ := stepObsRelLM3_2Tree_of_anneal_step hobs₁ hs₁
  obtain ⟨hsup₁, hnext₁⟩ := step_ref_supply_two hrel₀ rfl rfl
    (dstDecl := refMutU64Decl) (targetDecl := u64Decl) rfl rfl hu64 (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) rfl hm₁
  have htm₁ : tm₁ = [lm32TreeRoot .reserved] :=
    treeMap_eq_of_borrows_and_nextAllocId_two htree₁ rfl
      (by intro _ he; cases he with | head _ => rfl | tail _ h => cases h) hnext₁
  subst htm₁
  -- Step 2 (`bb0[1]`): `_3 = &mut *_2` (child tag `2`, `parentTag = some 1`)
  let s₂ := mkWitLocStateLM32 b 0 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr p1 8), .init (.ptr p2 8), .uninit, .uninit]
    [(lm32TreeChild .reserved).toBorrowEntry, (lm32TreeRoot .reserved).toBorrowEntry] 3
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => immediate_of_nextAllocId_two htree₁.erased_rel hsup₁ hnext₁
      (List.Mem.head _) rfl htf k (Or.inr hne)
  have hlive₂ : ∀ (ptrVal : ProvenancePtr) (e : ReborrowMapEntry),
      get? s₁.frame.locals 2 = some (.init (.ptr ptrVal 8)) →
      e ∈ [lm32TreeRoot .reserved] → e.tag = ptrVal.tag →
      get? s₁.frame.locals e.localIdx ≠ some .dead ∧
      get? s₁.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
      ¬(e.perm = .frozen ∧ BorrowKind.mut false ≠ .shared) ∧
      (∀ tgtDecl, get? b.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = .uint .u64) := by
    intro ptrVal e hp he _
    rcases ptrVal_of_some_initLM32 hp with rfl
    cases he with
    | tail _ h => cases h
    | head _ =>
      exact ⟨(fun h => nomatch h), (fun h => nomatch h), rfl, (fun h => nomatch h),
        (fun ⟨h, _⟩ => nomatch h), (fun d hd => by injection hd with hd'; subst hd'; rfl)⟩
  have hwt₂ : WellTypedLM3_2TreeStateStmt b s₁ m₁ [lm32TreeRoot .reserved]
      (mkStmt (.assign (local_ 3) (.ref (.mut false) (derefLocal 2)))) :=
    .reborrowSafeRef 3 2 (.mut false) refMutU64Decl refMutU64Decl .mut .mut
      (.uint .u64) (.uint .u64) _ rfl rfl rfl rfl hu64
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩) hlive₂
      (fun _ _ _ he _ => by cases he with | head _ => rfl | tail _ h => cases h)
  obtain ⟨tm₂, hobs₂⟩ := step_mir_lm3_2_tree_state_simulation htree₁ hphase rfl
    (Or.inl ⟨_, rfl, hwt₂⟩) hsup₁
  obtain ⟨m₂, hm₂, htree₂⟩ := stepObsRelLM3_2Tree_of_anneal_step hobs₂ hs₂
  have hflat₂ := evalRvalue_reborrow_safeRef_simulation htree₁.erased_rel hphase
    (dstIdx := 3) (refIdx := 2) (bk := .mut false) rfl rfl rfl rfl rfl rfl hu64
    (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
    (fun ptrVal e' hget he' htag' => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'; exact hlive₂ ptrVal e hget he htag')
  obtain ⟨_, m₂', _, _, hm₂', _, hmach₂', _⟩ :=
    hflat₂.2 p1 (lm32TreeRoot .reserved).toAllocMapEntry rfl (List.Mem.head _) rfl (fun h => nomatch h)
  have hmach₂ : m₂.machine = m₁.machine := (by have h := hm₂'.symm.trans hm₂; injection h : m₂' = m₂) ▸ hmach₂'
  have hsup₂ : AllocIdSupplyReady m₂.machine.memory := hmach₂ ▸ hsup₁
  have hnext₂ : m₂.machine.memory.nextAllocId = 2 := by rw [hmach₂]; exact hnext₁
  have htm₂ : tm₂ = [lm32TreeChild .reserved, lm32TreeRoot .reserved] :=
    treeMap_eq_of_borrows_and_nextAllocId_two htree₂ rfl
      (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> rfl) hnext₂
  subst htm₂
  -- Step 3 (`bb0[2]`): `*_3 = const 99_u64` (child write activates child & root)
  let s₃ := mkWitLocStateLM32 b 0 3
    [.uninit, .init (.scalar ⟨99, 8⟩), .init (.ptr p1 8), .init (.ptr p2 8), .uninit, .uninit]
    [(lm32TreeChild .active).toBorrowEntry, (lm32TreeRoot .active).toBorrowEntry] 3
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  have himm₂_3 : ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf 3 :=
    fun tf htf => immediate_of_nextAllocId_two htree₂.erased_rel hsup₂ hnext₂
      (List.Mem.head _) rfl htf 3 (Or.inr (by decide))
  have hwt₃ : WellTypedLM3_2TreeStateStmt b s₂ m₂
      [lm32TreeChild .reserved, lm32TreeRoot .reserved]
      (mkStmt (.assign (derefLocal 3) (.use (.constant (constU64 99))))) :=
    .safeRefDerefWrite 3 (.constant (constU64 99)) refMutU64Decl .mut (.uint .u64) u64Ty _
      rfl rfl hu64 rfl (fun tf _ => constU64_wellTypedLM32 b tf 99 (by decide)) himm₂_3
      (fun ptrVal e tgtDecl hp he htag htgt _ => by
        rcases ptrVal_of_some_initLM32 hp with rfl
        cases he with
        | head _ => injection htgt with hd; subst hd; exact ⟨rfl, Or.inr rfl, rfl⟩
        | tail _ h => cases h with | head _ => exact absurd htag (by decide) | tail _ h' => cases h')
      (fun ptrVal e hp he htag => by
        rcases ptrVal_of_some_initLM32 hp with rfl
        cases he with
        | head _ => rfl
        | tail _ h => cases h with | head _ => exact absurd htag (by decide) | tail _ h' => cases h')
  obtain ⟨tm₃, hobs₃⟩ := step_mir_lm3_2_tree_state_simulation htree₂ hphase rfl
    (Or.inl ⟨_, rfl, hwt₃⟩) hsup₂
  obtain ⟨m₃, hm₃, htree₃⟩ := stepObsRelLM3_2Tree_of_anneal_step hobs₃ hs₃
  obtain ⟨hsup₃, hnext₃⟩ := step_safeRef_deref_write_const_supply htree₂.erased_rel rfl rfl
    (refDecl := refMutU64Decl) rfl rfl hu64 rfl
    (fun tf _ => constU64_wellTypedLM32 b tf 99 (by decide)) himm₂_3
    (ptrVal := p2) (e := (lm32TreeChild .reserved).toAllocMapEntry)
    rfl (List.Mem.head _) rfl rfl (fun h => nomatch h)
    (fun d hd => by injection hd with hd'; subst hd'; rfl) hsup₂ hnext₂ rfl hm₃
  have htm₃ : tm₃ = [lm32TreeChild .active, lm32TreeRoot .active] :=
    treeMap_eq_of_borrows_and_nextAllocId_two htree₃ rfl
      (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> rfl) hnext₃
  subst htm₃
  -- Step 4 (`bb0[3]`): `_4 = &*_3` (grandchild tag `3`, `parentTag = some 2`)
  let tree₄ := [lm32TreeGrandchild .frozen, lm32TreeChild .active, lm32TreeRoot .active]
  let s₄ := mkWitLocStateLM32 b 0 4
    [.uninit, .init (.scalar ⟨99, 8⟩), .init (.ptr p1 8), .init (.ptr p2 8), .init (.ptr p3 8), .uninit]
    (tree₄.map ReborrowMapEntry.toBorrowEntry) 4
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => immediate_of_nextAllocId_two htree₃.erased_rel hsup₃ hnext₃
      (List.Mem.head _) rfl htf k (Or.inr hne)
  have hlive₄ : ∀ (ptrVal : ProvenancePtr) (e : ReborrowMapEntry),
      get? s₃.frame.locals 3 = some (.init (.ptr ptrVal 8)) →
      e ∈ [lm32TreeChild .active, lm32TreeRoot .active] → e.tag = ptrVal.tag →
      get? s₃.frame.locals e.localIdx ≠ some .dead ∧
      get? s₃.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
      ¬(e.perm = .frozen ∧ BorrowKind.shared ≠ .shared) ∧
      (∀ tgtDecl, get? b.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = .uint .u64) := by
    intro ptrVal e hp he htag
    rcases ptrVal_of_some_initLM32 hp with rfl
    cases he with
    | head _ =>
      exact ⟨(fun h => nomatch h), (fun h => nomatch h), rfl, (fun h => nomatch h),
        (fun ⟨_, h⟩ => h rfl), (fun d hd => by injection hd with hd'; subst hd'; rfl)⟩
    | tail _ h => cases h with | head _ => exact absurd htag (by decide) | tail _ h' => cases h'
  have hwt₄ : WellTypedLM3_2TreeStateStmt b s₃ m₃
      [lm32TreeChild .active, lm32TreeRoot .active]
      (mkStmt (.assign (local_ 4) (.ref .shared (derefLocal 3)))) :=
    .reborrowSafeRef 4 3 .shared refU64Decl refMutU64Decl .mut .not
      (.uint .u64) (.uint .u64) _ rfl rfl rfl rfl hu64
      (fun tf htf => ⟨himm₃ tf htf 4 (by decide), himm₃ tf htf 3 (by decide)⟩) hlive₄
      (fun ptrVal e hp he htag => by
        rcases ptrVal_of_some_initLM32 hp with rfl
        cases he with
        | head _ => rfl
        | tail _ h => cases h with | head _ => exact absurd htag (by decide) | tail _ h' => cases h')
  obtain ⟨tm₄, hobs₄⟩ := step_mir_lm3_2_tree_state_simulation htree₃ hphase rfl
    (Or.inl ⟨_, rfl, hwt₄⟩) hsup₃
  obtain ⟨m₄, hm₄, htree₄⟩ := stepObsRelLM3_2Tree_of_anneal_step hobs₄ hs₄
  have hflat₄ := evalRvalue_reborrow_safeRef_simulation htree₃.erased_rel hphase
    (dstIdx := 4) (refIdx := 3) (bk := .shared) rfl rfl rfl rfl rfl rfl hu64
    (fun tf htf => ⟨himm₃ tf htf 4 (by decide), himm₃ tf htf 3 (by decide)⟩)
    (fun ptrVal e' hget he' htag' => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'; exact hlive₄ ptrVal e hget he htag')
  obtain ⟨_, m₄', _, _, hm₄', _, hmach₄', _⟩ :=
    hflat₄.2 p2 (lm32TreeChild .active).toAllocMapEntry rfl (List.Mem.head _) rfl (fun h => nomatch h)
  have hmach₄ : m₄.machine = m₃.machine := (by have h := hm₄'.symm.trans hm₄; injection h : m₄' = m₄) ▸ hmach₄'
  have hsup₄ : AllocIdSupplyReady m₄.machine.memory := hmach₄ ▸ hsup₃
  have hnext₄ : m₄.machine.memory.nextAllocId = 2 := by rw [hmach₄]; exact hnext₃
  have htree₄_a1 : ∀ e ∈ tree₄, e.allocId = lm31AllocId1 := by
    intro e he
    simp only [tree₄, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> rfl
  have htm₄ : tm₄ = tree₄ :=
    treeMap_eq_of_borrows_and_nextAllocId_two htree₄ rfl htree₄_a1 hnext₄
  subst htm₄
  -- Step 5 (`bb0[4]`): `_5 = copy *_2` (root read yields `99_u64` & freezes child `tag 2`)
  let finalTree := [lm32TreeGrandchild .frozen, lm32TreeChild .frozen, lm32TreeRoot .active]
  have hfinal_a1 : ∀ e ∈ finalTree, e.allocId = lm31AllocId1 := by
    intro e he
    simp only [finalTree, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> rfl
  let s₅ := mkWitLocStateLM32 b 0 5
    [.uninit, .init (.scalar ⟨99, 8⟩), .init (.ptr p1 8), .init (.ptr p2 8),
     .init (.ptr p3 8), .init (.scalar ⟨99, 8⟩)]
    (finalTree.map ReborrowMapEntry.toBorrowEntry) 4
  have hs₅ : stepMirFn b s₄ = .step s₅ := rfl
  have himm₄ : ∀ tf, m₄.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => immediate_of_nextAllocId_two htree₄.erased_rel hsup₄ hnext₄
      (List.Mem.head _) rfl htf k (Or.inr hne)
  have hlive₅ : ∀ (ptrVal : ProvenancePtr), get? s₄.frame.locals 2 = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ tree₄, e.tag = ptrVal.tag →
        get? s₄.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, get? b.localDecls e.localIdx = some decl →
            decl.ty.kind = u64Decl.ty.kind) := by
    intro ptrVal hp e he htag _
    rcases ptrVal_of_some_initLM32 hp with rfl
    simp only [tree₄, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact absurd htag (by decide)
    · exact absurd htag (by decide)
    · exact ⟨rfl, (fun h => nomatch h), (fun d hd => by injection hd with hd'; subst hd'; rfl)⟩
  have hwt₅ : WellTypedLM3_2TreeStateStmt b s₄ m₄ tree₄
      (mkStmt (.assign (local_ 5) (.use (.copy (derefLocal 2))))) :=
    .safeRefDerefRead 5 2 MirAst.Operand.copy u64Decl refMutU64Decl .mut _
      (Or.inl rfl) rfl rfl rfl hu64
      (fun tf htf => ⟨himm₄ tf htf 5 (by decide), himm₄ tf htf 2 (by decide)⟩) hlive₅
      (fun ptrVal hp e he htag => by
        rcases ptrVal_of_some_initLM32 hp with rfl
        simp only [tree₄, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact absurd htag (by decide)
        · exact absurd htag (by decide)
        · rfl)
  obtain ⟨tm₅, hobs₅⟩ := step_mir_lm3_2_tree_state_simulation htree₄ hphase rfl
    (Or.inl ⟨_, rfl, hwt₅⟩) hsup₄
  obtain ⟨m₅, hm₅, htree₅⟩ := stepObsRelLM3_2Tree_of_anneal_step hobs₅ hs₅
  have hmach₅ : m₅.machine = m₄.machine :=
    (step_safeRef_deref_read_machine_and_preserves htree₄.erased_rel (Or.inl rfl) rfl rfl
      (dstDecl := u64Decl) (refDecl := refMutU64Decl) rfl rfl rfl hu64
      (fun tf htf => ⟨himm₄ tf htf 5 (by decide), himm₄ tf htf 2 (by decide)⟩)
      (fun ptrVal hget e' he' htag' hdead => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
        exact hlive₅ ptrVal hget e he htag' hdead) hm₅).1
  have hsup₅ : AllocIdSupplyReady m₅.machine.memory := hmach₅ ▸ hsup₄
  have hnext₅ : m₅.machine.memory.nextAllocId = 2 := by rw [hmach₅]; exact hnext₄
  have htm₅ : tm₅ = finalTree :=
    treeMap_eq_of_borrows_and_nextAllocId_two htree₅ rfl hfinal_a1 hnext₅
  subst htm₅
  -- Step 6 (`bb0` terminator): `SwitchInt(copy _5)` -> `bb1` emitting `MirObs.event 99`
  let s₆ := mkWitLocStateLM32 b 1 0 s₅.frame.locals s₅.memory.borrows 4
  have hs₆ : stepMirFn b s₅ = .emitStep (.event 99) s₆ := rfl
  have himm₅_5 : ∀ tf, m₅.stack.frames = #[tf] → IsImmediateFrameLocal tf 5 :=
    fun tf htf => immediate_of_nextAllocId_two htree₅.erased_rel hsup₅ hnext₅
      (List.Mem.head _) rfl htf 5 (Or.inr (by decide))
  have hcases : SwitchCasesFit u64Ty { branches := [(99, 1)], otherwise := 2 } := by
    intro v blk hmem
    rcases List.mem_singleton.mp hmem with ⟨rfl, rfl⟩
    exact ⟨by decide, fun hb => nomatch hb⟩
  have hwt₆ : WellTypedLM3_2TreeStateTerminator b m₅
      { statements := [
          mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
          mkStmt (.assign (local_ 3) (.ref (.mut false) (derefLocal 2))),
          mkStmt (.assign (derefLocal 3) (.use (.constant (constU64 99)))),
          mkStmt (.assign (local_ 4) (.ref .shared (derefLocal 3))),
          mkStmt (.assign (local_ 5) (.use (.copy (derefLocal 2))))],
        terminator := mkTerm (.switchInt (.copy (local_ 5)) { branches := [(99, 1)], otherwise := 2 }),
        isCleanup := false } :=
    .switchInt (.copy (local_ 5)) { branches := [(99, 1)], otherwise := 2 } u64Ty rfl
      (Or.inr (Or.inr ⟨.u64, rfl⟩))
      (fun tf htf => .copyLocal 5 u64Decl rfl (by decide) (himm₅_5 tf htf)) hcases
  obtain ⟨tm₆, hobs₆⟩ := step_mir_lm3_2_tree_state_simulation htree₅ hphase rfl
    (Or.inr ⟨rfl, rfl, hwt₆⟩) hsup₅
  obtain ⟨m₆, hm₆, htree₆⟩ := stepObsRelLM3_2Tree_of_anneal_emitEvent hobs₆ hs₆
  have hmach₆ : m₆.machine = m₅.machine :=
    step_terminator_switchInt_u64_machine_eq htree₅.erased_rel rfl rfl rfl
      (fun tf htf => .copyLocal 5 u64Decl rfl (by decide) (himm₅_5 tf htf)) hcases hm₆
  have hsup₆ : AllocIdSupplyReady m₆.machine.memory := hmach₆ ▸ hsup₅
  have hnext₆ : m₆.machine.memory.nextAllocId = 2 := by rw [hmach₆]; exact hnext₅
  have htm₆ : tm₆ = finalTree :=
    treeMap_eq_of_borrows_and_nextAllocId_two htree₆ rfl hfinal_a1 hnext₆
  subst htm₆
  -- Step 7 (`bb1` terminator): `Assert(const true == true)` -> `bb2`
  let s₇ := mkWitLocStateLM32 b 2 0 s₅.frame.locals s₅.memory.borrows 4
  have hs₇ : stepMirFn b s₆ = .step s₇ := rfl
  have hwt₇ : WellTypedLM3_2TreeStateTerminator b m₆
      { statements := [],
        terminator := mkTerm (.assert (.constant constBoolTrueLM32) true 2 .unreachable),
        isCleanup := false } :=
    .assert_ (.constant constBoolTrueLM32) boolTyLM32 true 2 rfl rfl
      (fun tf _ => constBoolTrue_wellTypedLM32 b tf rfl)
  obtain ⟨tm₇, hobs₇⟩ := step_mir_lm3_2_tree_state_simulation htree₆ hphase rfl
    (Or.inr ⟨rfl, rfl, hwt₇⟩) hsup₆
  obtain ⟨m₇, hm₇, htree₇⟩ := stepObsRelLM3_2Tree_of_anneal_step hobs₇ hs₇
  have hmach₇ : m₇.machine = m₆.machine :=
    step_terminator_assert_constTrue_machine_eq htree₆.erased_rel rfl rfl rfl rfl hm₇
  have hsup₇ : AllocIdSupplyReady m₇.machine.memory := hmach₇ ▸ hsup₆
  have hnext₇ : m₇.machine.memory.nextAllocId = 2 := by rw [hmach₇]; exact hnext₆
  have htm₇ : tm₇ = finalTree :=
    treeMap_eq_of_borrows_and_nextAllocId_two htree₇ rfl hfinal_a1 hnext₇
  subst htm₇
  -- Step 8 (`bb2[0]`): `_0 = move _4`
  let s₈ := mkWitLocStateLM32 b 2 1
    [.init (.ptr p3 8), .init (.scalar ⟨99, 8⟩), .init (.ptr p1 8), .init (.ptr p2 8),
     .uninit, .init (.scalar ⟨99, 8⟩)]
    s₅.memory.borrows 4
  have hs₈ : stepMirFn b s₇ = .step s₈ := rfl
  have himm₇_04 : ∀ tf, m₇.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 ∧ IsImmediateFrameLocal tf 4 :=
    fun tf htf =>
      ⟨immediate_of_nextAllocId_two htree₇.erased_rel hsup₇ hnext₇
        (List.Mem.head _) rfl htf 0 (Or.inr (by decide)),
       immediate_of_nextAllocId_two htree₇.erased_rel hsup₇ hnext₇
        (List.Mem.head _) rfl htf 4 (Or.inr (by decide))⟩
  have hwt₈ : WellTypedLM3_2TreeStateStmt b s₇ m₇ finalTree
      (mkStmt (.assign (local_ 0) (.use (.move (local_ 4))))) :=
    .safeRefUse 0 4 MirAst.Operand.move refU64Decl refU64Decl .not .not
      (.uint .u64) (.uint .u64) _ (Or.inr rfl) rfl rfl rfl rfl himm₇_04
  obtain ⟨tm₈, hobs₈⟩ := step_mir_lm3_2_tree_state_simulation htree₇ hphase rfl
    (Or.inl ⟨_, rfl, hwt₈⟩) hsup₇
  obtain ⟨m₈, hm₈, htree₈⟩ := stepObsRelLM3_2Tree_of_anneal_step hobs₈ hs₈
  have hmach₈ : m₈.machine = m₇.machine :=
    step_safeRef_use_machine_eq htree₇.erased_rel (Or.inr rfl) rfl rfl
      (dstDecl := refU64Decl) (srcDecl := refU64Decl) rfl rfl rfl rfl himm₇_04
      rfl (fun h => nomatch h) hm₈
  have hsup₈ : AllocIdSupplyReady m₈.machine.memory := hmach₈ ▸ hsup₇
  have hnext₈ : m₈.machine.memory.nextAllocId = 2 := by rw [hmach₈]; exact hnext₇
  have htm₈ : tm₈ = finalTree :=
    treeMap_eq_of_borrows_and_nextAllocId_two htree₈ rfl hfinal_a1 hnext₈
  subst htm₈
  -- Step 9 (`bb2` terminator): root-frame `return` of `_0 : &u64` (`p3`, tag `3`)
  have hs₉ : stepMirFn b s₈ = .retNormal (.ptr p3 8) s₈.memory := rfl
  have himm₈_0 : ∀ tf, m₈.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 :=
    fun tf htf => immediate_of_nextAllocId_two htree₈.erased_rel hsup₈ hnext₈
      (List.Mem.head _) rfl htf 0 (Or.inr (by decide))
  have hwt₉ : WellTypedLM3_2TreeStateTerminator b m₈
      { statements := [mkStmt (.assign (local_ 0) (.use (.move (local_ 4))))],
        terminator := mkTerm .return_,
        isCleanup := false } :=
    .return_ refU64Decl rfl rfl rfl (by decide) himm₈_0
  have hobs₉_uni := step_mir_lm3_2_tree_state_simulation htree₈ hphase rfl
    (Or.inr ⟨rfl, rfl, hwt₉⟩) hsup₈
  have hobs₉ := step_terminator_lm3_2_tree_state_simulation htree₈ hphase rfl rfl rfl hwt₉
  rw [hs₉] at hobs₉
  obtain ⟨decl0, imm0, hdecl0, hretOp, himmRel0, hm₉⟩ := hobs₉.retNormal_rel
  exact ⟨s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, decl0, imm0,
    hs₁, hm₁, htree₁, hs₂, hm₂, htree₂, hs₃, hm₃, htree₃, hs₄, hm₄, htree₄,
    hs₅, hm₅, htree₅, hs₆, hm₆, htree₆, rfl, hs₇, hm₇, htree₇, rfl,
    hs₈, hm₈, htree₈, hobs₉_uni, hs₉, hm₉, hdecl0, hretOp, himmRel0⟩

/-- 3-step `Runtime(PostCleanup)` MIR body building a 2-node Tree Borrows
parent-child hierarchy (`_2 = &mut _1; _3 = &mut *_2`) and then executing
`PlaceMention(*_4)` on `.uninit` `_4 : &u64` (`WellTypedLM3_2TreeStateStmt.placeMentionSafeRefDerefUninit`). -/
def lm32PlaceMentionSafeRefUninitBody : CapturedMir where
  defPath := "lm_3_2_witness::tree_place_mention_safe_ref_uninit_ub"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [refU64Decl, u64Decl, refMutU64Decl, refMutU64Decl, refU64Decl, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1))),
        mkStmt (.assign (local_ 3) (.ref (.mut false) (derefLocal 2))),
        mkStmt (.placeMention (derefLocal 4))],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_2_placeMention_safeRef_deref_uninit_tree_state_simulation_real_steps`**:
end-to-end 3-step execution of `lm32PlaceMentionSafeRefUninitBody` through
`step_mir_lm3_2_tree_state_simulation`: `_2 = &mut _1` -> `_3 = &mut *_2`
establishes `StateRelLM3_2Tree` with `[lm32TreeChild .reserved, lm32TreeRoot .reserved]`,
and `PlaceMention(*_4)` on `.uninit` `_4 : &u64` raises UB in lockstep across
BOTH machines (`WellTypedLM3_2TreeStateStmt.placeMentionSafeRefDerefUninit`). -/
theorem wit_lm3_2_placeMention_safeRef_deref_uninit_tree_state_simulation_real_steps :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState) (msg : String),
      let b := lm32PlaceMentionSafeRefUninitBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let s₀ := mkPre6AnnealLM32 b (.init (.scalar ⟨42, 8⟩))
      let m₀ := mkPre6MiriLM32 b refU64Ty lm32Mls42
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_2Tree b s₁ m₁ [lm32TreeRoot .reserved] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2Tree b s₂ m₂ [lm32TreeChild .reserved, lm32TreeRoot .reserved] ∧
      stepMirFn b s₂ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .error (.undefinedBehavior msg)) := by
  let b := lm32PlaceMentionSafeRefUninitBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hu64 : IsPrimScalarTy u64Ty := Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))
  obtain ⟨hrel₀, himm₀⟩ := mkPre6_stateRel_and_imm b refU64Decl u64Decl refMutU64Decl
    refMutU64Decl refU64Decl u64Decl rfl (.init (.scalar ⟨42, 8⟩)) lm32Mls42
    (fun _ h => nomatch h)
    (.immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩))
  have htree₀ : StateRelLM3_2Tree b (mkPre6AnnealLM32 b (.init (.scalar ⟨42, 8⟩)))
      (mkPre6MiriLM32 b refU64Ty lm32Mls42) [] := hrel₀.toLM3_1.toLM3_2.toTree
  let p1 : ProvenancePtr := { allocId := 1, offsetBytes := 0 }
  let p2 : ProvenancePtr := { allocId := 2, offsetBytes := 0 }
  let s₁ := mkWitLocStateLM32 b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr p1 8), .uninit, .uninit, .uninit]
    [(lm32TreeRoot .reserved).toBorrowEntry] 2
  have hs₁ : stepMirFn b (mkPre6AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ := rfl
  have hwt₁ : WellTypedLM3_2TreeStateStmt b (mkPre6AnnealLM32 b (.init (.scalar ⟨42, 8⟩)))
      (mkPre6MiriLM32 b refU64Ty lm32Mls42) []
      (mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1)))) :=
    .refAddrOf 2 1 (.mut false) refMutU64Decl u64Decl .mut (.uint .u64) _
      rfl rfl rfl hu64 (by decide) (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩)
  obtain ⟨tm₁, hobs₁⟩ := step_mir_lm3_2_tree_state_simulation htree₀ hphase rfl
    (Or.inl ⟨_, rfl, hwt₁⟩) AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, htree₁⟩ := stepObsRelLM3_2Tree_of_anneal_step hobs₁ hs₁
  obtain ⟨hsup₁, hnext₁⟩ := step_ref_supply_two hrel₀ rfl rfl
    (dstDecl := refMutU64Decl) (targetDecl := u64Decl) rfl rfl hu64 (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) rfl hm₁
  have htm₁ : tm₁ = [lm32TreeRoot .reserved] :=
    treeMap_eq_of_borrows_and_nextAllocId_two htree₁ rfl
      (by intro _ he; cases he with | head _ => rfl | tail _ h => cases h) hnext₁
  subst htm₁
  let s₂ := mkWitLocStateLM32 b 0 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.ptr p1 8), .init (.ptr p2 8), .uninit, .uninit]
    [(lm32TreeChild .reserved).toBorrowEntry, (lm32TreeRoot .reserved).toBorrowEntry] 3
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => immediate_of_nextAllocId_two htree₁.erased_rel hsup₁ hnext₁
      (List.Mem.head _) rfl htf k (Or.inr hne)
  have hlive₂ : ∀ (ptrVal : ProvenancePtr) (e : ReborrowMapEntry),
      get? s₁.frame.locals 2 = some (.init (.ptr ptrVal 8)) →
      e ∈ [lm32TreeRoot .reserved] → e.tag = ptrVal.tag →
      get? s₁.frame.locals e.localIdx ≠ some .dead ∧
      get? s₁.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
      ¬(e.perm = .frozen ∧ BorrowKind.mut false ≠ .shared) ∧
      (∀ tgtDecl, get? b.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = .uint .u64) := by
    intro ptrVal e hp he _
    rcases ptrVal_of_some_initLM32 hp with rfl
    cases he with
    | tail _ h => cases h
    | head _ =>
      exact ⟨(fun h => nomatch h), (fun h => nomatch h), rfl, (fun h => nomatch h),
        (fun ⟨h, _⟩ => nomatch h), (fun d hd => by injection hd with hd'; subst hd'; rfl)⟩
  have hwt₂ : WellTypedLM3_2TreeStateStmt b s₁ m₁ [lm32TreeRoot .reserved]
      (mkStmt (.assign (local_ 3) (.ref (.mut false) (derefLocal 2)))) :=
    .reborrowSafeRef 3 2 (.mut false) refMutU64Decl refMutU64Decl .mut .mut
      (.uint .u64) (.uint .u64) _ rfl rfl rfl rfl hu64
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩) hlive₂
      (fun _ _ _ he _ => by cases he with | head _ => rfl | tail _ h => cases h)
  obtain ⟨tm₂, hobs₂⟩ := step_mir_lm3_2_tree_state_simulation htree₁ hphase rfl
    (Or.inl ⟨_, rfl, hwt₂⟩) hsup₁
  obtain ⟨m₂, hm₂, htree₂⟩ := stepObsRelLM3_2Tree_of_anneal_step hobs₂ hs₂
  have hflat₂ := evalRvalue_reborrow_safeRef_simulation htree₁.erased_rel hphase
    (dstIdx := 3) (refIdx := 2) (bk := .mut false) rfl rfl rfl rfl rfl rfl hu64
    (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
    (fun ptrVal e' hget he' htag' => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'; exact hlive₂ ptrVal e hget he htag')
  obtain ⟨_, m₂', _, _, hm₂', _, hmach₂', _⟩ :=
    hflat₂.2 p1 (lm32TreeRoot .reserved).toAllocMapEntry rfl (List.Mem.head _) rfl (fun h => nomatch h)
  have hmach₂ : m₂.machine = m₁.machine := (by have h := hm₂'.symm.trans hm₂; injection h : m₂' = m₂) ▸ hmach₂'
  have hsup₂ : AllocIdSupplyReady m₂.machine.memory := hmach₂ ▸ hsup₁
  have hnext₂ : m₂.machine.memory.nextAllocId = 2 := by rw [hmach₂]; exact hnext₁
  have htm₂ : tm₂ = [lm32TreeChild .reserved, lm32TreeRoot .reserved] :=
    treeMap_eq_of_borrows_and_nextAllocId_two htree₂ rfl
      (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> rfl) hnext₂
  subst htm₂
  have himm₂_4 : ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf 4 :=
    fun tf htf => immediate_of_nextAllocId_two htree₂.erased_rel hsup₂ hnext₂
      (List.Mem.head _) rfl htf 4 (Or.inr (by decide))
  have hwt₃ : WellTypedLM3_2TreeStateStmt b s₂ m₂
      [lm32TreeChild .reserved, lm32TreeRoot .reserved]
      (mkStmt (.placeMention (derefLocal 4))) :=
    .placeMentionSafeRefDerefUninit 4 refU64Decl .not (.uint .u64) _
      rfl rfl hu64 himm₂_4 rfl
  obtain ⟨_, hobs₃⟩ := step_mir_lm3_2_tree_state_simulation htree₂ hphase rfl
    (Or.inl ⟨_, rfl, hwt₃⟩) hsup₂
  have hs₃ : stepMirFn b s₂ = .fail .ub := rfl
  obtain ⟨msg, hm₃⟩ := (StepObsRelLM3_2Tree.ub_iff hobs₃).mp hs₃
  exact ⟨s₁, s₂, m₁, m₂,
    (Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m₂).1,
    msg, hs₁, hm₁, htree₁, hs₂, hm₂, htree₂, hs₃, Prod.ext rfl hm₃⟩

end LeanMiriSpec.Correspondence.Witness

