/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.RefLM3_2

/-!
# `LM-3.2`: Safe References, Reborrows & Validity

Correspondence results between Anneal's `Trusted.Rustc.V2026_06_01.MirSemantics`
and `lean-miri` for safe references (`&T` / `&mut T`), stated over the
reference-aware relations `StateRelLM3_2` and `StepRelLM3_2` (`RefLM3_2`).

1. **`_d = &_t` / `_d = &mut _t` (`evalRvalue_ref_simulation`)**: real-step
   lockstep simulation of `Rvalue.Ref` on a live immediate primitive-scalar
   local under `Miri.Interpreter.Step.step` (`annealStepHooks`) and
   `stepMirFn`, promoting `_t` into a fresh stack allocation through
   `forceAllocation` (`.immediate -> .indirect`) and extending `allocMap` by the
   new reference's root borrow; undefined behavior in both machines on a dead
   `_t`.
2. **`_d = &*_p` / `_d = &mut *_p` (`evalRvalue_reborrow_simulation`)**:
   real-step correspondence of reborrowing through an offset-`0` raw pointer:
   undefined behavior in Anneal's `stepMirFn` exactly when `lean-miri`'s
   `Miri.Interpreter.Step.step` reports it, and otherwise both machines write
   a reference to the same stack allocation into `_d`.
3. **`evalRvalue_reborrow_dangling_divergence`**: the genuine divergence on a
   dangling pointee: Anneal steps (deferring the undefined behavior to the
   first use of the reference), while the reference that `lean-miri` writes
   fails the validity visitor's dereferenceability check and the eager
   safe-reference dereference check.
4. **`evalRvalue_reborrow_perm_divergence`**: the genuine divergence on a
   parent borrow that forbids the reborrow (`.disabled`, or `.frozen` for a
   mutable reborrow): Anneal reports undefined behavior, while `lean-miri`,
   whose hooks perform no Tree Borrows retag (`LM-3.3`), steps.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. `Rvalue.Ref` of a Local (`&_t`, `&mut _t`) -/

/-- The Tree Borrows permission Anneal's `evalRvalue (.ref bk ⟨targetIdx, .nil⟩)`
assigns to a fresh reference to a whole local: shared borrows get
`sharedBorrowPerm`, ordinary mutable borrows `.active`, and two-phase mutable
borrows `.reserved` (`Places.lean`, `Rvalue.ref`). -/
def refBorrowPerm (localDecls : List LocalDecl) (layouts : LayoutTable)
    (bk : BorrowKind) (targetIdx : Local) : TreeBorrowPerm :=
  match bk with
  | .shared => sharedBorrowPerm localDecls layouts ⟨targetIdx, .nil⟩
  | .mut false => .active
  | .mut true => .reserved

/-- The `allocMap` entry that records `&_target` / `&mut _target` at tag `tag`
as pointing into the `lean-miri` allocation `allocId`. -/
def refAllocMapEntry (localDecls : List LocalDecl) (layouts : LayoutTable)
    (bk : BorrowKind) (targetIdx : Local) (tag : Nat)
    (allocId : Miri.Memory.AllocId) : AllocMapEntry :=
  { tag := tag
    localIdx := targetIdx
    allocId := allocId
    perm := refBorrowPerm localDecls layouts bk targetIdx }

/-- Anneal's `evalRvalue (.ref bk ⟨targetIdx, .nil⟩)` on a live local pushes a
fresh root borrow entry with `tag := s.memory.nextTag` and returns
`.ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)`. -/
theorem evalRvalue_ref_live_eq
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (bk : BorrowKind) (targetIdx : Local) (slot : LocalSlot)
    (hslot : get? s.frame.locals targetIdx = some slot)
    (hlive : slot ≠ .dead) :
    let perm : TreeBorrowPerm := refBorrowPerm localDecls layouts bk targetIdx
    let entry : BorrowEntry :=
      { tag := s.memory.nextTag
        targetLocal := targetIdx
        targetProjection := .nil
        perm := perm }
    evalRvalue s.frame.locals (.ref bk ⟨targetIdx, .nil⟩) s.memory localDecls layouts =
      .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)
        s.frame.locals
        { s.memory with
          borrows := .cons entry s.memory.borrows
          nextTag := s.memory.nextTag + 1 } := by
  intro perm entry
  cases slot with
  | dead => exact absurd rfl hlive
  | uninit =>
    unfold evalRvalue
    dsimp only []
    rw [hslot]
    rcases bk with _ | ⟨_ | _⟩ <;> rfl
  | init v =>
    unfold evalRvalue
    dsimp only []
    rw [hslot]
    rcases bk with _ | ⟨_ | _⟩ <;> rfl

/-- Anneal's `evalRvalue (.ref bk ⟨targetIdx, .nil⟩)` on a `.dead` local fails
with `.ub`. -/
theorem evalRvalue_ref_dead_eq
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (bk : BorrowKind) (targetIdx : Local)
    (hdead : get? s.frame.locals targetIdx = some .dead) :
    evalRvalue s.frame.locals (.ref bk ⟨targetIdx, .nil⟩) s.memory localDecls layouts =
      .ub := by
  unfold evalRvalue
  dsimp only []
  rw [hdead]

/-- `evalRvalueIntoPlace` of `Rvalue.Ref` under `annealRvalueHooks`, once the
destination and source places are evaluated and `annealForceAllocation` moves
the source into memory: `MemPlace.toRef` turns the memory place into a pointer
immediate and `annealWriteImmediate` stores it in the destination. Retagging is
outside this fragment: `annealRvalueHooks.enforceValidity` is `true`, so the
`Ref` arm never calls `retagPtrValue`, and `withRetagMode` runs its action
unchanged. -/
theorem evalRvalueIntoPlace_ref_ok
    {ld : List LocalDecl} {ly : LayoutTable} {region : Miri.MIR.Region}
    {borrow : Miri.MIR.BorrowKind}
    {dst src : Miri.MIR.Place} {m m₁ m₂ m₃ : AnnealStepState}
    {dest srcPlace : Miri.Interpreter.RuntimePlace AnnealProv}
    {mp : Miri.Interpreter.MemPlace AnnealProv} {imm : Miri.Interpreter.Immediate AnnealProv}
    (hdst : annealEvalPlace ld ly dst m = .ok dest m₁)
    (hsrc : annealEvalPlace ld ly src m₁ = .ok srcPlace m₂)
    (hforce : annealForceAllocation ld ly srcPlace m₂ = .ok mp m₃)
    (href : mp.toRef annealTargetDataLayout = .ok imm) :
    Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks ld ly) ()
        (.Ref region borrow src) dst m =
      annealWriteImmediate imm dest m₃ := by
  unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
  simp only [bind, EStateM.bind, hdst, pure, EStateM.pure, hsrc, hforce, href,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- `evalRvalueIntoPlace` of `Rvalue.Ref` under `annealRvalueHooks` fails with
the error, and keeps the state, of a failing `annealForceAllocation`. -/
theorem evalRvalueIntoPlace_ref_force_error
    {ld : List LocalDecl} {ly : LayoutTable} {region : Miri.MIR.Region}
    {borrow : Miri.MIR.BorrowKind}
    {dst src : Miri.MIR.Place} {m m₁ m₂ m₃ : AnnealStepState}
    {dest srcPlace : Miri.Interpreter.RuntimePlace AnnealProv}
    {err : Miri.Interpreter.StepError}
    (hdst : annealEvalPlace ld ly dst m = .ok dest m₁)
    (hsrc : annealEvalPlace ld ly src m₁ = .ok srcPlace m₂)
    (hforce : annealForceAllocation ld ly srcPlace m₂ = .error err m₃) :
    Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks ld ly) ()
        (.Ref region borrow src) dst m =
      .error err m₃ := by
  unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
  simp only [bind, EStateM.bind, hdst, pure, hsrc, hforce]

/-- **`evalRvalue_ref_simulation` (`LM-3.2`)**: from any `StateRelLM3_2` state,
`_d = &_t` / `_d = &mut _t` (shared, mutable, or two-phase mutable) on a live
immediate local `_t` of primitive scalar type steps in lockstep under
`Miri.Interpreter.Step.step` (`annealStepHooks`) and `stepMirFn`.
`forceAllocation` promotes `_t` into the fresh stack allocation `nextAllocId`
(`.immediate -> .indirect`), Anneal pushes the fresh root borrow `nextTag`
with the borrow kind's permission (`refBorrowPerm`), `_d` holds the reference
in both machines (`LocalRelLM3_2.ref`), and `allocMap` extends by the new
entry while every existing invariant is preserved. A dead `_t` or `_d` is
undefined behavior in both machines. -/
theorem evalRvalue_ref_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {bk : BorrowKind} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : LocalDecl} {refMut : Mutability} {pointeeKind : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (hdst_ty : dstDecl.ty.kind = .ref refMut pointeeKind)
    (htgt_ty : IsPrimScalarTy targetDecl.ty)
    (hne : dstIdx ≠ targetIdx)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame targetIdx)
    (hsupply : AllocIdSupplyReady m.machine.memory) :
    StepRelLM3_2 body m
      (refAllocMapEntry body.localDecls body.layouts bk targetIdx s.memory.nextTag
        ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩ :: allocMap)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc,
    hdisj⟩ := id hstate
  obtain ⟨himm_dst, himm_tgt⟩ := himm tf hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hfra : FrameRelLM3_2 body m.machine allocMap s.frame tfa :=
    hfr.cache_local_layout hdecl_dst hlt_d
  have hstate_a : StateRelLM3_2 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_t, mls_t, hlt_af_t, hlt_t, hslot_t, hmls_t, hmls_t_eq, hloc_t⟩ :=
    hfra.lookup_local hdecl_tgt
  have hcache_t : ∀ l, (tfa.locals[targetIdx]'hlt_t).layout = some l →
      l = translateTy targetDecl.ty body.layouts := by
    rw [hmls_t_eq]; exact hloc_t.cachedLayout_eq
  have htgt_eval := annealEvalPlace_unprojected (m := { m with stack := ⟨#[tfa]⟩ }) rfl hlt_t
    hdecl_tgt hcache_t
  let tfb := cacheFrameLocalLayout tfa targetIdx hlt_t (translateTy targetDecl.ty body.layouts)
  have hstate_b : StateRelLM3_2 body s { m with stack := ⟨#[tfb]⟩ } allocMap :=
    hstate_a.cache_layout rfl hdecl_tgt hlt_t
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
          (.Ref .Erased (translateBorrowKind bk) ⟨targetIdx, #[]⟩) ⟨dstIdx, #[]⟩) m := rfl
  have hval_tb : (tfb.locals[targetIdx]'(by rw [cacheFrameLocalLayout_size]; exact hlt_t)).value =
      mls_t.value := by
    simp [tfb, cacheFrameLocalLayout, hmls_t_eq]
  rcases hloc_t with hloc_t | ⟨_, _, _, _, _, _, hty_ref, _⟩
  rotate_left
  · exfalso
    rcases htgt_ty with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] at hty_ref <;> cases hty_ref
  cases hloc_t with
  | rawPtr _ _ _ _ _ _ hty_raw _ =>
    exfalso
    rcases htgt_ty with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] at hty_raw <;> cases hty_raw
  | base hloc_t_b =>
    cases hloc_t_b with
    | indirect _ mp _ _ _ _ =>
      exact absurd rfl (himm_tgt.cache_layout hlt_d _ _ hmls_t mp)
    | dead cl _ =>
      have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt
        dsimp only
        rw [evalRvalue_ref_dead_eq s body.localDecls body.layouts bk targetIdx hslot_t]
      have hforce := annealForceAllocation_dead_eq (ld := body.localDecls) (ly := body.layouts)
        (m := { m with stack := ⟨#[tfb]⟩ }) rfl
        (by rw [cacheFrameLocalLayout_size]; exact hlt_t) hval_tb
        (translateTy targetDecl.ty body.layouts)
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "address of dead local")) := by
        rw [hm_stmt]
        unfold Miri.Interpreter.runRvalue
        rw [evalRvalueIntoPlace_ref_force_error (region := .Erased)
          (borrow := translateBorrowKind bk) hdst_eval htgt_eval hforce]
      rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      exact .ub _ _
    | immediate _ imm _ _ hval =>
      have hslot_ne_dead : slot_t ≠ .dead := by
        rcases hval with ⟨rfl, _⟩ | ⟨v, rfl, _⟩ <;> simp
      have hnot_tgt : ∀ e ∈ allocMap, e.localIdx ≠ targetIdx :=
        hstate.immediate_not_in_allocMap hframes hslot_t hslot_ne_dead himm_tgt
      have hlt_tb : targetIdx < tfb.locals.size := by
        rw [cacheFrameLocalLayout_size]; exact hlt_t
      have hlay_tb : (tfb.locals[targetIdx]'hlt_tb).layout =
          some (translateTy targetDecl.ty body.layouts) := by
        simp [tfb, cacheFrameLocalLayout]
      obtain ⟨hsized, allocation, htry⟩ := htgt_ty.layout_ok (layouts := body.layouts)
      obtain ⟨hsz_eq0, hmut0, halign_pow0, huninit0⟩ := freshStackAlloc_spec htry
      obtain ⟨halign0, hshape0⟩ :=
        StackScalarAllocShape.of_tryNew (none : Option Miri.TreeBorrows.BorrowTree) htry
      obtain ⟨mem', hres⟩ := hsupply.reserve_eq
      let freshId : Miri.Memory.AllocId := ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩
      have hfresh_mem' : mem'.live.any (fun x => x.1 == freshId) = false := by
        have hf := (reserveAllocId_ok_live hres).2
        rw [← (reserveAllocId_ok_live hres).1] at hf
        exact hf
      have hslot_t_sc : ∀ v, slot_t = .init v → ∃ sc, v = .scalar sc := by
        intro v hv
        rcases hval with ⟨h, _⟩ | ⟨v', hv', himmRel⟩
        · rw [h] at hv; cases hv
        · rw [hv'] at hv
          injection hv with hveq
          subst hveq
          obtain ⟨sc, _, rfl, -⟩ := himmRel.of_primitive_scalar htgt_ty
          exact ⟨sc, rfl⟩
      obtain ⟨alloc', hfill, halign_alloc', hshape_alloc', hnew_tgt⟩ :
          ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
            ((imm = .uninit ∧ alloc' = allocation.withExtra none) ∨
              ∃ sc, imm = .scalar sc ∧
                Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                  (Miri.Memory.allocRange Miri.ABI.Size.ZERO sc.size) sc
                  (allocation.withExtra none) = .ok () alloc') ∧
            alloc'.align = (translateTy targetDecl.ty body.layouts).layout.align.abi ∧
            StackScalarAllocShape (translateTy targetDecl.ty body.layouts).layout.size alloc' ∧
            LocalRelLM3_1 (stackAllocMachine m.machine mem' freshId alloc') allocMap
              targetDecl body.layouts slot_t
              { tfb.locals[targetIdx]'hlt_tb with
                value := .live (.indirect (stackAllocPlace freshId)) } := by
        have hlay_c : ∀ l ∈ (tfb.locals[targetIdx]'hlt_tb).layout,
            l = translateTy targetDecl.ty body.layouts := by
          rw [hlay_tb]; intro l hl; exact (Option.some.inj hl).symm
        have hnot_arr : ∀ elemKind count, targetDecl.ty.kind ≠ .array elemKind count := by
          intro elemKind count hk
          rcases htgt_ty with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] at hk <;> cases hk
        rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
        · refine ⟨allocation.withExtra none, Or.inl ⟨rfl, rfl⟩, halign0, hshape0,
            .base (.indirect .uninit (stackAllocPlace freshId) _ hlay_c (by simp) ?_)⟩
          exact stackAlloc_memPlaceRel hmut0 halign_pow0 hsz_eq0
            (fun _ hnz => huninit0 hnz)
            (fun _ hv => nomatch hv)
            (fun _ hv => nomatch hv)
            (fun elemKind count _ hk _ => absurd hk (hnot_arr elemKind count))
        · obtain ⟨sc, msc, rfl, rfl, hrel, hsz, hbool, hchar⟩ :=
            himmRel.of_primitive_scalar htgt_ty
          have hshape0' :
              StackScalarAllocShape (translateSizeBytes sc.sizeBytes)
                (allocation.withExtra none) :=
            hsz ▸ hshape0
          have htry' : Miri.Memory.Allocation.tryNew (translateSizeBytes sc.sizeBytes)
              (translateTy targetDecl.ty body.layouts).layout.align.abi .Uninit
              annealZeroedStorage = .ok allocation := hsz ▸ htry
          obtain ⟨alloc'', hw'', hsize'', hmut'', hinit'', hread''⟩ :=
            freshStackAlloc_writeScalar_readScalar hrel htry'
          obtain ⟨alloc₃, hw₃, halign₃, hshape₃, -⟩ :=
            StackScalarAllocShape.writeScalar_readScalar hrel hshape0'
          have halloc_eq : alloc₃ = alloc'' := by
            have h := hw₃.symm.trans hw''
            injection h
          subst halloc_eq
          refine ⟨alloc₃, Or.inr ⟨_, rfl, hw₃⟩, halign₃.trans halign0, hsz.symm ▸ hshape₃,
            .base (.indirect (.init (.scalar sc)) (stackAllocPlace freshId) _ hlay_c (by simp) ?_)⟩
          apply stackAlloc_memPlaceRel hmut'' halign_pow0 (by rw [hsize'', hsz])
          · intro h; cases h
          · intro _ _ _; rw [hsz]; exact hinit''
          · intro sc₂ hv
            injection hv with hv
            injection hv with hv
            subst hv
            exact ⟨hsz, hbool, hchar, msc, hrel, by rw [hsz]; exact hread''⟩
          · intro elemKind count _ hk _
            exact absurd hk (hnot_arr elemKind count)
      have hforce₀ := forceAllocation_promote_eq (m := { m with stack := ⟨#[tfb]⟩ }) rfl hdecl_tgt
        hlt_tb hlay_tb hval_tb hsized htry hres hfill
      obtain ⟨hlive_sub, hfreshne, hbase_sub⟩ :=
        stackAllocMachine_live_base (mach := m.machine) alloc' hres
      obtain ⟨tfb', hframes_b, -, -, hfrb, -, -, -, -, -, -, hdisj_b⟩ := hstate_b
      injection hframes_b with hfb₁
      injection hfb₁ with hfb₂
      subst hfb₂
      have hfrc₀ := (hfrb.of_live_base hlive_sub hbase_sub).update_local hdecl_tgt slot_t
        (.live (.indirect (stackAllocPlace freshId))) (.lm3_1 hnew_tgt)
      have hset_self : s.frame.locals.set targetIdx slot_t = s.frame.locals := by
        obtain ⟨_, hget⟩ := List.getElem_of_getElem? hslot_t
        rw [← hget, List.set_getElem_self]
      rw [hset_self] at hfrc₀
      have hdisj_c₀ : MemoryAllocDisjoint
          { tfb with
            locals := tfb.locals.set targetIdx
              { tfb.locals[targetIdx]'hlt_tb with
                value := .live (.indirect (stackAllocPlace freshId)) } hlt_tb } := by
        intro i j mp_i mp_j lay_i lay_j hij hi hj
        dsimp only at hi hj
        rw [Array.getElem?_set] at hi hj
        by_cases hi_idx : targetIdx = i
        · subst hi_idx
          have hj_idx : targetIdx ≠ j := hij
          simp only [hj_idx, ↓reduceIte] at hj
          simp only [↓reduceIte] at hi
          obtain ⟨a, la, ha, hla⟩ := hfrb.indirect_allocId hj
          injection hi with hi
          injection hi with hv _
          injection hv with hv
          injection hv with hv
          subst hv
          rw [ha]
          simp only [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
            Option.some.injEq]
          exact fun h => hfreshne a la hla h.symm
        · simp only [hi_idx, ↓reduceIte] at hi
          by_cases hj_idx : targetIdx = j
          · subst hj_idx
            simp only [↓reduceIte] at hj
            obtain ⟨a, la, ha, hla⟩ := hfrb.indirect_allocId hi
            injection hj with hj
            injection hj with hv _
            injection hv with hv
            injection hv with hv
            subst hv
            rw [ha]
            simp only [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
              Option.some.injEq]
            exact hfreshne a la hla
          · simp only [hj_idx, ↓reduceIte] at hj
            exact hdisj_b i j mp_i mp_j lay_i lay_j hij hi hj
      have hforce : annealForceAllocation body.localDecls body.layouts
          ⟨.local 0 targetIdx none tfa.localsIdentity, translateTy targetDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } =
          .ok (stackAllocPlace freshId)
            { stack := ⟨#[{ tfb with
                locals := tfb.locals.set targetIdx
                  { tfb.locals[targetIdx]'hlt_tb with
                    value := .live (.indirect (stackAllocPlace freshId)) } hlt_tb }]⟩
              machine := stackAllocMachine m.machine mem' freshId alloc' } := by
        unfold annealForceAllocation
        erw [hforce₀]
      have hrv := evalRvalueIntoPlace_ref_ok (region := .Erased)
        (borrow := translateBorrowKind bk) hdst_eval htgt_eval hforce
        (stackAllocPlace_toRef freshId)
      have hdc_eq₀ : ({ tfb with
          locals := tfb.locals.set targetIdx
            { tfb.locals[targetIdx]'hlt_tb with
              value := .live (.indirect (stackAllocPlace freshId)) }
            hlt_tb } :
          Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit).locals[dstIdx]? =
          some { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } := by
        simp only [tfb, tfa, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ (Ne.symm hne), Array.getElem?_set_ne _ (Ne.symm hne),
          Array.getElem?_set_self, hmls_d_eq]
      have htgt_c : ({ tfb with
          locals := tfb.locals.set targetIdx
            { tfb.locals[targetIdx]'hlt_tb with
              value := .live (.indirect (stackAllocPlace freshId)) }
            hlt_tb } :
          Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit).locals[targetIdx]? =
          some ⟨.live (.indirect (stackAllocPlace freshId)),
            some (translateTy targetDecl.ty body.layouts)⟩ := by
        simp only [Array.getElem?_set_self]
        rw [← hlay_tb]
      have hother_c : ∀ k, k ≠ dstIdx → k ≠ targetIdx →
          ({ tfb with
            locals := tfb.locals.set targetIdx
              { tfb.locals[targetIdx]'hlt_tb with
                value := .live (.indirect (stackAllocPlace freshId)) }
              hlt_tb } :
            Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit).locals[k]? =
          tf.locals[k]? := by
        intro k hkd hkt
        simp only [tfb, tfa, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ (Ne.symm hkt), Array.getElem?_set_ne _ (Ne.symm hkt),
          Array.getElem?_set_ne _ (Ne.symm hkd)]
      generalize htfc : ({ tfb with
          locals := tfb.locals.set targetIdx
            { tfb.locals[targetIdx]'hlt_tb with
              value := .live (.indirect (stackAllocPlace freshId)) }
            hlt_tb } : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) = tfc
        at hrv hfrc₀ hdisj_c₀ hdc_eq₀ htgt_c hother_c
      generalize hmachc : stackAllocMachine m.machine mem' freshId alloc' = machc at hrv hfrc₀
      have hdc_eq := hdc_eq₀
      obtain ⟨hlt_dc, -⟩ := Array.getElem?_eq_some_iff.mp hdc_eq
      -- Helper handling both immediate and existing-reference `_d` when `_d` is live.
      have hlive_dst_step :
          ∀ oldImm, mls_d.value = .live (.immediate oldImm) → slot_d ≠ .dead →
            StepRelLM3_2 body m
              (refAllocMapEntry body.localDecls body.layouts bk targetIdx
                s.memory.nextTag freshId :: allocMap)
              (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩
                body.localDecls body.layouts)
              (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
        intro oldImm hmls_d_imm hslot_d_ne
        have hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx :=
          hstate.immediate_not_in_allocMap hframes hslot_d hslot_d_ne himm_dst
        have hdc_imm : { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } =
            ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ := by
          rcases mls_d with ⟨mv, _⟩
          dsimp only at hmls_d_imm
          subst hmls_d_imm
          rfl
        rw [hdc_imm] at hdc_eq
        have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_eq
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
          rw [hm_stmt]
          unfold Miri.Interpreter.runRvalue
          rw [hrv, hw]
        have hloc_c : tfc.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hfrc₀.location_eq
        rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
          hloc_c]
        let newEntry := refAllocMapEntry body.localDecls body.layouts bk targetIdx
          s.memory.nextTag freshId
        have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩
            body.localDecls body.layouts =
            MirStepNode.step
              (advanceStmt s
                (s.frame.locals.set dstIdx
                  (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)))
                { s.memory with
                  borrows := newEntry.toBorrowEntry :: s.memory.borrows
                  nextTag := s.memory.nextTag + 1 }) := by
          unfold evalStmt
          dsimp only
          rw [evalRvalue_ref_live_eq s body.localDecls body.layouts bk targetIdx slot_t
            hslot_t hslot_ne_dead]
          dsimp only
          rw [hslot_d]
          have hbeq : Nat.beq targetIdx dstIdx = false := by
            cases h : Nat.beq targetIdx dstIdx
            · rfl
            · exact absurd (Nat.eq_of_beq_eq_true h).symm hne
          have hinv_tail := invalidateConflictingBorrows_eq_of_not_mem hbor dstIdx none hnot_dst
          cases slot_d with
          | dead => exact absurd rfl hslot_d_ne
          | uninit =>
            simp only [set?_eq_some_set hlt_af_d, hprot, invalidateConflictingBorrows_cons,
              updateBorrowPerm, hbeq, newEntry, refAllocMapEntry,
              AllocMapEntry.toBorrowEntry, hinv_tail]
          | init v =>
            simp only [set?_eq_some_set hlt_af_d, hprot, invalidateConflictingBorrows_cons,
              updateBorrowPerm, hbeq, newEntry, refAllocMapEntry,
              AllocMapEntry.toBorrowEntry, hinv_tail]
        rw [ha]
        apply StepRelLM3_2.step
        have hretCont_c : tfc.returnContinuation = .stop false := by
          rw [← htfc]; exact hretCont
        have hretPlace_c : ∃ retLay,
            tfc.returnPlace = .frameLocal 0 0 none retLay tfc.localsIdentity := by
          rw [← htfc]; exact hretPlace
        have hptr := PtrRel.of_stackAllocPlace
          (allocMap := newEntry :: allocMap) (e := newEntry)
          (List.Mem.head allocMap) hsupply.below_2pow32
        have hdc' : tfc.locals[dstIdx]'hlt_dc =
            ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ := by
          have h := Array.getElem?_eq_getElem hlt_dc
          rw [hdc_eq] at h
          exact (Option.some.inj h).symm
        have hnew : LocalRelLM3_2 machc (newEntry :: allocMap) dstDecl body.layouts
            (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
            { tfc.locals[dstIdx]'hlt_dc with
              value := .live (.immediate (.scalar
                (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                  ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr freshId),
                    .concrete freshId Miri.Memory.BorTag.one⟩))) } := by
          rw [hdc']
          exact .ref _ _ _ refMut pointeeKind (fun l hl => (Option.some.inj hl).symm)
            hdst_ty hptr
        have hfrd := (hfrc₀.mono_cons newEntry).update_local hdecl_dst _ _ hnew
        have hnodup_new : ((newEntry :: allocMap).map AllocMapEntry.tag).Nodup := by
          simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, halloc.tags_nodup⟩
          intro hmem
          obtain ⟨e, he, htag_eq⟩ := List.mem_map.mp hmem
          have hlt_tag := (halloc.borrow_sync e he).1
          dsimp only [newEntry, refAllocMapEntry] at htag_eq
          omega
        have hne_fresh : ∀ e ∈ allocMap, e.allocId ≠ freshId := by
          intro e he heq
          have hlt_id := (halloc.base_addr_valid e he).2.1
          rw [heq] at hlt_id
          exact Nat.lt_irrefl _ hlt_id
        refine .mk _ rfl hretCont_c hretPlace_c hfrd.advance hcal hstack hprot hcaller
          (by simp [advanceStmt, hbor, newEntry]) ?_ ?_
        · refine ⟨hnodup_new, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro e₁ h₁ e₂ h₂ hloc_eq
            rcases List.mem_cons.mp h₁ with rfl | hm₁ <;>
              rcases List.mem_cons.mp h₂ with rfl | hm₂
            · rfl
            · exact absurd hloc_eq.symm (hnot_tgt e₂ hm₂)
            · exact absurd hloc_eq (hnot_tgt e₁ hm₁)
            · exact halloc.local_to_alloc_unique e₁ hm₁ e₂ hm₂ hloc_eq
          · intro e₁ h₁ e₂ h₂ hid_eq
            rcases List.mem_cons.mp h₁ with rfl | hm₁ <;>
              rcases List.mem_cons.mp h₂ with rfl | hm₂
            · rfl
            · exact absurd hid_eq.symm (hne_fresh e₂ hm₂)
            · exact absurd hid_eq (hne_fresh e₁ hm₁)
            · exact halloc.alloc_to_local_injective e₁ hm₁ e₂ hm₂ hid_eq
          · intro e he
            rcases List.mem_cons.mp he with rfl | hm
            · exact ⟨targetDecl, hdecl_tgt, htgt_ty⟩
            · exact halloc.target_decl e hm
          · have hnext_lt : m.machine.memory.nextAllocId.toNat < machc.memory.nextAllocId.toNat := by
              rw [← hmachc]
              dsimp only [stackAllocMachine]
              exact nextAllocId_lt_after_reserve hres hsupply.below_2pow32
            intro e he
            rcases List.mem_cons.mp he with rfl | hm
            · refine ⟨hsupply.below_2pow32, hnext_lt, ?_⟩
              rw [← hmachc]
              exact lookupBaseAddr_stackAllocMachine_self _ _ _ _
            · obtain ⟨h32, hlt_old, hbase_old⟩ := halloc.base_addr_valid e hm
              refine ⟨h32, Nat.lt_trans hlt_old hnext_lt, ?_⟩
              rw [← hmachc, lookupBaseAddr_stackAllocMachine_ne _ _ _ (hne_fresh e hm)]
              exact hbase_old
          · intro e he
            have hlook_all := lookupBorrow_map_toBorrowEntry_of_nodup hnodup_new he
            rcases List.mem_cons.mp he with rfl | hm
            · exact ⟨Nat.lt_succ_self _,
                by simpa [advanceStmt, hbor, AllocMapEntry.toBorrowEntry] using hlook_all⟩
            · exact ⟨Nat.lt_trans (halloc.borrow_sync e hm).1 (Nat.lt_succ_self _),
                by simpa [advanceStmt, hbor, AllocMapEntry.toBorrowEntry] using hlook_all⟩
          · intro e he la₁ la₂ hla₁ hla₂
            rw [← hmachc] at hla₁ hla₂
            rcases List.mem_cons.mp he with rfl | hm
            · have h1 := mem_push_fresh_eq mem'.live _ _ la₁ hfresh_mem' hla₁
              have h2 := mem_push_fresh_eq mem'.live _ _ la₂ hfresh_mem' hla₂
              exact h1.trans h2.symm
            · have hne_id := hne_fresh e hm
              have hlive_eq := (reserveAllocId_ok_live hres).1
              have hin1 : (e.allocId, la₁) ∈ m.machine.memory.live.toList := by
                simp only [stackAllocMachine, Array.toList_push, List.mem_append,
                  List.mem_singleton] at hla₁
                rcases hla₁ with h | h
                · rwa [hlive_eq] at h
                · exact absurd (Prod.mk.inj h).1 hne_id
              have hin2 : (e.allocId, la₂) ∈ m.machine.memory.live.toList := by
                simp only [stackAllocMachine, Array.toList_push, List.mem_append,
                  List.mem_singleton] at hla₂
                rcases hla₂ with h | h
                · rwa [hlive_eq] at h
                · exact absurd (Prod.mk.inj h).1 hne_id
              exact halloc.live_key_unique e hm la₁ la₂ hin1 hin2
          · intro topFrame htop e he
            injection htop with h₁
            injection h₁ with h₂
            subst h₂
            have hlive_eq := (reserveAllocId_ok_live hres).1
            rcases List.mem_cons.mp he with rfl | hm
            · have hslot_after :
                  get? (s.frame.locals.set dstIdx
                    (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)))
                    targetIdx = some slot_t := by
                rw [get?_eq_getElem?, List.getElem?_set_ne hne, ← get?_eq_getElem?, hslot_t]
              refine ⟨fun slot hslot _ => ?_, fun hdead => ?_⟩
              · dsimp only [advanceStmt, newEntry, refAllocMapEntry] at hslot
                rw [hslot_after] at hslot
                injection hslot with hseq
                subst hseq
                refine ⟨⟨some (translateTy targetDecl.ty body.layouts), ?_⟩, hslot_t_sc, ?_⟩
                · show (tfc.locals.set dstIdx _ hlt_dc)[targetIdx]? = _
                  rw [Array.getElem?_set_ne _ hne]
                  exact htgt_c
                · intro decl_t hdecl_t'
                  dsimp only [newEntry, refAllocMapEntry] at hdecl_t'
                  rw [hdecl_tgt] at hdecl_t'
                  injection hdecl_t' with hdeq
                  subst hdeq
                  refine ⟨⟨.stack, alloc'⟩, ?_, rfl, halign_alloc', hshape_alloc'⟩
                  show machc.memory.live.find? _ = _
                  rw [← hmachc]
                  exact find?_push_fresh mem'.live _ _ hfresh_mem'
              · exfalso
                dsimp only [advanceStmt, newEntry, refAllocMapEntry] at hdead
                rw [hslot_after] at hdead
                exact hslot_ne_dead (Option.some.inj hdead)
            · have hne_d : dstIdx ≠ e.localIdx := Ne.symm (hnot_dst e hm)
              have hne_t : e.localIdx ≠ targetIdx := hnot_tgt e hm
              have hne_id : e.allocId ≠ freshId := hne_fresh e hm
              obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync tf hframes e hm
              have hslot_after :
                  get? (advanceStmt s
                    (s.frame.locals.set dstIdx
                      (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)))
                    { s.memory with
                      borrows := newEntry.toBorrowEntry :: s.memory.borrows
                      nextTag := s.memory.nextTag + 1 }).frame.locals e.localIdx =
                  get? s.frame.locals e.localIdx := by
                dsimp only [advanceStmt]
                rw [get?_eq_getElem?, List.getElem?_set_ne hne_d, ← get?_eq_getElem?]
              have hfind_push :
                  machc.memory.live.find? (fun x => x.1 == e.allocId) =
                    m.machine.memory.live.find? (fun x => x.1 == e.allocId) := by
                rw [← hmachc]
                show (mem'.live.push (freshId, ⟨.stack, alloc'⟩)).find?
                  (fun x => x.1 == e.allocId) = _
                rw [Array.find?_push, hlive_eq]
                cases h : m.machine.memory.live.find? (fun x => x.1 == e.allocId) with
                | some v => rfl
                | none =>
                  dsimp only []
                  rw [beq_false_of_ne (Ne.symm hne_id)]
                  rfl
              refine ⟨fun slot hslot hne_dead => ?_, fun hdead => ?_⟩
              · rw [hslot_after] at hslot
                obtain ⟨⟨lay, hlay⟩, hsc, hshape⟩ := hlive_e slot hslot hne_dead
                refine ⟨⟨lay, ?_⟩, hsc, fun decl_e hdecl_e => ?_⟩
                · show (tfc.locals.set dstIdx _ hlt_dc)[e.localIdx]? = _
                  rw [Array.getElem?_set_ne _ hne_d, hother_c e.localIdx (Ne.symm hne_d) hne_t]
                  exact hlay
                · obtain ⟨la, hfind0, hkind0, halign0', hsh0⟩ := hshape decl_e hdecl_e
                  exact ⟨la, hfind_push.trans hfind0, hkind0, halign0', hsh0⟩
              · rw [hslot_after] at hdead
                exact hfind_push.trans (hdead_e hdead)
        · apply MemoryAllocDisjoint.mono_immediate hdisj_c₀
          intro k
          by_cases hk : k = dstIdx
          · subst hk
            right
            refine ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr freshId),
                  .concrete freshId Miri.Memory.BorTag.one⟩),
              some (translateTy dstDecl.ty body.layouts), ?_⟩
            show (tfc.locals.set k _ hlt_dc)[k]? = _
            rw [Array.getElem?_set_self, hdc']
          · left
            show (tfc.locals.set dstIdx _ hlt_dc)[k]? = _
            rw [Array.getElem?_set_ne _ (Ne.symm hk)]
      rcases hloc_d with hloc_d | ⟨p, mptr, _, _, _, _, _, _⟩
      rotate_left
      · exact hlive_dst_step _ rfl (by simp)
      cases hloc_d with
      | rawPtr _ _ _ _ _ _ hty_raw _ =>
        exfalso
        rw [hdst_ty] at hty_raw
        cases hty_raw
      | base hloc_d_b =>
        cases hloc_d_b with
        | indirect _ mp _ _ _ _ =>
          exact absurd rfl (himm_dst _ hmls_d mp)
        | dead _ _ =>
          have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_eq
          have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩
              body.localDecls body.layouts = MirStepNode.fail .ub := by
            unfold evalStmt
            dsimp only
            rw [evalRvalue_ref_live_eq s body.localDecls body.layouts bk targetIdx slot_t
              hslot_t hslot_ne_dead]
            dsimp only
            rw [hslot_d]
          have hm_err : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) ()
              (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩)
              m =
              (⟨⟨#[tfc]⟩, machc⟩, .error (.undefinedBehavior "write to dead local")) := by
            rw [hm_stmt]
            unfold Miri.Interpreter.runRvalue
            rw [hrv, annealWriteImmediate_dead (m := ⟨⟨#[tfc]⟩, machc⟩) rfl hget_dc]
          rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
            hm_err]
          exact .ub _ _
        | immediate _ oldImm _ _ hvald =>
          have hslot_d_ne : slot_d ≠ .dead := by
            rcases hvald with ⟨rfl, _⟩ | ⟨v, rfl, _⟩ <;> simp
          exact hlive_dst_step oldImm rfl hslot_d_ne

/-! ## 2. Reborrowing (`&*_p`, `&mut *_p`) -/

/-- A local of raw-pointer type related by `LocalRelLM3_2` is related by
`LocalRelLM3_1`: the reference case needs a reference type. -/
theorem LocalRelLM3_2.toLM3_1_of_rawPtr {mach : AnnealMachine}
    {allocMap : List AllocMapEntry} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hty : decl.ty.kind = .rawPtr mutability pointeeKind)
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls) :
    LocalRelLM3_1 mach allocMap decl layouts slot mls := by
  cases h with
  | lm3_1 h => exact h
  | ref _ _ _ _ _ _ hty' _ => rw [hty] at hty'; cases hty'

/-- Every immediate safe-reference local related by `LocalRelLM3_2` is dead,
uninitialized, an integer-valued reference, or a `PtrRel`-related reference. -/
theorem LocalRelLM3_2.ref_immediate_cases
    {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {refDecl : LocalDecl} {layouts : LayoutTable}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    {slot_p : LocalSlot}
    {mls_p : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hloc : LocalRelLM3_2 mach allocMap refDecl layouts slot_p mls_p)
    (hnot_ind : ∀ mp, mls_p.value ≠ .live (.indirect mp)) :
    (slot_p = .dead ∧ mls_p.value = .dead) ∨
    (slot_p = .uninit ∧ mls_p.value = .live (.immediate .uninit)) ∨
    (∃ sc msc, slot_p = .init (.scalar sc) ∧ sc.sizeBytes = 8 ∧ ScalarRel sc msc ∧
      mls_p.value = .live (.immediate (.scalar (.fromScalarInt msc)))) ∨
    (∃ ptrVal mptr, slot_p = .init (.ptr ptrVal 8) ∧ PtrRel allocMap ptrVal mptr ∧
      mls_p.value = .live (.immediate (.scalar
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))) := by
  cases hloc with
  | ref ptrVal mptr _ _ _ _ _ hptr =>
    exact Or.inr (Or.inr (Or.inr ⟨ptrVal, mptr, rfl, hptr, rfl⟩))
  | lm3_1 h =>
    cases h with
    | rawPtr _ _ _ _ _ _ hty' _ => rw [hty] at hty'; cases hty'
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (hnot_ind mp)
      | dead _ _ => exact Or.inl ⟨rfl, rfl⟩
      | immediate _ _ _ _ hv =>
        rcases hv with ⟨rfl, rfl⟩ | ⟨v, rfl, himm⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · cases himm with
          | unit hz =>
            exfalso
            simp only [translateTy, hty] at hz
            cases hz
          | scalarPair _ _ _ _ _ _ hk =>
            exfalso
            rcases hk with ⟨_, h⟩ | ⟨_, _, h⟩ <;> rw [hty] at h <;> cases h
          | scalar sc msc hrel hsz _ _ =>
            have hsz8 : sc.sizeBytes = 8 := by
              simp only [translateTy, hty, translateSizeBytes] at hsz
              have hb_eq : (8 : UInt64) = UInt64.ofNat sc.sizeBytes :=
                congrArg Miri.ABI.Size.bytes hsz
              have hcan := hrel.validBytes
              rcases hcan with h1 | h1 | h1 | h1 | h1 <;> rw [h1] at hb_eq ⊢ <;>
                first | rfl | cases hb_eq
            exact Or.inr (Or.inr (Or.inl ⟨sc, msc, rfl, hsz8, hrel, rfl⟩))

/-- **`evalRvalue_reborrow_simulation` (`LM-3.2`)**: from any `StateRelLM3_2`
state in which `_p : *(const|mut) T` (`T` primitive scalar) is immediate and
not integer-valued, and every pointer it may hold has offset `0` and a parent
borrow that permits the reborrow (not `.disabled`, and not `.frozen` for a
mutable reborrow), the reborrow `_d = &*_p` / `_d = &mut *_p` into an
immediate safe-reference local `_d`:

1. reports undefined behavior in Anneal's `stepMirFn` exactly when
   `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) does (a dead
   or uninitialized `_p`, or a dead `_d`); and
2. otherwise steps in both machines, Anneal writing the fresh child borrow
   `nextTag` at offset `0` into `_d` and `lean-miri` writing a reference to
   the same stack allocation `e.allocId` that `_p` points into.

Raw-pointer dereference performs no eager checks
(`PointerPlaceMachine.fromImmediate`), so the step succeeds even when the
pointee is dead; `evalRvalue_reborrow_dangling_divergence` shows that the
reference it creates then fails validity. -/
theorem evalRvalue_reborrow_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : LocalDecl}
    {bk : BorrowKind} {ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hno_int : ∀ sc, get? s.frame.locals ptrIdx ≠ some (.init (.scalar sc)))
    (hzero_perm : ∀ ptrVal e,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared)) :
    ((stepMirFn body s = MirStepNode.fail .ub) ↔
      ∃ m' msg,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg))) ∧
    (∀ ptrVal e,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? s.frame.locals dstIdx ≠ some .dead →
      (∃ s', stepMirFn body s = .step s' ∧
        get? s'.frame.locals dstIdx =
          some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
      ∃ m' tf' borTag,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        m'.stack.frames = #[tf'] ∧ m'.machine = m.machine ∧
        (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
          some (.live (.immediate (.scalar
            (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
                .concrete e.allocId borTag⟩))))) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, _, halloc, _⟩ := id hstate
  obtain ⟨himm_d, himm_p⟩ := himm tf hframes
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hfra := hstate_a.frame_rel_singleton rfl
  obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_pa, hmls_pa, hmls_pa_eq, hloc_p⟩ :=
    hfra.lookup_local hdecl_ptr
  have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
    hloc_p.cachedLayout_eq
  have himm_pa : ∀ mp, mls_p.value ≠ .live (.indirect mp) :=
    himm_p.cache_layout hlt_d _ mls_p hmls_pa
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
        (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
          (.Ref .Erased (translateBorrowKind bk) (translatePlace ⟨ptrIdx, .cons .deref .nil⟩))
          ⟨dstIdx, #[]⟩) m := rfl
  have hmain :
      (stepMirFn body s = MirStepNode.fail .ub ∧
        ∃ m' msg,
          Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
            (m', .error (.undefinedBehavior msg))) ∨
      (∃ ptrVal e,
        get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) ∧
        e ∈ allocMap ∧ e.tag = ptrVal.tag ∧
        get? s.frame.locals dstIdx ≠ some .dead ∧
        (∃ s', stepMirFn body s = .step s' ∧
          get? s'.frame.locals dstIdx =
            some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
        ∃ m' tf' borTag,
          Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
            (m', .ok true) ∧
          m'.stack.frames = #[tf'] ∧ m'.machine = m.machine ∧
          (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
            some (.live (.immediate (.scalar
              (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
                  .concrete e.allocId borTag⟩))))) := by
    rcases (hloc_p.toLM3_1_of_rawPtr hptr_ty).rawPtr_immediate_cases hptr_ty himm_pa with
      ⟨hsp_dead, hmp_dead⟩ | ⟨hsp_un, hmp_un⟩ |
      ⟨sc_p, _, hsp_sc, _, _, _⟩ | ⟨ptrVal, mptr, hsp_ptr, hptrRel, hmp_ptr⟩
    · left
      have ha : stepMirFn body s = MirStepNode.fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]
        unfold evalStmt evalRvalue; dsimp only []; rw [hslot_pa, hsp_dead]
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa = ⟨.dead, mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_dead; subst hmp_dead; rfl
      have hsrc_dead := annealEvalPlace_deref_dead (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[cacheFrameLocalLayout tfa ptrIdx hlt_pa
              (translateTy ptrDecl.ty body.layouts)]⟩ },
            .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        have hrv_err : Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooks body.localDecls body.layouts) ()
            (.Ref .Erased (translateBorrowKind bk) (translatePlace ⟨ptrIdx, .cons .deref .nil⟩))
            ⟨dstIdx, #[]⟩ m =
            .error (.undefinedBehavior "read of dead local")
              { m with stack := ⟨#[cacheFrameLocalLayout tfa ptrIdx hlt_pa
                  (translateTy ptrDecl.ty body.layouts)]⟩ } := by
          unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
          simp only [bind, EStateM.bind, pure, tfa, hdst_eval, hsrc_dead]
        rw [hrv_err]
      exact ⟨ha, _, _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq
        hbb hstmt hm_err⟩
    · left
      have ha : stepMirFn body s = MirStepNode.fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]
        unfold evalStmt evalRvalue; dsimp only []; rw [hslot_pa, hsp_un]
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa = ⟨.live (.immediate .uninit), mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_un; subst hmp_un; rfl
      let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
      have hder_un := annealDerefOperandToMemPlace_uninit (ly := body.layouts)
        hdecl_ptr hptr_ty hpk_prim (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
      have hsrc_un : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) { m with stack := ⟨#[tfa]⟩ } =
          .error (.undefinedBehavior "read of uninitialized local")
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hsrc_live, EStateM.bind_eq_error hder_un]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        have hrv_err : Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooks body.localDecls body.layouts) ()
            (.Ref .Erased (translateBorrowKind bk) (translatePlace ⟨ptrIdx, .cons .deref .nil⟩))
            ⟨dstIdx, #[]⟩ m =
            .error (.undefinedBehavior "read of uninitialized local")
              { m with stack := ⟨#[tfb]⟩ } := by
          unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
          simp only [bind, EStateM.bind, pure, tfa, hdst_eval, hsrc_un]
        rw [hrv_err]
      exact ⟨ha, _, _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq
        hbb hstmt hm_err⟩
    · exact absurd (hslot_pa.trans (congrArg some hsp_sc)) (hno_int sc_p)
    · have hsp_full : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) :=
        hslot_pa.trans (congrArg some hsp_ptr)
      obtain ⟨_, borTag, hprov_eq, _, _, hmptr_off, ⟨e, he, htag, rfl⟩⟩ := hptrRel
      obtain ⟨hoff0, hne_dis, hnot_fmut⟩ := hzero_perm ptrVal e hsp_full he htag
      have hlookup := (halloc.borrow_sync e he).2
      rw [htag] at hlookup
      have hrv_a_ok : ∃ mem₁, evalRvalue s.frame.locals
          (.ref bk ⟨ptrIdx, .cons .deref .nil⟩) s.memory body.localDecls body.layouts =
          .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals mem₁ ∧
          mem₁.activeProtectors = .nil := by
        unfold evalRvalue; dsimp only []
        rw [hsp_full]; dsimp only []; rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry]
        cases hp : e.perm <;> rcases hm : bk with _ | ⟨_ | _⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact absurd ⟨hp, by rw [hm]; exact fun h => BorrowKind.noConfusion h⟩ hnot_fmut
        · exact absurd ⟨hp, by rw [hm]; exact fun h => BorrowKind.noConfusion h⟩ hnot_fmut
        · exact absurd hp hne_dis
        · exact absurd hp hne_dis
        · exact absurd hp hne_dis
      obtain ⟨mem₁, hrv_a, hprot₁⟩ := hrv_a_ok
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
      let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
      obtain ⟨_, _, _, _, hpow_pk, _⟩ := hpk_prim.size_align_ok body.layouts
      obtain ⟨mismatch, hmis_any⟩ := annealOffsetMisalignment_ok_of_pow2 mptr.offset _ hpow_pk
      have hder_ptr := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty hpk_prim mptr hmis_any
        (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
      have hsrc_eval : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.memory ⟨mptr.withOptionalProvenance, .none, mismatch⟩,
              translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hsrc_live, EStateM.bind_eq_ok hder_ptr]; rfl
      have hmptr_eq : mptr =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId), .concrete e.allocId borTag⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only at hprov_eq hmptr_off; subst hprov_eq hmptr_off
        rw [hoff0]
        simp
      have href : (⟨mptr.withOptionalProvenance, .none, mismatch⟩ :
            Miri.Interpreter.MemPlace AnnealProv).toRef annealTargetDataLayout =
          .ok (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)) := by
        rw [hmptr_eq]; rfl
      have hrv := evalRvalueIntoPlace_ref_ok (region := .Erased)
        (borrow := translateBorrowKind bk) hdst_eval hsrc_eval
        (annealForceAllocation_memory_eq _ _ _ _ _) href
      have hstate_b := hstate_a.cache_layout rfl hdecl_ptr hlt_pa
      have hfrb := hstate_b.frame_rel_singleton rfl
      obtain ⟨slot_db, mls_db, _, hlt_db, hslot_db, hmls_db, _, hloc_db⟩ :=
        hfrb.lookup_local hdecl_dst
      have hsdb_eq : slot_db = slot_d := Option.some.inj (hslot_db.symm.trans hslot_d)
      subst hsdb_eq
      have himm_db : ∀ mp, mls_db.value ≠ .live (.indirect mp) :=
        ((himm_d.cache_layout hlt_d _).cache_layout hlt_pa _) mls_db hmls_db
      rcases hloc_db.ref_immediate_cases hdst_ty himm_db with
        ⟨hsd_dead, hmd_dead⟩ | ⟨hsd_un, hmd_un⟩ |
        ⟨_, msc_d, hsd_sc, _, _, hmd_sc⟩ | ⟨_, mptr_d, hsd_ptr, _, hmd_ptr⟩
      · left
        have ha : stepMirFn body s = MirStepNode.fail .ub := by
          rw [stepMirFn_eq_of_not_other body s hcal hphase]
          simp only [hbb, hstmt]
          unfold evalStmt; dsimp only []; rw [hrv_a]; dsimp only []; rw [hslot_d, hsd_dead]
        have hdb_dead : tfb.locals[dstIdx]? = some ⟨.dead, mls_db.layout⟩ := by
          rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmd_dead; subst hmd_dead; rfl
        have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_dead
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
              (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
            ({ m with stack := ⟨#[tfb]⟩ },
              .error (.undefinedBehavior "write to dead local")) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
          rw [hrv, annealWriteImmediate_dead (m := { m with stack := ⟨#[tfb]⟩ })
            (id0 := tf.localsIdentity) rfl hget_db]
        exact ⟨ha, _, _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq
          hbb hstmt hm_err⟩
      · right
        have hlive_d : get? s.frame.locals dstIdx ≠ some .dead := by
          rw [hslot_d, hsd_un]; simp
        have hset := set?_eq_some_set hlt_af_d
          (LocalSlot.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
        have hget_set : get? (s.frame.locals.set dstIdx
            (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) dstIdx =
            some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
          rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
        have ha_step : ∃ s', stepMirFn body s = .step s' ∧
            get? s'.frame.locals dstIdx =
              some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
          rw [stepMirFn_eq_of_not_other body s hcal hphase]
          simp only [hbb, hstmt]
          unfold evalStmt; dsimp only []; rw [hrv_a]; dsimp only []; rw [hslot_d, hsd_un]
          simp only [hset, hprot₁]; exact ⟨_, rfl, hget_set⟩
        have hdb_imm : tfb.locals[dstIdx]? = some ⟨.live (.immediate .uninit), mls_db.layout⟩ := by
          rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmd_un; subst hmd_un; rfl
        have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
        have hw := annealWriteImmediate_live
          (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
          (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
              (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
            ({ m with stack := ⟨#[{ tfb with
                locals := tfb.locals.set dstIdx
                  { tfb.locals[dstIdx]'hlt_db with
                    value := .live (.immediate (.scalar
                      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) }
                  hlt_db }]⟩ }, .ok ()) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
        refine ⟨ptrVal, e, hsp_full, he, htag, hlive_d, ha_step, _, _, borTag,
          miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
            hfrb.location_eq, rfl, rfl, ?_⟩
        rw [hmptr_eq]; simp [Array.getElem?_set_self]
      · right
        have hlive_d : get? s.frame.locals dstIdx ≠ some .dead := by
          rw [hslot_d, hsd_sc]; simp
        have hset := set?_eq_some_set hlt_af_d
          (LocalSlot.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
        have hget_set : get? (s.frame.locals.set dstIdx
            (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) dstIdx =
            some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
          rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
        have ha_step : ∃ s', stepMirFn body s = .step s' ∧
            get? s'.frame.locals dstIdx =
              some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
          rw [stepMirFn_eq_of_not_other body s hcal hphase]
          simp only [hbb, hstmt]
          unfold evalStmt; dsimp only []; rw [hrv_a]; dsimp only []; rw [hslot_d, hsd_sc]
          simp only [hset, hprot₁]; exact ⟨_, rfl, hget_set⟩
        have hdb_imm : tfb.locals[dstIdx]? =
            some ⟨.live (.immediate (.scalar (.fromScalarInt msc_d))), mls_db.layout⟩ := by
          rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmd_sc; subst hmd_sc; rfl
        have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
        have hw := annealWriteImmediate_live
          (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
          (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
              (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
            ({ m with stack := ⟨#[{ tfb with
                locals := tfb.locals.set dstIdx
                  { tfb.locals[dstIdx]'hlt_db with
                    value := .live (.immediate (.scalar
                      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) }
                  hlt_db }]⟩ }, .ok ()) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
        refine ⟨ptrVal, e, hsp_full, he, htag, hlive_d, ha_step, _, _, borTag,
          miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
            hfrb.location_eq, rfl, rfl, ?_⟩
        rw [hmptr_eq]; simp [Array.getElem?_set_self]
      · right
        have hlive_d : get? s.frame.locals dstIdx ≠ some .dead := by
          rw [hslot_d, hsd_ptr]; simp
        have hset := set?_eq_some_set hlt_af_d
          (LocalSlot.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
        have hget_set : get? (s.frame.locals.set dstIdx
            (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) dstIdx =
            some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
          rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
        have ha_step : ∃ s', stepMirFn body s = .step s' ∧
            get? s'.frame.locals dstIdx =
              some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
          rw [stepMirFn_eq_of_not_other body s hcal hphase]
          simp only [hbb, hstmt]
          unfold evalStmt; dsimp only []; rw [hrv_a]; dsimp only []; rw [hslot_d, hsd_ptr]
          simp only [hset, hprot₁]; exact ⟨_, rfl, hget_set⟩
        have hdb_imm : tfb.locals[dstIdx]? =
            some ⟨.live (.immediate (.scalar
              (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr_d))),
              mls_db.layout⟩ := by
          rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmd_ptr; subst hmd_ptr; rfl
        have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
        have hw := annealWriteImmediate_live
          (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
          (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
              (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
            ({ m with stack := ⟨#[{ tfb with
                locals := tfb.locals.set dstIdx
                  { tfb.locals[dstIdx]'hlt_db with
                    value := .live (.immediate (.scalar
                      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) }
                  hlt_db }]⟩ }, .ok ()) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
        refine ⟨ptrVal, e, hsp_full, he, htag, hlive_d, ha_step, _, _, borTag,
          miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
            hfrb.location_eq, rfl, rfl, ?_⟩
        rw [hmptr_eq]; simp [Array.getElem?_set_self]
  refine ⟨?_, ?_⟩
  · rcases hmain with ⟨ha_ub, hm_ub⟩ | ⟨_, _, _, _, _, _, ⟨_, ha_ok, _⟩, ⟨_, _, _, hm_ok, _, _⟩⟩
    · exact ⟨fun _ => hm_ub, fun _ => ha_ub⟩
    · refine ⟨fun h => ?_, fun ⟨_, _, h⟩ => ?_⟩
      · rw [ha_ok] at h; cases h
      · rw [hm_ok] at h; cases h
  · intro ptrVal e hsp he htag hlive
    rcases hmain with ⟨ha_ub, _⟩ | ⟨ptrVal', e', hsp', he', htag', _, ha_step, hm_step⟩
    · exfalso
      obtain ⟨_, hne_dis, hnot_fmut⟩ := hzero_perm ptrVal e hsp he htag
      have hlookup := (halloc.borrow_sync e he).2
      rw [htag] at hlookup
      have hrv_ok' : ∃ mem₁, evalRvalue s.frame.locals
          (.ref bk ⟨ptrIdx, .cons .deref .nil⟩) s.memory body.localDecls body.layouts =
          .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals mem₁ ∧
          mem₁.activeProtectors = .nil := by
        clear ha_ub
        unfold evalRvalue; dsimp only []
        rw [hsp]; dsimp only []; rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry]
        cases hp : e.perm <;> rcases hm : bk with _ | ⟨_ | _⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact absurd ⟨hp, by rw [hm]; exact fun h => BorrowKind.noConfusion h⟩ hnot_fmut
        · exact absurd ⟨hp, by rw [hm]; exact fun h => BorrowKind.noConfusion h⟩ hnot_fmut
        · exact absurd hp hne_dis
        · exact absurd hp hne_dis
        · exact absurd hp hne_dis
      obtain ⟨mem₁, hrv₁, hprot₁⟩ := hrv_ok'
      rw [stepMirFn_eq_of_not_other body s hcal hphase] at ha_ub
      simp only [hbb, hstmt] at ha_ub
      unfold evalStmt at ha_ub
      dsimp only [] at ha_ub
      rw [hrv₁] at ha_ub
      dsimp only [] at ha_ub
      rw [hslot_d] at ha_ub
      cases slot_d with
      | dead => exact hlive hslot_d
      | uninit => simp only [set?_eq_some_set hlt_af_d, hprot₁] at ha_ub; cases ha_ub
      | init _ => simp only [set?_eq_some_set hlt_af_d, hprot₁] at ha_ub; cases ha_ub
    · have hp_eq : ptrVal' = ptrVal := by
        have hv := Option.some.inj (hsp'.symm.trans hsp)
        injection hv with hv'
        injection hv'
      subst hp_eq
      have he_eq : e' = e :=
        mem_eq_of_map_nodup halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst he_eq
      exact ⟨ha_step, hm_step⟩

/-- **`evalRvalue_reborrow_dangling_divergence` (`LM-3.2`, genuine divergence)**:
when the raw pointer `_p` points into a local that `StorageDead` has already
killed (its `lean-miri` allocation is freed), the reborrow `_d = &*_p` /
`_d = &mut *_p` diverges between the two semantics:

1. Anneal's `stepMirFn` steps: `Rvalue.ref` of `*_p` consults only the parent
   borrow entry, which `StorageDead` does not remove, so Anneal creates a
   dangling reference (and reports undefined behavior only when it is used);
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) also takes
   the step (raw-pointer dereference performs no eager check), but the
   reference it writes is rejected by the validity visitor's
   dereferenceability leaf (`checkPointerAccess`, `annealValidityAccessCheck`)
   and by the eager safe-reference dereference check: `lean-miri`'s reference
   creation plus validity check (`writePlaceImmediate` → `validate`) is
   undefined behavior.

Both `trusted/lean` and `lean-miri/vendor` are fixed, so this is a real
semantic difference, not a modeling gap: Anneal defers dangling-reference UB to
the first use, while Miri reports it when the reference is created. -/
theorem evalRvalue_reborrow_dangling_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : LocalDecl}
    {bk : BorrowKind} {ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hno_int : ∀ sc, get? s.frame.locals ptrIdx ≠ some (.init (.scalar sc)))
    (hzero_perm : ∀ ptrVal e,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared))
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hdead_t : get? s.frame.locals e.localIdx = some .dead)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    {targetDecl : LocalDecl} (hdecl_t : get? body.localDecls e.localIdx = some targetDecl) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx =
        some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              .concrete e.allocId borTag⟩)))) ∧
      (∃ err, annealValidityAccessCheck m'.machine
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId), some (.concrete e.allocId borTag)⟩
        (translateTy targetDecl.ty body.layouts).layout.size = .error err) ∧
      annealSafeRefDerefCheck m'.machine
          (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              .concrete e.allocId borTag⟩))
          (translateTy targetDecl.ty body.layouts) =
        .error (.undefinedBehavior "dereferencing a dangling reference") := by
  obtain ⟨tf, hframes, _, _, _, _, _, _, _, _, halloc, _⟩ := id hstate
  have hsim := (evalRvalue_reborrow_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr
    hptr_ty hdst_ty hpk_prim himm hno_int hzero_perm).2 ptrVal e hslot_p he htag hdst_live
  obtain ⟨ha, m', tf', borTag, hstep, hframes', hmach, hval⟩ := hsim
  refine ⟨ha, m', tf', borTag, hstep, hframes', hval, ?_, ?_⟩ <;> rw [hmach]
  · obtain ⟨d, hd, hprim⟩ := halloc.target_decl e he
    rw [hdecl_t] at hd
    cases hd
    obtain ⟨hsize, hpos, hfit, _, _, _⟩ := hprim.size_align_ok body.layouts
    obtain ⟨hid, _, hbase⟩ := halloc.base_addr_valid e he
    have hfind := (halloc.local_alloc_sync tf hframes e he).2 hdead_t
    have hacc := (annealValidityAccessCheck_stack m.machine e.allocId borTag 0
      (translateTy targetDecl.ty body.layouts).layout.size hid (by decide) hbase hsize
      (by exact_mod_cast hpos) hfit).2.2 hfind
    have h0 : annealStackBaseAddr e.allocId + UInt64.ofNat 0 = annealStackBaseAddr e.allocId := by
      simp
    rw [h0] at hacc
    exact hacc
  · obtain ⟨d, hd, hprim⟩ := halloc.target_decl e he
    rw [hdecl_t] at hd
    cases hd
    obtain ⟨hsize, hpos, hfit, _, _, _⟩ := hprim.size_align_ok body.layouts
    obtain ⟨hid, _, hbase⟩ := halloc.base_addr_valid e he
    have hfind := (halloc.local_alloc_sync tf hframes e he).2 hdead_t
    have hck := annealSafeRefDerefCheck_dead_err (mach := m.machine) e.allocId borTag 0
      (translateTy targetDecl.ty body.layouts) hid (by decide) hbase hfind hsize
      (by exact_mod_cast hpos) hfit
    have h0 : annealStackBaseAddr e.allocId + UInt64.ofNat 0 = annealStackBaseAddr e.allocId := by
      simp
    rw [h0] at hck
    exact hck


/-- **`evalRvalue_reborrow_perm_divergence` (`LM-3.2`, genuine divergence)**:
in `StateRelLM3_2`-related states where `_p : *(const|mut) T` (`T` primitive
scalar) holds `.init (.ptr ptrVal 8)` (`e ∈ allocMap`, `e.tag = ptrVal.tag`),
`_d` is a live immediate safe-reference local, and the parent borrow forbids
the reborrow (`e.perm = .disabled`, or `e.perm = .frozen` for a mutable
reborrow), executing `_d = &*_p` / `_d = &mut *_p` diverges:

1. Anneal's `stepMirFn` rejects the reborrow with `MirStepNode.fail .ub`
   (`Places.lean`, `Rvalue.ref`); while
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) steps,
   writing a reference to the same stack allocation, because `annealRvalueHooks`
   performs no Tree Borrows retag (`enforceValidity` is `true`, so the `Ref` arm
   never calls `retagPtrValue`); the permission state machine is `LM-3.3`'s
   subject. -/
theorem evalRvalue_reborrow_perm_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : LocalDecl}
    {bk : BorrowKind} {ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy}
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .disabled ∨ (e.perm = .frozen ∧ bk ≠ .shared)) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
              .concrete e.allocId borTag⟩)))) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, halloc, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · have hlookup := (halloc.borrow_sync e he).2
    rw [htag] at hlookup
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue; dsimp only []
    rw [hslot_p]; dsimp only []; rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry]
    rcases hperm with hp | ⟨hp, hm⟩
    · rw [hp]
    · rw [hp]
      rcases bk with _ | _
      · exact absurd rfl hm
      · rfl
  · obtain ⟨himm_d, himm_p⟩ := himm tf hframes
    obtain ⟨slot_d, mls_d, _, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ :=
      hfr.lookup_local hdecl_dst
    have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
    have hfra := hstate_a.frame_rel_singleton rfl
    obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_pa, hmls_pa, hmls_pa_eq, hloc_p⟩ :=
      hfra.lookup_local hdecl_ptr
    have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
      hloc_p.cachedLayout_eq
    have himm_pa : ∀ mp, mls_p.value ≠ .live (.indirect mp) :=
      himm_p.cache_layout hlt_d _ mls_p hmls_pa
    have hsp_eq : slot_p = .init (.ptr ptrVal 8) := Option.some.inj (hslot_pa.symm.trans hslot_p)
    subst hsp_eq
    rcases (hloc_p.toLM3_1_of_rawPtr hptr_ty).rawPtr_immediate_cases hptr_ty himm_pa with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmp_ptr⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
      obtain ⟨_, borTag, hprov_eq, _, _, hmptr_off, ⟨e', he', htag', rfl⟩⟩ := hptrRel
      have he_eq : e' = e :=
        mem_eq_of_map_nodup halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst he_eq
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
      let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
      obtain ⟨_, _, _, _, hpow_pk, _⟩ := hpk_prim.size_align_ok body.layouts
      obtain ⟨mismatch, hmis_any⟩ := annealOffsetMisalignment_ok_of_pow2 mptr.offset _ hpow_pk
      have hder_ptr := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty hpk_prim mptr hmis_any
        (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
      have hsrc_eval : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.memory ⟨mptr.withOptionalProvenance, .none, mismatch⟩,
              translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hsrc_live, EStateM.bind_eq_ok hder_ptr]; rfl
      have hmptr_eq : mptr =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId + UInt64.ofNat ptrVal.offsetBytes),
            .concrete e'.allocId borTag⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only at hprov_eq hmptr_off; subst hprov_eq hmptr_off; rfl
      have href : (⟨mptr.withOptionalProvenance, .none, mismatch⟩ :
            Miri.Interpreter.MemPlace AnnealProv).toRef annealTargetDataLayout =
          .ok (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)) := by
        rw [hmptr_eq]; rfl
      have hrv := evalRvalueIntoPlace_ref_ok (region := .Erased)
        (borrow := translateBorrowKind bk) hdst_eval hsrc_eval
        (annealForceAllocation_memory_eq _ _ _ _ _) href
      have hstate_b := hstate_a.cache_layout rfl hdecl_ptr hlt_pa
      have hfrb := hstate_b.frame_rel_singleton rfl
      obtain ⟨slot_db, mls_db, _, hlt_db, hslot_db, hmls_db, _, hloc_db⟩ :=
        hfrb.lookup_local hdecl_dst
      have hsdb_eq : slot_db = slot_d := Option.some.inj (hslot_db.symm.trans hslot_d)
      subst hsdb_eq
      have himm_db : ∀ mp, mls_db.value ≠ .live (.indirect mp) :=
        ((himm_d.cache_layout hlt_d _).cache_layout hlt_pa _) mls_db hmls_db
      obtain ⟨oldImm, hmdb_imm⟩ : ∃ oldImm, mls_db.value = .live (.immediate oldImm) := by
        rcases hloc_db.ref_immediate_cases hdst_ty himm_db with
          ⟨rfl, _⟩ | ⟨_, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
        · exact absurd rfl hsd_ne
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      have hdb_imm : tfb.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_db.layout⟩ := by
        rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmdb_imm; subst hmdb_imm; rfl
      have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
      have hw := annealWriteImmediate_live
        (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
        (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
      have hm_stmt : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
          Miri.Interpreter.runRvalue
            (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
              (.Ref .Erased (translateBorrowKind bk) (translatePlace ⟨ptrIdx, .cons .deref .nil⟩))
              ⟨dstIdx, #[]⟩) m := rfl
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[{ tfb with
              locals := tfb.locals.set dstIdx
                { tfb.locals[dstIdx]'hlt_db with
                  value := .live (.immediate (.scalar
                    (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) }
                hlt_db }]⟩ }, .ok ()) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
      refine ⟨_, _, borTag, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq
        hbb hstmt hm_ok rfl hfrb.location_eq, rfl, ?_⟩
      rw [hmptr_eq]
      simp [Array.getElem?_set_self]

end LeanMiriSpec.Correspondence
