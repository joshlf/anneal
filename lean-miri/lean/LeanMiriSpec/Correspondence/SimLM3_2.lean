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

1. **`_d = &_t` / `_d = &mut _t` (`evalRvalue_ref_simulation` &
   `evalRvalue_ref_indirect_simulation`)**: real-step lockstep simulation of
   `Rvalue.Ref` on both immediate primitive-scalar locals (promoting `_t` into
   a fresh stack allocation through `forceAllocation`) and already memory-backed
   locals (`e₀ ∈ allocMap`, reusing `e₀.allocId` without allocating), extending
   `allocMap` by the new reference's root borrow; undefined behavior in both
   machines on a dead `_t` or dead `_d`.
2. **`_d = &*_p` / `_d = &mut *_p` (`evalRvalue_reborrow_simulation` &
   `evalRvalue_reborrow_safeRef_simulation`)**: real-step correspondence of
   reborrowing through both offset-`0` raw pointers (`*const T` / `*mut T`) and
   safe references (`&T` / `&mut T`): exact undefined-behavior equivalence and
   same-allocation reference creation across dead, uninitialized, null/integer
   (on safe references), and live cases.
3. **Genuine Reborrow Divergences (`evalRvalue_reborrow_dangling_divergence`,
   `evalRvalue_reborrow_safeRef_dangling_divergence`,
   `evalRvalue_reborrow_rawPtr_int_divergence`, and
   `evalRvalue_reborrow_perm_divergence`)**:
   * dangling raw-pointer reborrow: both machines step at reborrow time, while
     `ValidityVisitor` and `annealSafeRefDerefCheck` reject the resulting
     dangling reference;
   * dangling safe-reference reborrow (`&*_r` after `StorageDead`): Anneal
     steps, whereas `lean-miri`'s `Miri.Interpreter.Step.step` immediately
     fails with `"dereferencing a dangling reference"`;
   * integer-scalar raw-pointer reborrow (`&*_p` when `_p` holds an integer
     without provenance): Anneal fails with UB, whereas `lean-miri` steps and
     creates a reference without provenance;
   * parent-borrow permission conflict (`.disabled`, or `.frozen` for `&mut`):
     Anneal fails with Tree Borrows UB, whereas `lean-miri` (pre-`LM-3.3`
     retag) steps.
4. **Safe-Reference Copy/Move & Dereference Read/Write
   (`step_safeRef_use_simulation`, `step_safeRef_deref_read_simulation`, and
   `step_safeRef_deref_write_simulation`)**: full `StepRelLM3_2` real-step
   lockstep simulation of `_d = (copy|move) _r`, `_d = (copy|move) *_r`, and
   `*_r = op` across dead/uninitialized/null/integer references, dangling or
   uninitialized pointees, and live scalar pointees with borrow-table updates.
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
      rw [hsdb_eq] at hloc_db
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
      rw [hsdb_eq] at hloc_db
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

/-! ## 3. Indirect `Rvalue.Ref`, Safe-Reference Reborrow, Use, and Dereference Read/Write -/

/-- `lookupDerefPointeeLayout` returns `none` on any declared safe-reference
local (`_r : &T` or `&mut T`), ensuring `annealDerefOperandToMemPlace` always
routes safe-reference dereferences through `annealDerefSafeRefToMemPlace`'s
eager non-null, dereferenceability, and alignment checks. -/
theorem lookupDerefPointeeLayout_safeRef_eq
    {ld : List LocalDecl} {ly : LayoutTable}
    {refIdx : Local} {refDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? ld refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (ptrLay : Miri.Interpreter.LocalLayout) :
    lookupDerefPointeeLayout ld ly refIdx ptrLay = none := by
  unfold lookupDerefPointeeLayout
  rw [hdecl]
  dsimp only []
  rw [hty]

/-- `lookupRefDerefPointeeLayout` resolves the exact pointee `LocalLayout` of a
declared safe-reference local `_r : &(mut) T` whenever `T` is a primitive scalar
type. -/
theorem lookupRefDerefPointeeLayout_safeRef_eq
    {ld : List LocalDecl} {ly : LayoutTable}
    {refIdx : Local} {refDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? ld refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 }) :
    lookupRefDerefPointeeLayout ld ly refIdx =
      some (translateTy { kind := pointeeKind, layoutIdx := 0 } ly) := by
  have hexact : derefPointeeKindHasExactLayout pointeeKind = true := by
    rcases hpk with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> dsimp only at h <;> rw [h] <;> rfl
  unfold lookupRefDerefPointeeLayout
  rw [hdecl]
  dsimp only []
  rw [hty]
  simp [hexact]

/-- Dereferencing an uninitialized safe-reference local `_r : &(mut) T` raises
`"read of uninitialized local"`. -/
theorem annealDerefOperandToMemPlace_safeRef_uninit
    {ld : List LocalDecl} {ly : LayoutTable}
    {refIdx : Local} {refDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? ld refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (ptrLay : Miri.Interpreter.LocalLayout) (st : AnnealStepState) :
    annealDerefOperandToMemPlace ld ly refIdx (.immediate .uninit) ptrLay st =
      .error (.undefinedBehavior "read of uninitialized local") st := by
  unfold annealDerefOperandToMemPlace annealDerefSafeRefToMemPlace
  rw [lookupDerefPointeeLayout_safeRef_eq hdecl hty ptrLay,
    lookupRefDerefPointeeLayout_safeRef_eq hdecl hty hpk]
  rfl

/-- Dereferencing a safe-reference local `_r : &(mut) T` holding an 8-byte
provenance-free integer scalar raises eager undefined behavior (`"dereferencing a
null reference"` when `sc.bits = 0`, and `"dereferencing a dangling reference"`
when `sc.bits ≠ 0`). -/
theorem annealDerefOperandToMemPlace_safeRef_scalarInt
    {ld : List LocalDecl} {ly : LayoutTable}
    {refIdx : Local} {refDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? ld refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8)
    (ptrLay : Miri.Interpreter.LocalLayout) (st : AnnealStepState) :
    (sc.bits = 0 →
      annealDerefOperandToMemPlace ld ly refIdx (.immediate (.scalar (.fromScalarInt msc)))
        ptrLay st =
        .error (.undefinedBehavior "dereferencing a null reference") st) ∧
    (sc.bits ≠ 0 →
      annealDerefOperandToMemPlace ld ly refIdx (.immediate (.scalar (.fromScalarInt msc)))
        ptrLay st =
        .error (.undefinedBehavior "dereferencing a dangling reference") st) := by
  obtain ⟨hsize, hpos, hfit, _, _, _⟩ := hpk.size_align_ok ly
  have hpos_nat :
      0 < (translateTy { kind := pointeeKind, layoutIdx := 0 } ly).layout.size.bytes.toNat := by
    exact_mod_cast hpos
  refine ⟨fun h0 => ?_, fun hne => ?_⟩
  · unfold annealDerefOperandToMemPlace annealDerefSafeRefToMemPlace
    rw [lookupDerefPointeeLayout_safeRef_eq hdecl hty ptrLay,
      lookupRefDerefPointeeLayout_safeRef_eq hdecl hty hpk]
    simp only [annealReadImmediate, bind, EStateM.bind, pure, EStateM.pure,
      get, getThe, MonadStateOf.get, EStateM.get,
      annealSafeRefDerefCheck_int_null_err st.machine _ hrel hsz8 h0]
    rfl
  · unfold annealDerefOperandToMemPlace annealDerefSafeRefToMemPlace
    rw [lookupDerefPointeeLayout_safeRef_eq hdecl hty ptrLay,
      lookupRefDerefPointeeLayout_safeRef_eq hdecl hty hpk]
    simp only [annealReadImmediate, bind, EStateM.bind, pure, EStateM.pure,
      get, getThe, MonadStateOf.get, EStateM.get,
      annealSafeRefDerefCheck_int_dangling_err st.machine _ hrel hsz8 hne hsize hpos_nat hfit]
    rfl

/-- Dereferencing a safe-reference local `_r : &(mut) T` holding a pointer
immediate delegates directly to `annealSafeRefDerefCheck`. -/
theorem annealDerefOperandToMemPlace_safeRef_pointer_eq
    {ld : List LocalDecl} {ly : LayoutTable}
    {refIdx : Local} {refDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? ld refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (mptr : Miri.Memory.Pointer AnnealProv)
    (ptrLay : Miri.Interpreter.LocalLayout) (st : AnnealStepState) :
    annealDerefOperandToMemPlace ld ly refIdx
        (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))
        ptrLay st =
      match annealSafeRefDerefCheck st.machine
          (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          (translateTy { kind := pointeeKind, layoutIdx := 0 } ly) with
      | .ok mplace => .ok (mplace, translateTy { kind := pointeeKind, layoutIdx := 0 } ly) st
      | .error err => .error err st := by
  unfold annealDerefOperandToMemPlace annealDerefSafeRefToMemPlace
  rw [lookupDerefPointeeLayout_safeRef_eq hdecl hty ptrLay,
    lookupRefDerefPointeeLayout_safeRef_eq hdecl hty hpk]
  simp only [annealReadImmediate, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get]
  cases annealSafeRefDerefCheck st.machine
      (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
      (translateTy { kind := pointeeKind, layoutIdx := 0 } ly) <;> rfl

/-- **`evalRvalue_ref_indirect_simulation` (`LM-3.2`)**: taking `& _t` / `&mut _t`
on a primitive-scalar local `_t` that is ALREADY memory-backed (`e₀ ∈ allocMap`,
`e₀.localIdx = targetIdx`). Unlike `evalRvalue_ref_simulation` (which promotes a
fresh immediate local), `forceAllocation` here reuses `e₀.allocId` without
allocating or requiring `AllocIdSupplyReady`, Anneal pushes the fresh root
borrow `nextTag` with `refBorrowPerm`, `_d` holds the new safe reference
(`LocalRelLM3_2.ref`), and dead `_t` or dead `_d` is undefined behavior in both
machines. -/
theorem evalRvalue_ref_indirect_simulation
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
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    {e₀ : AllocMapEntry} (he₀ : e₀ ∈ allocMap) (he₀_loc : e₀.localIdx = targetIdx) :
    StepRelLM3_2 body m
      (refAllocMapEntry body.localDecls body.layouts bk targetIdx s.memory.nextTag
        e₀.allocId :: allocMap)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc,
    hdisj⟩ := id hstate
  have himm_d := himm_dst tf hframes
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
  obtain ⟨slot_t, mls_t, _, hlt_t, hslot_t, _, hmls_t_eq, hloc_t⟩ :=
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
  have hlt_tb : targetIdx < tfb.locals.size := by
    rw [cacheFrameLocalLayout_size]; exact hlt_t
  have hval_tb : (tfb.locals[targetIdx]'hlt_tb).value = mls_t.value := by
    simp [tfb, cacheFrameLocalLayout, hmls_t_eq]
  rcases hloc_t with hloc_t_1 | ⟨_, _, _, _, _, _, hty_ref, _⟩
  rotate_left
  · exfalso
    rcases htgt_ty with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] at hty_ref <;> cases hty_ref
  by_cases ht_dead : slot_t = .dead
  · subst ht_dead
    have hmls_t_dead : mls_t.value = .dead := by
      cases hloc_t_1 with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hne_d _ => exact absurd rfl hne_d
    have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only
      rw [evalRvalue_ref_dead_eq s body.localDecls body.layouts bk targetIdx hslot_t]
    have hforce := annealForceAllocation_dead_eq (ld := body.localDecls) (ly := body.layouts)
      (m := { m with stack := ⟨#[tfb]⟩ }) rfl hlt_tb (hval_tb.trans hmls_t_dead)
      (translateTy targetDecl.ty body.layouts)
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "address of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [evalRvalueIntoPlace_ref_force_error (region := .Erased)
        (borrow := translateBorrowKind bk) hdst_eval htgt_eval hforce]
    rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · obtain ⟨tfb', hfb, -, -, hfrb, -, -, -, -, -, halloc_b, hdisj_b⟩ := hstate_b
    injection hfb with hfb₁
    injection hfb₁ with hfb₂
    subst hfb₂
    obtain ⟨⟨lay_t, hlay_t⟩, _, _⟩ :=
      (halloc_b.local_alloc_sync tfb rfl e₀ he₀).1 slot_t (he₀_loc ▸ hslot_t) ht_dead
    rw [he₀_loc] at hlay_t
    have hval_tb_ind :
        (tfb.locals[targetIdx]'hlt_tb).value = .live (.indirect (stackAllocPlace e₀.allocId)) := by
      have h := Array.getElem?_eq_getElem hlt_tb
      rw [hlay_t] at h
      exact congrArg Miri.Interpreter.LocalState.value (Option.some.inj h).symm
    have hforce : annealForceAllocation body.localDecls body.layouts
        ⟨.local 0 targetIdx none tfa.localsIdentity, translateTy targetDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } =
        .ok (stackAllocPlace e₀.allocId) { m with stack := ⟨#[tfb]⟩ } :=
      annealForceAllocation_indirect_eq (m := { m with stack := ⟨#[tfb]⟩ }) rfl hlt_tb
        hval_tb_ind (translateTy targetDecl.ty body.layouts)
    have hrv := evalRvalueIntoPlace_ref_ok (region := .Erased)
      (borrow := translateBorrowKind bk) hdst_eval htgt_eval hforce
      (stackAllocPlace_toRef e₀.allocId)
    have hdb_eq : tfb.locals[dstIdx]? =
        some { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } := by
      simp only [tfb, tfa, cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hne), Array.getElem?_set_self, hmls_d_eq]
    obtain ⟨hlt_db, -⟩ := Array.getElem?_eq_some_iff.mp hdb_eq
    have hlive_dst_step :
        ∀ oldImm, mls_d.value = .live (.immediate oldImm) → slot_d ≠ .dead →
          StepRelLM3_2 body m
            (refAllocMapEntry body.localDecls body.layouts bk targetIdx
              s.memory.nextTag e₀.allocId :: allocMap)
            (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩
              body.localDecls body.layouts)
            (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
      intro oldImm hmls_d_imm hslot_d_ne
      have hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx :=
        hstate.immediate_not_in_allocMap hframes hslot_d hslot_d_ne himm_d
      have hdb_imm : tfb.locals[dstIdx]? =
          some ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ := by
        rw [hdb_eq]; rcases mls_d with ⟨v0, l0⟩; dsimp only at hmls_d_imm; subst hmls_d_imm; rfl
      have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
      have hw := annealWriteImmediate_live
        (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e₀.allocId),
            .concrete e₀.allocId Miri.Memory.BorTag.one⟩))
        (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[{ tfb with
              locals := tfb.locals.set dstIdx
                { tfb.locals[dstIdx]'hlt_db with
                  value := .live (.immediate (.scalar
                    (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e₀.allocId),
                        .concrete e₀.allocId Miri.Memory.BorTag.one⟩))) }
                hlt_db }]⟩ },
            .ok ()) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
      have hloc_b : tfb.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hfrb.location_eq
      rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
        hloc_b]
      let newEntry := refAllocMapEntry body.localDecls body.layouts bk targetIdx
        s.memory.nextTag e₀.allocId
      have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩
          body.localDecls body.layouts =
          MirStepNode.step
            (advanceStmt s
              (s.frame.locals.set dstIdx
                (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)))
              { s.memory with
                borrows := newEntry.toBorrowEntry :: s.memory.borrows
                nextTag := s.memory.nextTag + 1 }) := by
        unfold evalStmt; dsimp only
        rw [evalRvalue_ref_live_eq s body.localDecls body.layouts bk targetIdx slot_t
          hslot_t ht_dead]
        dsimp only; rw [hslot_d]
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
        | init _ =>
          simp only [set?_eq_some_set hlt_af_d, hprot, invalidateConflictingBorrows_cons,
            updateBorrowPerm, hbeq, newEntry, refAllocMapEntry,
            AllocMapEntry.toBorrowEntry, hinv_tail]
      rw [ha]
      apply StepRelLM3_2.step
      have h32_e0 := (halloc_b.base_addr_valid e₀ he₀).1
      have hptr := PtrRel.of_stackAllocPlace
        (allocMap := newEntry :: allocMap) (e := newEntry)
        (List.Mem.head allocMap) h32_e0
      have hdb' : tfb.locals[dstIdx]'hlt_db =
          ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ :=
        Option.some.inj ((Array.getElem?_eq_getElem hlt_db).symm.trans hdb_imm)
      have hnew : LocalRelLM3_2 m.machine (newEntry :: allocMap) dstDecl body.layouts
          (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
          { tfb.locals[dstIdx]'hlt_db with
            value := .live (.immediate (.scalar
              (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e₀.allocId),
                  .concrete e₀.allocId Miri.Memory.BorTag.one⟩))) } := by
        rw [hdb']
        exact .ref _ _ _ refMut pointeeKind (fun l hl => (Option.some.inj hl).symm)
          hdst_ty hptr
      have hfrd := (hfrb.mono_cons newEntry).update_local hdecl_dst _ _ hnew
      have hnodup_new : ((newEntry :: allocMap).map AllocMapEntry.tag).Nodup := by
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, halloc_b.tags_nodup⟩
        intro hmem
        obtain ⟨e, he, htag_eq⟩ := List.mem_map.mp hmem
        have hlt_tag := (halloc_b.borrow_sync e he).1
        dsimp only [newEntry, refAllocMapEntry] at htag_eq
        omega
      have hretCont_b : tfb.returnContinuation = .stop false := by
        simp [tfb, tfa, cacheFrameLocalLayout, hretCont]
      have hretPlace_b : ∃ retLay,
          tfb.returnPlace = .frameLocal 0 0 none retLay tfb.localsIdentity := by
        simp [tfb, tfa, cacheFrameLocalLayout]; exact hretPlace
      refine .mk _ rfl hretCont_b hretPlace_b hfrd.advance hcal hstack hprot hcaller
        (by simp [advanceStmt, hbor, newEntry]) ?_ ?_
      · refine ⟨hnodup_new, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro e₁ h₁ e₂ h₂ hloc_eq
          rcases List.mem_cons.mp h₁ with rfl | hm₁ <;>
            rcases List.mem_cons.mp h₂ with rfl | hm₂
          · rfl
          · exact halloc_b.local_to_alloc_unique e₀ he₀ e₂ hm₂ (he₀_loc.trans hloc_eq)
          · exact halloc_b.local_to_alloc_unique e₁ hm₁ e₀ he₀ (hloc_eq.trans he₀_loc.symm)
          · exact halloc_b.local_to_alloc_unique e₁ hm₁ e₂ hm₂ hloc_eq
        · intro e₁ h₁ e₂ h₂ hid_eq
          rcases List.mem_cons.mp h₁ with rfl | hm₁ <;>
            rcases List.mem_cons.mp h₂ with rfl | hm₂
          · rfl
          · exact he₀_loc.symm.trans (halloc_b.alloc_to_local_injective e₀ he₀ e₂ hm₂ hid_eq)
          · exact (halloc_b.alloc_to_local_injective e₁ hm₁ e₀ he₀ hid_eq).trans he₀_loc
          · exact halloc_b.alloc_to_local_injective e₁ hm₁ e₂ hm₂ hid_eq
        · intro e he
          rcases List.mem_cons.mp he with rfl | hm
          · exact ⟨targetDecl, hdecl_tgt, htgt_ty⟩
          · exact halloc_b.target_decl e hm
        · intro e he
          rcases List.mem_cons.mp he with rfl | hm
          · exact halloc_b.base_addr_valid e₀ he₀
          · exact halloc_b.base_addr_valid e hm
        · intro e he
          have hlook_all := lookupBorrow_map_toBorrowEntry_of_nodup hnodup_new he
          rcases List.mem_cons.mp he with rfl | hm
          · exact ⟨Nat.lt_succ_self _,
              by simpa [advanceStmt, hbor, AllocMapEntry.toBorrowEntry] using hlook_all⟩
          · exact ⟨Nat.lt_trans (halloc_b.borrow_sync e hm).1 (Nat.lt_succ_self _),
              by simpa [advanceStmt, hbor, AllocMapEntry.toBorrowEntry] using hlook_all⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | hm
          · exact halloc_b.live_key_unique e₀ he₀
          · exact halloc_b.live_key_unique e hm
        · intro topFrame htop e he
          injection htop with h₁
          injection h₁ with h₂
          subst h₂
          have he_mem_or : ∃ e_orig ∈ allocMap,
              e.localIdx = e_orig.localIdx ∧ e.allocId = e_orig.allocId := by
            rcases List.mem_cons.mp he with rfl | hm
            · exact ⟨e₀, he₀, he₀_loc.symm, rfl⟩
            · exact ⟨e, hm, rfl, rfl⟩
          obtain ⟨e_orig, he_orig, heloc, heaid⟩ := he_mem_or
          rw [heloc, heaid]
          have hne_d : dstIdx ≠ e_orig.localIdx := Ne.symm (hnot_dst e_orig he_orig)
          obtain ⟨hlive_e, hdead_e⟩ := halloc_b.local_alloc_sync tfb rfl e_orig he_orig
          have hslot_after :
              get? (advanceStmt s
                (s.frame.locals.set dstIdx
                  (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)))
                { s.memory with
                  borrows := newEntry.toBorrowEntry :: s.memory.borrows
                  nextTag := s.memory.nextTag + 1 }).frame.locals e_orig.localIdx =
              get? s.frame.locals e_orig.localIdx := by
            dsimp only [advanceStmt]
            rw [get?_eq_getElem?, List.getElem?_set_ne hne_d, ← get?_eq_getElem?]
          refine ⟨fun slot hslot hne_dead => ?_, fun hdead => ?_⟩
          · rw [hslot_after] at hslot
            obtain ⟨⟨lay_e, hlay_e⟩, hsc_e, hshape_e⟩ := hlive_e slot hslot hne_dead
            refine ⟨⟨lay_e, ?_⟩, hsc_e, hshape_e⟩
            show (tfb.locals.set dstIdx _ hlt_db)[e_orig.localIdx]? = _
            rw [Array.getElem?_set_ne _ hne_d]
            exact hlay_e
          · rw [hslot_after] at hdead
            exact hdead_e hdead
      · apply MemoryAllocDisjoint.mono_immediate hdisj_b
        intro k
        by_cases hk : k = dstIdx
        · subst hk
          right
          refine ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e₀.allocId),
                .concrete e₀.allocId Miri.Memory.BorTag.one⟩),
            some (translateTy dstDecl.ty body.layouts), ?_⟩
          show (tfb.locals.set k _ hlt_db)[k]? = _
          rw [Array.getElem?_set_self, hdb']
        · left
          show (tfb.locals.set dstIdx _ hlt_db)[k]? = _
          rw [Array.getElem?_set_ne _ (Ne.symm hk)]
    rcases hloc_d with hloc_d_1 | ⟨_, _, _, _, _, _, _, _⟩
    rotate_left
    · exact hlive_dst_step _ rfl (by simp)
    cases hloc_d_1 with
    | rawPtr _ _ _ _ _ _ hty_raw _ =>
      exfalso; rw [hdst_ty] at hty_raw; cases hty_raw
    | base hloc_d_b =>
      cases hloc_d_b with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm_d _ hmls_d mp)
      | dead _ _ =>
        have hdb_dead : tfb.locals[dstIdx]? =
            some ⟨.dead, some (translateTy dstDecl.ty body.layouts)⟩ := hdb_eq
        have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_dead
        have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; dsimp only
          rw [evalRvalue_ref_live_eq s body.localDecls body.layouts bk targetIdx slot_t
            hslot_t ht_dead]
          dsimp only; rw [hslot_d]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩) m =
            ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
          rw [hrv, annealWriteImmediate_dead (m := { m with stack := ⟨#[tfb]⟩ })
            (id0 := tf.localsIdentity) rfl hget_db]
        rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
          hm_err]
        exact .ub _ _
      | immediate _ oldImm _ _ hvald =>
        have hslot_d_ne : slot_d ≠ .dead := by
          rcases hvald with ⟨rfl, _⟩ | ⟨v, rfl, _⟩ <;> simp
        exact hlive_dst_step oldImm rfl hslot_d_ne

/-- **`evalRvalue_reborrow_rawPtr_int_divergence` (`LM-3.2`, genuine divergence)**:
closing the `hno_int` hypothesis of `evalRvalue_reborrow_simulation`: when a raw
pointer `_p : *(const|mut) T` (`T` primitive scalar) holds an 8-byte integer
scalar `.init (.scalar sc)` (for instance from integer-to-pointer cast `0 as *const T`
or `0x1000 as *const T`), executing `_d = &*_p` / `_d = &mut *_p` into a live
immediate safe-reference local `_d` diverges:

1. Anneal's `stepMirFn` reports `MirStepNode.fail .ub` (`evalRvalue` requires a
   provenance pointer `.ptr` in `_p`);
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) evaluates
   `*_p` without eager checks (`PointerPlaceMachine.fromImmediate`) and writes
   the provenance-free address scalar into `_d`, which `ValidityVisitor.validatePlace`
   (`validatePlace_ref_nonrecursive_simulation`) and `annealSafeRefDerefCheck`
   reject as undefined behavior. -/
theorem evalRvalue_reborrow_rawPtr_int_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : LocalDecl}
    {bk : BorrowKind} {ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy}
    {sc : MirAst.ScalarInt} {span : String}
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
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.scalar sc))) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' msc,
      ScalarRel sc msc ∧ sc.sizeBytes = 8 ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc)))) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue; dsimp only []
    rw [hslot_p]
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
    have hsp_eq : slot_p = .init (.scalar sc) := Option.some.inj (hslot_pa.symm.trans hslot_p)
    subst hsp_eq
    rcases (hloc_p.toLM3_1_of_rawPtr hptr_ty).rawPtr_immediate_cases hptr_ty himm_pa with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨sc', msc, hs_eq, hsz8, hrel, hmp_sc⟩ | ⟨_, _, h, _⟩
    · cases h
    · cases h
    · injection hs_eq with hv_eq; injection hv_eq with hsc_eq; subst hsc_eq
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa =
          ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_sc; subst hmp_sc; rfl
      let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
      obtain ⟨mismatch, hder_sc⟩ := annealDerefOperandToMemPlace_scalarInt (ly := body.layouts)
        hdecl_ptr hptr_ty hpk_prim hrel hsz8 (translateTy ptrDecl.ty body.layouts)
        { m with stack := ⟨#[tfb]⟩ }
      have hsrc_eval : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.memory ⟨Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits),
              .none, mismatch⟩,
            translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hsrc_live, EStateM.bind_eq_ok hder_sc]; rfl
      have hmsc_eq : msc = Miri.Memory.ScalarInt.ofUInt64 (UInt64.ofNat sc.bits) := by
        have hcan := hrel.canonical
        rw [hsz8] at hcan
        have hlt64 : sc.bits < 2 ^ 64 := by
          have : scalarModulus 8 = 2 ^ 64 := by decide
          omega
        have hu64 : (UInt64.ofNat sc.bits).toNat = sc.bits := UInt64.toNat_ofNat_of_lt hlt64
        have hd := hrel.data_eq
        have hs := hrel.size_eq
        rw [hsz8] at hs
        with_unfolding_all
          cases msc with | _ raw bsz =>
          dsimp only [Miri.Memory.ScalarInt.data, Miri.Memory.ScalarInt.size,
            translateSizeBytes, Miri.Memory.ScalarInt.ofUInt64] at hd hs ⊢
          subst hd hs
          rw [hu64]
          rfl
      have htry8 : Miri.Memory.ScalarInt.tryFromUInt
          (BitVec.ofNat 128 (UInt64.ofNat sc.bits).toNat) (Miri.ABI.Size.ofBytes 8) =
          .ok (some (Miri.Memory.ScalarInt.ofUInt64 (UInt64.ofNat sc.bits))) := by
        let addr := UInt64.ofNat sc.bits
        have hbv : BitVec.zeroExtend 128
            (BitVec.extractLsb (((Miri.ABI.Size.ofBytes 8).bytes * 8).toNat - 1) 0
              (BitVec.ofNat 128 addr.toNat)) =
            BitVec.ofNat 128 addr.toNat := by
          have hlt64 : addr.toNat < 2 ^ 64 := addr.toNat_lt
          have hlt128 : addr.toNat < 2 ^ 128 := by omega
          apply BitVec.eq_of_toNat_eq
          change (BitVec.zeroExtend 128 (BitVec.extractLsb 63 0
              (BitVec.ofNat 128 addr.toNat))).toNat =
            (BitVec.ofNat 128 addr.toNat).toNat
          simp [BitVec.extractLsb, BitVec.extractLsb', Nat.mod_eq_of_lt hlt128]
        with_unfolding_all
          conv => lhs; whnf
          rw [hbv, bne_self_eq_false]
          rfl
      have hfromMaybe : Miri.Memory.Scalar.fromMaybePointer (Prov := AnnealProv)
          annealTargetDataLayout
          (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits)) =
          .ok (.fromScalarInt msc) := by
        rw [hmsc_eq]
        with_unfolding_all
          change ((do
              let scalar ← (Miri.Memory.ScalarInt.tryFromUInt
                (BitVec.ofNat 128 (UInt64.ofNat sc.bits).toNat)
                (Miri.ABI.Size.ofBytes 8)).mapError Miri.Memory.ScalarError.scalarInt
              match scalar with
              | some scalar => pure (Miri.Memory.Scalar.fromScalarInt scalar)
              | none => throw (.pointerOffsetDoesNotFit
                  (Miri.ABI.Size.ofBytes (UInt64.ofNat sc.bits)) (Miri.ABI.Size.ofBytes 8))) :
              Except Miri.Memory.ScalarError (Miri.Memory.Scalar AnnealProv)) =
            .ok (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 (UInt64.ofNat sc.bits)))
          rw [htry8]
          rfl
      have htoRef : (⟨Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits),
            .none, mismatch⟩ : Miri.Interpreter.MemPlace AnnealProv).toRef
            annealTargetDataLayout =
          .ok (.scalar (.fromScalarInt msc)) := by
        unfold Miri.Interpreter.MemPlace.toRef Miri.Interpreter.Immediate.newPointerWithMeta
        dsimp only []
        rw [hfromMaybe]
        rfl
      have hrv := evalRvalueIntoPlace_ref_ok (region := .Erased)
        (borrow := translateBorrowKind bk) hdst_eval hsrc_eval
        (annealForceAllocation_memory_eq _ _ _ _ _) htoRef
      have hstate_b := hstate_a.cache_layout rfl hdecl_ptr hlt_pa
      have hfrb := hstate_b.frame_rel_singleton rfl
      obtain ⟨slot_db, mls_db, _, hlt_db, hslot_db, hmls_db, _, hloc_db⟩ :=
        hfrb.lookup_local hdecl_dst
      have hsdb_eq : slot_db = slot_d := Option.some.inj (hslot_db.symm.trans hslot_d)
      rw [hsdb_eq] at hloc_db
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
        (val := .scalar (.fromScalarInt msc))
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
                  value := .live (.immediate (.scalar (.fromScalarInt msc))) }
                hlt_db }]⟩ }, .ok ()) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
      refine ⟨_, _, msc, hrel, hsz8,
        miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq
          hbb hstmt hm_ok rfl hfrb.location_eq, rfl, ?_⟩
      simp [Array.getElem?_set_self]
    · cases h

/-- Dereferencing a `PtrRel`-related safe-reference local `_r : &(mut) T` whose
pointee local `e.localIdx` is `.dead` (dangling reference after `StorageDead`)
eagerly raises `"dereferencing a dangling reference"`. -/
theorem annealDerefOperandToMemPlace_safeRef_ptr_dead
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {refIdx : Local} {refDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? body.localDecls refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    {ptrVal : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    {e : AllocMapEntry}
    (hptrRel : PtrRel allocMap ptrVal mptr)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hdead_t : get? s.frame.locals e.localIdx = some .dead)
    (ptrLay : Miri.Interpreter.LocalLayout)
    {st : AnnealStepState} (hmach : st.machine = m.machine) :
    annealDerefOperandToMemPlace body.localDecls body.layouts refIdx
        (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))
        ptrLay st =
      .error (.undefinedBehavior "dereferencing a dangling reference") st := by
  obtain ⟨tf, hframes, _, _, _, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨_, borTag, hprov_eq, hid_lt, hoff_lt, hmptr_off, ⟨e', he', htag', rfl⟩⟩ := hptrRel
  have he_eq : e = e' :=
    mem_eq_of_map_nodup halloc.tags_nodup he he' (htag.trans htag'.symm)
  subst he_eq
  obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
  have hfind_none := (halloc.local_alloc_sync tf hframes e he).2 hdead_t
  obtain ⟨hsz, hpos, hfit, _, _, _⟩ := hpk.size_align_ok body.layouts
  have hmptr_eq : mptr =
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
        .concrete e.allocId borTag⟩ := by
    rcases mptr with ⟨off, prov⟩
    dsimp only at hprov_eq hmptr_off; subst hprov_eq hmptr_off; rfl
  rw [annealDerefOperandToMemPlace_safeRef_pointer_eq hdecl hty hpk mptr ptrLay st,
    hmach, hmptr_eq,
    annealSafeRefDerefCheck_dead_err (mach := m.machine) e.allocId borTag ptrVal.offsetBytes
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts) hid_lt hoff_lt hbase
      hfind_none hsz (by exact_mod_cast hpos) hfit]

/-- Dereferencing a `PtrRel`-related safe-reference local `_r : &(mut) T` at
offset `0` into a live pointee local `e.localIdx` of matching primitive scalar
type `pointeeKind` succeeds in `annealDerefOperandToMemPlace` and yields the
aligned zero-offset memory place of `e.allocId`. -/
theorem annealDerefOperandToMemPlace_safeRef_ptr_live
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {refIdx : Local} {refDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? body.localDecls refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    {ptrVal : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    {e : AllocMapEntry} {borTag : Miri.Memory.BorTag}
    (hprov_eq : mptr.provenance = .concrete e.allocId borTag)
    (hmptr_off : mptr.offset =
      Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
    (he : e ∈ allocMap)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hlive_t : get? s.frame.locals e.localIdx ≠ some .dead)
    (htgt_kind : ∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
      tgtDecl.ty.kind = pointeeKind)
    (ptrLay : Miri.Interpreter.LocalLayout)
    {st : AnnealStepState} (hmach : st.machine = m.machine) :
    annealDerefOperandToMemPlace body.localDecls body.layouts refIdx
        (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))
        ptrLay st =
      .ok (⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
            some (.concrete e.allocId borTag)⟩, .none, none⟩,
        translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts) st := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨tgtDecl, hdecl_tgt, htgt_prim⟩ := halloc.target_decl e he
  obtain ⟨slot_t, _, _, _, hslot_t, _, _, _⟩ := hfr.lookup_local hdecl_tgt
  have ht_ne_dead : slot_t ≠ .dead := fun hd => hlive_t (hslot_t.trans (congrArg some hd))
  obtain ⟨_, _, hshape_fn⟩ := (halloc.local_alloc_sync tf hframes e he).1 slot_t hslot_t ht_ne_dead
  obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hshape_fn tgtDecl hdecl_tgt
  obtain ⟨hid_lt, _, hbase⟩ := halloc.base_addr_valid e he
  obtain ⟨hsz, hpos, hfit, _, hpow, _⟩ := hpk.size_align_ok body.layouts
  have htr_tgt : translateTy tgtDecl.ty body.layouts =
      translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts := by
    rw [← htgt_prim.translateTy_layoutIdx body.layouts, htgt_kind tgtDecl hdecl_tgt]
  rw [htr_tgt] at hshape_la
  have hinbounds : 0 +
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat := by
    rw [Nat.zero_add, hshape_la.byteSize_eq]
    exact Nat.le_refl _
  have h0_add : annealStackBaseAddr e.allocId + UInt64.ofNat 0 = annealStackBaseAddr e.allocId := by
    simp
  have haligned : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat 0))
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.align.abi =
      .ok none := by
    rw [h0_add]
    exact annealOffsetMisalignment_stackBase_eq_none e.allocId _ hpow
  have hmptr_eq : mptr =
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat 0),
        .concrete e.allocId borTag⟩ := by
    rcases mptr with ⟨off, prov⟩
    dsimp only at hprov_eq hmptr_off; subst hprov_eq hmptr_off; rw [hoff0]
  have hck := annealSafeRefDerefCheck_live_ok (mach := m.machine) e.allocId borTag 0
    (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts) localAlloc
    hid_lt (by decide) hbase hfind_la hsz (by exact_mod_cast hpos) hfit hinbounds haligned
  rw [annealDerefOperandToMemPlace_safeRef_pointer_eq hdecl hty hpk mptr ptrLay st,
    hmach, hmptr_eq, hck, h0_add]

/-- **`evalRvalue_reborrow_safeRef_simulation` (`LM-3.2` Safe-Reference Reborrow)**:
from any `StateRelLM3_2` state in which `_r : &(mut) T` (`T` primitive scalar)
is an immediate safe-reference local whose tracked pointers target a live local
of type `T` at offset `0` with a parent borrow permitting `bk`, reborrowing
`_d = &*_r` / `_d = &mut *_r` into an immediate safe-reference local `_d`:

1. reports undefined behavior in Anneal's `stepMirFn` **if and only if**
   `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) reports
   undefined behavior — WITH NO `hno_int` hypothesis (null and integer-valued
   safe references are eagerly rejected by `annealSafeRefDerefCheck` in
   `Step.step`, matching `stepMirFn`); and
2. otherwise steps in both machines, writing the fresh child borrow `nextTag` at
   offset `0` into `_d` in Anneal and the reference to `e.allocId` into `_d` in
   `lean-miri`. -/
theorem evalRvalue_reborrow_safeRef_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {dstDecl refDecl : LocalDecl}
    {bk : BorrowKind} {refMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref refMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_zero_perm : ∀ ptrVal e,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? s.frame.locals e.localIdx ≠ some .dead ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind)) :
    ((stepMirFn body s = MirStepNode.fail .ub) ↔
      ∃ m' msg,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg))) ∧
    (∀ ptrVal e,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
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
  obtain ⟨himm_d, himm_r⟩ := himm tf hframes
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hfra := hstate_a.frame_rel_singleton rfl
  obtain ⟨slot_r, mls_r, _, hlt_ra, hslot_ra, hmls_ra, hmls_ra_eq, hloc_r⟩ :=
    hfra.lookup_local hdecl_ref
  have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
    hloc_r.cachedLayout_eq
  have himm_ra : ∀ mp, mls_r.value ≠ .live (.indirect mp) :=
    himm_r.cache_layout hlt_d _ mls_r hmls_ra
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
        (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
          (.Ref .Erased (translateBorrowKind bk) (translatePlace ⟨refIdx, .cons .deref .nil⟩))
          ⟨dstIdx, #[]⟩) m := rfl
  have hmain :
      (stepMirFn body s = MirStepNode.fail .ub ∧
        ∃ m' msg,
          Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
            (m', .error (.undefinedBehavior msg))) ∨
      (∃ ptrVal e,
        get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) ∧
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
    rcases hloc_r.ref_immediate_cases href_ty himm_ra with
      ⟨hsr_dead, hmr_dead⟩ | ⟨hsr_un, hmr_un⟩ |
      ⟨sc_r, msc_r, hsr_sc, hsz8_r, hrel_r, hmr_sc⟩ |
      ⟨ptrVal, mptr, hsr_ptr, hptrRel, hmr_ptr⟩
    · left
      have ha : stepMirFn body s = MirStepNode.fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]
        unfold evalStmt evalRvalue; dsimp only []; rw [hslot_ra, hsr_dead]
      have hmls_ra' : tfa.locals[refIdx]'hlt_ra = ⟨.dead, mls_r.layout⟩ := by
        rw [hmls_ra_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_dead; subst hmr_dead; rfl
      have hsrc_dead := annealEvalPlace_deref_dead (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_ra hdecl_ref hmls_ra' hcache_r
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[cacheFrameLocalLayout tfa refIdx hlt_ra
              (translateTy refDecl.ty body.layouts)]⟩ },
            .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        have hrv_err : Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooks body.localDecls body.layouts) ()
            (.Ref .Erased (translateBorrowKind bk) (translatePlace ⟨refIdx, .cons .deref .nil⟩))
            ⟨dstIdx, #[]⟩ m =
            .error (.undefinedBehavior "read of dead local")
              { m with stack := ⟨#[cacheFrameLocalLayout tfa refIdx hlt_ra
                  (translateTy refDecl.ty body.layouts)]⟩ } := by
          unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
          simp only [bind, EStateM.bind, pure, tfa, hdst_eval, hsrc_dead]
        rw [hrv_err]
      exact ⟨ha, _, _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq
        hbb hstmt hm_err⟩
    · left
      have ha : stepMirFn body s = MirStepNode.fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]
        unfold evalStmt evalRvalue; dsimp only []; rw [hslot_ra, hsr_un]
      have hmls_ra' : tfa.locals[refIdx]'hlt_ra = ⟨.live (.immediate .uninit), mls_r.layout⟩ := by
        rw [hmls_ra_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_un; subst hmr_un; rfl
      let tfb := cacheFrameLocalLayout tfa refIdx hlt_ra (translateTy refDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_ra hdecl_ref hmls_ra' hcache_r
      have hder_un := annealDerefOperandToMemPlace_safeRef_uninit (ly := body.layouts)
        hdecl_ref href_ty hpk_prim (translateTy refDecl.ty body.layouts)
        { m with stack := ⟨#[tfb]⟩ }
      have hsrc_un : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨refIdx, .cons .deref .nil⟩) { m with stack := ⟨#[tfa]⟩ } =
          .error (.undefinedBehavior "read of uninitialized local")
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hsrc_live, EStateM.bind_eq_error hder_un]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        have hrv_err : Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooks body.localDecls body.layouts) ()
            (.Ref .Erased (translateBorrowKind bk) (translatePlace ⟨refIdx, .cons .deref .nil⟩))
            ⟨dstIdx, #[]⟩ m =
            .error (.undefinedBehavior "read of uninitialized local")
              { m with stack := ⟨#[tfb]⟩ } := by
          unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
          simp only [bind, EStateM.bind, pure, tfa, hdst_eval, hsrc_un]
        rw [hrv_err]
      exact ⟨ha, _, _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq
        hbb hstmt hm_err⟩
    · left
      have ha : stepMirFn body s = MirStepNode.fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]
        unfold evalStmt evalRvalue; dsimp only []; rw [hslot_ra, hsr_sc]
      have hmls_ra' : tfa.locals[refIdx]'hlt_ra =
          ⟨.live (.immediate (.scalar (.fromScalarInt msc_r))), mls_r.layout⟩ := by
        rw [hmls_ra_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_sc; subst hmr_sc; rfl
      let tfb := cacheFrameLocalLayout tfa refIdx hlt_ra (translateTy refDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_ra hdecl_ref hmls_ra' hcache_r
      have hsc_chk := annealDerefOperandToMemPlace_safeRef_scalarInt (ly := body.layouts)
        hdecl_ref href_ty hpk_prim hrel_r hsz8_r (translateTy refDecl.ty body.layouts)
        { m with stack := ⟨#[tfb]⟩ }
      have hex_msg : ∃ msg, annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨refIdx, .cons .deref .nil⟩) { m with stack := ⟨#[tfa]⟩ } =
          .error (.undefinedBehavior msg) { m with stack := ⟨#[tfb]⟩ } := by
        by_cases h0 : sc_r.bits = 0
        · exact ⟨_, by rw [hsrc_live, EStateM.bind_eq_error (hsc_chk.1 h0)]⟩
        · exact ⟨_, by rw [hsrc_live, EStateM.bind_eq_error (hsc_chk.2 h0)]⟩
      obtain ⟨msg, hsrc_err⟩ := hex_msg
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior msg)) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        have hrv_err : Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooks body.localDecls body.layouts) ()
            (.Ref .Erased (translateBorrowKind bk) (translatePlace ⟨refIdx, .cons .deref .nil⟩))
            ⟨dstIdx, #[]⟩ m =
            .error (.undefinedBehavior msg) { m with stack := ⟨#[tfb]⟩ } := by
          unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
          simp only [bind, EStateM.bind, pure, tfa, hdst_eval, hsrc_err]
        rw [hrv_err]
      exact ⟨ha, _, _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq
        hbb hstmt hm_err⟩
    · have hsr_full : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) :=
        hslot_ra.trans (congrArg some hsr_ptr)
      obtain ⟨_, borTag, hprov_eq, _, _, hmptr_off, ⟨e, he, htag, rfl⟩⟩ := hptrRel
      obtain ⟨hlive_t, hoff0, hne_dis, hnot_fmut, htgt_kind⟩ :=
        hlive_zero_perm ptrVal e hsr_full he htag
      have hlookup := (halloc.borrow_sync e he).2
      rw [htag] at hlookup
      have hrv_a_ok : ∃ mem₁, evalRvalue s.frame.locals
          (.ref bk ⟨refIdx, .cons .deref .nil⟩) s.memory body.localDecls body.layouts =
          .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals mem₁ ∧
          mem₁.activeProtectors = .nil := by
        unfold evalRvalue; dsimp only []
        rw [hsr_full]; dsimp only []; rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry]
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
      have hmls_ra' : tfa.locals[refIdx]'hlt_ra =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_r.layout⟩ := by
        rw [hmls_ra_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
      let tfb := cacheFrameLocalLayout tfa refIdx hlt_ra (translateTy refDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_ra hdecl_ref hmls_ra' hcache_r
      have hder_ptr := annealDerefOperandToMemPlace_safeRef_ptr_live hstate hdecl_ref href_ty
        hpk_prim hprov_eq hmptr_off he hoff0 hlive_t htgt_kind
        (translateTy refDecl.ty body.layouts) (st := { m with stack := ⟨#[tfb]⟩ }) rfl
      have hsrc_eval : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨refIdx, .cons .deref .nil⟩) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.memory ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
                some (.concrete e.allocId borTag)⟩, .none, none⟩,
              translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hsrc_live, EStateM.bind_eq_ok hder_ptr]; rfl
      have hmptr_eq : mptr =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId), .concrete e.allocId borTag⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only at hprov_eq hmptr_off; subst hprov_eq hmptr_off; rw [hoff0]; simp
      have href : (⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
            some (.concrete e.allocId borTag)⟩, .none, none⟩ :
            Miri.Interpreter.MemPlace AnnealProv).toRef annealTargetDataLayout =
          .ok (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)) := by
        rw [hmptr_eq]; rfl
      have hrv := evalRvalueIntoPlace_ref_ok (region := .Erased)
        (borrow := translateBorrowKind bk) hdst_eval hsrc_eval
        (annealForceAllocation_memory_eq _ _ _ _ _) href
      have hstate_b := hstate_a.cache_layout rfl hdecl_ref hlt_ra
      have hfrb := hstate_b.frame_rel_singleton rfl
      obtain ⟨slot_db, mls_db, _, hlt_db, hslot_db, hmls_db, _, hloc_db⟩ :=
        hfrb.lookup_local hdecl_dst
      have hsdb_eq : slot_db = slot_d := Option.some.inj (hslot_db.symm.trans hslot_d)
      rw [hsdb_eq] at hloc_db
      have himm_db : ∀ mp, mls_db.value ≠ .live (.indirect mp) :=
        ((himm_d.cache_layout hlt_d _).cache_layout hlt_ra _) mls_db hmls_db
      have hd_live_case : ∀ oldImm, mls_db.value = .live (.immediate oldImm) →
          slot_d ≠ .dead →
          (get? s.frame.locals dstIdx ≠ some .dead) ∧
          (∃ s', stepMirFn body s = .step s' ∧
            get? s'.frame.locals dstIdx =
              some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
          ∃ m' tf' borTag',
            Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
              (m', .ok true) ∧
            m'.stack.frames = #[tf'] ∧ m'.machine = m.machine ∧
            (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
              some (.live (.immediate (.scalar
                (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                  ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
                    .concrete e.allocId borTag'⟩)))) := by
        intro oldImm hmdb_imm hsd_ne
        have hlive_d : get? s.frame.locals dstIdx ≠ some .dead :=
          fun hd => hsd_ne (Option.some.inj (hslot_d.symm.trans hd))
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
          unfold evalStmt; dsimp only []; rw [hrv_a]; dsimp only []; rw [hslot_d]
          cases slot_d with
          | dead => exact absurd rfl hsd_ne
          | uninit => simp only [hset, hprot₁]; exact ⟨_, rfl, hget_set⟩
          | init _ => simp only [hset, hprot₁]; exact ⟨_, rfl, hget_set⟩
        have hdb_imm : tfb.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_db.layout⟩ := by
          rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmdb_imm; subst hmdb_imm; rfl
        have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
        have hw := annealWriteImmediate_live
          (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
          (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
              (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩) m =
            ({ m with stack := ⟨#[{ tfb with
                locals := tfb.locals.set dstIdx
                  { tfb.locals[dstIdx]'hlt_db with
                    value := .live (.immediate (.scalar
                      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) }
                  hlt_db }]⟩ }, .ok ()) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
        refine ⟨hlive_d, ha_step, _, _, borTag,
          miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
            hfrb.location_eq, rfl, rfl, ?_⟩
        rw [hmptr_eq]; simp [Array.getElem?_set_self]
      rcases hloc_db.ref_immediate_cases hdst_ty himm_db with
        ⟨hsd_dead, hmd_dead⟩ | ⟨hsd_un, hmd_un⟩ |
        ⟨_, _, hsd_sc, _, _, hmd_sc⟩ | ⟨_, _, hsd_ptr, _, hmd_ptr⟩
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
              (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩) m =
            ({ m with stack := ⟨#[tfb]⟩ },
              .error (.undefinedBehavior "write to dead local")) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
          rw [hrv, annealWriteImmediate_dead (m := { m with stack := ⟨#[tfb]⟩ })
            (id0 := tf.localsIdentity) rfl hget_db]
        exact ⟨ha, _, _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq
          hbb hstmt hm_err⟩
      · obtain ⟨hlive_d, ha_step, hm_step⟩ := hd_live_case _ hmd_un (by rw [hsd_un]; simp)
        exact Or.inr ⟨ptrVal, e, hsr_full, he, htag, hlive_d, ha_step, hm_step⟩
      · obtain ⟨hlive_d, ha_step, hm_step⟩ := hd_live_case _ hmd_sc (by rw [hsd_sc]; simp)
        exact Or.inr ⟨ptrVal, e, hsr_full, he, htag, hlive_d, ha_step, hm_step⟩
      · obtain ⟨hlive_d, ha_step, hm_step⟩ := hd_live_case _ hmd_ptr (by rw [hsd_ptr]; simp)
        exact Or.inr ⟨ptrVal, e, hsr_full, he, htag, hlive_d, ha_step, hm_step⟩
  refine ⟨?_, ?_⟩
  · rcases hmain with ⟨ha_ub, hm_ub⟩ | ⟨_, _, _, _, _, _, ⟨_, ha_ok, _⟩, ⟨_, _, _, hm_ok, _, _⟩⟩
    · exact ⟨fun _ => hm_ub, fun _ => ha_ub⟩
    · refine ⟨fun h => ?_, fun ⟨_, _, h⟩ => ?_⟩
      · rw [ha_ok] at h; cases h
      · rw [hm_ok] at h; cases h
  · intro ptrVal e hsr he htag hlive
    rcases hmain with ⟨ha_ub, _⟩ | ⟨ptrVal', e', hsr', he', htag', _, ha_step, hm_step⟩
    · exfalso
      obtain ⟨_, _, hne_dis, hnot_fmut, _⟩ := hlive_zero_perm ptrVal e hsr he htag
      have hlookup := (halloc.borrow_sync e he).2
      rw [htag] at hlookup
      have hrv_ok' : ∃ mem₁, evalRvalue s.frame.locals
          (.ref bk ⟨refIdx, .cons .deref .nil⟩) s.memory body.localDecls body.layouts =
          .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals mem₁ ∧
          mem₁.activeProtectors = .nil := by
        clear ha_ub
        unfold evalRvalue; dsimp only []
        rw [hsr]; dsimp only []; rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry]
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
      unfold evalStmt at ha_ub; dsimp only [] at ha_ub
      rw [hrv₁] at ha_ub; dsimp only [] at ha_ub; rw [hslot_d] at ha_ub
      cases slot_d with
      | dead => exact hlive hslot_d
      | uninit => simp only [set?_eq_some_set hlt_af_d, hprot₁] at ha_ub; cases ha_ub
      | init _ => simp only [set?_eq_some_set hlt_af_d, hprot₁] at ha_ub; cases ha_ub
    · have hp_eq : ptrVal' = ptrVal := by
        have hv := Option.some.inj (hsr'.symm.trans hsr)
        injection hv with hv'
        injection hv'
      subst hp_eq
      have he_eq : e' = e :=
        mem_eq_of_map_nodup halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst he_eq
      exact ⟨ha_step, hm_step⟩

/-- **`evalRvalue_reborrow_safeRef_dangling_divergence` (`LM-3.2`, genuine divergence)**:
when a safe reference `_r : &(mut) T` (`T` primitive scalar) points into a local
`e.localIdx` that `StorageDead` has already killed, reborrowing `_d = &*_r` /
`_d = &mut *_r` into a live destination local `_d` exhibits a direct real-step
divergence between `stepMirFn` and `Miri.Interpreter.Step.step`:

1. Anneal's `stepMirFn` steps (`MirStepNode.step s'`), creating a child borrow
   because `Rvalue.ref` on `*_r` inspects only the borrow entry `e` (which
   `StorageDead` does not remove) and defers liveness checking until use;
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) **directly
   fails during the step itself** with
   `(m', .error (.undefinedBehavior "dereferencing a dangling reference"))`
   because safe-reference dereference runs `annealSafeRefDerefCheck` eagerly
   (`PointerPlaceMachine.dereference` on `Kind.reference`). -/
theorem evalRvalue_reborrow_safeRef_dangling_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {dstDecl refDecl : LocalDecl}
    {bk : BorrowKind} {refMut : Mutability} {pointeeKind : RigidTy}
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref refMut pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared))
    (hdead_t : get? s.frame.locals e.localIdx = some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx =
        some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing a dangling reference")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, _, halloc, _⟩ := id hstate
  have himm_r := himm_ref tf hframes
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  refine ⟨?_, ?_⟩
  · have hlookup := (halloc.borrow_sync e he).2
    rw [htag] at hlookup
    have hrv_ok : ∃ mem₁, evalRvalue s.frame.locals
        (.ref bk ⟨refIdx, .cons .deref .nil⟩) s.memory body.localDecls body.layouts =
        .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals mem₁ ∧
        mem₁.activeProtectors = .nil := by
      unfold evalRvalue; dsimp only []
      rw [hslot_r]; dsimp only []; rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry]
      cases hp : e.perm <;> rcases hm : bk with _ | ⟨_ | _⟩
      · exact ⟨_, rfl, hprot⟩
      · exact ⟨_, rfl, hprot⟩
      · exact ⟨_, rfl, hprot⟩
      · exact ⟨_, rfl, hprot⟩
      · exact ⟨_, rfl, hprot⟩
      · exact ⟨_, rfl, hprot⟩
      · exact ⟨_, rfl, hprot⟩
      · exact absurd ⟨hp, by rw [hm]; exact fun h => BorrowKind.noConfusion h⟩ hperm.2
      · exact absurd ⟨hp, by rw [hm]; exact fun h => BorrowKind.noConfusion h⟩ hperm.2
      · exact absurd hp hperm.1
      · exact absurd hp hperm.1
      · exact absurd hp hperm.1
    obtain ⟨mem₁, hrv₁, hprot₁⟩ := hrv_ok
    have hset := set?_eq_some_set hlt_af_d
      (LocalSlot.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
    have hget_set : get? (s.frame.locals.set dstIdx
        (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) dstIdx =
        some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
      rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt; dsimp only []; rw [hrv₁]; dsimp only []; rw [hslot_d]
    cases slot_d with
    | dead => exact absurd hslot_d hdst_live
    | uninit => simp only [hset, hprot₁]; exact ⟨_, rfl, hget_set⟩
    | init _ => simp only [hset, hprot₁]; exact ⟨_, rfl, hget_set⟩
  · have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
    have hfra := hstate_a.frame_rel_singleton rfl
    obtain ⟨slot_r, mls_r, _, hlt_ra, hslot_ra, hmls_ra, hmls_ra_eq, hloc_r⟩ :=
      hfra.lookup_local hdecl_ref
    have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
      hloc_r.cachedLayout_eq
    have himm_ra : ∀ mp, mls_r.value ≠ .live (.indirect mp) :=
      himm_r.cache_layout hlt_d _ mls_r hmls_ra
    have hsr_eq : slot_r = .init (.ptr ptrVal 8) := Option.some.inj (hslot_ra.symm.trans hslot_r)
    subst hsr_eq
    rcases hloc_r.ref_immediate_cases href_ty himm_ra with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hs_eq, hptrRel, hmr_ptr⟩
    · cases h
    · cases h
    · cases h
    · injection hs_eq with hv_eq; injection hv_eq with hp_eq; subst hp_eq
      have hmls_ra' : tfa.locals[refIdx]'hlt_ra =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_r.layout⟩ := by
        rw [hmls_ra_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
      let tfb := cacheFrameLocalLayout tfa refIdx hlt_ra (translateTy refDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_ra hdecl_ref hmls_ra' hcache_r
      have hder_err := annealDerefOperandToMemPlace_safeRef_ptr_dead hstate hdecl_ref href_ty
        hpk_prim hptrRel he htag hdead_t (translateTy refDecl.ty body.layouts)
        (st := { m with stack := ⟨#[tfb]⟩ }) rfl
      have hsrc_err : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨refIdx, .cons .deref .nil⟩) { m with stack := ⟨#[tfa]⟩ } =
          .error (.undefinedBehavior "dereferencing a dangling reference")
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hsrc_live, EStateM.bind_eq_error hder_err]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ },
            .error (.undefinedBehavior "dereferencing a dangling reference")) := by
        change Miri.Interpreter.runRvalue
          (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
            (.Ref .Erased (translateBorrowKind bk) (translatePlace ⟨refIdx, .cons .deref .nil⟩))
            ⟨dstIdx, #[]⟩) m = _
        unfold Miri.Interpreter.runRvalue
        have hrv_err : Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooks body.localDecls body.layouts) ()
            (.Ref .Erased (translateBorrowKind bk) (translatePlace ⟨refIdx, .cons .deref .nil⟩))
            ⟨dstIdx, #[]⟩ m =
            .error (.undefinedBehavior "dereferencing a dangling reference")
              { m with stack := ⟨#[tfb]⟩ } := by
          unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
          simp only [bind, EStateM.bind, pure, tfa, hdst_eval, hsrc_err]
        rw [hrv_err]
      exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq
        hbb hstmt hm_err⟩

/-! ## 4. Safe-Reference Copy/Move (`_d = (copy|move) _r`) and Dereference Read/Write (`*_r`) -/

/-- Updating `id`'s allocation in `mach.memory.live` via `setLiveAllocation`
preserves `LocalRelLM3_2` for any local that does not own `id`. -/
theorem LocalRelLM3_2.of_setLiveAllocation_ne
    {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {id : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {newMem : AnnealMemory}
    (hfind : mach.memory.live.find? (fun x => x.1 == id) = some (id, localAlloc))
    (hset : mach.memory.setLiveAllocation id alloc' = .ok newMem)
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls)
    (hne : ∀ mp, mls.value = .live (.indirect mp) →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) :
    LocalRelLM3_2 { mach with memory := newMem } allocMap decl layouts slot mls := by
  cases h with
  | lm3_1 h1 => exact .lm3_1 (h1.of_setLiveAllocation_ne hfind hset hne)
  | ref p mptr cl mutability pointeeKind hc hty hptr =>
    exact .ref p mptr cl mutability pointeeKind hc hty hptr

/-- `FrameRelLM3_2` survives any `allocMap` map that preserves `.tag` and
`.allocId`. -/
theorem FrameRelLM3_2.map_preserve
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    (f : AllocMapEntry → AllocMapEntry)
    (htag : ∀ e, (f e).tag = e.tag)
    (halloc : ∀ e, (f e).allocId = e.allocId)
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_2 body mach allocMap af mf) :
    FrameRelLM3_2 body mach (allocMap.map f) af mf where
  body_eq := hfr.body_eq
  location_eq := hfr.location_eq
  af_locals_len := hfr.af_locals_len
  mf_locals_size := hfr.mf_locals_size
  locals_rel i decl slot mls hdecl hslot hmls :=
    (hfr.locals_rel i decl slot mls hdecl hslot hmls).map_preserve f htag halloc

/-- Perm-only map on `allocMap` + writing a live immediate local `dstIdx`
(`dstIdx` absent from `allocMap`) preserves `StateRelLM3_2`. -/
theorem StateRelLM3_2.advance_write_immediate_perm_map
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (f : AllocMapEntry → AllocMapEntry)
    (htag : ∀ e, (f e).tag = e.tag)
    (hloc_idx : ∀ e, (f e).localIdx = e.localIdx)
    (halloc_id : ∀ e, (f e).allocId = e.allocId)
    {dstIdx : Local} {dstDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {hlt_d : dstIdx < tf.locals.size}
    {oldImm newImm : Miri.Interpreter.Immediate AnnealProv}
    (_hd_imm : (tf.locals[dstIdx]'hlt_d).value = .live (.immediate oldImm))
    {newSlot : LocalSlot}
    (hnew : LocalRelLM3_2 m.machine (allocMap.map f) dstDecl body.layouts newSlot
      { tf.locals[dstIdx]'hlt_d with value := .live (.immediate newImm) })
    {mem' : Memory}
    (hmem_cal : mem'.activeCallee = none)
    (hmem_stack : mem'.callStack = .nil)
    (hmem_prot : mem'.activeProtectors = .nil)
    (hmem_caller : mem'.callerLocals = .nil)
    (hmem_bor : mem'.borrows = (allocMap.map f).map AllocMapEntry.toBorrowEntry)
    (hmem_next : mem'.nextTag = s.memory.nextTag) :
    StateRelLM3_2 body
      (advanceStmt s (s.frame.locals.set dstIdx newSlot) mem')
      { m with stack := ⟨#[{ { tf with
          locals := tf.locals.set dstIdx
            { tf.locals[dstIdx]'hlt_d with value := .live (.immediate newImm) } hlt_d } with
          location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }]⟩ }
      (allocMap.map f) := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, _, _, _, _, _, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  have hfr' := ((hfr.map_preserve f htag halloc_id).update_local hdecl_dst newSlot
    (.live (.immediate newImm)) hnew).advance
  have hnodup' : ((allocMap.map f).map AllocMapEntry.tag).Nodup := by
    have hmap_tag : (allocMap.map f).map AllocMapEntry.tag = allocMap.map AllocMapEntry.tag := by
      rw [List.map_map]
      exact List.map_congr_left (fun e _ => htag e)
    rw [hmap_tag]
    exact halloc.tags_nodup
  refine .mk _ rfl hretCont hretPlace hfr' hmem_cal hmem_stack hmem_prot hmem_caller hmem_bor
    ?_ ?_
  · refine ⟨hnodup', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e₁ h₁ e₂ h₂ heq
      obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp h₁
      obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.mp h₂
      rw [hloc_idx, hloc_idx] at heq
      rw [halloc_id, halloc_id]
      exact halloc.local_to_alloc_unique x₁ hx₁ x₂ hx₂ heq
    · intro e₁ h₁ e₂ h₂ heq
      obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp h₁
      obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.mp h₂
      rw [halloc_id, halloc_id] at heq
      rw [hloc_idx, hloc_idx]
      exact halloc.alloc_to_local_injective x₁ hx₁ x₂ hx₂ heq
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      rw [hloc_idx]
      exact halloc.target_decl e he
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      rw [halloc_id]
      exact halloc.base_addr_valid e he
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      have hlook := lookupBorrow_map_toBorrowEntry_of_nodup hnodup' he'
      refine ⟨?_, ?_⟩
      · dsimp only [advanceStmt]
        rw [hmem_next, htag]
        exact (halloc.borrow_sync e he).1
      · dsimp only [advanceStmt]
        rw [hmem_bor]
        simpa [AllocMapEntry.toBorrowEntry] using hlook
    · intro e' he' la₁ la₂ hla₁ hla₂
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      rw [halloc_id] at hla₁ hla₂
      exact halloc.live_key_unique e he la₁ la₂ hla₁ hla₂
    · intro tf' htf' e' he'
      injection htf' with h₁
      injection h₁ with h₂
      subst h₂
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      have hne_d : dstIdx ≠ e.localIdx := Ne.symm (hnot_dst e he)
      obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync tf hframes e he
      have hget_ne :
          get? (advanceStmt s (s.frame.locals.set dstIdx newSlot) mem').frame.locals
            (f e).localIdx = get? s.frame.locals e.localIdx := by
        dsimp only [advanceStmt]
        rw [hloc_idx, get?_eq_getElem?, List.getElem?_set_ne hne_d, ← get?_eq_getElem?]
      refine ⟨fun slot' hslot' hne_dead => ?_, fun hdead' => ?_⟩
      · rw [hget_ne] at hslot'
        obtain ⟨⟨lay, hlay⟩, hsc, hshape⟩ := hlive_e slot' hslot' hne_dead
        refine ⟨⟨lay, ?_⟩, hsc, ?_⟩
        · dsimp only []
          rw [hloc_idx, halloc_id, Array.getElem?_set_ne _ hne_d]
          exact hlay
        · intro decl_e hdecl_e
          rw [hloc_idx] at hdecl_e
          rw [halloc_id]
          exact hshape decl_e hdecl_e
      · rw [hget_ne] at hdead'
        rw [halloc_id]
        exact hdead_e hdead'
  · apply MemoryAllocDisjoint.mono_immediate hdisj
    intro k
    by_cases hk : k = dstIdx
    · subst hk
      right
      refine ⟨newImm, (tf.locals[k]'hlt_d).layout, ?_⟩
      dsimp only []
      rw [Array.getElem?_set_self]
    · left
      dsimp only []
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]

/-- Deinitializing a live immediate local `srcIdx` in both machines preserves
`StateRelLM3_2`. -/
theorem StateRelLM3_2.deinit_immediate_local
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {srcIdx : Local} {srcDecl : LocalDecl}
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {slot_s : LocalSlot}
    (hslot_s : get? s.frame.locals srcIdx = some slot_s)
    (hne_dead : slot_s ≠ .dead)
    (himm_src : IsImmediateFrameLocal tf srcIdx)
    (hlt_s : srcIdx < tf.locals.size) :
    StateRelLM3_2 body
      { s with frame := { s.frame with locals := s.frame.locals.set srcIdx .uninit } }
      { m with stack := ⟨#[deinitFrameLocal tf srcIdx hlt_s]⟩ }
      allocMap := by
  have hnot_src : ∀ e ∈ allocMap, e.localIdx ≠ srcIdx :=
    hstate.immediate_not_in_allocMap hframes hslot_s hne_dead himm_src
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  obtain ⟨_, mls_s, _, _, _, _, hmls_s_eq, hloc_s⟩ := hfr.lookup_local hdecl_src
  have hnew_s : LocalRelLM3_2 m.machine allocMap srcDecl body.layouts .uninit
      { tf.locals[srcIdx]'hlt_s with value := .live (.immediate .uninit) } :=
    .lm3_1 (.base (.immediate .uninit .uninit (tf.locals[srcIdx]'hlt_s).layout
      (by rw [hmls_s_eq]; exact hloc_s.cachedLayout_eq)
      (Or.inl ⟨rfl, rfl⟩)))
  have hfr' := hfr.update_local hdecl_src .uninit (.live (.immediate .uninit)) hnew_s
  refine .mk (deinitFrameLocal tf srcIdx hlt_s) rfl hretCont hretPlace hfr'
    hcal hstack hprot hcaller hbor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro tf' htf' e he
    injection htf' with h₁
    injection h₁ with h₂
    subst h₂
    have hne_s : srcIdx ≠ e.localIdx := Ne.symm (hnot_src e he)
    obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync tf hframes e he
    have hget_ne :
        get? (s.frame.locals.set srcIdx .uninit) e.localIdx =
          get? s.frame.locals e.localIdx := by
      rw [get?_eq_getElem?, List.getElem?_set_ne hne_s, ← get?_eq_getElem?]
    refine ⟨fun slot' hslot' hne_d => ?_, fun hdead' => ?_⟩
    · dsimp only [] at hslot'
      rw [hget_ne] at hslot'
      obtain ⟨⟨lay, hlay⟩, hsc, hshape⟩ := hlive_e slot' hslot' hne_d
      refine ⟨⟨lay, ?_⟩, hsc, hshape⟩
      dsimp only [deinitFrameLocal]
      rw [Array.getElem?_set_ne _ hne_s]
      exact hlay
    · dsimp only [] at hdead'
      rw [hget_ne] at hdead'
      exact hdead_e hdead'
  · apply MemoryAllocDisjoint.mono_immediate hdisj
    intro k
    by_cases hk : k = srcIdx
    · subst hk
      right
      refine ⟨.uninit, (tf.locals[k]'hlt_s).layout, ?_⟩
      dsimp only [deinitFrameLocal]
      rw [Array.getElem?_set_self]
    · left
      dsimp only [deinitFrameLocal]
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]

/-- Shared post-operand write step into an immediate local `dstIdx` from an
operand-updated `StateRelLM3_2` mid-state `(s_mid, tf_mid)` (such as after
deinitializing a moved source local). -/
private theorem finish_write_immediate_lm3_2_from_mid
    {body : CapturedMir} {s s_mid : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    {tf tf_mid : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (hbody : tf.body = translateBody body)
    (hloc : tf.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hstate_mid : StateRelLM3_2 body s_mid { m with stack := ⟨#[tf_mid]⟩ } allocMap)
    (hs_frame_eq : s_mid = { s with frame := { s.frame with locals := s_mid.frame.locals } })
    {bb : BasicBlockData} {dstIdx : Local} {dstDecl : LocalDecl} {rv : Rvalue} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (himm_dst_mid : IsImmediateFrameLocal tf_mid dstIdx)
    {val : Value} {newImm : Miri.Interpreter.Immediate AnnealProv}
    (hrv_anneal : evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
      .ok val s_mid.frame.locals s.memory)
    (hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate newImm
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tf_mid]⟩ })
    (hnew_rel : ∀ cachedLay,
      (∀ l, cachedLay = some l → l = translateTy dstDecl.ty body.layouts) →
      LocalRelLM3_2 m.machine allocMap dstDecl body.layouts (.init val)
        ⟨.live (.immediate newImm), cachedLay⟩) :
    StepRelLM3_2 body m allocMap
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  have hfr_m := hstate_mid.frame_rel_singleton rfl
  obtain ⟨_, _, _, _, _, hcal_m, hstack_m, hprot_m, hcaller_m, hbor_m, _, _⟩ := id hstate_mid
  obtain ⟨slot_dm, mls_dm, hlt_af_dm, hlt_dm, hslot_dm, hmls_dm, hmls_dm_eq, hloc_dm⟩ :=
    hfr_m.lookup_local hdecl_dst
  have hs_mem : s_mid.memory = s.memory := by rw [hs_frame_eq]
  have hb_eq : s_mid.frame.blockIdx = s.frame.blockIdx := by rw [hs_frame_eq]
  have hsi_eq : s_mid.frame.stmtIdx = s.frame.stmtIdx := by rw [hs_frame_eq]
  have hd_dead_helper : slot_dm = .dead → mls_dm.value = .dead →
      StepRelLM3_2 body m allocMap
        (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
    intro hsd_dead hmd_dead
    have hdm_dead : tf_mid.locals[dstIdx]? = some ⟨.dead, mls_dm.layout⟩ := by
      rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_dead; subst hmd_dead; rfl
    have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_dead
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hslot_dm, hsd_dead]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
        ({ m with stack := ⟨#[tf_mid]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
      rw [hm_write]; unfold Miri.Interpreter.runRvalue
      rw [annealWriteImmediate_dead (m := { m with stack := ⟨#[tf_mid]⟩ })
        (id0 := tf.localsIdentity) rfl hget_dm]
    rw [ha_ub, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]
    exact .ub _ _
  have hd_live_helper : ∀ oldImm, mls_dm.value = .live (.immediate oldImm) →
      slot_dm ≠ .dead →
      StepRelLM3_2 body m allocMap
        (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
    intro oldImm hmd_imm hsd_ne
    have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
      hstate_mid.immediate_not_in_allocMap rfl hslot_dm hsd_ne himm_dst_mid
    have hbor_s : s.memory.borrows = allocMap.map AllocMapEntry.toBorrowEntry := by
      rw [← hs_mem]; exact hbor_m
    have hprot_s : s.memory.activeProtectors = .nil := by
      rw [← hs_mem]; exact hprot_m
    have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor_s dstIdx none hnot_dst
    have hdm_live : tf_mid.locals[dstIdx]? =
        some ⟨.live (.immediate oldImm), mls_dm.layout⟩ := by
      rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
    have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_live
    have hw_ok := annealWriteImmediate_live (val := newImm)
      (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
      (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dm hget_dm
    have hm_ok : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
        ({ m with stack := ⟨#[{ tf_mid with
            locals := tf_mid.locals.set dstIdx
              { tf_mid.locals[dstIdx]'hlt_dm with value := .live (.immediate newImm) }
              hlt_dm }]⟩ }, .ok ()) := by
      rw [hm_write]; unfold Miri.Interpreter.runRvalue; rw [hw_ok]
    have hloc_mid : tf_mid.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
      have hl := hfr_m.location_eq
      rw [hb_eq, hsi_eq] at hl
      exact hl
    rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid]
    have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
        MirStepNode.step
          (advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init val)) s_mid.memory) := by
      have hadv_eq : advanceStmt s (s_mid.frame.locals.set dstIdx (.init val)) s.memory =
          advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init val)) s_mid.memory := by
        rw [hs_frame_eq]; rfl
      rw [← hadv_eq]
      unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hslot_dm]
      cases slot_dm with
      | dead => exact absurd rfl hsd_ne
      | uninit =>
        simp only [set?_eq_some_set hlt_af_dm, hprot_s, hbor_inv]
        congr 2; generalize s.memory = mem at hprot_s ⊢
        cases mem; dsimp at hprot_s ⊢; subst hprot_s; rfl
      | init _ =>
        simp only [set?_eq_some_set hlt_af_dm, hprot_s, hbor_inv]
        congr 2; generalize s.memory = mem at hprot_s ⊢
        cases mem; dsimp at hprot_s ⊢; subst hprot_s; rfl
    rw [ha_ok]
    refine .step _ _ ?_
    have hnew_d : LocalRelLM3_2 m.machine (allocMap.map id) dstDecl body.layouts (.init val)
        { tf_mid.locals[dstIdx]'hlt_dm with value := .live (.immediate newImm) } := by
      rw [List.map_id]
      exact hnew_rel (tf_mid.locals[dstIdx]'hlt_dm).layout
        (by rw [hmls_dm_eq]; exact hloc_dm.cachedLayout_eq)
    have hstep_rel := hstate_mid.advance_write_immediate_perm_map rfl id
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hdecl_dst hnot_dst (by rw [hmls_dm_eq]; exact hmd_imm) hnew_d
      hcal_m hstack_m hprot_m hcaller_m (by rw [List.map_id]; exact hbor_m) rfl
    rw [List.map_id, hb_eq, hsi_eq] at hstep_rel
    exact hstep_rel
  rcases hloc_dm with hloc_dm_1 | ⟨_, _, _, _, _, _, _, _⟩
  rotate_left
  · exact hd_live_helper _ rfl (by simp)
  cases hloc_dm_1 with
  | rawPtr _ _ _ _ _ _ _ _ => exact hd_live_helper _ rfl (by simp)
  | base hb =>
    cases hb with
    | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst_mid _ hmls_dm mp)
    | dead _ _ => exact hd_dead_helper rfl rfl
    | immediate _ oldImm _ _ hvd =>
      exact hd_live_helper oldImm rfl (by rcases hvd with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> simp)

/-- **`step_safeRef_use_simulation` (`LM-3.2` Safe-Reference Copy/Move)**:
direct copy or move assignment `_d = .use (opKind ⟨srcIdx, .nil⟩)`
(`opKind ∈ {.copy, .move}`) between immediate safe-reference locals
(`srcDecl.ty.kind = .ref srcMut srcPointee`, `dstDecl.ty.kind = .ref dstMut dstPointee`)
steps in lockstep under `StepRelLM3_2`:
* dead or uninitialized `_s`, or dead `_d`: undefined behavior in both machines;
* `PtrRel` safe reference (or 8-byte integer scalar): copied into `_d` (and `_s`
  deinitialized to `.uninit` in both machines when `opKind = .move`), including
  self-assignment `dstIdx = srcIdx`. -/
theorem step_safeRef_use_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl : LocalDecl} {srcMut dstMut : Mutability}
    {srcPointee dstPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .ref srcMut srcPointee)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_dst, himm_src⟩ := himm tf hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨dstIdx, .nil⟩ (opKind ⟨srcIdx, .nil⟩) span m
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_copy : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  have htr_move : translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ := rfl
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, hlt_af_s, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx :=
    himm_src.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  have himm_d_tfa : IsImmediateFrameLocal tfa dstIdx :=
    himm_dst.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have himm_d_tfb : IsImmediateFrameLocal tfb dstIdx :=
    himm_d_tfa.cache_layout hlt_sa (translateTy srcDecl.ty body.layouts)
  have himm_s_tfb : IsImmediateFrameLocal tfb srcIdx :=
    himm_s_tfa.cache_layout hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by
    rw [cacheFrameLocalLayout_size]; exact hlt_sa
  rcases hloc_s.ref_immediate_cases hsrc_ty (himm_s_tfa mls_s hmls_s) with
    ⟨hss_dead, hms_dead⟩ | ⟨hss_un, hms_un⟩ |
    ⟨sc_s, msc_s, hss_sc, hsz8, hrel_sc, hms_sc⟩ |
    ⟨ptrVal, mptr, hss_ptr, hptrRel, hms_ptr⟩
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_dead; subst hms_dead; rfl
    rcases hopKind with rfl | rfl
    · have hsrc_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_dead]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_stmt, htr_dst, htr_copy]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
    · have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_dead]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_un; subst hms_un; rfl
    rcases hopKind with rfl | rfl
    · have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_un]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_stmt, htr_dst, htr_copy]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
    · have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_un]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
          ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc_s))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_sc; subst hms_sc; rfl
    have hnew_sc : ∀ cachedLay,
        (∀ l, cachedLay = some l → l = translateTy dstDecl.ty body.layouts) →
        LocalRelLM3_2 m.machine allocMap dstDecl body.layouts (.init (.scalar sc_s))
          ⟨.live (.immediate (.scalar (.fromScalarInt msc_s))), cachedLay⟩ := by
      intro cachedLay hc
      refine .lm3_1 (.base (.immediate (.init (.scalar sc_s)) (.scalar (.fromScalarInt msc_s))
        cachedLay hc (Or.inr ⟨.scalar sc_s, rfl, .scalar sc_s msc_s hrel_sc ?_ ?_ ?_⟩)))
      · unfold translateTy; rw [hdst_ty, hsz8]; rfl
      · intro hb; rw [hdst_ty] at hb; cases hb
      · intro hc'; rw [hdst_ty] at hc'; cases hc'
    rcases hopKind with rfl | rfl
    · have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hrv_a : evalRvalue s.frame.locals (.use (.copy ⟨srcIdx, .nil⟩)) s.memory
          body.localDecls body.layouts = .ok (.scalar sc_s) s.frame.locals s.memory := by
        unfold evalRvalue evalOperand readProjectedValue; dsimp only []; rw [hslot_s, hss_sc]
      have hm_w : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate (.scalar (.fromScalarInt msc_s))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hm_stmt, htr_dst, htr_copy]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
      exact finish_write_immediate_lm3_2_from_mid hframes hfr.body_eq hfr.location_eq hstate_b rfl
        hbb hstmt hdecl_dst himm_d_tfb hrv_a hm_w hnew_sc
    · have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hslot_s
        (by rw [hss_sc]; simp) himm_s_tfb hlt_sb
      have hrv_a : evalRvalue s.frame.locals (.use (.move ⟨srcIdx, .nil⟩)) s.memory
          body.localDecls body.layouts =
          .ok (.scalar sc_s) (s.frame.locals.set srcIdx .uninit) s.memory := by
        unfold evalRvalue evalOperand; dsimp only []
        rw [hslot_s, hss_sc, set?_eq_some_set hlt_af_s]
      have hm_w : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate (.scalar (.fromScalarInt msc_s))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
            { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
        rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
      exact finish_write_immediate_lm3_2_from_mid hframes hfr.body_eq hfr.location_eq hstate_mid rfl
        hbb hstmt hdecl_dst (himm_d_tfb.deinit_local hlt_sb) hrv_a hm_w hnew_sc
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_ptr; subst hms_ptr; rfl
    have hnew_ptr : ∀ cachedLay,
        (∀ l, cachedLay = some l → l = translateTy dstDecl.ty body.layouts) →
        LocalRelLM3_2 m.machine allocMap dstDecl body.layouts (.init (.ptr ptrVal 8))
          ⟨.live (.immediate (.scalar
            (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))), cachedLay⟩ :=
      fun cachedLay hc => .ref ptrVal mptr cachedLay dstMut dstPointee hc hdst_ty hptrRel
    rcases hopKind with rfl | rfl
    · have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hrv_a : evalRvalue s.frame.locals (.use (.copy ⟨srcIdx, .nil⟩)) s.memory
          body.localDecls body.layouts = .ok (.ptr ptrVal 8) s.frame.locals s.memory := by
        unfold evalRvalue evalOperand readProjectedValue; dsimp only []; rw [hslot_s, hss_ptr]
      have hm_w : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate
              (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hm_stmt, htr_dst, htr_copy]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
      exact finish_write_immediate_lm3_2_from_mid hframes hfr.body_eq hfr.location_eq hstate_b rfl
        hbb hstmt hdecl_dst himm_d_tfb hrv_a hm_w hnew_ptr
    · have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hslot_s
        (by rw [hss_ptr]; simp) himm_s_tfb hlt_sb
      have hrv_a : evalRvalue s.frame.locals (.use (.move ⟨srcIdx, .nil⟩)) s.memory
          body.localDecls body.layouts =
          .ok (.ptr ptrVal 8) (s.frame.locals.set srcIdx .uninit) s.memory := by
        unfold evalRvalue evalOperand; dsimp only []
        rw [hslot_s, hss_ptr, set?_eq_some_set hlt_af_s]
      have hm_w : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate
              (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
            { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
        rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
      exact finish_write_immediate_lm3_2_from_mid hframes hfr.body_eq hfr.location_eq hstate_mid rfl
        hbb hstmt hdecl_dst (himm_d_tfb.deinit_local hlt_sb) hrv_a hm_w hnew_ptr

private theorem annealReadImmediate_indirect_prim_eq₂
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

/-- **`step_safeRef_deref_read_simulation_explicit` (`LM-3.2` Safe-Reference Deref Read)**:
from any `StateRelLM3_2` state, reading a primitive scalar through an immediate
safe-reference local `_d = (copy|move) *_r` (`refDecl.ty.kind = .ref mutability dstDecl.ty.kind`)
steps in lockstep under `StepRelLM3_2` with post-step borrow table
`derefReadNextAllocMap s.frame.locals allocMap refIdx`:

* dead `_r`, uninitialized `_r`, null/integer `_r` (`annealSafeRefDerefCheck`),
  dangling pointee (`slot_t = .dead`), uninitialized pointee (`slot_t = .uninit`),
  or dead `_d`: undefined behavior in both `stepMirFn` and
  `Miri.Interpreter.Step.step`;
* live initialized scalar pointee into live `_d`: lockstep `StepRelLM3_2.step`,
  freezing foreign active borrows on `e.localIdx` in `allocMap`. -/
theorem step_safeRef_deref_read_simulation_explicit
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
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
            decl.ty.kind = dstDecl.ty.kind)) :
    StepRelLM3_2 body m (derefReadNextAllocMap s.frame.locals allocMap refIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, _⟩ := id hstate
  obtain ⟨himm_dst, himm_ref⟩ := himm tf hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨dstIdx, .nil⟩ (opKind ⟨refIdx, .cons .deref .nil⟩) span m
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  rw [htr_dst] at hm_stmt
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hfra := hstate_a.frame_rel_singleton rfl
  obtain ⟨slot_r, mls_r, _, hlt_ra, hslot_r, hmls_r, hmls_r_eq, hloc_r⟩ :=
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
    ⟨hsr_dead, hmr_dead⟩ | ⟨hsr_un, hmr_un⟩ |
    ⟨sc_r, msc_r, hsr_sc, hsz8_r, hrel_r, hmr_sc⟩ |
    ⟨ptrVal, mptr, hsr_ptr, hptrRel, hmr_ptr⟩
  · -- Case 1: `_r` is `.dead` -> UB in both!
    have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      rcases hopKind with rfl | rfl <;>
      · unfold evalStmt evalRvalue evalOperand; dsimp only []
        rw [hslot_r, hsr_dead, hcaller]
    have hmls_r' : tfa.locals[refIdx]'hlt_ra = ⟨.dead, mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_dead; subst hmr_dead; rfl
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
        m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error (hop_deref_dead hmls_r')]
    rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 2: `_r` is `.uninit` -> UB in both!
    have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      rcases hopKind with rfl | rfl <;>
      · unfold evalStmt evalRvalue evalOperand; dsimp only []
        rw [hslot_r, hsr_un, hcaller]
    have hmls_r' : tfa.locals[refIdx]'hlt_ra = ⟨.live (.immediate .uninit), mls_r.layout⟩ := by
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
    rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 3: `_r` holds integer scalar `sc_r` -> UB in both!
    have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      rcases hopKind with rfl | rfl <;>
      · unfold evalStmt evalRvalue evalOperand; dsimp only []
        rw [hslot_r, hsr_sc, hcaller]
    have hmls_r' : tfa.locals[refIdx]'hlt_ra =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc_r))), mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_sc; subst hmr_sc; rfl
    have hsc_chk := annealDerefOperandToMemPlace_safeRef_scalarInt (ly := body.layouts)
      hdecl_ref href_ty hprim0 hrel_r hsz8_r (translateTy refDecl.ty body.layouts)
      { m with stack := ⟨#[tfb]⟩ }
    have hex_msg : ∃ msg, annealEvalOperand body.localDecls body.layouts
        (translateOperand (opKind ⟨refIdx, .cons .deref .nil⟩))
        (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
        .error (.undefinedBehavior msg) { m with stack := ⟨#[tfb]⟩ } := by
      by_cases h0 : sc_r.bits = 0
      · exact ⟨_, by rw [hop_deref_live _ hmls_r', EStateM.bind_eq_error (hsc_chk.1 h0)]⟩
      · exact ⟨_, by rw [hop_deref_live _ hmls_r', EStateM.bind_eq_error (hsc_chk.2 h0)]⟩
    obtain ⟨msg, hop_err⟩ := hex_msg
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
        m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior msg)) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hop_err]
    rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 4: `_r` holds `PtrRel`-related pointer `ptrVal` / `mptr`.
    subst hsr_ptr
    have hmls_r' : tfa.locals[refIdx]'hlt_ra =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
    have hop_ptr := hop_deref_live _ hmls_r'
    obtain ⟨_, borTag, hprov_eq, hid_lt, _, hmptr_off, ⟨e, he, htag, rfl⟩⟩ := id hptrRel
    obtain ⟨tgtDecl, hdecl_tgt, htgt_prim⟩ := halloc.target_decl e he
    obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
    have hbor_look : lookupBorrow s.memory.borrows e.tag = some e.toBorrowEntry := by
      rw [hbor]
      exact lookupBorrow_map_toBorrowEntry_of_nodup halloc.tags_nodup he
    obtain ⟨_, _, _, halloc_a⟩ : ∃ a b c, AllocMapRel body s { m with stack := ⟨#[tfa]⟩ } allocMap := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc_a, _⟩ := id hstate_a
      exact ⟨(), (), (), halloc_a⟩
    obtain ⟨slot_t, mls_t, _, _, hslot_t, hmls_t, _, hloc_t⟩ := hfra.lookup_local hdecl_tgt
    obtain ⟨hlive_e, _⟩ := halloc_a.local_alloc_sync tfa rfl e he
    by_cases ht_dead : slot_t = .dead
    · -- Subcase 4a: pointee `e.localIdx` is `.dead` -> eager UB in both!
      subst ht_dead
      have ha : evalStmt s
          ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        have hop_ub : evalOperand s.frame.locals (opKind ⟨refIdx, .cons .deref .nil⟩)
            s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals = .ub := by
          rcases hopKind with rfl | rfl <;>
          · unfold evalOperand readProjectedValue; dsimp only []
            rw [hslot_r, hcaller]; dsimp only []
            rw [← htag, hbor_look]; dsimp only [AllocMapEntry.toBorrowEntry]
            cases e.perm <;> simp [hslot_t]
        unfold evalStmt evalRvalue; dsimp only []; rw [hop_ub]
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
      rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      exact .ub _ _
    · -- Subcase 4b: pointee `e.localIdx` is live (`slot_t ≠ .dead`).
      have ht_ne_some_dead : get? s.frame.locals e.localIdx ≠ some .dead := by
        rw [hslot_t]; intro h; exact ht_dead (Option.some.inj h)
      obtain ⟨hoff0, hperm_ok, hkind_tgt⟩ := hlive_ref ptrVal hslot_r e he htag ht_ne_some_dead
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
      have hun_la : slot_t = .uninit →
          localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO
              (translateTy dstDecl.ty body.layouts).layout.size) ≠ .ok (.ok ()) := by
        rw [← htr_tgt]; exact hun_la'
      have hsc_la : ∀ sc, slot_t = .init (.scalar sc) →
          (translateTy tgtDecl.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes ∧
          (tgtDecl.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
          (tgtDecl.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
          ∃ msc, ScalarRel sc msc ∧
            localAlloc.allocation.readScalar annealTargetDataLayout
              (Miri.Memory.allocRange Miri.ABI.Size.ZERO
                (translateTy dstDecl.ty body.layouts).layout.size) false =
              .ok (.fromScalarInt msc) := by
        intro sc hs
        rw [← htr_tgt]
        exact hsc_la' sc hs
      cases hs_t : slot_t with
      | dead => exact absurd hs_t ht_dead
      | uninit =>
        have ha : evalStmt s
            ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          have hop_ub : evalOperand s.frame.locals (opKind ⟨refIdx, .cons .deref .nil⟩)
              s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals = .ub := by
            rcases hopKind with rfl | rfl <;>
            · unfold evalOperand readProjectedValue; dsimp only []
              rw [hslot_r, hcaller]; dsimp only []
              rw [← htag, hbor_look]; dsimp only [AllocMapEntry.toBorrowEntry]
              cases e.perm <;> simp [hslot_t, hs_t]
          unfold evalStmt evalRvalue; dsimp only []; rw [hop_ub]
        obtain ⟨_, hread_err⟩ := hshape_la.uninit_readScalar_err (hun_la hs_t) false
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
          rw [annealReadImmediate_indirect_prim_eq₂ hdst_prim]
          rw [EStateM.bind_eq_error hread_m]
        rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        exact .ub _ _
      | init v_t =>
        obtain ⟨sc_t, rfl⟩ := hsc_t v_t hs_t
        obtain ⟨hsz_t, hbool_t, hchar_t, msc_t, hrel_t, hread_ok⟩ := hsc_la sc_t hs_t
        have hop_anneal : evalOperand s.frame.locals (opKind ⟨refIdx, .cons .deref .nil⟩)
            s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
            .ok (.scalar sc_t) s.frame.locals := by
          rcases hopKind with rfl | rfl <;>
          · unfold evalOperand readProjectedValue; dsimp only []
            rw [hslot_r]; dsimp only []
            rw [← htag, hbor_look]; dsimp only [AllocMapEntry.toBorrowEntry]
            cases hp : e.perm
            · rw [hslot_t, hs_t]
            · rw [hslot_t, hs_t]
            · rw [hslot_t, hs_t]
            · exact absurd hp hperm_ok
        have himm_dst_rel : ImmediateRel dstDecl.ty body.layouts (.scalar sc_t)
            (.scalar (.fromScalarInt msc_t)) :=
          ImmediateRel.of_ty_kind_eq htgt_prim htgt_kind_eq
            (.scalar sc_t msc_t hrel_t hsz_t hbool_t hchar_t)
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
        have hf_tag := derefReadMapFn_tag allocMap e.localIdx ptrVal.tag
        have hf_loc := derefReadMapFn_localIdx allocMap e.localIdx ptrVal.tag
        have hf_aid := derefReadMapFn_allocId allocMap e.localIdx ptrVal.tag
        have hrv_anneal :
            evalRvalue s.frame.locals (.use (opKind ⟨refIdx, .cons .deref .nil⟩))
              s.memory body.localDecls body.layouts =
            .ok (.scalar sc_t) s.frame.locals
              { s.memory with
                borrows := (allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag)).map
                  AllocMapEntry.toBorrowEntry } := by
          unfold evalRvalue; dsimp only []; rw [hop_anneal]
          match hm_cases : allocMap with
          | [] => exact False.elim (List.not_mem_nil he)
          | [single] =>
            have hbor1 : s.memory.borrows = [single.toBorrowEntry] := by simpa using hbor
            rcases hopKind with rfl | rfl <;>
            · rw [hbor1]
              simp only [List.map_cons, List.map_nil, derefReadMapFn, id_eq]
              rw [← hbor1]
          | e₁ :: e₂ :: rest =>
            have hfrz := freezeDerefReadBorrowsAt_map_toBorrowEntry s.frame.locals e₁ e₂ rest
              (hm_cases ▸ halloc_a.tags_nodup) refIdx ptrVal 8 e (hm_cases ▸ he) htag hslot_r
            rcases hopKind with rfl | rfl <;>
            · simp only [hbor, List.map_cons] at hfrz ⊢
              rw [hfrz]
              simp only [derefReadMapFn, updateAllocMapOnDerefRead, List.map_cons]
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
        have hnext_eq : derefReadNextAllocMap s.frame.locals allocMap refIdx =
            allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag) := by
          simp only [derefReadNextAllocMap, hslot_r,
            lookupAllocMapByTag_of_mem_nodup halloc_a.tags_nodup he htag]
        have hd_live_helper :
            ∀ oldImm, mls_d.value = .live (.immediate oldImm) → slot_d ≠ .dead →
              StepRelLM3_2 body m (derefReadNextAllocMap s.frame.locals allocMap refIdx)
                (evalStmt s
                  ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩
                  body.localDecls body.layouts)
                (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
          intro oldImm hmd_imm hsd_ne
          have hnot_dst : ∀ x ∈ allocMap, x.localIdx ≠ dstIdx :=
            hstate.immediate_not_in_allocMap hframes hslot_d hsd_ne himm_dst
          have hnot_dst' :
              ∀ x ∈ allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag),
                x.localIdx ≠ dstIdx := by
            intro x hx
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            rw [hf_loc]; exact hnot_dst y hy
          have hdb_eq : tfb.locals[dstIdx]? =
              some ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ := by
            rw [hdb_get]; rcases mls_d with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
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
            rw [annealReadImmediate_indirect_prim_eq₂ hdst_prim]
            rw [EStateM.bind_eq_ok hread_m, hw_ok]
          have hloc_b : tfb.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
            hfrb.location_eq
          rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok
            rfl hloc_b]
          have hinv_d := invalidateConflictingBorrows_eq_of_not_mem
            (borrows := (allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag)).map
              AllocMapEntry.toBorrowEntry) rfl
            dstIdx none hnot_dst'
          have ha_ok : evalStmt s
              ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩
              body.localDecls body.layouts =
              MirStepNode.step
                (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc_t)))
                  { s.memory with
                    borrows := (allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag)).map
                      AllocMapEntry.toBorrowEntry }) := by
            unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hslot_d]
            cases slot_d with
            | dead => exact absurd rfl hsd_ne
            | uninit => simp only [set?_eq_some_set hlt_af_d, hprot, hinv_d]
            | init _ => simp only [set?_eq_some_set hlt_af_d, hprot, hinv_d]
          rw [ha_ok, hnext_eq]
          apply StepRelLM3_2.step
          have hnew_d :
              LocalRelLM3_2 m.machine
                (allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag))
                dstDecl body.layouts (.init (.scalar sc_t))
                { tfb.locals[dstIdx]'hlt_db with
                  value := .live (.immediate (.scalar (.fromScalarInt msc_t))) } :=
            .lm3_1 (.base (.immediate (.init (.scalar sc_t)) (.scalar (.fromScalarInt msc_t)) _
              (by rw [hd_Lay]; intro l hl; exact (Option.some.inj hl).symm)
              (Or.inr ⟨.scalar sc_t, rfl, himm_dst_rel⟩)))
          exact hstate_b.advance_write_immediate_perm_map rfl
            (derefReadMapFn allocMap e.localIdx ptrVal.tag) hf_tag hf_loc hf_aid
            hdecl_dst hnot_dst (hd_Val.trans hmd_imm) hnew_d
            hcal hstack hprot hcaller rfl rfl
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
            have ha_ub : evalStmt s
                ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩
                body.localDecls body.layouts = MirStepNode.fail .ub := by
              unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hslot_d]
            have hm_err : Miri.Interpreter.Step.evalStatement
                (annealStepHooks body.localDecls body.layouts) ()
                (translateStmt
                  ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
                m =
                ({ m with stack := ⟨#[tfb]⟩ },
                  .error (.undefinedBehavior "write to dead local")) := by
              rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
              rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_ok]
              rw [annealReadImmediate_indirect_prim_eq₂ hdst_prim]
              rw [EStateM.bind_eq_ok hread_m,
                annealWriteImmediate_dead (m := { m with stack := ⟨#[tfb]⟩ })
                  (id0 := tf.localsIdentity) rfl hget_db]
            rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb
              hstmt hm_err]
            exact .ub _ _
          | immediate _ oldImm _ _ hvald =>
            have hsd_ne : slot_d ≠ .dead := by
              rcases hvald with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> simp
            exact hd_live_helper oldImm rfl hsd_ne

/-- **`step_safeRef_deref_read_simulation` (`LM-3.2` Safe-Reference Deref Read)**:
existential-`allocMap'` corollary of `step_safeRef_deref_read_simulation_explicit`. -/
theorem step_safeRef_deref_read_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
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
            decl.ty.kind = dstDecl.ty.kind)) :
    ∃ allocMap',
      StepRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  ⟨_, step_safeRef_deref_read_simulation_explicit hstate hphase hopKind hbb hstmt hdecl_dst
    hdecl_ref href_ty hdst_prim himm hlive_ref⟩

private theorem list_filter_ne_find?₂ {β : Type}
    (l : List (Miri.Memory.AllocId × β))
    {id₀ id : Miri.Memory.AllocId} (hne : id₀ ≠ id) :
    (l.filter (fun entry => entry.1 != id₀)).find? (fun x => x.1 == id) =
      l.find? (fun x => x.1 == id) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    by_cases hid : (hd.1 == id) = true
    · have hhd : hd.1 = id := beq_iff_eq.mp hid
      have hne' : (hd.1 != id₀) = true := by
        rw [hhd, bne_iff_ne]; exact Ne.symm hne
      simp only [List.filter, hne', List.find?, hid]
    · have hidf : (hd.1 == id) = false := Bool.eq_false_iff.mpr hid
      cases hkeep : hd.1 != id₀ <;> simp only [List.filter, hkeep, List.find?, hidf, ih]

private theorem list_filter_self_find?_none₂ {β : Type}
    (l : List (Miri.Memory.AllocId × β)) (id : Miri.Memory.AllocId) :
    (l.filter (fun entry => entry.1 != id)).find? (fun x => x.1 == id) = none := by
  rw [List.find?_eq_none]
  intro x hx
  rw [List.mem_filter] at hx
  have hne : x.1 ≠ id := bne_iff_ne.mp hx.2
  exact beq_eq_false_iff_ne.mpr hne ▸ Bool.false_ne_true

private theorem live_find_filter_push_self₂ {β : Type}
    (live : Array (Miri.Memory.AllocId × β))
    (id : Miri.Memory.AllocId) (newLa : β) :
    ((live.filter (fun x => x.1 != id)).push (id, newLa)).find? (fun x => x.1 == id) =
      some (id, newLa) := by
  rw [Array.find?_push, ← Array.find?_toList, Array.toList_filter,
    list_filter_self_find?_none₂]
  simp

private theorem live_find_filter_push_ne₂ {β : Type}
    (live : Array (Miri.Memory.AllocId × β))
    {id₀ id : Miri.Memory.AllocId} (hne : id₀ ≠ id) (newLa : β) :
    ((live.filter (fun x => x.1 != id₀)).push (id₀, newLa)).find? (fun x => x.1 == id) =
      live.find? (fun x => x.1 == id) := by
  rw [Array.find?_push, ← Array.find?_toList, Array.toList_filter,
    list_filter_ne_find?₂ live.toList hne, Array.find?_toList]
  cases live.find? (fun x => x.1 == id) with
  | some _ => rfl
  | none => simp [beq_false_of_ne hne]

private theorem estate_bind_assoc₂ {ε σ α β γ : Type}
    (ma : EStateM ε σ α) (f : α → EStateM ε σ β) (g : β → EStateM ε σ γ) (s : σ) :
    (ma >>= fun a => f a >>= g) s = ((ma >>= f) >>= g) s := by
  simp only [Bind.bind, EStateM.bind]
  cases ma s <;> rfl

/-- Overwriting `e.allocId`'s live stack allocation at offset `0` with scalar
`sc` (`msc`) and mapping `f` (preserving `.tag`, `.localIdx`, `.allocId`) across
`allocMap` preserves `StateRelLM3_2`. -/
theorem StateRelLM3_2.advance_write_deref_scalar
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (f : AllocMapEntry → AllocMapEntry)
    (hf_tag : ∀ x, (f x).tag = x.tag)
    (hf_loc : ∀ x, (f x).localIdx = x.localIdx)
    (hf_aid : ∀ x, (f x).allocId = x.allocId)
    {e : AllocMapEntry} (he : e ∈ allocMap)
    {tgtDecl : LocalDecl} (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_prim : IsPrimScalarTy tgtDecl.ty)
    {slot_t : LocalSlot} (hslot_t : get? s.frame.locals e.localIdx = some slot_t)
    (ht_ne_dead : slot_t ≠ .dead)
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hkind_la : localAlloc.kind = .stack)
    (halign_la : localAlloc.allocation.align =
      (translateTy tgtDecl.ty body.layouts).layout.align.abi)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel_sc : ScalarRel sc msc)
    (hsz_tgt : (translateTy tgtDecl.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hbool_tgt : tgtDecl.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar_tgt : tgtDecl.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (halign_alloc' : alloc'.align = localAlloc.allocation.align)
    (hshape_alloc' : StackScalarAllocShape (translateSizeBytes sc.sizeBytes) alloc')
    (hinit_alloc' : alloc'.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) = .ok (.ok ()))
    (hread_alloc' : alloc'.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
      .ok (.fromScalarInt msc)) :
    StateRelLM3_2 body
      (advanceStmt s (s.frame.locals.set e.localIdx (.init (.scalar sc)))
        { s.memory with
          borrows := (allocMap.map f).map AllocMapEntry.toBorrowEntry })
      { stack := ⟨#[{ tf with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }]⟩
        machine := { m.machine with
          memory := { m.machine.memory with
            live := (m.machine.memory.live.filter (fun x => x.1 != e.allocId)).push
              (e.allocId, ⟨localAlloc.kind, alloc'⟩) } } }
      (allocMap.map f) := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, _, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  let newLive := (m.machine.memory.live.filter (fun x => x.1 != e.allocId)).push
    (e.allocId, ⟨localAlloc.kind, alloc'⟩)
  let newMem : AnnealMemory := { m.machine.memory with live := newLive }
  let mach' : AnnealMachine := { m.machine with memory := newMem }
  have hset_mem : m.machine.memory.setLiveAllocation e.allocId alloc' = .ok newMem :=
    Miri.Memory.MemoryState.setLiveAllocation_of_find m.machine.memory e.allocId localAlloc
      alloc' hfind_la
  obtain ⟨⟨lay_e, hlay_e⟩, _, _⟩ := (halloc.local_alloc_sync tf hframes e he).1 slot_t hslot_t
    ht_ne_dead
  obtain ⟨_, _, hbase_e⟩ := halloc.base_addr_valid e he
  obtain ⟨_, _, _, _, hpow_t, _⟩ := htgt_prim.size_align_ok body.layouts
  have hlt_af_e : e.localIdx < s.frame.locals.length := by
    cases h : s.frame.locals[e.localIdx]? with
    | none => rw [get?_eq_getElem?, h] at hslot_t; cases hslot_t
    | some _ => exact (List.getElem?_eq_some_iff.mp h).1
  have hloc_e0 := hfr.locals_rel e.localIdx tgtDecl slot_t
    ⟨.live (.indirect (stackAllocPlace e.allocId)), lay_e⟩ hdecl_tgt hslot_t hlay_e
  have hnew_mp : MemPlaceRel mach' tgtDecl.ty body.layouts (some (.scalar sc))
      (stackAllocPlace e.allocId) := by
    refine .mk e.allocId Miri.Memory.BorTag.one (annealStackBaseAddr e.allocId)
      Miri.ABI.Size.ZERO ⟨localAlloc.kind, alloc'⟩
      rfl rfl rfl ?_ hbase_e ?_ ?_ hshape_alloc'.mutability_eq ?_ ?_ ?_ ?_ ?_
      (fun _ _ _ _ hs => nomatch hs)
    · exact Array.mem_toList_iff.mpr (Array.mem_push_self ..)
    · simp only [Miri.ABI.Size.ZERO, UInt64.toNat_zero, Nat.add_zero]
      exact (annealStackBaseAddr e.allocId).toBitVec.isLt
    · simp [stackAllocPlace, Miri.ABI.Size.ZERO]
    · exact annealStackBaseAddr_isAligned e.allocId _ hpow_t
    · simp [Miri.ABI.Size.ZERO, hshape_alloc'.byteSize_eq, hsz_tgt]
    · intro h; cases h
    · intros; rw [hsz_tgt]; exact hinit_alloc'
    · intro sc' hs'
      injection hs' with hv
      injection hv with hsc_eq
      subst hsc_eq
      exact ⟨hsz_tgt, hbool_tgt, hchar_tgt, msc, hrel_sc, hsz_tgt ▸ hread_alloc'⟩
  have hnew_e : LocalRelLM3_2 mach' (allocMap.map f) tgtDecl body.layouts (.init (.scalar sc))
      ⟨.live (.indirect (stackAllocPlace e.allocId)), lay_e⟩ :=
    .lm3_1 (.base (.indirect (.init (.scalar sc)) (stackAllocPlace e.allocId) lay_e
      hloc_e0.cachedLayout_eq (by simp) hnew_mp))
  have hfr' : FrameRelLM3_2 body mach' (allocMap.map f)
      { s.frame with locals := s.frame.locals.set e.localIdx (.init (.scalar sc)) } tf := by
    refine ⟨hfr.body_eq, hfr.location_eq, by rw [List.length_set, hfr.af_locals_len],
      hfr.mf_locals_size, ?_⟩
    intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    by_cases h_eq : e.localIdx = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af_e, Option.some.injEq] at hslot_i
      have hdecl_eq : decl_i = tgtDecl := by
        rw [hdecl_tgt] at hdecl_i; exact Option.some.inj hdecl_i.symm
      have hmls_eq : mls_i = ⟨.live (.indirect (stackAllocPlace e.allocId)), lay_e⟩ := by
        rw [hlay_e] at hmls_i; exact Option.some.inj hmls_i.symm
      subst hdecl_eq hslot_i hmls_eq
      exact hnew_e
    · simp only [h_eq, ↓reduceIte] at hslot_i
      rw [← get?_eq_getElem?] at hslot_i
      have hloc_i := (hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).map_preserve
        f hf_tag hf_aid
      apply hloc_i.of_setLiveAllocation_ne hfind_la hset_mem
      intro mp hv
      have hmls_ind : tf.locals[i]? = some ⟨.live (.indirect mp), mls_i.layout⟩ := by
        rcases mls_i with ⟨v0, l0⟩
        dsimp only at hv; subst hv; exact hmls_i
      have hd := hdisj e.localIdx i (stackAllocPlace e.allocId) mp lay_e mls_i.layout h_eq
        hlay_e hmls_ind
      exact fun heq => hd (by simpa [stackAllocPlace, Option.bind,
        Miri.Memory.Provenance.getAllocId] using heq.symm)
  have hnodup' : ((allocMap.map f).map AllocMapEntry.tag).Nodup := by
    have hmap_tag : (allocMap.map f).map AllocMapEntry.tag = allocMap.map AllocMapEntry.tag := by
      rw [List.map_map]
      exact List.map_congr_left (fun x _ => hf_tag x)
    rw [hmap_tag]
    exact halloc.tags_nodup
  refine .mk _ rfl hretCont hretPlace hfr'.advance hcal hstack hprot hcaller rfl ?_ hdisj
  refine ⟨hnodup', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e₁ h₁ e₂ h₂ heq
    obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp h₁
    obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.mp h₂
    rw [hf_loc, hf_loc] at heq; rw [hf_aid, hf_aid]
    exact halloc.local_to_alloc_unique x₁ hx₁ x₂ hx₂ heq
  · intro e₁ h₁ e₂ h₂ heq
    obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp h₁
    obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.mp h₂
    rw [hf_aid, hf_aid] at heq; rw [hf_loc, hf_loc]
    exact halloc.alloc_to_local_injective x₁ hx₁ x₂ hx₂ heq
  · intro e' he'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    rw [hf_loc]; exact halloc.target_decl x hx
  · intro e' he'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    rw [hf_aid]; exact halloc.base_addr_valid x hx
  · intro e' he'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    have hlook := lookupBorrow_map_toBorrowEntry_of_nodup hnodup' he'
    refine ⟨?_, ?_⟩
    · dsimp only [advanceStmt]; rw [hf_tag]; exact (halloc.borrow_sync x hx).1
    · dsimp only [advanceStmt]; simpa [AllocMapEntry.toBorrowEntry] using hlook
  · intro e' he' la₁ la₂ hla₁ hla₂
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    rw [hf_aid] at hla₁ hla₂
    dsimp only [] at hla₁ hla₂
    simp only [Array.toList_push, List.mem_append, List.mem_singleton,
      Array.toList_filter, List.mem_filter] at hla₁ hla₂
    by_cases ha : x.allocId = e.allocId
    · rw [ha] at hla₁ hla₂
      rcases hla₁ with ⟨_, hb⟩ | h1
      · simp at hb
      · rcases hla₂ with ⟨_, hb⟩ | h2
        · simp at hb
        · exact (Prod.mk.inj h1).2.trans (Prod.mk.inj h2).2.symm
    · rcases hla₁ with ⟨hl₁, _⟩ | h1
      · rcases hla₂ with ⟨hl₂, _⟩ | h2
        · exact halloc.live_key_unique x hx la₁ la₂ hl₁ hl₂
        · exact absurd (Prod.mk.inj h2).1 ha
      · exact absurd (Prod.mk.inj h1).1 ha
  · intro tf' htf' e' he'
    injection htf' with h₁
    injection h₁ with h₂
    subst h₂
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    rw [hf_loc, hf_aid]
    by_cases hx_eq : x.localIdx = e.localIdx
    · have ha_eq : x.allocId = e.allocId := halloc.local_to_alloc_unique x hx e he hx_eq
      rw [hx_eq, ha_eq]
      have hget_self :
          get? (advanceStmt s (s.frame.locals.set e.localIdx (.init (.scalar sc)))
            { s.memory with borrows := (allocMap.map f).map AllocMapEntry.toBorrowEntry }).frame.locals
            e.localIdx = some (.init (.scalar sc)) := by
        dsimp only [advanceStmt]
        rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_e]
      refine ⟨fun slot' hslot' _ => ?_, fun hdead' => ?_⟩
      · rw [hget_self] at hslot'
        injection hslot' with hs'
        subst hs'
        refine ⟨⟨lay_e, hlay_e⟩, fun v hv => ⟨sc, (by injection hv : Value.scalar sc = v).symm⟩,
          fun decl_e hdecl_e => ?_⟩
        rw [hdecl_tgt] at hdecl_e
        injection hdecl_e with hd_eq
        subst hd_eq
        exact ⟨⟨localAlloc.kind, alloc'⟩,
          live_find_filter_push_self₂ m.machine.memory.live e.allocId _,
          hkind_la, halign_alloc'.trans halign_la, hsz_tgt ▸ hshape_alloc'⟩
      · rw [hget_self] at hdead'; cases hdead'
    · have ha_ne : e.allocId ≠ x.allocId := fun ha =>
        hx_eq (halloc.alloc_to_local_injective x hx e he ha.symm)
      obtain ⟨hlive_x, hdead_x⟩ := halloc.local_alloc_sync tf hframes x hx
      have hget_ne :
          get? (advanceStmt s (s.frame.locals.set e.localIdx (.init (.scalar sc)))
            { s.memory with borrows := (allocMap.map f).map AllocMapEntry.toBorrowEntry }).frame.locals
            x.localIdx = get? s.frame.locals x.localIdx := by
        dsimp only [advanceStmt]
        rw [get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hx_eq), ← get?_eq_getElem?]
      have hfind_ne := live_find_filter_push_ne₂ m.machine.memory.live ha_ne
        (⟨localAlloc.kind, alloc'⟩ : Miri.Memory.LocalAllocation AnnealProv
          (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind)
      refine ⟨fun slot' hslot' hne_d => ?_, fun hdead' => ?_⟩
      · rw [hget_ne] at hslot'
        obtain ⟨⟨lay_x, hlay_x⟩, hsc_x, hsh_x⟩ := hlive_x slot' hslot' hne_d
        refine ⟨⟨lay_x, hlay_x⟩, hsc_x, fun decl_x hdecl_x => ?_⟩
        obtain ⟨la_x, hf_x, hk_x, hal_x, hs_x⟩ := hsh_x decl_x hdecl_x
        exact ⟨la_x, hfind_ne.trans hf_x, hk_x, hal_x, hs_x⟩
      · rw [hget_ne] at hdead'
        exact hfind_ne.trans (hdead_x hdead')

/-- Evaluate a `WellTypedScalarOperand` (`constScalar` or `copyLocal` of an
immediate primitive-scalar local) from a `StateRelLM3_2`-related state. -/
theorem evalOperand_scalar_lm3_2_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (hprim : IsPrimScalarTy ty)
    (known : Option Miri.Interpreter.LocalLayout) :
    (∃ m' msg,
      evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ub ∧
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediate) m = .error (.undefinedBehavior msg) m') ∨
    (∃ sc msc tf',
      evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ok (.scalar sc) s.frame.locals ∧
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediate) m =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy ty body.layouts⟩
          { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_2 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      ImmediateRel ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)) ∧
      tf'.localsIdentity = tf.localsIdentity ∧
      (∀ (k : Nat), (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) := by
  rcases id hstate with
    ⟨tf₀, hframes₀, _, _, hfr, _, _, _, _, _, _, _⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  have hsame : { m with stack := ⟨#[tf]⟩ } = m :=
    stepState_with_same_singleton m tf hframes
  cases hop with
  | constScalar c sc hval hprim_c hsz hcan hlaysz hbool hchar =>
    obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
    have heval_a :
        evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals = .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    have heval_m : annealEvalOperand body.localDecls body.layouts
        (translateOperand (.constant c)) known m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ m := by
      with_unfolding_all
        unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
        dsimp only
        rw [hval]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton m.stack tf hframes, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry, hprim_c.layoutOfEncoded]
    right
    refine ⟨sc, msc, tf, heval_a, ?_, by rw [hsame]; exact hstate,
      .scalar sc msc hrel hlaysz hbool hchar, rfl, fun _ => rfl⟩
    rw [EStateM.bind_eq_ok heval_m, hsame]; rfl
  | copyLocal idx decl hdecl _ himm =>
    obtain ⟨slot, mls, _, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
    have hcache := hloc.cachedLayout_eq
    have himm' := himm mls hmls
    have htr : translateOperand (.copy ⟨idx, .nil⟩) = .Copy ⟨idx, #[]⟩ := rfl
    rcases hloc with hloc_1 | ⟨_, _, _, _, _, _, hty_ref, _⟩
    rotate_left
    · exfalso
      rcases hprim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hty_ref <;> cases hty_ref
    cases hloc_1 with
    | rawPtr _ _ _ _ _ _ hty_raw _ =>
      exfalso
      rcases hprim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hty_raw <;> cases hty_raw
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm' mp)
      | dead _ _ =>
        left
        refine ⟨{ m with stack := ⟨#[cacheFrameLocalLayout tf idx hlt_mf
            (translateTy decl.ty body.layouts)]⟩ }, "read of dead local", ?_, ?_⟩
        · simp [evalOperand, hslot]
        · rw [htr]
          exact EStateM.bind_eq_error (annealEvalOperand_copy_dead hframes hlt_mf hdecl hmls_eq hcache)
      | immediate _ imm _ _ hval =>
        let tf' := cacheFrameLocalLayout tf idx hlt_mf (translateTy decl.ty body.layouts)
        have hstate' : StateRelLM3_2 body s { m with stack := ⟨#[tf']⟩ } allocMap :=
          hstate.cache_layout hframes hdecl hlt_mf
        rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
        · left
          refine ⟨{ m with stack := ⟨#[tf']⟩ }, "read of uninitialized local", ?_, ?_⟩
          · simp [evalOperand, hslot]
          · rw [htr, EStateM.bind_eq_ok
              (annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache)]
            rfl
        · obtain ⟨sc, msc, rfl, rfl, hrel, hsz_sc, hbool, hchar⟩ :=
            himmRel.of_primitive_scalar hprim
          right
          refine ⟨sc, msc, tf', ?_, ?_, hstate',
            .scalar sc msc hrel hsz_sc hbool hchar, rfl, ?_⟩
          · simp [evalOperand, readProjectedValue, hslot]
          · rw [htr, EStateM.bind_eq_ok
              (annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache)]
            rfl
          · intro k
            simp only [tf', cacheFrameLocalLayout]
            by_cases hki : idx = k
            · subst hki
              rw [Array.getElem?_set_self, Array.getElem?_eq_getElem hlt_mf]
              rfl
            · rw [Array.getElem?_set_ne _ hki]

/-- **`step_safeRef_deref_write_simulation_explicit` (`LM-3.2` Safe-Reference Deref Write)**:
from any `StateRelLM3_2` state, writing a primitive scalar through an immediate
safe-reference local `*_r = .use op` (`refDecl.ty.kind = .ref mutability pointeeKind`,
`valTy.kind = pointeeKind`) steps in lockstep under `StepRelLM3_2` with post-step
borrow table `derefWriteNextAllocMap s.frame.locals allocMap refIdx`:

* dead `_r`, uninitialized `_r`, null/integer `_r` (`annealSafeRefDerefCheck`),
  dangling pointee (`slot_t = .dead`), or UB evaluating `op`: undefined behavior
  in both `stepMirFn` and `Miri.Interpreter.Step.step`;
* live pointee with writable borrow (`e.perm ∈ {.active, .reserved}`): lockstep
  `StepRelLM3_2.step`, updating both `s.frame.locals` and `e.allocId`'s stack
  allocation in `m.machine.memory.live` while updating borrow permissions via
  `updateAllocMapOnWrite`. -/
theorem step_safeRef_deref_write_simulation_explicit
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl : LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hval_prim : IsPrimScalarTy valTy)
    (hval_kind : valTy.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal e tgtDecl,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
        tgtDecl.ty.kind = pointeeKind) :
    StepRelLM3_2 body m (derefWriteNextAllocMap s.frame.locals allocMap refIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, hcaller, hbor, halloc, _⟩ := id hstate
  have himm_r := himm_ref tf hframes
  have hop_tf := hop tf hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨refIdx, .cons .deref .nil⟩ op span m
  obtain ⟨slot_r, mls_r, _, hlt_r, hslot_r, hmls_r, hmls_r_eq, hloc_r⟩ :=
    hfr.lookup_local hdecl_ref
  have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
    hloc_r.cachedLayout_eq
  let tfa := cacheFrameLocalLayout tf refIdx hlt_r (translateTy refDecl.ty body.layouts)
  have hstate_a : StateRelLM3_2 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_ref hlt_r
  have hop_tfa : WellTypedScalarOperand body tfa op valTy :=
    hop_tf.of_cacheFrameLocalLayout refIdx hlt_r (translateTy refDecl.ty body.layouts)
  have hpt_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 } := by
    rcases hval_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact Or.inl (hval_kind ▸ hk)
    · exact Or.inr (Or.inl (hval_kind ▸ hk))
    · exact Or.inr (Or.inr (Or.inl ⟨it, hval_kind ▸ hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ut, hval_kind ▸ hk⟩))
  have hlay0_eq : translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts =
      translateTy valTy body.layouts := by
    have h1 := hval_prim.translateTy_layoutIdx body.layouts
    rw [hval_kind] at h1
    exact h1
  have hanneal_bad_ref :
      (slot_r = .dead ∨ slot_r = .uninit ∨ ∃ sc, slot_r = .init (.scalar sc)) →
      evalStmt s ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
    intro hbad
    rcases evalOperand_scalar_lm3_2_simulation hstate hframes hop_tf hval_prim none with
      ⟨_, _, hop_ub, _⟩ | ⟨sc, _, _, hop_ok, _, _, _, _⟩
    · unfold evalStmt; dsimp only []
      rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ub]
    · unfold evalStmt; dsimp only []
      rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ok]
      dsimp only [evalPlaceWrite, writePlaceValue]
      rw [hprot]; dsimp only []
      rcases hbad with hs | hs | ⟨_, hs⟩ <;> rw [hslot_r, hs, hcaller]
  rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
    ⟨hsr_dead, hmr_dead⟩ | ⟨hsr_un, hmr_un⟩ |
    ⟨sc_r, msc_r, hsr_sc, hsz8_r, hrel_r, hmr_sc⟩ |
    ⟨ptrVal, mptr, hsr_ptr, hptrRel, hmr_ptr⟩
  · -- Case 1: `_r` is `.dead` -> UB in both!
    have hmls_r' : tf.locals[refIdx]'hlt_r = ⟨.dead, mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_dead; subst hmr_dead; rfl
    have hdst_err := annealEvalPlace_deref_dead hframes hlt_r hdecl_ref hmls_r' hcache_r
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
        ({ m with stack := ⟨#[tfa]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hdst_err]
    rw [hanneal_bad_ref (Or.inl hsr_dead),
      miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 2: `_r` is `.uninit` -> UB in both!
    have hmls_r' : tf.locals[refIdx]'hlt_r = ⟨.live (.immediate .uninit), mls_r.layout⟩ := by
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
        (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
        ({ m with stack := ⟨#[tfa]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hdst_err]
    rw [hanneal_bad_ref (Or.inr (Or.inl hsr_un)),
      miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 3: `_r` holds integer scalar -> eager UB in `annealSafeRefDerefCheck` & UB in Anneal!
    have hmls_r' : tf.locals[refIdx]'hlt_r =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc_r))), mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_sc; subst hmr_sc; rfl
    have hdst_live := annealEvalPlace_deref_live hframes hlt_r hdecl_ref hmls_r' hcache_r
    have hsc_chk := annealDerefOperandToMemPlace_safeRef_scalarInt (ly := body.layouts)
      hdecl_ref href_ty hpt_prim hrel_r hsz8_r (translateTy refDecl.ty body.layouts)
      { m with stack := ⟨#[tfa]⟩ }
    have hex_msg : ∃ msg, annealEvalPlace body.localDecls body.layouts
        (translatePlace ⟨refIdx, .cons .deref .nil⟩) m =
        .error (.undefinedBehavior msg) { m with stack := ⟨#[tfa]⟩ } := by
      by_cases h0 : sc_r.bits = 0
      · exact ⟨_, by rw [hdst_live, EStateM.bind_eq_error (hsc_chk.1 h0)]⟩
      · exact ⟨_, by rw [hdst_live, EStateM.bind_eq_error (hsc_chk.2 h0)]⟩
    obtain ⟨msg, hdst_err⟩ := hex_msg
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
        ({ m with stack := ⟨#[tfa]⟩ }, .error (.undefinedBehavior msg)) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hdst_err]
    rw [hanneal_bad_ref (Or.inr (Or.inr ⟨sc_r, hsr_sc⟩)),
      miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 4: `_r` holds `PtrRel`-related pointer `ptrVal` / `mptr`.
    subst hsr_ptr
    have hmls_r' : tf.locals[refIdx]'hlt_r =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_r.layout⟩ := by
      rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
    have hdst_live := annealEvalPlace_deref_live hframes hlt_r hdecl_ref hmls_r' hcache_r
    obtain ⟨_, borTag, hprov_eq, hid_lt, _, hmptr_off, ⟨e, he, htag, rfl⟩⟩ := id hptrRel
    obtain ⟨tgtDecl, hdecl_tgt, htgt_prim⟩ := halloc.target_decl e he
    obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
    have hbor_look : lookupBorrow s.memory.borrows ptrVal.tag = some e.toBorrowEntry := by
      rw [← htag, hbor]
      exact lookupBorrow_map_toBorrowEntry_of_nodup halloc.tags_nodup he
    obtain ⟨slot_t, _, hlt_af_t, _, hslot_t, _, _, _⟩ := hfr.lookup_local hdecl_tgt
    by_cases ht_dead : slot_t = .dead
    · -- Subcase 4a: `e.localIdx` is `.dead` -> eager UB in `annealSafeRefDerefCheck` & UB in Anneal!
      have hdead_t : get? s.frame.locals e.localIdx = some .dead :=
        hslot_t.trans (congrArg some ht_dead)
      have hder_err := annealDerefOperandToMemPlace_safeRef_ptr_dead hstate hdecl_ref href_ty
        hpt_prim hptrRel he htag hdead_t (translateTy refDecl.ty body.layouts)
        (st := { m with stack := ⟨#[tfa]⟩ }) rfl
      have hdst_err : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨refIdx, .cons .deref .nil⟩) m =
          .error (.undefinedBehavior "dereferencing a dangling reference")
            { m with stack := ⟨#[tfa]⟩ } := by
        rw [hdst_live, EStateM.bind_eq_error hder_err]
      have ha_ub : evalStmt s ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        rcases evalOperand_scalar_lm3_2_simulation hstate hframes hop_tf hval_prim none with
          ⟨_, _, hop_ub, _⟩ | ⟨_, _, _, hop_ok, _, _, _, _⟩
        · unfold evalStmt; dsimp only []; rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ub]
        · unfold evalStmt; dsimp only []; rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ok]
          dsimp only [evalPlaceWrite, writePlaceValue]; rw [hprot]; dsimp only []
          rw [hslot_r]; dsimp only []; rw [hbor_look]; dsimp only [AllocMapEntry.toBorrowEntry]
          cases hp : e.perm <;> simp [hslot_t, ht_dead, hcaller]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
          ({ m with stack := ⟨#[tfa]⟩ },
            .error (.undefinedBehavior "dereferencing a dangling reference")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hdst_err]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      exact .ub _ _
    · -- Subcase 4b: `e.localIdx` is live (`slot_t ≠ .dead`).
      have hs_not_dead : get? s.frame.locals e.localIdx ≠ some .dead := by
        rw [hslot_t]; exact fun h => ht_dead (Option.some.inj h)
      obtain ⟨hoff0, hperm_ok, htgt_kind⟩ :=
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
            translateTy valTy body.layouts⟩ { m with stack := ⟨#[tfa]⟩ } := by
        rw [hdst_live, EStateM.bind_eq_ok hder_ok]; rfl
      rcases evalOperand_scalar_lm3_2_simulation hstate_a rfl hop_tfa hval_prim
          (some (translateTy valTy body.layouts)) with
        ⟨m_op, msg_op, hop_ub, hm_op_ub⟩ | ⟨sc, msc, tf', hop_ok, hm_op_ok, hstate_tf', himm_sc, _⟩
      · have ha_ub : evalStmt s ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; dsimp only []; rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ub]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
            (m_op, .error (.undefinedBehavior msg_op)) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_ok]; dsimp only []
          rw [estate_bind_assoc₂, EStateM.bind_eq_error hm_op_ub]
        rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
          hm_err]
        exact .ub _ _
      · rcases id hstate_tf' with ⟨tf₀', hframes_tf', _, _, hfr_tf', _, _, _, _, _, halloc_tf', _⟩
        injection hframes_tf' with h1_tf
        injection h1_tf with h2_tf
        subst h2_tf
        obtain ⟨hlive_sync, _⟩ := halloc_tf'.local_alloc_sync tf' rfl e he
        have htr_tgt : translateTy tgtDecl.ty body.layouts = translateTy valTy body.layouts := by
          rw [← htgt_prim.translateTy_layoutIdx body.layouts,
            ← hval_prim.translateTy_layoutIdx body.layouts, htgt_kind, hval_kind]
        obtain ⟨_, _, hshape_fn⟩ := hlive_sync slot_t hslot_t ht_dead
        obtain ⟨localAlloc, hfind_la, hkind_la, halign_la, hshape_la⟩ :=
          hshape_fn tgtDecl hdecl_tgt
        obtain ⟨sc', msc', hsc_eq, hmsc_eq, hrel_sc, hsz_sc, hbool_val, hchar_val⟩ :=
          himm_sc.of_primitive_scalar hval_prim
        injection hsc_eq with hsc_eq'
        subst hsc_eq'
        have hmsc_eq' : msc = msc' := by
          injection hmsc_eq with h1
          unfold Miri.Memory.Scalar.fromScalarInt at h1
          injection h1 with h2
          injection h2
        subst hmsc_eq'
        have hshape_sc : StackScalarAllocShape (translateSizeBytes sc.sizeBytes)
            localAlloc.allocation := by
          rw [← hsz_sc, ← htr_tgt]; exact hshape_la
        obtain ⟨alloc', hw_alloc, halign_alloc', hshape_alloc', hinit_alloc', hread_alloc'⟩ :=
          hshape_sc.writeScalar_readScalar hrel_sc
        have hmsc_sz : msc.size = (translateTy valTy body.layouts).layout.size := by
          rw [hrel_sc.size_eq, ← hsz_sc]
        have hw_alloc_lay : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy valTy body.layouts).layout.size)
            (.fromScalarInt msc) localAlloc.allocation = .ok () alloc' := by
          rw [← hmsc_sz]; exact hw_alloc
        have hval_sc : annealValidateScalarForTyId (translateTy valTy body.layouts).ty
            (.fromScalarInt msc) = true :=
          annealValidateScalarForTyId_of_scalarRel hval_prim hrel_sc hbool_val hchar_val
        have hw_m := annealWriteMemoryPlace_zero_offset_scalar_ok hval_prim hid_lt hbase hfind_la
          hshape_la.mutability_eq (htr_tgt ▸ hshape_la.byteSize_eq) hmsc_sz hval_sc hw_alloc_lay
          (borTag := borTag) (st := { m with stack := ⟨#[tf']⟩ })
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
            ({ stack := ⟨#[tf']⟩
               machine := { m.machine with
                 memory := { m.machine.memory with
                   live := (m.machine.memory.live.filter (fun x => x.1 != e.allocId)).push
                     (e.allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_ok]; dsimp only []
          rw [estate_bind_assoc₂, EStateM.bind_eq_ok hm_op_ok,
            annealWriteImmediate_memory_eq rfl, hw_m]
        have hloc_tf' : tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
          hfr_tf'.location_eq
        rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok
          rfl hloc_tf']
        have hinv_bor := invalidateDerefWriteBorrows_map_toBorrowEntry s.frame.locals allocMap
          halloc.tags_nodup refIdx ptrVal 8 e he htag hslot_r
        rw [← hbor] at hinv_bor
        have ha_ok : evalStmt s ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩
            body.localDecls body.layouts =
            MirStepNode.step
              (advanceStmt s (s.frame.locals.set e.localIdx (.init (.scalar sc)))
                { s.memory with
                  borrows := (updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag)).map
                    AllocMapEntry.toBorrowEntry }) := by
          unfold evalStmt; dsimp only []
          rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ok]
          dsimp only [evalPlaceWrite, writePlaceValue]
          rw [hprot]; dsimp only []
          rw [hslot_r]; dsimp only []
          rw [hbor_look]; dsimp only [AllocMapEntry.toBorrowEntry]
          rcases hperm_ok with hp | hp <;> rw [hp] <;> dsimp only [] <;>
          · rw [hslot_t]
            cases slot_t with
            | dead => exact absurd rfl ht_dead
            | uninit => simp only [set?_eq_some_set hlt_af_t, hinv_bor]
            | init _ => simp only [set?_eq_some_set hlt_af_t, hinv_bor]
        have hnext_eq : derefWriteNextAllocMap s.frame.locals allocMap refIdx =
            updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag) := by
          simp only [derefWriteNextAllocMap, hslot_r,
            lookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he htag]
        rw [ha_ok, hnext_eq]
        apply StepRelLM3_2.step
        have hbool_tgt : tgtDecl.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1) :=
          fun hb => hbool_val (hval_kind.trans (htgt_kind.symm.trans hb))
        have hchar_tgt : tgtDecl.ty.kind = .char →
            sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true :=
          fun hc => hchar_val (hval_kind.trans (htgt_kind.symm.trans hc))
        exact hstate_tf'.advance_write_deref_scalar rfl
          (fun x => x.updateOnWrite e.localIdx (some ptrVal.tag))
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          he hdecl_tgt htgt_prim hslot_t ht_dead hfind_la hkind_la halign_la
          hrel_sc ((congrArg (fun tl => tl.layout.size) htr_tgt).trans hsz_sc) hbool_tgt hchar_tgt
          halign_alloc' hshape_alloc' hinit_alloc' hread_alloc'

/-- **`step_safeRef_deref_write_simulation` (`LM-3.2` Safe-Reference Deref Write)**:
existential-`allocMap'` corollary of `step_safeRef_deref_write_simulation_explicit`. -/
theorem step_safeRef_deref_write_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl : LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hval_prim : IsPrimScalarTy valTy)
    (hval_kind : valTy.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal e tgtDecl,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
        tgtDecl.ty.kind = pointeeKind) :
    ∃ allocMap',
      StepRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  ⟨_, step_safeRef_deref_write_simulation_explicit hstate hphase hbb hstmt hdecl_ref href_ty
    hval_prim hval_kind hop himm_ref hlive_ref⟩

/-! ## 5. `StorageDead` and `StorageLive` Under `StateRelLM3_2` -/

/-- A local related by `LocalRelLM3_2` owns, if anything, a live allocation. -/
theorem LocalRelLM3_2.allocLive {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls) :
    LocalAllocLive mach.memory mls.value := by
  cases h with
  | lm3_1 h1 => exact h1.allocLive
  | ref _ _ _ _ _ _ _ _ =>
    intro mp hv
    cases hv

/-- Deallocating the allocation of one local keeps the `LocalRelLM3_2` of every
local that owns a different allocation (including safe-reference locals). -/
theorem LocalRelLM3_2.of_dealloc {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {v : Miri.Interpreter.LocalValue AnnealProv}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls)
    (hdisj : ∀ mp mp', v = .live (.indirect mp) → mls.value = .live (.indirect mp') →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp'.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    LocalRelLM3_2 { mach with memory := deallocLocalMemory mach.memory v }
      allocMap decl layouts slot mls := by
  cases h with
  | lm3_1 h1 => exact .lm3_1 (h1.of_dealloc hdisj)
  | ref p mptr cl mutability pointeeKind hc hty hptr =>
    exact .ref p mptr cl mutability pointeeKind hc hty hptr

private theorem deallocLocalMemory_nextAllocId₂
    (mem : AnnealMemory) (v : Miri.Interpreter.LocalValue AnnealProv) :
    (deallocLocalMemory mem v).nextAllocId = mem.nextAllocId := by
  unfold deallocLocalMemory
  cases v with
  | dead => rfl
  | live op =>
    cases op with
    | immediate _ => rfl
    | indirect mp =>
      dsimp only []
      cases hid : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId <;> rfl

private theorem deallocLocalMemory_sublist₂
    (mem : AnnealMemory) (v : Miri.Interpreter.LocalValue AnnealProv)
    {x : Miri.Memory.AllocId ×
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hx : x ∈ (deallocLocalMemory mem v).live.toList) :
    x ∈ mem.live.toList := by
  unfold deallocLocalMemory at hx
  cases v with
  | dead => exact hx
  | live op =>
    cases op with
    | immediate _ => exact hx
    | indirect mp =>
      dsimp only [] at hx
      cases hid : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none =>
        rw [hid] at hx
        exact hx
      | some id =>
        rw [hid] at hx
        dsimp only [] at hx
        rw [Array.toList_filter, List.mem_filter] at hx
        exact hx.1

private theorem deallocLocalMemory_find?_self₂
    (mem : AnnealMemory) (id : Miri.Memory.AllocId) :
    (deallocLocalMemory mem (.live (.indirect (stackAllocPlace id)))).live.find?
      (fun x => x.1 == id) = none := by
  unfold deallocLocalMemory stackAllocPlace
  dsimp only [Option.bind, Miri.Memory.Provenance.getAllocId]
  rw [← Array.find?_toList, Array.toList_filter]
  exact list_filter_self_find?_none₂ mem.live.toList id

private theorem deallocLocalMemory_find?_ne₂
    (mem : AnnealMemory) (v : Miri.Interpreter.LocalValue AnnealProv)
    (id : Miri.Memory.AllocId)
    (hne : ∀ mp, v = .live (.indirect mp) →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) :
    (deallocLocalMemory mem v).live.find? (fun x => x.1 == id) =
      mem.live.find? (fun x => x.1 == id) := by
  unfold deallocLocalMemory
  cases v with
  | dead => rfl
  | live op =>
    cases op with
    | immediate _ => rfl
    | indirect mp =>
      have hne_mp := hne mp rfl
      dsimp only []
      cases hid : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none => rfl
      | some id₀ =>
        have hne₀ : id₀ ≠ id := fun heq => hne_mp (hid.trans (congrArg some heq))
        dsimp only []
        rw [← Array.find?_toList, ← Array.find?_toList, Array.toList_filter]
        exact list_filter_ne_find?₂ mem.live.toList hne₀

/-- **`step_storageDead_lm3_2_simulation`**: `StorageDead(loc)` (`loc ≠ 0`) from
any `StateRelLM3_2`-related state — whether `loc` is a safe-reference local, an
immediate local, or a borrowed pointee local whose stack allocation is freed
while safe references to it remain in scope — steps in lockstep under
`StepRelLM3_2`. -/
theorem step_storageDead_lm3_2_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne0 : loc ≠ 0) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_prot, ht_caller, ht_bor,
      halloc, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have ha : evalStmt s ⟨.storageDead loc, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc .dead)) := by
    unfold evalStmt
    dsimp only
    rw [hslot, set?_eq_some_set hlt_af]
  rw [ha]
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
    exact annealStepHooks_storageDead_any_eq hframes hlt_mf hne0 hlive
  rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq]
  apply StepRelLM3_2.step
  let mach' : AnnealMachine :=
    { m.machine with
      memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
  have hnew : LocalRelLM3_2 mach' allocMap decl body.layouts .dead
      { topFrame.locals[loc]'hlt_mf with value := .dead } := by
    rw [hmls_eq]
    exact .lm3_1 (.base (.dead mls.layout hloc.cachedLayout_eq))
  have hfr' : FrameRelLM3_2 body mach' allocMap
      { s.frame with locals := s.frame.locals.set loc .dead }
      { topFrame with
        locals := topFrame.locals.set loc
          { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf } := by
    refine ⟨hfr.body_eq, hfr.location_eq,
      by rw [List.length_set, hfr.af_locals_len],
      by rw [Array.size_set, hfr.mf_locals_size], ?_⟩
    intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : loc = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i hmls_i
      have hdecl_eq : decl_i = decl := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
      subst hdecl_eq hslot_i hmls_i
      exact hnew
    · simp only [h_eq, ↓reduceIte] at hslot_i hmls_i
      apply (hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).of_dealloc
      intro mp mp' hv hv'
      apply hdisj loc i mp mp' (topFrame.locals[loc]'hlt_mf).layout mls_i.layout h_eq
      · rw [Array.getElem?_eq_getElem hlt_mf, ← hv]
      · rw [hmls_i, ← hv']
  refine .mk _ rfl ht_ret ht_retp hfr'.advance hcal_none ht_stack ht_prot ht_caller ht_bor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, ?_, halloc.borrow_sync, ?_, ?_⟩
    · intro e he
      obtain ⟨h32, hnext, hbase⟩ := halloc.base_addr_valid e he
      exact ⟨h32, by simpa [mach', deallocLocalMemory_nextAllocId₂] using hnext, hbase⟩
    · intro e he la₁ la₂ hla₁ hla₂
      exact halloc.live_key_unique e he la₁ la₂
        (deallocLocalMemory_sublist₂ _ _ hla₁)
        (deallocLocalMemory_sublist₂ _ _ hla₂)
    · intro tf' htf' e he
      injection htf' with h₁
      injection h₁ with h₂
      subst h₂
      obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync topFrame hframes e he
      by_cases heloc : loc = e.localIdx
      · have hget_dead :
            get? (advanceStmt s (s.frame.locals.set loc .dead)).frame.locals e.localIdx =
              some .dead := by
          dsimp only [advanceStmt]
          rw [← heloc, get?_eq_getElem?, List.getElem?_set_self hlt_af]
        refine ⟨fun slot' hslot' hne_d => ?_, fun _ => ?_⟩
        · rw [hget_dead] at hslot'
          exact absurd (Option.some.inj hslot').symm hne_d
        · by_cases hs_dead : slot = .dead
          · subst hs_dead
            have hv_dead : (topFrame.locals[loc]'hlt_mf).value = .dead := by
              rw [hmls_eq]
              cases hloc with
              | lm3_1 h1 =>
                cases h1 with
                | base hb =>
                  cases hb with
                  | dead _ _ => rfl
                  | immediate _ _ _ _ hv =>
                    rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
                  | indirect _ _ _ _ hne _ => exact absurd rfl hne
            show (deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value).live.find?
              _ = none
            rw [hv_dead]
            exact hdead_e (heloc ▸ hslot)
          · obtain ⟨⟨lay, hlay⟩, _⟩ := hlive_e slot (heloc ▸ hslot) hs_dead
            have hv_ind : (topFrame.locals[loc]'hlt_mf).value =
                .live (.indirect (stackAllocPlace e.allocId)) := by
              rw [← heloc, Array.getElem?_eq_getElem hlt_mf] at hlay
              injection hlay with hls
              rw [hls]
            show (deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value).live.find?
              _ = none
            rw [hv_ind]
            exact deallocLocalMemory_find?_self₂ m.machine.memory e.allocId
      · have hget_ne :
            get? (advanceStmt s (s.frame.locals.set loc .dead)).frame.locals e.localIdx =
              get? s.frame.locals e.localIdx := by
          dsimp only [advanceStmt]
          rw [get?_eq_getElem?, List.getElem?_set_ne heloc, ← get?_eq_getElem?]
        refine ⟨fun slot' hslot' hne_d => ?_, fun hdead' => ?_⟩
        · rw [hget_ne] at hslot'
          obtain ⟨⟨lay, hlay⟩, hsc, hshape⟩ := hlive_e slot' hslot' hne_d
          have hne_alloc : ∀ mp, (topFrame.locals[loc]'hlt_mf).value = .live (.indirect mp) →
              mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some e.allocId := by
            intro mp hv
            have hd := hdisj loc e.localIdx mp (stackAllocPlace e.allocId)
              (topFrame.locals[loc]'hlt_mf).layout lay heloc
              (by rw [Array.getElem?_eq_getElem hlt_mf, ← hv]) hlay
            simpa [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId] using hd
          refine ⟨⟨lay, ?_⟩, hsc, fun decl_e hdecl_e => ?_⟩
          · dsimp only
            rw [Array.getElem?_set_ne _ heloc]
            exact hlay
          · obtain ⟨la, hfind, hkind, halign, hsh⟩ := hshape decl_e hdecl_e
            refine ⟨la, ?_, hkind, halign, hsh⟩
            show (deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value).live.find?
              _ = _
            rw [deallocLocalMemory_find?_ne₂ _ _ _ hne_alloc]
            exact hfind
        · rw [hget_ne] at hdead'
          have hfind0 := hdead_e hdead'
          show (deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value).live.find?
            _ = none
          rw [Array.find?_eq_none] at hfind0 ⊢
          intro x hx
          exact hfind0 x (Array.mem_toList_iff.mp
            (deallocLocalMemory_sublist₂ _ _ (Array.mem_toList_iff.mpr hx)))
  · intro i j mp_i mp_j lay_i lay_j hij hi hj
    dsimp only at hi hj
    rw [Array.getElem?_set] at hi hj
    by_cases hi_loc : loc = i
    · subst hi_loc; simp only [↓reduceIte] at hi; cases hi
    · by_cases hj_loc : loc = j
      · subst hj_loc; simp only [↓reduceIte] at hj; cases hj
      · simp only [hi_loc, hj_loc, ↓reduceIte] at hi hj
        exact hdisj i j mp_i mp_j lay_i lay_j hij hi hj

/-- **`step_storageLive_lm3_2_simulation`**: `StorageLive(loc)` for any declared
local `loc` not tracked in `allocMap` (`∀ e ∈ allocMap, e.localIdx ≠ loc`) steps
in lockstep from any `StateRelLM3_2`-related state. -/
theorem step_storageLive_lm3_2_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hnot_mapped : ∀ e ∈ allocMap, e.localIdx ≠ loc) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_prot, ht_caller, ht_bor,
      halloc, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have ha : evalStmt s ⟨.storageLive loc, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc .uninit)) := by
    unfold evalStmt
    dsimp only
    rw [hslot, set?_eq_some_set hlt_af]
  rw [ha]
  have hty : ∃ ty, topFrame.body.locals[loc]? = some ty := by
    rw [hfr.body_eq, translateBody_locals_getElem? body loc, hdecl]
    exact ⟨_, rfl⟩
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.storageLive loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
    exact annealStepHooks_storageLive_any_eq hframes hlt_mf hty hlive
  rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq]
  apply StepRelLM3_2.step
  let mach' : AnnealMachine :=
    { m.machine with
      memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
  have hnew : LocalRelLM3_2 mach' allocMap decl body.layouts .uninit
      { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } := by
    rw [hmls_eq]
    exact .lm3_1 (.base (.immediate .uninit .uninit mls.layout hloc.cachedLayout_eq
      (Or.inl ⟨rfl, rfl⟩)))
  have hfr' : FrameRelLM3_2 body mach' allocMap
      { s.frame with locals := s.frame.locals.set loc .uninit }
      { topFrame with
        locals := topFrame.locals.set loc
          { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf } := by
    refine ⟨hfr.body_eq, hfr.location_eq,
      by rw [List.length_set, hfr.af_locals_len],
      by rw [Array.size_set, hfr.mf_locals_size], ?_⟩
    intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : loc = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i hmls_i
      have hdecl_eq : decl_i = decl := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
      subst hdecl_eq hslot_i hmls_i
      exact hnew
    · simp only [h_eq, ↓reduceIte] at hslot_i hmls_i
      apply (hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).of_dealloc
      intro mp mp' hv hv'
      apply hdisj loc i mp mp' (topFrame.locals[loc]'hlt_mf).layout mls_i.layout h_eq
      · rw [Array.getElem?_eq_getElem hlt_mf, ← hv]
      · rw [hmls_i, ← hv']
  refine .mk _ rfl ht_ret ht_retp hfr'.advance hcal_none ht_stack ht_prot ht_caller ht_bor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, ?_, halloc.borrow_sync, ?_, ?_⟩
    · intro e he
      obtain ⟨h32, hnext, hbase⟩ := halloc.base_addr_valid e he
      exact ⟨h32, by simpa [mach', deallocLocalMemory_nextAllocId₂] using hnext, hbase⟩
    · intro e he la₁ la₂ hla₁ hla₂
      exact halloc.live_key_unique e he la₁ la₂
        (deallocLocalMemory_sublist₂ _ _ hla₁)
        (deallocLocalMemory_sublist₂ _ _ hla₂)
    · intro tf' htf' e he
      injection htf' with h₁
      injection h₁ with h₂
      subst h₂
      have heloc : loc ≠ e.localIdx := Ne.symm (hnot_mapped e he)
      obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync topFrame hframes e he
      have hget_ne :
          get? (advanceStmt s (s.frame.locals.set loc .uninit)).frame.locals e.localIdx =
            get? s.frame.locals e.localIdx := by
        dsimp only [advanceStmt]
        rw [get?_eq_getElem?, List.getElem?_set_ne heloc, ← get?_eq_getElem?]
      refine ⟨fun slot' hslot' hne_d => ?_, fun hdead' => ?_⟩
      · rw [hget_ne] at hslot'
        obtain ⟨⟨lay, hlay⟩, hsc, hshape⟩ := hlive_e slot' hslot' hne_d
        have hne_alloc : ∀ mp, (topFrame.locals[loc]'hlt_mf).value = .live (.indirect mp) →
            mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some e.allocId := by
          intro mp hv
          have hd := hdisj loc e.localIdx mp (stackAllocPlace e.allocId)
            (topFrame.locals[loc]'hlt_mf).layout lay heloc
            (by rw [Array.getElem?_eq_getElem hlt_mf, ← hv]) hlay
          simpa [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId] using hd
        refine ⟨⟨lay, ?_⟩, hsc, fun decl_e hdecl_e => ?_⟩
        · dsimp only
          rw [Array.getElem?_set_ne _ heloc]
          exact hlay
        · obtain ⟨la, hfind, hkind, halign, hsh⟩ := hshape decl_e hdecl_e
          refine ⟨la, ?_, hkind, halign, hsh⟩
          show (deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value).live.find?
            _ = _
          rw [deallocLocalMemory_find?_ne₂ _ _ _ hne_alloc]
          exact hfind
      · rw [hget_ne] at hdead'
        have hfind0 := hdead_e hdead'
        show (deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value).live.find?
          _ = none
        rw [Array.find?_eq_none] at hfind0 ⊢
        intro x hx
        exact hfind0 x (Array.mem_toList_iff.mp
          (deallocLocalMemory_sublist₂ _ _ (Array.mem_toList_iff.mpr hx)))
  · apply MemoryAllocDisjoint.mono_immediate hdisj
    intro k
    by_cases hk : loc = k
    · subst hk
      right
      exact ⟨.uninit, (topFrame.locals[loc]'hlt_mf).layout, by
        simp only [Array.getElem?_set, ↓reduceIte]⟩
    · left
      simp only [hk, Array.getElem?_set, ↓reduceIte]

end LeanMiriSpec.Correspondence
