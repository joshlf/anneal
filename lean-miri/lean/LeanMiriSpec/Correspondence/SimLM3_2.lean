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
3. **Reborrow Boundaries (`evalRvalue_reborrow_dangling_divergence`,
   `evalRvalue_reborrow_uninit_target_divergence`,
   `evalRvalue_reborrow_safeRef_dangling_simulation`,
   `evalRvalue_reborrow_rawPtr_int_divergence`, and
   `evalRvalue_reborrow_perm_divergence`)**:
   * dangling raw-pointer reborrow: Anneal rejects the reborrow eagerly with
     `MirStepNode.fail .ub`, whereas `lean-miri` steps at reborrow time and only
     its `ValidityVisitor` and `annealSafeRefDerefCheck` reject the resulting
     dangling reference;
   * uninitialized live-local raw-pointer reborrow (`&*_p` when `e.localIdx` is
     `.uninit`): Anneal rejects eagerly with `MirStepNode.fail .ub`
     (`targetRootAndDeclsOpt = none`), whereas `lean-miri` steps and creates a
     valid reference to the live stack allocation;
   * dangling safe-reference reborrow (`&*_r` after `StorageDead`): Stage-1
     resolved this divergence; BOTH machines now report undefined behavior
     (`StepRelLM3_2.ub`, `lean-miri`: `"dereferencing a dangling reference"`);
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
`sharedBorrowPerm` and mutable borrows, ordinary and two-phase alike,
`mutableBorrowPerm` (`Places.lean`, `Rvalue.ref`). -/
def refBorrowPerm (localDecls : List LocalDecl) (layouts : LayoutTable)
    (bk : BorrowKind) (targetIdx : Local) : TreeBorrowPerm :=
  match bk with
  | .shared => sharedBorrowPerm localDecls layouts ⟨targetIdx, .nil⟩
  | .mut _ => mutableBorrowPerm localDecls layouts ⟨targetIdx, .nil⟩

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

private theorem findDeclTyWithKind?_prim_kind₂ {ld : List LocalDecl} {pk : RigidTy}
    (h : IsPrimScalarTy { kind := pk, layoutIdx := 0 }) {dTy : Ty}
    (hf : findDeclTyWithKind? ld pk = some dTy) :
    dTy.kind = pk := by
  induction ld with
  | nil => cases hf
  | cons decl rest ih =>
    unfold findDeclTyWithKind? at hf
    cases hreq : rigidTyEq decl.ty.kind pk
    · rw [hreq] at hf; exact ih hf
    · rw [hreq] at hf
      injection hf with h1
      rw [← h1]
      exact (h.rigidTyEq_iff decl.ty.kind).mp hreq

private theorem findContainerElemTyWithKind?_kind₂ {ly : LayoutTable} {ld : List LocalDecl}
    {pk : RigidTy} {dTy : Ty}
    (hf : findContainerElemTyWithKind? ly ld pk = some dTy) :
    dTy.kind = pk := by
  induction ld with
  | nil => cases hf
  | cons decl rest ih =>
    unfold findContainerElemTyWithKind? at hf
    dsimp only [] at hf
    split at hf
    · split at hf
      · exact ih hf
      · split at hf
        · injection hf with h1; rw [← h1]
        · exact ih hf
    · exact ih hf

theorem placeTyResolved_deref_safeRef_prim
    {ld : List LocalDecl} {layouts : LayoutTable} {refIdx : Local} {refDecl : LocalDecl}
    {mutability : Mutability} {pk : RigidTy}
    (hdecl : get? ld refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pk)
    (hprim : IsPrimScalarTy { kind := pk, layoutIdx := 0 } := by
      first
        | assumption
        | (rcases (by assumption : IsPrimScalarTy _) with h | h | ⟨i, h⟩ | ⟨u, h⟩
           · exact Or.inl h
           · exact Or.inr (Or.inl h)
           · exact Or.inr (Or.inr (Or.inl ⟨i, h⟩))
           · exact Or.inr (Or.inr (Or.inr ⟨u, h⟩)))) :
    ∃ accTy : Ty,
      placeTyResolved ld layouts ⟨refIdx, .cons .deref .nil⟩ = some accTy ∧
      accTy.kind = pk := by
  rcases refDecl with ⟨_, ⟨ptk, ptl⟩, _⟩
  dsimp only at hty
  subst hty
  unfold placeTyResolved
  dsimp only []
  rw [hdecl]
  unfold resolveProjectedTyResolved pointeeTyOf
  dsimp only []
  unfold findDeclOrContainerElemTyWithKind?
  cases hf1 : findDeclTyWithKind? ld pk with
  | some dTy =>
    dsimp only []
    exact ⟨dTy, rfl, findDeclTyWithKind?_prim_kind₂ hprim hf1⟩
  | none =>
    dsimp only []
    cases hf2 : findContainerElemTyWithKind? layouts ld pk with
    | some dTy =>
      dsimp only []
      exact ⟨dTy, rfl, findContainerElemTyWithKind?_kind₂ hf2⟩
    | none =>
      dsimp only []
      refine ⟨_, rfl, ?_⟩
      split
      · split <;> rfl
      · rfl

theorem StateRelLM3_2.alloc_target_init_scalar
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {e : AllocMapEntry} (he : e ∈ allocMap)
    (hne_dead : get? s.frame.locals e.localIdx ≠ some .dead)
    (hne_uninit : get? s.frame.locals e.localIdx ≠ some .uninit) :
    ∃ (tgtDecl : LocalDecl) (sc_t : MirAst.ScalarInt) (msc_t : Miri.Memory.ScalarInt),
      get? body.localDecls e.localIdx = some tgtDecl ∧
      IsPrimScalarTy tgtDecl.ty ∧
      get? s.frame.locals e.localIdx = some (.init (.scalar sc_t)) ∧
      (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat = sc_t.sizeBytes ∧
      (translateTy tgtDecl.ty body.layouts).layout.size = translateSizeBytes sc_t.sizeBytes ∧
      ScalarRel sc_t msc_t := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨tgtDecl, hdecl_tgt, htgt_prim⟩ := halloc.target_decl e he
  obtain ⟨slot_t, mls_t, _, _, hslot_t, hmls_t, _, hloc_t⟩ := hfr.lookup_local hdecl_tgt
  obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
  obtain ⟨hlive_e, _⟩ := halloc.local_alloc_sync tf hframes e he
  have ht_ne_dead : slot_t ≠ .dead := fun hd => hne_dead (hslot_t.trans (congrArg some hd))
  have ht_ne_uninit : slot_t ≠ .uninit := fun hu => hne_uninit (hslot_t.trans (congrArg some hu))
  obtain ⟨⟨lay_t, hlay_t⟩, hsc_t, hshape_f⟩ := hlive_e slot_t hslot_t ht_ne_dead
  obtain ⟨localAlloc, hfind_la, _, _, _⟩ := hshape_f tgtDecl hdecl_tgt
  obtain ⟨_, _, _, _, _, hnz_sz⟩ := htgt_prim.size_align_ok body.layouts
  rw [hlay_t] at hmls_t
  have hmls_t_eq' : mls_t = ⟨.live (.indirect (stackAllocPlace e.allocId)), lay_t⟩ :=
    Option.some.inj hmls_t.symm
  have hloc_t_1 : LocalRelLM3_1 m.machine allocMap tgtDecl body.layouts slot_t mls_t := by
    rw [hmls_t_eq'] at hloc_t ⊢
    exact hloc_t.indirect_base
  obtain ⟨_, hsc_la⟩ := hloc_t_1.indirect_stackAllocPlace_spec hmls_t_eq' hbase hfind_la
    (halloc.live_key_unique e he) hnz_sz
  cases hs_t : slot_t with
  | dead => exact absurd hs_t ht_ne_dead
  | uninit => exact absurd hs_t ht_ne_uninit
  | init v_t =>
    obtain ⟨sc_t, rfl⟩ := hsc_t v_t hs_t
    obtain ⟨hsz_t, _, _, msc_t, hrel_t, _⟩ := hsc_la sc_t hs_t
    have hsz_nat : (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat = sc_t.sizeBytes := by
      have hb := congrArg (fun sz => sz.bytes.toNat) hsz_t
      rw [hb]
      rcases hrel_t.validBytes with hv | hv | hv | hv | hv <;> (rw [hv]; decide)
    exact ⟨tgtDecl, sc_t, msc_t, hdecl_tgt, htgt_prim, hslot_t.trans (congrArg some hs_t),
      hsz_nat, hsz_t, hrel_t⟩

theorem resolveRefDerefTarget?_prim_scalar_zero
    (locals : List LocalSlot) {localDecls : List LocalDecl} {layouts : LayoutTable}
    (hlay_coh : PrimLayoutsCoherent layouts)
    {e : BorrowEntry} {ptrVal : ProvenancePtr} {accTy : Ty} {tgtDecl : LocalDecl}
    {sc_t : MirAst.ScalarInt}
    (hacc_prim : IsPrimScalarTy accTy)
    (hdecl_t : get? localDecls e.targetLocal = some tgtDecl)
    (hproj : e.targetProjection = .nil)
    (htgt_kind : tgtDecl.ty.kind = accTy.kind)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hsz_sc : (translateTy tgtDecl.ty layouts).layout.size.bytes.toNat = sc_t.sizeBytes) :
    resolveRefDerefTarget? locals (.scalar sc_t) e ptrVal .nil localDecls layouts
      (some accTy) (some accTy) false localDecls = .some (.some (.nil, 0)) := by
  cases hld : localDecls with
  | nil => rw [hld] at hdecl_t; cases hdecl_t
  | cons d₀ ds =>
    let ld := d₀ :: ds
    have hdecl_ld : get? ld e.targetLocal = some tgtDecl := by
      dsimp only [ld]; rw [← hld]; exact hdecl_t
    have halign1 : checkTargetPlaceAlign ld layouts (some accTy) e ptrVal (some (.scalar sc_t)) =
        true :=
      hacc_prim.checkTargetPlaceAlign_zero_nil ld hlay_coh hdecl_ld hproj htgt_kind hoff0
        (some (.scalar sc_t))
    have halign2 :
        checkTargetPlaceAlign ld layouts (some accTy)
          { e with targetProjection := .nil } { ptrVal with offsetBytes := 0 }
          (some (.scalar sc_t)) = true :=
      hacc_prim.checkTargetPlaceAlign_zero_nil ld hlay_coh hdecl_ld
        (e := { e with targetProjection := .nil }) (ptrVal := { ptrVal with offsetBytes := 0 })
        rfl htgt_kind rfl (some (.scalar sc_t))
    let rAccTy := resolveTyWithLocalDecls ld layouts accTy
    have hrAcc_kind : rAccTy.kind = accTy.kind := resolveTyWithLocalDecls_kind ld layouts accTy
    have hrAcc_prim : IsPrimScalarTy rAccTy := hacc_prim.of_kind_eq hrAcc_kind
    have htgt_prim : IsPrimScalarTy tgtDecl.ty := hacc_prim.of_kind_eq htgt_kind
    have htr_rAcc : translateTy rAccTy layouts = translateTy tgtDecl.ty layouts := by
      rw [← hrAcc_prim.translateTy_layoutIdx layouts, hrAcc_kind, ← htgt_kind,
        htgt_prim.translateTy_layoutIdx layouts]
    have hbs_rAcc : tyByteSize ld layouts rAccTy = some sc_t.sizeBytes := by
      rw [hrAcc_prim.tyByteSize_eq ld layouts, htr_rAcc, hsz_sc]
    have hts_rAcc : tyScalarBytes rAccTy = some sc_t.sizeBytes := by
      rw [(hrAcc_prim.tyScalarBytes_eq layouts).1, htr_rAcc, hsz_sc]
    have hres_proj :
        resolveStackThinPtrTargetProjWithResidual? locals (.scalar sc_t) e ptrVal .nil
          ld layouts (some accTy) (some sc_t.sizeBytes) = .some (.nil, 0) := by
      unfold resolveStackThinPtrTargetProjWithResidual?
      rw [hproj, hoff0]
      dsimp only [stripTransparentProjections, normalizeSubsliceProjections,
        normalizeAdjacentSubslices, endsWithSubslice, startsWithArrayOrSliceProj]
      have hpt_tgt : placeTyResolved ld layouts { local_ := e.targetLocal, projection := .nil } =
          some tgtDecl.ty := by
        unfold placeTyResolved resolveProjectedTyResolved
        rw [hdecl_ld]
      rw [hpt_tgt]
      rcases accTy with ⟨ak, ali⟩
      rcases hrt : tgtDecl.ty with ⟨rtk, rtli⟩
      rw [hrt] at htgt_kind
      dsimp only at htgt_kind
      subst htgt_kind
      rcases hacc_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> dsimp only at hk <;> subst hk <;>
        (dsimp only [readProjectedValue, projHasSubslice];
         cases tyScalarBytes { kind := _, layoutIdx := ali } <;> rfl)
    have hcore :
        resolveRefDerefTargetCore? locals (.scalar sc_t) e ptrVal .nil ld layouts
          (some accTy) (some accTy) false ld = .some (.some (.nil, 0)) := by
      unfold resolveRefDerefTargetCore?
      rw [hproj]
      dsimp only [ld]
      change (let resolvedAccTyOpt := some rAccTy; _) = _
      dsimp only []
      rw [hbs_rAcc]
      dsimp only []
      rw [hres_proj]
      dsimp only [readProjectedForLocal, readProjectedValue]
      rw [hts_rAcc]
      have hble : Nat.ble (Nat.add 0 sc_t.sizeBytes) sc_t.sizeBytes = true := by
        rw [Nat.add_eq, Nat.zero_add]
        exact Nat.ble_eq.mpr (Nat.le_refl _)
      have hrAcc_def : resolveTyWithLocalDecls (d₀ :: ds) layouts accTy = rAccTy := rfl
      rw [hrAcc_def]
      rcases rAccTy with ⟨rak, rali⟩
      rcases hrAcc_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> dsimp only at hk <;> subst hk <;>
      · cases placeTyResolved (d₀ :: ds) layouts { local_ := e.targetLocal, projection := .nil } <;>
          (dsimp only []; rw [hble])
    unfold resolveRefDerefTarget?
    rw [hproj]
    dsimp only []
    rw [halign1]
    dsimp only []
    rw [hcore]
    dsimp only [checkDerefAlign, Nat.beq]
    rw [halign2]
    rfl

/-- On a root borrow table without protectors (the borrow shape that
`StateRelLM3_2` maintains), Anneal's reborrow
`evalRvalue (.ref bk ⟨ptrIdx, [.deref]⟩)` through the pointer stored in
`ptrIdx`, whose tag belongs to entry `e`, succeeds whenever `e` is neither
`.disabled` nor a `.frozen` parent of a mutable reborrow and the pointee local
`e.localIdx` holds an initialized scalar of matching primitive type: the initial
child read through `e` is never undefined behavior (`hasTreeReadUB`), and the
step leaves the protector set empty. -/
theorem evalRvalue_reborrow_root_ok
    {s : MachineState} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {allocMap : List AllocMapEntry}
    (hnodup : (allocMap.map AllocMapEntry.tag).Nodup)
    (hbor : s.memory.borrows = allocMap.map AllocMapEntry.toBorrowEntry)
    (hprot : s.memory.activeProtectors = .nil)
    {bk : BorrowKind} {ptrIdx : Local} {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    (hsp : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hne_dis : e.perm ≠ .disabled) (hnot_fmut : ¬(e.perm = .frozen ∧ bk ≠ .shared))
    (hlay_coh : PrimLayoutsCoherent layouts)
    {accTy : Ty} {tgtDecl : LocalDecl} {sc_t : MirAst.ScalarInt}
    (hpt_res : placeTyResolved localDecls layouts ⟨ptrIdx, .cons .deref .nil⟩ = some accTy)
    (hacc_prim : IsPrimScalarTy accTy)
    (hdecl_t : get? localDecls e.localIdx = some tgtDecl)
    (htgt_kind : tgtDecl.ty.kind = accTy.kind)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hslot_t : get? s.frame.locals e.localIdx = some (.init (.scalar sc_t)))
    (hsz_sc : (translateTy tgtDecl.ty layouts).layout.size.bytes.toNat = sc_t.sizeBytes) :
    ∃ mem₁, evalRvalue s.frame.locals (.ref bk ⟨ptrIdx, .cons .deref .nil⟩) s.memory
        localDecls layouts =
      .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals mem₁ ∧
      mem₁.activeProtectors = .nil := by
  have hlookup : lookupBorrow s.memory.borrows ptrVal.tag = some e.toBorrowEntry := by
    rw [hbor, ← htag]
    exact lookupBorrow_map_toBorrowEntry_of_nodup hnodup he
  have hperm_tag : ∀ x ∈ allocMap, x.tag = ptrVal.tag → x.perm ≠ .disabled := by
    rw [← htag]
    exact perm_ne_disabled_of_tag_eq_of_nodup hnodup he hne_dis
  have hrd : hasTreeReadUB s.memory.borrows s.memory.borrows s.memory.activeProtectors
      e.localIdx (some ptrVal.tag) .nil 0 0 = false := by
    rw [hprot, hbor]
    exact hasTreeReadUB_map_toBorrowEntry_eq_false allocMap allocMap e.localIdx ptrVal.tag
      hperm_tag
  have hnf : e.perm = .frozen → bk = .shared := fun hfz => by
    rcases hbk : bk with _ | _
    · rfl
    · exact absurd ⟨hfz, by rw [hbk]; exact fun h => BorrowKind.noConfusion h⟩ hnot_fmut
  have hcda : checkDerefAlign localDecls layouts (some accTy) ptrVal.offsetBytes = true := by
    rw [hoff0]
  have hres_tgt :
      resolveRefDerefTarget? s.frame.locals (.scalar sc_t) e.toBorrowEntry ptrVal .nil
        localDecls layouts (some accTy) (some accTy) false localDecls =
        .some (.some (.nil, 0)) :=
    resolveRefDerefTarget?_prim_scalar_zero s.frame.locals hlay_coh hacc_prim hdecl_t rfl
      htgt_kind hoff0 hsz_sc
  have htl : e.toBorrowEntry.targetLocal = e.localIdx := rfl
  have hro : e.toBorrowEntry.rangeOffset = 0 := rfl
  have hrl : e.toBorrowEntry.rangeLen = 0 := rfl
  have hperm_eq : e.toBorrowEntry.perm = e.perm := rfl
  unfold evalRvalue evalRvalueRefDeref
  dsimp only [stripTransparentProjections]
  rw [hlay_coh.1, hpt_res, hsp]
  dsimp only [Nat.beq]
  rw [hcda, Bool.true_and, hlookup]
  dsimp only []
  rw [htl, hslot_t]
  dsimp only []
  rw [hro, hrl, hperm_eq, hres_tgt]
  dsimp only [resolveBorrowProjectionElems]
  cases hp : e.perm <;> rcases hm : bk with _ | ⟨_ | _⟩
  all_goals first
    | exact absurd hp hne_dis
    | exact BorrowKind.noConfusion (hm.symm.trans (hnf hp))
    | (dsimp only [];
       cases hb : s.memory.borrows with
       | nil => exact ⟨_, rfl, hprot⟩
       | cons b₁ rest =>
         cases rest with
         | nil => exact ⟨_, rfl, hprot⟩
         | cons b₂ rest' =>
           dsimp only []
           have hrd' :
               hasTreeReadUB (b₁ :: b₂ :: rest') (b₁ :: b₂ :: rest') s.memory.activeProtectors
                 e.localIdx (some ptrVal.tag) .nil 0 0 = false := hb ▸ hrd
           rw [hrd']
           cases (sharedBorrowPerm localDecls layouts ⟨ptrIdx, .cons .deref .nil⟩) <;>
             cases (mutableBorrowPerm localDecls layouts ⟨ptrIdx, .cons .deref .nil⟩) <;>
             cases (placeIsZeroSized localDecls layouts ⟨ptrIdx, .cons .deref .nil⟩) <;>
             exact ⟨_, rfl, hprot⟩)

/-- **`evalRvalue_reborrow_simulation` (`LM-3.2`)**: from any `StateRelLM3_2`
state in which `_p : *(const|mut) T` (`T` primitive scalar) is immediate and
not integer-valued, and every pointer it may hold targets a live initialized
local of type `T` at offset `0` with a parent borrow that permits the reborrow
(not `.disabled`, and not `.frozen` for a mutable reborrow), the reborrow
`_d = &*_p` / `_d = &mut *_p` into an immediate safe-reference local `_d`:

1. reports undefined behavior in Anneal's `stepMirFn` exactly when
   `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) does (a dead
   or uninitialized `_p`, or a dead `_d`); and
2. otherwise steps in both machines, Anneal writing the fresh child borrow
   `nextTag` at offset `0` into `_d` and `lean-miri` writing a reference to
   the same stack allocation `e.allocId` that `_p` points into.

Boundary (excluded by `hzero_perm`, not covered here): on the Stage-1 repaired
semantics Anneal's reborrow requires the pointee local to be `.init`
(`evalRvalue`, `targetRootAndDeclsOpt`), so reborrowing through a pointer into
an `.uninit` local is undefined behavior in Anneal, whereas `lean-miri`'s
shallow reference validity (before `LM-3.3` retags) does not require an
initialized pointee. -/
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
      get? s.frame.locals e.localIdx ≠ some .dead ∧
      get? s.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind))
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
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
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, hbor, halloc, _⟩ := id hstate
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
  obtain ⟨accTy, hpt_res, hacc_kind⟩ :=
    placeTyResolved_deref_rawPtr_prim hpk_prim hdecl_ptr hptr_ty
  have hacc_prim : IsPrimScalarTy accTy := hpk_prim.of_kind_eq hacc_kind
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
        unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []; rw [hslot_pa, hsp_dead]
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
        unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []; rw [hslot_pa, hsp_un]
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
      obtain ⟨hlive_t, hun_t, hoff0, hne_dis, hnot_fmut, htgt_kind⟩ :=
        hzero_perm ptrVal e hsp_full he htag
      obtain ⟨tgtDecl, sc_t, _, hdecl_t, _, hslot_t, hsz_sc, _, _⟩ :=
        hstate.alloc_target_init_scalar he hlive_t hun_t
      have hrv_a_ok : ∃ mem₁, evalRvalue s.frame.locals
          (.ref bk ⟨ptrIdx, .cons .deref .nil⟩) s.memory body.localDecls body.layouts =
          .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals mem₁ ∧
          mem₁.activeProtectors = .nil :=
        evalRvalue_reborrow_root_ok halloc.tags_nodup hbor hprot hsp_full he htag hne_dis
          hnot_fmut hlay_coh hpt_res hacc_prim hdecl_t
          ((htgt_kind tgtDecl hdecl_t).trans hacc_kind.symm) hoff0 hslot_t hsz_sc
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
      obtain ⟨hlive_t, hun_t, hoff0, hne_dis, hnot_fmut, htgt_kind⟩ :=
        hzero_perm ptrVal e hsp he htag
      obtain ⟨tgtDecl, sc_t, _, hdecl_t, _, hslot_t, hsz_sc, _, _⟩ :=
        hstate.alloc_target_init_scalar he hlive_t hun_t
      have hrv_ok' : ∃ mem₁, evalRvalue s.frame.locals
          (.ref bk ⟨ptrIdx, .cons .deref .nil⟩) s.memory body.localDecls body.layouts =
          .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals mem₁ ∧
          mem₁.activeProtectors = .nil :=
        evalRvalue_reborrow_root_ok halloc.tags_nodup hbor hprot hsp he htag hne_dis hnot_fmut
          hlay_coh hpt_res hacc_prim hdecl_t
          ((htgt_kind tgtDecl hdecl_t).trans hacc_kind.symm) hoff0 hslot_t hsz_sc
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

private theorem miri_reborrow_rawPtr_step_ok
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
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
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag) :
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧ m'.machine = m.machine ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
              .concrete e.allocId borTag⟩)))) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨himm_d, himm_p⟩ := himm tf hframes
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
      hbb hstmt hm_ok rfl hfrb.location_eq, rfl, rfl, ?_⟩
    rw [hmptr_eq]
    simp [Array.getElem?_set_self]

/-- **`evalRvalue_reborrow_dangling_divergence` (`LM-3.2`)**:
when the raw pointer `_p` points into a local that `StorageDead` has already
killed (its `lean-miri` allocation is freed), the reborrow `_d = &*_p` /
`_d = &mut *_p` is rejected with `MirStepNode.fail .ub` in Anneal's
`stepMirFn` (`evalRvalueRefDeref` checks `get? locals parentEntry.targetLocal`),
matching `lean-miri`'s validity visitor (`annealValidityAccessCheck`) and eager
safe-reference dereference check (`annealSafeRefDerefCheck`) on the reference
that `Miri.Interpreter.Step.step` (`annealStepHooks`) writes. -/
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
    stepMirFn body s = MirStepNode.fail .ub ∧
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
  have _ := hno_int
  obtain ⟨tf, hframes, _, _, _, hcal, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨hoff0, _, _⟩ := hzero_perm ptrVal e hslot_p he htag
  have ha : stepMirFn body s = MirStepNode.fail .ub := by
    have hlookup := (halloc.borrow_sync e he).2
    rw [htag] at hlookup
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []
    rw [hslot_p]; dsimp only []
    cases Bool.and (Nat.beq 8 (layoutPointerBytes body.layouts))
        (checkDerefAlign body.localDecls body.layouts _ ptrVal.offsetBytes)
    · rfl
    · dsimp only []
      rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry, resolveBorrowProjectionElems]
      rw [hdead_t]
      cases e.perm <;> cases bk <;> rfl
  obtain ⟨m', tf', borTag, hstep, hframes', hmach, hval⟩ :=
    miri_reborrow_rawPtr_step_ok hstate hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpk_prim
      himm hdst_live hslot_p he htag
  have h0_off : annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes =
      annealStackBaseAddr e.allocId := by
    rw [hoff0]; simp
  rw [h0_off] at hval
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

/-- **`evalRvalue_reborrow_uninit_target_divergence` (`LM-3.2` Stage-1
Uninitialized-Target Reborrow Divergence)**:
when `_p` holds a `StateRelLM3_2`-related raw pointer `.ptr ptrVal 8` whose
target local `e.localIdx` is live but uninitialized (`get? s.frame.locals e.localIdx = some .uninit`,
e.g. after `StorageLive(_x); _p = &raw mut _x`), and `e.perm` permits `bk`,
reborrowing `_d = &*_p` / `_d = &mut *_p` diverges:
1. Anneal's `stepMirFn` rejects the reborrow with `MirStepNode.fail .ub`
   (`evalRvalueRefDeref` requires `targetRootAndDeclsOpt = some (v, ...)` with
   `get? locals parentEntry.targetLocal = some (.init v)`); while
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) steps normally
   to `(m', .ok true)` and writes a reference whose stack allocation is live and
   dereferenceable (`annealValidityAccessCheck = .ok ()`), because safe-reference
   creation in Miri checks allocation liveness, bounds, and alignment rather than
   pointee byte initialization (when `T` is inhabited). -/
theorem evalRvalue_reborrow_uninit_target_divergence
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
    (huninit_t : get? s.frame.locals e.localIdx = some .uninit)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    {targetDecl : LocalDecl} (hdecl_t : get? body.localDecls e.localIdx = some targetDecl) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              .concrete e.allocId borTag⟩)))) ∧
      annealValidityAccessCheck m'.machine
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId), some (.concrete e.allocId borTag)⟩
        (translateTy targetDecl.ty body.layouts).layout.size = .ok () := by
  have _ := hno_int
  obtain ⟨tf, hframes, _, _, _, hcal, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨hoff0, _, _⟩ := hzero_perm ptrVal e hslot_p he htag
  have ha : stepMirFn body s = MirStepNode.fail .ub := by
    have hlookup := (halloc.borrow_sync e he).2
    rw [htag] at hlookup
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []
    rw [hslot_p]; dsimp only []
    cases Bool.and (Nat.beq 8 (layoutPointerBytes body.layouts))
        (checkDerefAlign body.localDecls body.layouts _ ptrVal.offsetBytes)
    · rfl
    · dsimp only []
      rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry, resolveBorrowProjectionElems]
      rw [huninit_t]
      cases e.perm <;> cases bk <;> rfl
  obtain ⟨m', tf', borTag, hstep, hframes', hmach, hval⟩ :=
    miri_reborrow_rawPtr_step_ok hstate hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpk_prim
      himm hdst_live hslot_p he htag
  have h0_off : annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes =
      annealStackBaseAddr e.allocId := by
    rw [hoff0]; simp
  rw [h0_off] at hval
  refine ⟨ha, m', tf', borTag, hstep, hframes', hval, ?_⟩
  rw [hmach]
  obtain ⟨d, hd, hprim⟩ := halloc.target_decl e he
  rw [hdecl_t] at hd
  cases hd
  obtain ⟨hsize, hpos, hfit, _, _, _⟩ := hprim.size_align_ok body.layouts
  obtain ⟨hid, _, hbase⟩ := halloc.base_addr_valid e he
  obtain ⟨_, _, hsh⟩ := (halloc.local_alloc_sync tf hframes e he).1 .uninit huninit_t (by decide)
  obtain ⟨localAlloc, hfind, _, _, hshape⟩ := hsh targetDecl hdecl_t
  have hinb : 0 + (translateTy targetDecl.ty body.layouts).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat := by
    rw [Nat.zero_add, hshape.byteSize_eq]
    exact Nat.le_refl _
  have hacc := (annealValidityAccessCheck_stack m.machine e.allocId borTag 0
    (translateTy targetDecl.ty body.layouts).layout.size hid (by decide) hbase hsize
    (by exact_mod_cast hpos) hfit).1 localAlloc hfind hinb
  have h0 : annealStackBaseAddr e.allocId + UInt64.ofNat 0 = annealStackBaseAddr e.allocId := by
    simp
  rw [h0] at hacc
  exact hacc


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
  obtain ⟨_, _, _, _, _, hcal, _, _, _, _, halloc, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · have hlookup := (halloc.borrow_sync e he).2
    rw [htag] at hlookup
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []
    rw [hslot_p]; dsimp only []
    cases Bool.and (Nat.beq 8 (layoutPointerBytes body.layouts))
        (checkDerefAlign body.localDecls body.layouts _ ptrVal.offsetBytes)
    · rfl
    · dsimp only []
      rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry]
      rcases hperm with hp | ⟨hp, hm⟩
      · rw [hp]
      · rw [hp]
        rcases bk with _ | _
        · exact absurd rfl hm
        · rfl
  · obtain ⟨m', tf', borTag, hstep, hframes', _, hval⟩ :=
      miri_reborrow_rawPtr_step_ok hstate hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpk_prim
        himm hdst_live hslot_p he htag
    exact ⟨m', tf', borTag, hstep, hframes', hval⟩

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
    unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []
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
   `lean-miri`.

Boundary (excluded by `hlive_zero_perm`, not covered here): on the Stage-1
repaired semantics Anneal's reborrow requires the pointee local to be `.init`,
so reborrowing through a reference into an `.uninit` local is undefined behavior
in Anneal, whereas `lean-miri`'s shallow reference validity (before `LM-3.3`
retags) does not require an initialized pointee. -/
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
      get? s.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind))
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
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
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, hbor, halloc, _⟩ := id hstate
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
        unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []; rw [hslot_ra, hsr_dead]
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
        unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []; rw [hslot_ra, hsr_un]
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
        unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []; rw [hslot_ra, hsr_sc]
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
      obtain ⟨hlive_t, hun_t, hoff0, hne_dis, hnot_fmut, htgt_kind⟩ :=
        hlive_zero_perm ptrVal e hsr_full he htag
      obtain ⟨tgtDecl, sc_t, _, hdecl_t, _, hslot_t, hsz_sc, _⟩ :=
        hstate.alloc_target_init_scalar he hlive_t hun_t
      obtain ⟨accTy, hpt_res, hacc_kind⟩ :=
        placeTyResolved_deref_safeRef_prim (layouts := body.layouts) hdecl_ref href_ty
      have hacc_prim : IsPrimScalarTy accTy := hpk_prim.of_kind_eq hacc_kind
      have hrv_a_ok : ∃ mem₁, evalRvalue s.frame.locals
          (.ref bk ⟨refIdx, .cons .deref .nil⟩) s.memory body.localDecls body.layouts =
          .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals mem₁ ∧
          mem₁.activeProtectors = .nil :=
        evalRvalue_reborrow_root_ok halloc.tags_nodup hbor hprot hsr_full he htag hne_dis
          hnot_fmut hlay_coh hpt_res hacc_prim hdecl_t ((htgt_kind tgtDecl hdecl_t).trans hacc_kind.symm)
          hoff0 hslot_t hsz_sc
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
      obtain ⟨hlive_t, hun_t, hoff0, hne_dis, hnot_fmut, htgt_kind⟩ :=
        hlive_zero_perm ptrVal e hsr he htag
      obtain ⟨tgtDecl, sc_t, _, hdecl_t, _, hslot_t, hsz_sc, _⟩ :=
        hstate.alloc_target_init_scalar he hlive_t hun_t
      obtain ⟨accTy, hpt_res, hacc_kind⟩ :=
        placeTyResolved_deref_safeRef_prim (layouts := body.layouts) hdecl_ref href_ty
      have hacc_prim : IsPrimScalarTy accTy := hpk_prim.of_kind_eq hacc_kind
      have hrv_ok' : ∃ mem₁, evalRvalue s.frame.locals
          (.ref bk ⟨refIdx, .cons .deref .nil⟩) s.memory body.localDecls body.layouts =
          .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals mem₁ ∧
          mem₁.activeProtectors = .nil :=
        evalRvalue_reborrow_root_ok halloc.tags_nodup hbor hprot hsr he htag hne_dis hnot_fmut
          hlay_coh hpt_res hacc_prim hdecl_t ((htgt_kind tgtDecl hdecl_t).trans hacc_kind.symm)
          hoff0 hslot_t hsz_sc
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

/-- Both-UB core of `evalRvalue_reborrow_safeRef_dangling_simulation`: Anneal's `stepMirFn` fails with `.ub` and
`lean-miri`'s `Miri.Interpreter.Step.step` reports the stated
`StepError.undefinedBehavior`. -/
private theorem evalRvalue_reborrow_safeRef_dangling_both_ub
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
    (_hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hdead_t : get? s.frame.locals e.localIdx = some .dead) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing a dangling reference")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, hbor, halloc, _⟩ := id hstate
  have himm_r := himm_ref tf hframes
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  refine ⟨?_, ?_⟩
  · have hlookup : lookupBorrow s.memory.borrows ptrVal.tag = some e.toBorrowEntry := by
      rw [hbor, ← htag]
      exact lookupBorrow_map_toBorrowEntry_of_nodup halloc.tags_nodup he
    have htl : e.toBorrowEntry.targetLocal = e.localIdx := rfl
    have htp : e.toBorrowEntry.targetProjection = .nil := rfl
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []
    rw [hslot_r]; dsimp only []
    cases Bool.and (Nat.beq 8 (layoutPointerBytes body.layouts))
        (checkDerefAlign body.localDecls body.layouts _ ptrVal.offsetBytes)
    · rfl
    · dsimp only []
      rw [hlookup]
      dsimp only []
      rw [htl, hdead_t]
      dsimp only []
      cases e.toBorrowEntry.perm <;>
      · first | rfl | (cases bk <;> rfl)
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

/-- **`evalRvalue_reborrow_safeRef_dangling_simulation` (`LM-3.2`, upgraded to UB simulation)**:
when a safe reference `_r : &(mut) T` (`T` primitive scalar) points into a local
`e.localIdx` that `StorageDead` has already killed, reborrowing `_d = &*_r` /
`_d = &mut *_r` into a live destination local `_d` raises undefined behavior in
BOTH `stepMirFn` (`MirStepNode.fail .ub` via `resolveRefDerefTarget?`) and
`Miri.Interpreter.Step.step` (`annealStepHooks`,
`"dereferencing a dangling reference"`). -/
theorem evalRvalue_reborrow_safeRef_dangling_simulation
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
    (_hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hdead_t : get? s.frame.locals e.localIdx = some .dead) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing a dangling reference")) := by
  obtain ⟨ha, m', hm⟩ := evalRvalue_reborrow_safeRef_dangling_both_ub hstate hphase hbb hstmt hdecl_dst hdecl_ref href_ty hpk_prim himm_ref _hdst_live hslot_r he htag hdead_t
  exact ⟨by rw [ha, hm]; exact .ub m' _, ha, m', hm⟩

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

private theorem validateLoadedValue_ref_local_eq_true
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcIdx : Local} {srcDecl : LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl_src : get? localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .ref mutability pointeeKind)
    {opKind : Place → MirAst.Operand}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (v : Value) :
    validateLoadedValue layouts localDecls (opKind ⟨srcIdx, .nil⟩) v = true := by
  rcases hopKind with rfl | rfl <;>
  · unfold validateLoadedValue operandTy placeTy
    dsimp only []
    rw [hdecl_src]
    dsimp only [resolveProjectedTy]
    rcases srcDecl with ⟨_, ⟨sk, sli⟩, _⟩
    dsimp only at hsrc_ty
    subst hsrc_ty
    rfl

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
        unfold evalRvalue evalOperand readProjectedValue; dsimp only []
        rw [hslot_s, hss_sc]
        dsimp only []
        rw [validateLoadedValue_ref_local_eq_true hdecl_src hsrc_ty (Or.inl rfl)]
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
        dsimp only []
        rw [validateLoadedValue_ref_local_eq_true hdecl_src hsrc_ty (Or.inr rfl)]
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
        unfold evalRvalue evalOperand readProjectedValue; dsimp only []
        rw [hslot_s, hss_ptr]
        dsimp only []
        rw [validateLoadedValue_ref_local_eq_true hdecl_src hsrc_ty (Or.inl rfl)]
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
        dsimp only []
        rw [validateLoadedValue_ref_local_eq_true hdecl_src hsrc_ty (Or.inr rfl)]
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

theorem annealReadImmediate_indirect_prim_eq₂
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

/-- Dereferencing a `PtrRel`-related safe-reference local `_r : &(mut) T` at
offset `0` into a live pointee local `e.localIdx` whose stack allocation size
matches `sizeof(T)` succeeds in `annealDerefOperandToMemPlace` even when
`allocDecl.ty.kind ≠ T` (e.g. a transmuted `&bool` pointing at a `u8` local). -/
theorem annealDerefOperandToMemPlace_safeRef_ptr_same_size
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {refIdx : Local} {refDecl allocDecl : LocalDecl}
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
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (hlive_t : get? s.frame.locals e.localIdx ≠ some .dead)
    (hsize : (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size =
      (translateTy allocDecl.ty body.layouts).layout.size)
    (ptrLay : Miri.Interpreter.LocalLayout)
    {st : AnnealStepState} (hmach : st.machine = m.machine) :
    annealDerefOperandToMemPlace body.localDecls body.layouts refIdx
        (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))
        ptrLay st =
      .ok (⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
            some (.concrete e.allocId borTag)⟩, .none, none⟩,
        translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts) st := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨slot_t, _, _, _, hslot_t, _, _, _⟩ := hfr.lookup_local hdecl_a
  have ht_ne_dead : slot_t ≠ .dead := fun hd => hlive_t (hslot_t.trans (congrArg some hd))
  obtain ⟨_, _, hshape_fn⟩ := (halloc.local_alloc_sync tf hframes e he).1 slot_t hslot_t ht_ne_dead
  obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hshape_fn allocDecl hdecl_a
  obtain ⟨hid_lt, _, hbase⟩ := halloc.base_addr_valid e he
  obtain ⟨hsz, hpos, hfit, _, hpow, _⟩ := hpk.size_align_ok body.layouts
  have hinbounds : 0 +
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat := by
    rw [Nat.zero_add, hshape_la.byteSize_eq, hsize]
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

/-- Both-UB core of `step_safeRef_deref_read_invalid_scalar_simulation`: Anneal's `stepMirFn` fails with `.ub` and
`lean-miri`'s `Miri.Interpreter.Step.step` reports the stated
`StepError.undefinedBehavior`. -/
private theorem step_safeRef_deref_read_invalid_scalar_both_ub
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
    {dstDecl refDecl allocDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hoff0 : ptrVal.offsetBytes = 0)
    (_hperm : e.perm ≠ .disabled)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hsize : (translateTy dstDecl.ty body.layouts).layout.size =
      (translateTy allocDecl.ty body.layouts).layout.size)
    (hinvalid : ¬ AnnealScalarValid dstDecl.ty sc)
    (_hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "reading invalid value")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, halloc, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · have hlookup : lookupBorrow s.memory.borrows ptrVal.tag = some e.toBorrowEntry := by
      rw [← htag]; exact (halloc.borrow_sync e he).2
    obtain ⟨tgtDecl, sc_t, msc_t, hdecl_t, _, hslot_t, _, hsz_t, hrel_t⟩ :=
      hstate.alloc_target_init_scalar he (by rw [htarget]; simp) (by rw [htarget]; simp)
    have htgt_eq : tgtDecl = allocDecl := Option.some.inj (hdecl_t.symm.trans hdecl_a)
    have hsc_eq : sc_t = sc := by
      have h := Option.some.inj (hslot_t.symm.trans htarget)
      injection h with h'; injection h'
    subst htgt_eq; subst sc_t
    have hsz_dst : (translateTy dstDecl.ty body.layouts).layout.size =
        translateSizeBytes sc.sizeBytes :=
      hsize.trans hsz_t
    obtain ⟨accTy, hpt_res, hacc_kind⟩ :=
      placeTyResolved_deref_safeRef_prim (layouts := body.layouts) hdecl_ref href_ty
    let rAccTy := resolveTyWithLocalDecls body.localDecls body.layouts accTy
    have hrAcc_kind : rAccTy.kind = dstDecl.ty.kind :=
      (resolveTyWithLocalDecls_kind body.localDecls body.layouts accTy).trans hacc_kind
    have hrAcc_prim : IsPrimScalarTy rAccTy := hdst_prim.of_kind_eq hrAcc_kind
    have hts_r : tyScalarBytes rAccTy = some sc.sizeBytes := by
      rw [IsPrimScalarTy.tyScalarBytes_eq hrAcc_prim body.layouts |>.1,
        ← hrAcc_prim.translateTy_layoutIdx body.layouts, hrAcc_kind,
        hdst_prim.translateTy_layoutIdx body.layouts, hsz_dst]
      rcases hrel_t.validBytes with h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> rfl
    have hex_sc : extractScalarSlice? sc 0 sc.sizeBytes = some sc := by
      unfold extractScalarSlice?
      rcases hrel_t.validBytes with h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> rfl
    have hvf_sc : validateValueForTy? body.layouts (some rAccTy) (.scalar sc) = false := by
      rcases rAccTy with ⟨rak, rali⟩
      dsimp only at hrAcc_kind
      cases hvf : validateValueForTy? body.layouts (some ⟨rak, rali⟩) (.scalar sc) with
      | false => rfl
      | true =>
        exfalso; apply hinvalid
        refine ⟨fun hb => ?_, fun hc => ?_⟩
        · have hrak : rak = .bool := hrAcc_kind.trans hb
          subst hrak
          unfold validateValueForTy? at hvf; dsimp only [] at hvf
          have hble : Nat.ble sc.bits 1 = true := (Bool.and_eq_true _ _).mp hvf |>.2
          have hle : sc.bits ≤ 1 := Nat.le_of_ble_eq_true hble
          omega
        · have hrak : rak = .char := hrAcc_kind.trans hc
          subst hrak
          unfold validateValueForTy? at hvf; dsimp only [] at hvf
          exact (Bool.and_eq_true _ _).mp hvf |>.2
    have hop_ub : evalOperand s.frame.locals (opKind ⟨refIdx, .cons .deref .nil⟩)
        s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals body.localDecls =
        .ub := by
      cases hld : body.localDecls with
      | nil => rw [hld] at hdecl_ref; cases hdecl_ref
      | cons d₀ ds =>
        have hd_eq : body.localDecls = d₀ :: ds := hld
        have htl : e.toBorrowEntry.targetLocal = e.localIdx := rfl
        have htp : e.toBorrowEntry.targetProjection = .nil := rfl
        have hperm_eq : e.toBorrowEntry.perm = e.perm := rfl
        have hbody : evalStackThinPtrTypedDerefRead s.frame.locals (.scalar sc) e.toBorrowEntry
            ptrVal .nil body.localDecls body.layouts (some accTy) (some accTy)
            (placeTyResolved body.localDecls body.layouts
              { local_ := e.toBorrowEntry.targetLocal,
                projection := e.toBorrowEntry.targetProjection }) = .ub := by
          unfold evalStackThinPtrTypedDerefRead
          rw [htp, htl]
          dsimp only [stripTransparentProjections]
          change (let resolvedAccTyOpt := some rAccTy; _) = _
          dsimp only []
          cases Bool.and
            (checkDerefAlign body.localDecls body.layouts _ ptrVal.offsetBytes)
            (checkTargetPlaceAlign body.localDecls body.layouts _ e.toBorrowEntry ptrVal
              (some (.scalar sc)))
          · rfl
          · dsimp only [readProjectedForLocal, readProjectedValue]
            rw [hts_r, hoff0]
            dsimp only []
            rw [hex_sc]
            dsimp only []
            rw [hvf_sc]
        rcases hopKind with rfl | rfl <;>
        · unfold evalOperand
          dsimp only []
          rw [← hd_eq]
          rw [hpt_res, hslot_r]
          dsimp only []
          rw [hlookup]
          dsimp only []
          rw [htl, htarget, hperm_eq]
          cases e.perm <;> first | rfl | exact hbody
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue; dsimp only []; rw [hop_ub]
  · have himm_r := himm_ref tf hframes
    have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
      ⟨dstIdx, .nil⟩ (opKind ⟨refIdx, .cons .deref .nil⟩) span m
    obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
    have hfra := hstate_a.frame_rel_singleton rfl
    obtain ⟨slot_r, mls_r, _, hlt_ra, hslot_r', hmls_r, hmls_r_eq, hloc_r⟩ :=
      hfra.lookup_local hdecl_ref
    have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
      hloc_r.cachedLayout_eq
    have himm_ra : ∀ mp, mls_r.value ≠ .live (.indirect mp) :=
      himm_r.cache_layout hlt_d _ mls_r hmls_r
    have hsr_eq : slot_r = .init (.ptr ptrVal 8) :=
      Option.some.inj (hslot_r'.symm.trans hslot_r)
    rcases hloc_r.ref_immediate_cases href_ty himm_ra with
      ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨_, _, hs, _⟩ | ⟨ptrVal', mptr, hs, hptrRel, hmr_ptr⟩
    · rw [hsr_eq] at hs; cases hs
    · rw [hsr_eq] at hs; cases hs
    · rw [hsr_eq] at hs; cases hs
    · rw [hsr_eq] at hs; injection hs with hv; injection hv with hp_eq _; subst hp_eq
      obtain ⟨_, borTag, hprov_eq, _, _, hmptr_off, ⟨e', he', htag', rfl⟩⟩ := hptrRel
      have he_eq : e' = e :=
        Option.some.inj ((lookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he' htag').symm.trans
          (lookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he htag))
      subst he_eq
      have hmls_r' : tfa.locals[refIdx]'hlt_ra =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_r.layout⟩ := by
        rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
      let tfb := cacheFrameLocalLayout tfa refIdx hlt_ra (translateTy refDecl.ty body.layouts)
      have hop_ptr : annealEvalOperand body.localDecls body.layouts
          (translateOperand (opKind ⟨refIdx, .cons .deref .nil⟩))
          (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
          (annealDerefOperandToMemPlace body.localDecls body.layouts refIdx
            (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))
            (translateTy refDecl.ty body.layouts) >>= fun (mp, lay) => pure ⟨.indirect mp, lay⟩)
            { m with stack := ⟨#[tfb]⟩ } := by
        rcases hopKind with rfl | rfl
        · exact annealEvalOperand_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
            (Or.inl rfl) rfl hlt_ra hdecl_ref hmls_r' hcache_r
        · exact annealEvalOperand_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
            (Or.inr rfl) rfl hlt_ra hdecl_ref hmls_r' hcache_r
      have hprim0 : IsPrimScalarTy { kind := dstDecl.ty.kind, layoutIdx := 0 } := by
        rcases hdst_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
        · exact Or.inl hk
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr (Or.inl ⟨it, hk⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨ut, hk⟩))
      have hlay0_eq : translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts =
          translateTy dstDecl.ty body.layouts :=
        hdst_prim.translateTy_layoutIdx body.layouts
      have ht_ne_some_dead : get? s.frame.locals e'.localIdx ≠ some .dead := by
        rw [htarget]; simp
      have hsize0 :
          (translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts).layout.size =
            (translateTy allocDecl.ty body.layouts).layout.size := by
        rw [hlay0_eq]; exact hsize
      have hder_ok := annealDerefOperandToMemPlace_safeRef_ptr_same_size hstate_a hdecl_ref
        href_ty hprim0 hprov_eq hmptr_off he' hoff0 hdecl_a ht_ne_some_dead hsize0
        (translateTy refDecl.ty body.layouts) (st := { m with stack := ⟨#[tfb]⟩ }) rfl
      rw [hlay0_eq] at hder_ok
      have hop_ok : annealEvalOperand body.localDecls body.layouts
          (translateOperand (opKind ⟨refIdx, .cons .deref .nil⟩))
          (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId),
              some (.concrete e'.allocId borTag)⟩, .none, none⟩,
            translateTy dstDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } := by
        rw [hop_ptr, EStateM.bind_eq_ok hder_ok]; rfl
      obtain ⟨hid_a, _, hbase_a'⟩ := halloc.base_addr_valid e' he'
      obtain ⟨hloc_sync, _⟩ := halloc.local_alloc_sync tf hframes e' he'
      obtain ⟨⟨lay_a, hlay_a⟩, _, hfind_decl⟩ :=
        hloc_sync (.init (.scalar sc)) htarget (by simp)
      obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hfind_decl allocDecl hdecl_a
      have hsz_eq : localAlloc.allocation.byteSize =
          (translateTy dstDecl.ty body.layouts).layout.size :=
        hshape_la.byteSize_eq.trans hsize.symm
      obtain ⟨slot_t, mls_t, _, _, hs_slot_t, hmls_t_opt, _, hloc_t⟩ :=
        hfr.lookup_local hdecl_a
      have hslot_t_eq : slot_t = .init (.scalar sc) :=
        Option.some.inj (hs_slot_t.symm.trans htarget)
      subst hslot_t_eq
      rw [hlay_a] at hmls_t_opt
      have hmls_t_eq : mls_t = ⟨.live (.indirect (stackAllocPlace e'.allocId)), lay_a⟩ :=
        Option.some.inj hmls_t_opt.symm
      have hloc_t_1 :
          LocalRelLM3_1 m.machine allocMap allocDecl body.layouts (.init (.scalar sc)) mls_t := by
        rw [hmls_t_eq] at hloc_t ⊢
        exact hloc_t.indirect_base
      have hmm := LocalRelLM3_1.indirect_stackAllocPlace_spec hloc_t_1 hmls_t_eq hbase_a'
        hfind_la (halloc.live_key_unique e' he') (hsize ▸ hdst_prim.size_ne_zero)
      obtain ⟨hsz_msc, _, _, msc, hsc_rel, hread_msc⟩ := hmm.2 sc rfl
      have hread_msc' :
          localAlloc.allocation.readScalar annealTargetDataLayout
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO
              (translateTy dstDecl.ty body.layouts).layout.size) false =
            .ok (.fromScalarInt msc) := by
        rw [hsize]; exact hread_msc
      have hread_mem_eq := annealReadMemoryPlace_zero_offset_eq hdst_prim hid_a hbase_a'
        hfind_la hsz_eq (borTag := borTag) (st := { m with stack := ⟨#[tfb]⟩ })
      have hval_false := annealValidateScalarForTyId_false_of_not_scalarValid body.layouts
        hsc_rel (hsize.trans hsz_msc) hinvalid
      have hread_err : annealReadImmediate
          ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId),
            some (.concrete e'.allocId borTag)⟩, .none, none⟩,
            translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } =
          .error (.undefinedBehavior "reading invalid value") { m with stack := ⟨#[tfb]⟩ } := by
        rw [annealReadImmediate_indirect_prim_eq₂ hdst_prim, hread_mem_eq, hread_msc']
        dsimp only []
        rw [hval_false]
        rfl
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt
            ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ },
            .error (.undefinedBehavior "reading invalid value")) := by
        have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
        rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_ok,
          EStateM.bind_eq_error hread_err]
      exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb
        hstmt hm_err⟩

/-- **`step_safeRef_deref_read_invalid_scalar_simulation` (`LM-3.2` Safe-Reference Deref Read Invalid Scalar, upgraded to UB simulation)**:
from any `StateRelLM3_2` state where `_r : &(mut) T` (`T` primitive scalar, e.g.
`bool` or `char`) points at offset `0` with non-disabled permission to a live
stack local `e.localIdx` of equal byte size (e.g. `u8` holding `2` or `u32`
holding `0xD800`) whose scalar `sc` violates `AnnealScalarValid dstDecl.ty sc`,
executing `_d = (copy|move) *_r` into a live destination `dstIdx` raises
undefined behavior in BOTH `stepMirFn` (`MirStepNode.fail .ub` via
`validateValueForTy?`) and `Miri.Interpreter.Step.step` (`annealStepHooks`,
`"reading invalid value"`). -/
theorem step_safeRef_deref_read_invalid_scalar_simulation
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
    {dstDecl refDecl allocDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hoff0 : ptrVal.offsetBytes = 0)
    (_hperm : e.perm ≠ .disabled)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hsize : (translateTy dstDecl.ty body.layouts).layout.size =
      (translateTy allocDecl.ty body.layouts).layout.size)
    (hinvalid : ¬ AnnealScalarValid dstDecl.ty sc)
    (_hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "reading invalid value")) := by
  obtain ⟨ha, m', hm⟩ := step_safeRef_deref_read_invalid_scalar_both_ub hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ref href_ty hdst_prim himm_ref hslot_r he htag hoff0 _hperm hdecl_a htarget hsize hinvalid _hdst_live
  exact ⟨by rw [ha, hm]; exact .ub m' _, ha, m', hm⟩

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
            decl.ty.kind = dstDecl.ty.kind))
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
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
        cases body.localDecls <;> simp [hslot_r, hsr_dead]
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
        cases body.localDecls <;> simp [hslot_r, hsr_un]
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
        cases body.localDecls <;> simp [hslot_r, hsr_sc]
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
            s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals body.localDecls = .ub := by
          rcases hopKind with rfl | rfl <;>
          · unfold evalOperand readProjectedValue; dsimp only []
            cases body.localDecls <;>
            · simp only [hslot_r, hcaller, ← htag, hbor_look, AllocMapEntry.toBorrowEntry]
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
              s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals body.localDecls = .ub := by
            rcases hopKind with rfl | rfl <;>
            · unfold evalOperand readProjectedValue; dsimp only []
              cases body.localDecls <;>
              · simp only [hslot_r, hcaller, ← htag, hbor_look, AllocMapEntry.toBorrowEntry]
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
            s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals body.localDecls =
            .ok (.scalar sc_t) s.frame.locals := by
          have hsz_dst : (translateTy dstDecl.ty body.layouts).layout.size =
              translateSizeBytes sc_t.sizeBytes := by
            rw [← htr_tgt]; exact hsz_t
          have hbool_dst : dstDecl.ty.kind = .bool →
              sc_t.sizeBytes = 1 ∧ (sc_t.bits = 0 ∨ sc_t.bits = 1) :=
            fun hb => hbool_t (htgt_kind_eq.trans hb)
          have hchar_dst : dstDecl.ty.kind = .char →
              sc_t.sizeBytes = 4 ∧ isValidCharCode sc_t.bits = true :=
            fun hc => hchar_t (htgt_kind_eq.trans hc)
          obtain ⟨accTy, hpt_res, hacc_kind⟩ :=
            placeTyResolved_deref_safeRef_prim (layouts := body.layouts) hdecl_ref href_ty
          let rAccTy := resolveTyWithLocalDecls body.localDecls body.layouts accTy
          have hrAcc_kind : rAccTy.kind = dstDecl.ty.kind :=
            (resolveTyWithLocalDecls_kind body.localDecls body.layouts accTy).trans hacc_kind
          have hrAcc_prim : IsPrimScalarTy rAccTy := hdst_prim.of_kind_eq hrAcc_kind
          have hts_r : tyScalarBytes rAccTy = some sc_t.sizeBytes := by
            rw [IsPrimScalarTy.tyScalarBytes_eq hrAcc_prim body.layouts |>.1,
              ← hrAcc_prim.translateTy_layoutIdx body.layouts, hrAcc_kind, hlay0_eq, hsz_dst]
            rcases hrel_t.validBytes with h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> rfl
          have hextract : extractScalarSlice? sc_t 0 sc_t.sizeBytes = some sc_t := by
            unfold extractScalarSlice?
            rcases hrel_t.validBytes with h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> rfl
          have hval_acc : validateValueForTy? body.layouts (some rAccTy) (.scalar sc_t) = true :=
            IsPrimScalarTy.validateValueForTy_scalar hrAcc_prim body.layouts
              (fun hb => hbool_dst (hrAcc_kind.symm.trans hb))
              (fun hc => hchar_dst (hrAcc_kind.symm.trans hc))
          have halign_tgt :
              checkTargetPlaceAlign body.localDecls body.layouts (some rAccTy)
                e.toBorrowEntry ptrVal (some (.scalar sc_t)) = true :=
            hrAcc_prim.checkTargetPlaceAlign_zero_nil body.localDecls hlay_coh hdecl_tgt rfl
              (htgt_kind_eq.trans hrAcc_kind.symm) hoff0 (some (.scalar sc_t))
          cases hld : body.localDecls with
          | nil => rw [hld] at hdecl_ref; cases hdecl_ref
          | cons d₀ ds =>
            dsimp only [rAccTy] at halign_tgt hts_r hval_acc
            rw [hld] at hpt_res halign_tgt hts_r hval_acc
            let rAccTy_ds := resolveTyWithLocalDecls (d₀ :: ds) body.layouts accTy
            have halign_tgt' : checkTargetPlaceAlign (d₀ :: ds) body.layouts (some rAccTy_ds)
                e.toBorrowEntry ptrVal (some (.scalar sc_t)) = true := halign_tgt
            have hts_r' : tyScalarBytes rAccTy_ds = some sc_t.sizeBytes := hts_r
            have hval_acc' : validateValueForTy? body.layouts (some rAccTy_ds) (.scalar sc_t) =
                true := hval_acc
            have hcda : checkDerefAlign (d₀ :: ds) body.layouts (some rAccTy_ds)
                ptrVal.offsetBytes = true := by rw [hoff0]
            have htl : e.toBorrowEntry.targetLocal = e.localIdx := rfl
            have htp : e.toBorrowEntry.targetProjection = .nil := rfl
            have hperm_eq : e.toBorrowEntry.perm = e.perm := rfl
            rcases hopKind with rfl | rfl <;>
            · unfold evalOperand
              dsimp only []
              rw [hpt_res, hslot_r]
              dsimp only []
              rw [← htag, hbor_look]
              dsimp only []
              rw [htl, hslot_t, hs_t, hperm_eq]
              cases hp : e.perm
              all_goals first
                | exact absurd hp hperm_ok
                | (dsimp only []
                   unfold evalStackThinPtrTypedDerefRead
                   rw [htp, htl]
                   dsimp only [stripTransparentProjections]
                   rw [hcda, halign_tgt']
                   dsimp only [Bool.true_and, readProjectedForLocal, readProjectedValue]
                   rw [hts_r', hoff0]
                   dsimp only []
                   rw [hextract]
                   dsimp only []
                   rw [hval_acc']
                   rfl)
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
        have hval_load :
            validateLoadedValue body.layouts body.localDecls
              (opKind ⟨refIdx, .cons .deref .nil⟩) (.scalar sc_t) = true := by
          have hbool_dst : dstDecl.ty.kind = .bool →
              sc_t.sizeBytes = 1 ∧ (sc_t.bits = 0 ∨ sc_t.bits = 1) :=
            fun hb => hbool_t (htgt_kind_eq.trans hb)
          rcases refDecl with ⟨_, ⟨rk, rli⟩, _⟩
          dsimp only at href_ty
          subst href_ty
          rcases hopKind with rfl | rfl <;>
          · unfold validateLoadedValue operandTy placeTy
            dsimp only []
            rw [hdecl_ref]
            dsimp only [resolveProjectedTy, pointeeTyOf]
            by_cases hbk : dstDecl.ty.kind = .bool
            · rw [hbk]
              obtain ⟨_, hb01⟩ := hbool_dst hbk
              rcases hb01 with hb | hb <;> simp [hb]
            · cases hk : dstDecl.ty.kind <;> first | rfl | exact absurd hk hbk
        have hrv_anneal :
            evalRvalue s.frame.locals (.use (opKind ⟨refIdx, .cons .deref .nil⟩))
              s.memory body.localDecls body.layouts =
            .ok (.scalar sc_t) s.frame.locals
              { s.memory with
                borrows := (allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag)).map
                  AllocMapEntry.toBorrowEntry } := by
          unfold evalRvalue; dsimp only []; rw [hop_anneal]; dsimp only []; rw [hval_load]
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
            have hub := derefReadTreeUB_map_toBorrowEntry_eq_false s.frame.locals
              (e₁ :: e₂ :: rest) (hm_cases ▸ halloc_a.tags_nodup) refIdx ptrVal 8 e
              (hm_cases ▸ he) htag hslot_r hperm_ok
            rcases hopKind with rfl | rfl <;>
            · simp only [hbor, hprot, List.map_cons] at hfrz hub ⊢
              simp only [hub]
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
            decl.ty.kind = dstDecl.ty.kind))
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    ∃ allocMap',
      StepRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  ⟨_, step_safeRef_deref_read_simulation_explicit hstate hphase hopKind hbb hstmt hdecl_dst
    hdecl_ref href_ty hdst_prim himm hlive_ref hlay_coh⟩

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

theorem StateRelLM3_2.validateLoadedValue_wtScalar
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    {mem : Memory} {v : Value} {locals' : List LocalSlot}
    (hok : evalOperand s.frame.locals op mem.borrows mem.globals body.layouts mem.callerLocals =
      .ok v locals') :
    validateLoadedValue body.layouts body.localDecls op v = true := by
  cases hop with
  | constScalar _ _ _ _ _ _ _ _ _ => rfl
  | copyLocal idx decl hdecl _ himm =>
    obtain ⟨tf₀, hfr₀, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
    rw [hframes] at hfr₀
    injection hfr₀ with h1
    injection h1 with h2
    subst h2
    obtain ⟨slot, mls, _, _, hslot, hmls, _, hloc⟩ := hfr.lookup_local hdecl
    have hnot_ind := himm mls hmls
    unfold evalOperand readProjectedValue at hok
    dsimp only [] at hok
    rw [hslot] at hok
    rcases hloc with hloc_1 | ⟨_, _, _, _, _, _, href, _⟩
    rotate_left
    · dsimp only [] at hok
      injection hok with hv_eq _
      subst hv_eq
      rcases decl with ⟨_, ⟨dk, dli⟩, _⟩
      dsimp only at href
      subst href
      unfold validateLoadedValue operandTy placeTy
      dsimp only []
      rw [hdecl]
    cases hloc_1 with
    | rawPtr _ _ _ _ _ _ hraw _ =>
      dsimp only [] at hok
      injection hok with hv_eq _
      subst hv_eq
      rcases decl with ⟨_, ⟨dk, dli⟩, _⟩
      dsimp only at hraw
      subst hraw
      unfold validateLoadedValue operandTy placeTy
      dsimp only []
      rw [hdecl]
    | base hb =>
      cases hb with
      | dead _ _ => simp at hok
      | indirect _ mp _ _ _ _ => exact absurd rfl (hnot_ind mp)
      | immediate _ _ _ _ hval =>
        rcases hval with ⟨rfl, _⟩ | ⟨_, rfl, himm_rel⟩
        · simp at hok
        · dsimp only [] at hok
          injection hok with hv_eq _
          subst hv_eq
          rcases decl with ⟨_, ⟨dk, dli⟩, _⟩
          unfold validateLoadedValue operandTy placeTy
          dsimp only []
          rw [hdecl]
          dsimp only [resolveProjectedTy]
          by_cases hbk : dk = .bool
          · subst hbk
            cases himm_rel with
            | unit hzero =>
              have htr : (translateTy { kind := .bool, layoutIdx := dli } body.layouts).layout.size ≠
                  Miri.ABI.Size.ZERO := by
                unfold translateTy; dsimp only []; decide
              exact absurd hzero htr
            | scalar sc _ _ _ hb_sc _ =>
              obtain ⟨_, hb01⟩ := hb_sc rfl
              dsimp only []
              rcases hb01 with hb0 | hb1
              · rw [hb0]; rfl
              · rw [hb1]; rfl
            | scalarPair _ _ _ _ _ _ hagg _ =>
              rcases hagg with ⟨_, hk⟩ | ⟨_, _, hk⟩ <;> cases hk
          · cases dk <;> first | rfl | exact absurd rfl hbk

theorem evalRvalue_use_scalarOperand_eq_lm3_2
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (mem : Memory) :
    evalRvalue s.frame.locals (.use op) mem body.localDecls body.layouts =
      match evalOperand s.frame.locals op mem.borrows mem.globals body.layouts mem.callerLocals with
      | .ok v locals' => .ok v locals' mem
      | .ub => .ub
      | .unsupported => .unsupported :=
  evalRvalue_use_scalarOperand_eq hop s.frame.locals mem
    (fun _ _ hok => hstate.validateLoadedValue_wtScalar hframes hop hok)

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
        tgtDecl.ty.kind = pointeeKind)
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
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
      rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes hop_tf, hop_ub]
    · unfold evalStmt; dsimp only []
      rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes hop_tf, hop_ok]
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
        · unfold evalStmt; dsimp only []
          rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes hop_tf, hop_ub]
        · unfold evalStmt; dsimp only []
          rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes hop_tf, hop_ok]
          dsimp only [evalPlaceWrite]; rw [hprot]; dsimp only []
          cases hld : body.localDecls with
          | nil => rw [hld] at hdecl_ref; cases hdecl_ref
          | cons d₀ ds =>
            unfold writePlaceValue; dsimp only []
            rw [hslot_r]; dsimp only []; rw [hbor_look]; dsimp only [AllocMapEntry.toBorrowEntry]
            cases hp : e.perm <;> first | (rw [hcaller]; done) | (
              unfold writeStackThinPtrTypedDeref
              dsimp only []
              rw [hslot_t, ht_dead]
              dsimp only []
              cases Bool.and _ _ <;> rw [hcaller])
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
          unfold evalStmt; dsimp only []
          rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes hop_tf, hop_ub]
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
        have hwub : derefWriteTreeUB s.frame.locals s.memory.borrows
            ⟨refIdx, .cons .deref .nil⟩ = false := by
          rw [hbor]
          exact derefWriteTreeUB_map_toBorrowEntry_eq_false _ _ _
        have hbool_tgt : tgtDecl.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1) :=
          fun hb => hbool_val (hval_kind.trans (htgt_kind.symm.trans hb))
        have hchar_tgt : tgtDecl.ty.kind = .char →
            sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true :=
          fun hc => hchar_val (hval_kind.trans (htgt_kind.symm.trans hc))
        have hsz_tgt : (translateTy tgtDecl.ty body.layouts).layout.size =
            translateSizeBytes sc.sizeBytes :=
          (congrArg (fun tl => tl.layout.size) htr_tgt).trans hsz_sc
        have hwrite_ok :
            writePlaceValue s.frame.locals s.memory.borrows
              ⟨refIdx, .cons .deref .nil⟩ (.scalar sc)
              body.localDecls body.layouts =
              .ok (s.frame.locals.set e.localIdx (.init (.scalar sc))) := by
          obtain ⟨accTy, hpt_res, hacc_kind⟩ :=
            placeTyResolved_deref_safeRef_prim (layouts := body.layouts) hdecl_ref href_ty
          let rAccTy := resolveTyWithLocalDecls body.localDecls body.layouts accTy
          have hrAcc_kind : rAccTy.kind = pointeeKind :=
            (resolveTyWithLocalDecls_kind body.localDecls body.layouts accTy).trans hacc_kind
          have hrAcc_prim : IsPrimScalarTy rAccTy := hpt_prim.of_kind_eq hrAcc_kind
          have hts_r : tyScalarBytes rAccTy = some sc.sizeBytes := by
            rw [IsPrimScalarTy.tyScalarBytes_eq hrAcc_prim body.layouts |>.1,
              ← hrAcc_prim.translateTy_layoutIdx body.layouts, hrAcc_kind, hlay0_eq, hsz_sc]
            rcases hrel_sc.validBytes with h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> rfl
          have hval_acc : validateValueForTy? body.layouts (some rAccTy) (.scalar sc) = true :=
            IsPrimScalarTy.validateValueForTy_scalar hrAcc_prim body.layouts
              (fun hb => hbool_val (hval_kind.trans (hrAcc_kind.symm.trans hb)))
              (fun hc => hchar_val (hval_kind.trans (hrAcc_kind.symm.trans hc)))
          have halign_tgt : ∀ vOpt,
              checkTargetPlaceAlign body.localDecls body.layouts (some rAccTy)
                e.toBorrowEntry ptrVal vOpt = true :=
            fun vOpt => hrAcc_prim.checkTargetPlaceAlign_zero_nil body.localDecls hlay_coh hdecl_tgt rfl
              (htgt_kind.trans hrAcc_kind.symm) hoff0 vOpt
          cases hld : body.localDecls with
          | nil => rw [hld] at hdecl_ref; cases hdecl_ref
          | cons d₀ ds =>
            have hd_eq : body.localDecls = d₀ :: ds := hld
            dsimp only [rAccTy] at halign_tgt hts_r hval_acc
            rw [hld] at hpt_res halign_tgt hts_r hval_acc
            let rAccTy_ds := resolveTyWithLocalDecls (d₀ :: ds) body.layouts accTy
            have halign_tgt' : ∀ vOpt, checkTargetPlaceAlign (d₀ :: ds) body.layouts (some rAccTy_ds)
                e.toBorrowEntry ptrVal vOpt = true := halign_tgt
            have hts_r' : tyScalarBytes rAccTy_ds = some sc.sizeBytes := hts_r
            have hval_acc' : validateValueForTy? body.layouts (some rAccTy_ds) (.scalar sc) =
                true := hval_acc
            have hcda : checkDerefAlign (d₀ :: ds) body.layouts (some rAccTy_ds)
                ptrVal.offsetBytes = true := by rw [hoff0]
            have htl : e.toBorrowEntry.targetLocal = e.localIdx := rfl
            have htp : e.toBorrowEntry.targetProjection = .nil := rfl
            have hperm_eq : e.toBorrowEntry.perm = e.perm := rfl
            have hbody :
                writeStackThinPtrTypedDeref s.frame.locals s.frame.locals e.toBorrowEntry ptrVal .nil
                  (.scalar sc) (d₀ :: ds) body.layouts (some accTy) (some accTy) =
                  .ok (s.frame.locals.set e.localIdx (.init (.scalar sc))) := by
              unfold writeStackThinPtrTypedDeref
              rw [htp, htl]
              dsimp only [stripTransparentProjections]
              rw [hcda, halign_tgt', Bool.true_and, hval_acc', Bool.true_and]
              rw [hslot_t]
              cases slot_t with
              | dead => exact absurd rfl ht_dead
              | uninit =>
                have hdecl_tgt_ds : get? (d₀ :: ds) e.localIdx = some tgtDecl := hd_eq ▸ hdecl_tgt
                have hrAcc_ds_eq : rAccTy_ds = rAccTy := by
                  dsimp only [rAccTy_ds, rAccTy]; rw [← hd_eq]
                have hdeclTy_kind :
                    (resolveTyWithLocalDecls (d₀ :: ds) body.layouts tgtDecl.ty).kind =
                      rAccTy_ds.kind :=
                  (resolveTyWithLocalDecls_kind (d₀ :: ds) body.layouts tgtDecl.ty).trans
                    (htgt_kind.trans (hrAcc_ds_eq ▸ hrAcc_kind).symm)
                have hrAcc_prim_ds : IsPrimScalarTy rAccTy_ds := hrAcc_ds_eq.symm ▸ hrAcc_prim
                dsimp only []
                rw [hoff0, hdecl_tgt_ds]
                dsimp only [Nat.beq]
                dsimp only [rAccTy_ds] at hdeclTy_kind hrAcc_prim_ds
                generalize resolveTyWithLocalDecls (d₀ :: ds) body.layouts accTy = rTy
                  at hdeclTy_kind hrAcc_prim_ds ⊢
                rcases rTy with ⟨rak, rali⟩
                rcases hrAcc_prim_ds with hk | hk | ⟨w, hk⟩ | ⟨w, hk⟩
                · dsimp only at hk; subst hk
                  dsimp only [rigidTyEq]; rw [hdeclTy_kind]; dsimp only []; rw [set?_eq_some_set hlt_af_t]
                · dsimp only at hk; subst hk
                  dsimp only [rigidTyEq]; rw [hdeclTy_kind]; dsimp only []; rw [set?_eq_some_set hlt_af_t]
                · dsimp only at hk; subst hk
                  dsimp only [rigidTyEq]; rw [hdeclTy_kind]
                  cases w <;> (dsimp only [intTyEq]; rw [set?_eq_some_set hlt_af_t])
                · dsimp only at hk; subst hk
                  dsimp only [rigidTyEq]; rw [hdeclTy_kind]
                  cases w <;> (dsimp only [uintTyEq]; rw [set?_eq_some_set hlt_af_t])
              | init oldVal =>
                obtain ⟨⟨_, _⟩, hsc_old, _⟩ := hlive_sync (.init oldVal) hslot_t (by simp)
                obtain ⟨sc_old, rfl⟩ := hsc_old oldVal rfl
                obtain ⟨tgtDecl', sc_old', _, hdecl_t', _, hslot_t', _, hsz_old, hrel_old⟩ :=
                  hstate.alloc_target_init_scalar he hs_not_dead (by rw [hslot_t]; simp)
                have htgt_eq' : tgtDecl' = tgtDecl := Option.some.inj (hdecl_t'.symm.trans hdecl_tgt)
                subst htgt_eq'
                have hsc_old_eq : sc_old' = sc_old := by
                  rw [hslot_t] at hslot_t'
                  injection hslot_t' with h1
                  injection h1 with h2
                  injection h2 with h3
                  exact h3.symm
                subst hsc_old_eq
                have hsz_eq_old : sc.sizeBytes = sc_old'.sizeBytes :=
                  translateSizeBytes_inj hrel_sc.validBytes hrel_old.validBytes
                    (hsz_tgt.symm.trans hsz_old)
                have hspl_ok : spliceScalarSlice? sc_old' ptrVal.offsetBytes sc = some sc := by
                  unfold spliceScalarSlice?
                  rw [hoff0, ← hsz_eq_old]
                  rcases hrel_sc.validBytes with h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> rfl
                dsimp only [readProjectedForLocal, readProjectedValue]
                rw [hspl_ok]
                dsimp only []
                rw [set?_eq_some_set hlt_af_t]
            unfold writePlaceValue
            dsimp only []
            rw [hpt_res, hslot_r]
            dsimp only []
            rw [hbor_look]
            dsimp only []
            rw [hperm_eq]
            rcases hperm_ok with hp | hp <;> rw [hp] <;> exact hbody
        have ha_ok : evalStmt s ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩
            body.localDecls body.layouts =
            MirStepNode.step
              (advanceStmt s (s.frame.locals.set e.localIdx (.init (.scalar sc)))
                { s.memory with
                  borrows := (updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag)).map
                    AllocMapEntry.toBorrowEntry }) := by
          unfold evalStmt; dsimp only []
          rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes hop_tf, hop_ok]
          dsimp only []
          unfold evalPlaceWrite
          rw [hprot, hwrite_ok]
          simp only [hinv_bor, hwub]
        have hnext_eq : derefWriteNextAllocMap s.frame.locals allocMap refIdx =
            updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag) := by
          simp only [derefWriteNextAllocMap, hslot_r,
            lookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he htag]
        rw [ha_ok, hnext_eq]
        apply StepRelLM3_2.step
        exact hstate_tf'.advance_write_deref_scalar rfl
          (fun x => x.updateOnWrite e.localIdx (some ptrVal.tag))
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          he hdecl_tgt htgt_prim hslot_t ht_dead hfind_la hkind_la halign_la
          hrel_sc hsz_tgt hbool_tgt hchar_tgt
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
        tgtDecl.ty.kind = pointeeKind)
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    ∃ allocMap',
      StepRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  ⟨_, step_safeRef_deref_write_simulation_explicit hstate hphase hbb hstmt hdecl_ref href_ty
    hval_prim hval_kind hop himm_ref hlive_ref hlay_coh⟩

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
    StepRelLM3_2 body m (disableAllocMapLocal allocMap loc)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_prot, ht_caller, ht_bor,
      halloc, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have ha : evalStmt s ⟨.storageDead loc, span⟩ body.localDecls body.layouts =
      MirStepNode.step
        (advanceStmt s (s.frame.locals.set loc .dead)
          { s.memory with borrows := disableLocalBorrows s.memory.borrows loc }) := by
    unfold evalStmt
    dsimp only
    rw [hslot, set?_eq_some_set hlt_af, ht_prot]
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
  let fDis : AllocMapEntry → AllocMapEntry := fun e =>
    match Nat.beq e.localIdx loc with
    | true => { e with perm := .disabled }
    | false => e
  have hf_tag : ∀ e, (fDis e).tag = e.tag := fun e => by
    dsimp only [fDis]; cases Nat.beq e.localIdx loc <;> rfl
  have hf_loc : ∀ e, (fDis e).localIdx = e.localIdx := fun e => by
    dsimp only [fDis]; cases Nat.beq e.localIdx loc <;> rfl
  have hf_aid : ∀ e, (fDis e).allocId = e.allocId := fun e => by
    dsimp only [fDis]; cases Nat.beq e.localIdx loc <;> rfl
  have hnew : LocalRelLM3_2 mach' (disableAllocMapLocal allocMap loc) decl body.layouts .dead
      { topFrame.locals[loc]'hlt_mf with value := .dead } := by
    rw [hmls_eq]
    exact .lm3_1 (.base (.dead mls.layout hloc.cachedLayout_eq))
  have hfr' : FrameRelLM3_2 body mach' (disableAllocMapLocal allocMap loc)
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
      have hloc_dealloc : LocalRelLM3_2 mach' allocMap decl_i body.layouts slot_i mls_i := by
        apply (hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).of_dealloc
        intro mp mp' hv hv'
        apply hdisj loc i mp mp' (topFrame.locals[loc]'hlt_mf).layout mls_i.layout h_eq
        · rw [Array.getElem?_eq_getElem hlt_mf, ← hv]
        · rw [hmls_i, ← hv']
      exact hloc_dealloc.map_preserve fDis hf_tag hf_aid
  have hnodup' : ((disableAllocMapLocal allocMap loc).map AllocMapEntry.tag).Nodup := by
    have hmap_eq : (disableAllocMapLocal allocMap loc).map AllocMapEntry.tag =
        allocMap.map AllocMapEntry.tag := by
      dsimp only [disableAllocMapLocal]
      rw [List.map_map]
      congr 1; funext x; exact hf_tag x
    rw [hmap_eq]; exact halloc.tags_nodup
  have hbor' :
      disableLocalBorrows s.memory.borrows loc =
        (disableAllocMapLocal allocMap loc).map AllocMapEntry.toBorrowEntry := by
    rw [ht_bor, disableAllocMapLocal_map_toBorrowEntry]
  refine .mk _ rfl ht_ret ht_retp hfr'.advance hcal_none ht_stack ht_prot ht_caller hbor' ?_ ?_
  · refine ⟨hnodup', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e₁ h₁ e₂ h₂ hloc_eq
      change e₁ ∈ allocMap.map fDis at h₁
      change e₂ ∈ allocMap.map fDis at h₂
      obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp h₁
      obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.mp h₂
      rw [hf_loc, hf_loc] at hloc_eq
      rw [hf_aid, hf_aid]
      exact halloc.local_to_alloc_unique x₁ hx₁ x₂ hx₂ hloc_eq
    · intro e₁ h₁ e₂ h₂ hid_eq
      change e₁ ∈ allocMap.map fDis at h₁
      change e₂ ∈ allocMap.map fDis at h₂
      obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp h₁
      obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.mp h₂
      rw [hf_aid, hf_aid] at hid_eq
      rw [hf_loc, hf_loc]
      exact halloc.alloc_to_local_injective x₁ hx₁ x₂ hx₂ hid_eq
    · intro e he
      change e ∈ allocMap.map fDis at he
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      rw [hf_loc]
      exact halloc.target_decl x hx
    · intro e he
      change e ∈ allocMap.map fDis at he
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      rw [hf_aid]
      obtain ⟨h32, hnext, hbase⟩ := halloc.base_addr_valid x hx
      exact ⟨h32, by simpa [mach', deallocLocalMemory_nextAllocId₂] using hnext, hbase⟩
    · intro e he
      have hlook := lookupBorrow_map_toBorrowEntry_of_nodup hnodup' he
      change e ∈ allocMap.map fDis at he
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      refine ⟨?_, ?_⟩
      · rw [hf_tag]; exact (halloc.borrow_sync x hx).1
      · dsimp only [advanceStmt]
        rw [hbor']
        exact hlook
    · intro e he la₁ la₂ hla₁ hla₂
      change e ∈ allocMap.map fDis at he
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      rw [hf_aid] at hla₁ hla₂
      exact halloc.live_key_unique x hx la₁ la₂
        (deallocLocalMemory_sublist₂ _ _ hla₁)
        (deallocLocalMemory_sublist₂ _ _ hla₂)
    · intro tf' htf' e he
      injection htf' with h₁
      injection h₁ with h₂
      subst h₂
      change e ∈ allocMap.map fDis at he
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      rw [hf_loc, hf_aid]
      obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync topFrame hframes x hx
      by_cases heloc : loc = x.localIdx
      · have hget_dead :
            get? (advanceStmt s (s.frame.locals.set loc .dead)
              { s.memory with borrows := disableLocalBorrows s.memory.borrows loc }).frame.locals
              x.localIdx = some .dead := by
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
                .live (.indirect (stackAllocPlace x.allocId)) := by
              rw [← heloc, Array.getElem?_eq_getElem hlt_mf] at hlay
              injection hlay with hls
              rw [hls]
            show (deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value).live.find?
              _ = none
            rw [hv_ind]
            exact deallocLocalMemory_find?_self₂ m.machine.memory x.allocId
      · have hget_ne :
            get? (advanceStmt s (s.frame.locals.set loc .dead)
              { s.memory with borrows := disableLocalBorrows s.memory.borrows loc }).frame.locals
              x.localIdx = get? s.frame.locals x.localIdx := by
          dsimp only [advanceStmt]
          rw [get?_eq_getElem?, List.getElem?_set_ne heloc, ← get?_eq_getElem?]
        refine ⟨fun slot' hslot' hne_d => ?_, fun hdead' => ?_⟩
        · rw [hget_ne] at hslot'
          obtain ⟨⟨lay, hlay⟩, hsc, hshape⟩ := hlive_e slot' hslot' hne_d
          have hne_alloc : ∀ mp, (topFrame.locals[loc]'hlt_mf).value = .live (.indirect mp) →
              mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some x.allocId := by
            intro mp hv
            have hd := hdisj loc x.localIdx mp (stackAllocPlace x.allocId)
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
          intro y hy
          exact hfind0 y (Array.mem_toList_iff.mp
            (deallocLocalMemory_sublist₂ _ _ (Array.mem_toList_iff.mpr hy)))
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
  have hbor_dis_eq : disableLocalBorrows s.memory.borrows loc = s.memory.borrows := by
    apply disableLocalBorrows_eq_self_of_forall_ne
    intro b hb
    rw [ht_bor] at hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
    exact hnot_mapped e he
  have hmem_dis_eq : { s.memory with borrows := disableLocalBorrows s.memory.borrows loc } =
      s.memory := by
    rw [hbor_dis_eq]
  have ha : evalStmt s ⟨.storageLive loc, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc .uninit)) := by
    unfold evalStmt
    dsimp only
    rw [hslot, set?_eq_some_set hlt_af]
    dsimp only
    rw [hmem_dis_eq, ht_prot]
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

/-! ## Typed Copy of a Dangling Reference -/

/-- **`step_safeRef_copy_dangling_validity_divergence` (`LM-3.2`, genuine
divergence)**: a typed copy `_d = copy _r` of a safe reference `_r : &T`
whose pointee local has been killed by `StorageDead`:

1. Anneal's `evalOperand` reads the dangling reference `.ptr p 8` without any
   check (Anneal validates a reference only when it is dereferenced), and the
   real step is the lockstep `StepRelLM3_2` of `step_safeRef_use_simulation`:
   `annealRvalueHooks.copyOp` writes the pointer without validating it;
2. the vendored validity visitor rejects the copied value
   (`ValidityVisitor.validatePlace` on `_r`: "encountered a dangling reference
   (use-after-free)"). Miri's `copy_op` validates its destination when
   validity is enforced (`writePlaceImmediate` → `validate`), and that
   destination holds exactly this value, so in Miri the typed copy itself is
   undefined behavior.

Both semantics are fixed (`trusted/lean`, `lean-miri/vendor`): Anneal defers
the undefined behavior of a dangling reference to its first dereference, while
Miri reports it at the first typed copy. -/
theorem step_safeRef_copy_dangling_validity_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl : LocalDecl} {srcMut dstMut : Mutability}
    {dstPointee : RigidTy} {targetDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .ref srcMut targetDecl.ty.kind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv} {e : AllocMapEntry}
    (hslot_src : get? s.frame.locals srcIdx = some (.init (.ptr p 8)))
    (hptr : PtrRel allocMap p mptr) (he : e ∈ allocMap) (htag : e.tag = p.tag)
    (hdecl_t : get? body.localDecls e.localIdx = some targetDecl)
    (hdead_t : get? s.frame.locals e.localIdx = some .dead)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) (hlt : srcIdx < tf.locals.size)
    (hval_src : (tf.locals[srcIdx]'hlt).value =
      .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))))
    (fuel : Nat) :
    evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ok (.ptr p 8) s.frame.locals ∧
    StepRelLM3_2 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) srcDecl.ty
        (fuel + 1) ⟨.local 0 srcIdx none tf.localsIdentity, translateTy srcDecl.ty body.layouts⟩
        false false m =
      .error (.undefinedBehavior
        "validation: encountered a dangling reference (use-after-free)") m := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨d, hd, hprim⟩ := halloc.target_decl e he
  rw [hdecl_t] at hd
  cases hd
  refine ⟨?_, step_safeRef_use_simulation hstate hphase (Or.inl rfl) hbb hstmt hdecl_dst
    hdecl_src hsrc_ty hdst_ty himm, ?_⟩
  · unfold evalOperand
    dsimp only []
    rw [hslot_src]
    rfl
  · exact ((validatePlace_ref_nonrecursive_simulation hstate hframes hlt hprim hsrc_ty fuel).2.2.2
      hptr he htag ⟨targetDecl, hdecl_t, rfl⟩ hval_src).2.2 hdead_t

/-- **`step_safeRef_use_dangling_post_validity_divergence` (`LM-3.2`, genuine
post-copy/move destination validity divergence)**: strengthening
`step_safeRef_copy_dangling_validity_divergence` across both `Operand.copy` and
`Operand.move` (including self-move `_r = move _r`), with no redundant Miri
pointer or frame hypotheses, and validating the **destination** local `dstIdx`
in the **post-state** `m'` (matching Miri's `copy_op` → `writePlaceImmediate` →
`validate` on the written destination place):

1. Anneal's `stepMirFn` steps (`stepMirFn body s = .step s'`) and writes the
   dangling pointer `.init (.ptr p 8)` into `dstIdx`;
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) steps in
   lockstep to `(m', .ok true)` with `StateRelLM3_2 body s' m' allocMap`;
3. `ValidityVisitor.validatePlace` on the destination `dstIdx` in the post-state
   `m'` rejects the copied/moved reference with
   `"validation: encountered a dangling reference (use-after-free)"` for every
   `fuel + 1`. -/
theorem step_safeRef_use_dangling_post_validity_divergence
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
    {dstDecl srcDecl targetDecl : LocalDecl} {srcMut dstMut : Mutability}
    {srcPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .ref srcMut srcPointee)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut targetDecl.ty.kind)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    {p : ProvenancePtr} {e : AllocMapEntry}
    (hslot_src : get? s.frame.locals srcIdx = some (.init (.ptr p 8)))
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (he : e ∈ allocMap) (htag : e.tag = p.tag)
    (hdecl_t : get? body.localDecls e.localIdx = some targetDecl)
    (hdead_t : get? s.frame.locals e.localIdx = some .dead) :
    ∃ s' m' tf',
      stepMirFn body s = .step s' ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      StateRelLM3_2 body s' m' allocMap ∧
      m'.stack.frames = #[tf'] ∧
      get? s'.frame.locals dstIdx = some (.init (.ptr p 8)) ∧
      dstIdx < tf'.locals.size ∧
      ∀ fuel,
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts)
          dstDecl.ty (fuel + 1)
          ⟨.local 0 dstIdx none tf'.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          false false m' =
        .error (.undefinedBehavior
          "validation: encountered a dangling reference (use-after-free)") m' := by
  have hsim := step_safeRef_use_simulation hstate hphase hopKind hbb hstmt hdecl_dst hdecl_src
    hsrc_ty hdst_ty himm
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨d_t, hd_t, hprim⟩ := halloc.target_decl e he
  rw [hdecl_t] at hd_t; injection hd_t with hd_eq; subst hd_eq
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
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hss_eq : slot_s = .init (.ptr p 8) := Option.some.inj (hslot_s.symm.trans hslot_src)
  subst hss_eq
  rcases hloc_s.ref_immediate_cases hsrc_ty (himm_s_tfa mls_s hmls_s) with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨p', mptr, hp_eq, hptrRel, hms_ptr⟩
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
    have hmid_step : ∃ (tf_mid : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
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
        refine ⟨tfb, s, hstate_b, himm_d_tfb, hdst_live, (hstate_b.frame_rel_singleton rfl).location_eq, ?_⟩
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
    obtain ⟨tf_mid, s_mid, hstate_mid, himm_d_mid, hlive_mid, hloc_mid, hm_w⟩ := hmid_step
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
    have hm_step := miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt
      hm_ok rfl hloc_mid
    have ha_step : ∃ s₁, stepMirFn body s = .step s₁ ∧
        get? s₁.frame.locals dstIdx = some (.init (.ptr p 8)) := by
      obtain ⟨_, _, _, _, _, _, _, hprot, _, _, _, _⟩ := id hstate
      obtain ⟨_, _, hlt_af_d, _, _, _, _, _⟩ := hfr.lookup_local hdecl_dst
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]
      rcases hopKind with rfl | rfl
      · have hget_d' : get? (s.frame.locals.set dstIdx (.init (.ptr p 8))) dstIdx =
            some (.init (.ptr p 8)) := by
          rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
        unfold evalStmt evalRvalue evalOperand readProjectedValue; dsimp only []
        rw [hslot_src]; dsimp only []
        rw [validateLoadedValue_ref_local_eq_true hdecl_src hsrc_ty (Or.inl rfl)]
        dsimp only []; rw [hslot_d]
        cases slot_d with
        | dead => exact absurd rfl hsd_ne
        | uninit => simp only [set?_eq_some_set hlt_af_d, hprot]; exact ⟨_, rfl, hget_d'⟩
        | init _ => simp only [set?_eq_some_set hlt_af_d, hprot]; exact ⟨_, rfl, hget_d'⟩
      · have hlt_af_d' : dstIdx < (s.frame.locals.set srcIdx .uninit).length := by
          rw [List.length_set]; exact hlt_af_d
        have hget_d' : get? ((s.frame.locals.set srcIdx .uninit).set dstIdx (.init (.ptr p 8)))
            dstIdx = some (.init (.ptr p 8)) := by
          rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d']
        unfold evalStmt evalRvalue evalOperand; dsimp only []
        rw [hslot_src, set?_eq_some_set hlt_af_s]; dsimp only []
        rw [validateLoadedValue_ref_local_eq_true hdecl_src hsrc_ty (Or.inr rfl)]
        dsimp only []
        have hsl_mid : ∃ sl, get? (s.frame.locals.set srcIdx .uninit) dstIdx = some sl ∧
            sl ≠ .dead := by
          rw [get?_eq_getElem?, List.getElem?_set]
          by_cases h_eq : srcIdx = dstIdx
          · subst h_eq; exact ⟨.uninit, by simp [hlt_af_s], by simp⟩
          · simp only [h_eq, ↓reduceIte, ← get?_eq_getElem?]
            exact ⟨slot_d, hslot_d, hsd_ne⟩
        obtain ⟨sl, hsl_get, hsl_ne⟩ := hsl_mid
        rw [hsl_get]
        cases sl with
        | dead => exact absurd rfl hsl_ne
        | uninit => simp only [set?_eq_some_set hlt_af_d', hprot]; exact ⟨_, rfl, hget_d'⟩
        | init _ => simp only [set?_eq_some_set hlt_af_d', hprot]; exact ⟨_, rfl, hget_d'⟩
    obtain ⟨s', hs'_step, hs'_dst⟩ := ha_step
    rw [hs'_step, hm_step] at hsim
    let tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
      { { tf_mid with
          locals := tf_mid.locals.set dstIdx
            { tf_mid.locals[dstIdx]'hlt_dm with
              value := .live (.immediate
                (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) }
            hlt_dm } with
        location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
    have hstate' : StateRelLM3_2 body s' { m with stack := ⟨#[tf']⟩ } allocMap := by
      generalize ha_eq : MirStepNode.step s' = aNode at hsim
      generalize hm_eq : ({ m with stack := ⟨#[tf']⟩ }, Except.ok true) = mNode at hsim
      cases hsim with
      | step s₂ m₂ hrel =>
        cases ha_eq
        cases hm_eq
        exact hrel
      | retRoot _ _ _ _ _ _ _ _ _ => cases ha_eq
      | ub _ _ => cases ha_eq
    have hlt_d' : dstIdx < tf'.locals.size := by
      dsimp only [tf']; rw [Array.size_set]; exact hlt_dm
    have hval_d' : (tf'.locals[dstIdx]'hlt_d').value =
        .live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) := by
      dsimp only [tf']; rw [Array.getElem_set_self]
    obtain ⟨_, _, _, _, hfr', _, _, _, _, _, halloc', _⟩ := id hstate'
    have hfind_none := (halloc.local_alloc_sync tf hframes e he).2 hdead_t
    have hdead_t' : get? s'.frame.locals e.localIdx = some .dead := by
      obtain ⟨slot_e', _, _, _, hslot_e', _, _, _⟩ := hfr'.lookup_local hdecl_t
      by_cases hne_e : slot_e' = .dead
      · subst hne_e; exact hslot_e'
      · exfalso
        obtain ⟨_, _, hsh_fn⟩ := (halloc'.local_alloc_sync tf' rfl e he).1 slot_e' hslot_e' hne_e
        obtain ⟨la, hfind_la, _⟩ := hsh_fn targetDecl hdecl_t
        rw [hfind_none] at hfind_la
        cases hfind_la
    refine ⟨s', { m with stack := ⟨#[tf']⟩ }, tf', hs'_step, hm_step, hstate', rfl,
      hs'_dst, hlt_d', fun fuel => ?_⟩
    exact ((validatePlace_ref_nonrecursive_simulation hstate' rfl hlt_d' hprim hdst_ty fuel).2.2.2
      hptrRel he htag ⟨targetDecl, hdecl_t, rfl⟩ hval_d').2.2 hdead_t'

/-! ## 6. Safe-Reference Out-of-Bounds & Misaligned Dereference UB Simulations -/

/-- Dereferencing a `PtrRel`-related safe-reference local `_r : &(mut) P` whose
pointee range `ptrVal.offsetBytes + sizeof(P)` extends past the live stack
allocation of `e.localIdx` (`sizeof(allocDecl.ty) < ptrVal.offsetBytes + sizeof(P)`)
eagerly raises `"dereferencing a dangling reference"` in
`annealDerefOperandToMemPlace`. -/
theorem annealDerefOperandToMemPlace_safeRef_ptr_oob
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {refIdx : Local} {refDecl allocDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? body.localDecls refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    {ptrVal : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    {e : AllocMapEntry}
    (hptrRel : PtrRel allocMap ptrVal mptr)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (hlive_a : get? s.frame.locals e.localIdx ≠ some .dead)
    (hoob : (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat <
      ptrVal.offsetBytes +
        (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat)
    (ptrLay : Miri.Interpreter.LocalLayout)
    {st : AnnealStepState} (hmach : st.machine = m.machine) :
    annealDerefOperandToMemPlace body.localDecls body.layouts refIdx
        (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))
        ptrLay st =
      .error (.undefinedBehavior "dereferencing a dangling reference") st := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨_, borTag, hprov_eq, hid_lt, hoff_lt, hmptr_off, ⟨e', he', htag', rfl⟩⟩ := hptrRel
  have he_eq : e = e' :=
    mem_eq_of_map_nodup halloc.tags_nodup he he' (htag.trans htag'.symm)
  subst he_eq
  obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
  obtain ⟨slot_a, _, _, _, hslot_a, _, _, _⟩ := hfr.lookup_local hdecl_a
  have ha_ne_dead : slot_a ≠ .dead := fun hd => hlive_a (hslot_a.trans (congrArg some hd))
  obtain ⟨_, _, hshape_fn⟩ := (halloc.local_alloc_sync tf hframes e he).1 slot_a hslot_a ha_ne_dead
  obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hshape_fn allocDecl hdecl_a
  obtain ⟨hsz, hpos, hfit, _, _, _⟩ := hpk.size_align_ok body.layouts
  have hoob_la : localAlloc.allocation.byteSize.bytes.toNat <
      ptrVal.offsetBytes +
        (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat := by
    rw [hshape_la.byteSize_eq]; exact hoob
  have hmptr_eq : mptr =
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
        .concrete e.allocId borTag⟩ := by
    rcases mptr with ⟨off, prov⟩
    dsimp only at hprov_eq hmptr_off; subst hprov_eq hmptr_off; rfl
  rw [annealDerefOperandToMemPlace_safeRef_pointer_eq hdecl hty hpk mptr ptrLay st,
    hmach, hmptr_eq,
    annealSafeRefDerefCheck_oob_err (mach := m.machine) e.allocId borTag ptrVal.offsetBytes
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts) localAlloc hid_lt hoff_lt
      hbase hfind_la hsz (by exact_mod_cast hpos) hfit hoob_la]

/-- Dereferencing a `PtrRel`-related safe-reference local `_r : &(mut) P` whose
pointee range `ptrVal.offsetBytes + sizeof(P)` lies in bounds of `e.localIdx`'s
live stack allocation (`≤ sizeof(allocDecl.ty)`) but whose address is misaligned
for `P` (`annealOffsetMisalignment ... = .ok (some mis)`) eagerly raises
`"dereferencing an unaligned reference"` in `annealDerefOperandToMemPlace`. -/
theorem annealDerefOperandToMemPlace_safeRef_ptr_misaligned
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {refIdx : Local} {refDecl allocDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? body.localDecls refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    {ptrVal : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    {e : AllocMapEntry}
    (hptrRel : PtrRel allocMap ptrVal mptr)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (hlive_a : get? s.frame.locals e.localIdx ≠ some .dead)
    (hinbounds : ptrVal.offsetBytes +
        (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat ≤
      (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat)
    {mis : Miri.Memory.Misalignment}
    (hmis : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.align.abi =
      .ok (some mis))
    (ptrLay : Miri.Interpreter.LocalLayout)
    {st : AnnealStepState} (hmach : st.machine = m.machine) :
    annealDerefOperandToMemPlace body.localDecls body.layouts refIdx
        (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))
        ptrLay st =
      .error (.undefinedBehavior "dereferencing an unaligned reference") st := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨_, borTag, hprov_eq, hid_lt, hoff_lt, hmptr_off, ⟨e', he', htag', rfl⟩⟩ := hptrRel
  have he_eq : e = e' :=
    mem_eq_of_map_nodup halloc.tags_nodup he he' (htag.trans htag'.symm)
  subst he_eq
  obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
  obtain ⟨slot_a, _, _, _, hslot_a, _, _, _⟩ := hfr.lookup_local hdecl_a
  have ha_ne_dead : slot_a ≠ .dead := fun hd => hlive_a (hslot_a.trans (congrArg some hd))
  obtain ⟨_, _, hshape_fn⟩ := (halloc.local_alloc_sync tf hframes e he).1 slot_a hslot_a ha_ne_dead
  obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hshape_fn allocDecl hdecl_a
  obtain ⟨hsz, hpos, hfit, _, _, _⟩ := hpk.size_align_ok body.layouts
  have hin_la : ptrVal.offsetBytes +
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat := by
    rw [hshape_la.byteSize_eq]; exact hinbounds
  have hmptr_eq : mptr =
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
        .concrete e.allocId borTag⟩ := by
    rcases mptr with ⟨off, prov⟩
    dsimp only at hprov_eq hmptr_off; subst hprov_eq hmptr_off; rfl
  rw [annealDerefOperandToMemPlace_safeRef_pointer_eq hdecl hty hpk mptr ptrLay st,
    hmach, hmptr_eq,
    annealSafeRefDerefCheck_misaligned_err (mach := m.machine) e.allocId borTag ptrVal.offsetBytes
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts) localAlloc hid_lt hoff_lt
      hbase hfind_la hsz (by exact_mod_cast hpos) hfit hin_la hmis]

private theorem encodeLittleEndianBytes_length₂ (bits n : Nat)
    (prov : Option (Nat × Nat)) :
    (encodeLittleEndianBytes bits n prov).length = n := by
  induction n generalizing bits with
  | zero => rfl
  | succ k ih =>
    dsimp only [encodeLittleEndianBytes, List.length]
    rw [ih]

private theorem nat_ble_eq_false_of_lt {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hble : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hble) (Nat.not_le_of_gt h)

private theorem nat_beq_eq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hbeq : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hbeq) h

private theorem decodeSubValueAtByteOffset_scalar_oob_none₂
    (layouts : LayoutTable) (baseTyOpt : Option Ty) (sc : MirAst.ScalarInt)
    (offsetBytes : Nat) (accTy : Ty) (decls : List LocalDecl)
    (hprim : IsPrimScalarTy accTy)
    (hoob : sc.sizeBytes < offsetBytes + (translateTy accTy layouts).layout.size.bytes.toNat) :
    decodeSubValueAtByteOffset? layouts baseTyOpt (.scalar sc) offsetBytes accTy decls = none := by
  have hr_kind := resolveTyWithLocalDecls_kind decls layouts accTy
  have hr_prim : IsPrimScalarTy (resolveTyWithLocalDecls decls layouts accTy) :=
    hprim.of_kind_eq hr_kind
  have htr_eq : translateTy (resolveTyWithLocalDecls decls layouts accTy) layouts =
      translateTy accTy layouts := by
    rw [← hr_prim.translateTy_layoutIdx layouts, hr_kind, hprim.translateTy_layoutIdx layouts]
  have hsz := hr_prim.tyByteSize_eq decls layouts
  rw [htr_eq] at hsz
  unfold decodeSubValueAtByteOffset?
  dsimp only []
  rw [hsz]
  dsimp only [encodeUntypedValueToBytes, encodeScalarBytes, defaultCodecFuel]
  cases Nat.beq sc.sizeBytes 0
  · dsimp only [sliceAbstractBytes]
    have hlen : length (encodeLittleEndianBytes sc.bits sc.sizeBytes none) = sc.sizeBytes :=
      encodeLittleEndianBytes_length₂ sc.bits sc.sizeBytes none
    have hble_f :
        Nat.ble (Nat.add offsetBytes (translateTy accTy layouts).layout.size.bytes.toNat)
          (length (encodeLittleEndianBytes sc.bits sc.sizeBytes none)) = false := by
      rw [hlen]
      exact nat_ble_eq_false_of_lt hoob
    rw [hble_f]
  · rfl

private theorem writeAbstractBytesAt_none_of_lt
    (buf : List AbstractByte) (off : Nat) (wList : List AbstractByte)
    (hne : wList ≠ [])
    (hlt : buf.length < off + wList.length) :
    writeAbstractBytesAt buf off wList = none := by
  induction buf generalizing off wList with
  | nil =>
    cases wList with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  | cons b bufRest ih =>
    cases off with
    | zero =>
      cases wList with
      | nil => exact absurd rfl hne
      | cons w wRest =>
        cases wRest with
        | nil => simp [List.length] at hlt
        | cons w₂ ws =>
          dsimp only [writeAbstractBytesAt]
          rw [ih 0 (w₂ :: ws) (by simp)
            (by simp only [List.length_cons] at hlt ⊢; omega)]
    | succ off' =>
      cases wList with
      | nil => exact absurd rfl hne
      | cons w wRest =>
        dsimp only [writeAbstractBytesAt]
        rw [ih off' (w :: wRest) (by simp)
          (by simp only [List.length_cons] at hlt ⊢; omega)]

private theorem spliceSubValueAtByteOffset_scalar_oob_none
    (localDecls targetDecls : List LocalDecl) (layouts : LayoutTable)
    (subTyOpt accTyOpt : Option Ty) (oldSc wSc : MirAst.ScalarInt) (offsetBytes : Nat)
    (hoob : oldSc.sizeBytes < offsetBytes + wSc.sizeBytes) :
    spliceSubValueAtByteOffset? localDecls targetDecls layouts subTyOpt
      (.scalar oldSc) offsetBytes accTyOpt (.scalar wSc) = none := by
  unfold spliceSubValueAtByteOffset?
  dsimp only [encodeUntypedValueToBytes, encodeScalarBytes, defaultCodecFuel]
  cases hb0 : Nat.beq wSc.sizeBytes 0
  · dsimp only []
    have hlen_old : (encodeLittleEndianBytes oldSc.bits oldSc.sizeBytes none).length =
        oldSc.sizeBytes :=
      encodeLittleEndianBytes_length₂ oldSc.bits oldSc.sizeBytes none
    have hlen_w : (encodeLittleEndianBytes wSc.bits wSc.sizeBytes none).length =
        wSc.sizeBytes :=
      encodeLittleEndianBytes_length₂ wSc.bits wSc.sizeBytes none
    have hw_ne : encodeLittleEndianBytes wSc.bits wSc.sizeBytes none ≠ [] := by
      intro hnil
      have hlen0 : (encodeLittleEndianBytes wSc.bits wSc.sizeBytes none).length = 0 := by
        rw [hnil]; rfl
      rw [hlen_w] at hlen0
      rw [hlen0] at hb0
      cases hb0
    rw [writeAbstractBytesAt_none_of_lt _ _ _ hw_ne (by rw [hlen_old, hlen_w]; exact hoob)]
  · rfl

private theorem divModBytesAux_snd_mod₂ (fuel rem stride quot : Nat)
    (hpos : 0 < stride) (hfuel : rem ≤ fuel) :
    (divModBytesAux fuel rem stride quot).2 = rem % stride := by
  induction fuel generalizing rem quot with
  | zero =>
    have h0 : rem = 0 := Nat.eq_zero_of_le_zero hfuel
    subst h0; rfl
  | succ f ih =>
    unfold divModBytesAux
    by_cases hle : stride ≤ rem
    · rw [Nat.ble_eq.mpr hle]
      dsimp only [Nat.sub_eq, Nat.succ_eq_add_one]
      rw [ih (rem - stride) (quot + 1) (by omega), Nat.mod_eq_sub_mod hle]
    · have hlt : rem < stride := Nat.lt_of_not_le hle
      rw [nat_ble_eq_false_of_lt hlt, Nat.mod_eq_of_lt hlt]

private theorem PrimScalar_misaligned_offset_mod_ne_zero₂
    {ty : Ty} (hprim : IsPrimScalarTy ty) (ly : LayoutTable)
    {allocId : Miri.Memory.AllocId} {offsetBytes : Nat}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hoff_lt : offsetBytes < 2 ^ 32)
    (hmis : (Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes)).isAligned
      (translateTy ty ly).layout.align.abi = .ok false) :
    offsetBytes ≠ 0 ∧
    1 < (translateTy ty ly).layout.size.bytes.toNat ∧
    offsetBytes % (translateTy ty ly).layout.size.bytes.toNat ≠ 0 := by
  have haddr : (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes).toNat =
      allocId.value.toNat * 2 ^ 32 + offsetBytes := by
    have hbase : (annealStackBaseAddr allocId).toNat = allocId.value.toNat * 2 ^ 32 := by
      unfold annealStackBaseAddr
      rw [UInt64.toNat_shiftLeft]
      have hlt64 : allocId.value.toNat * 2 ^ 32 < 2 ^ 64 := by omega
      simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlt64]
    have hoff_lt64 : offsetBytes < 2 ^ 64 := by omega
    have hoff_u64 : (UInt64.ofNat offsetBytes).toNat = offsetBytes :=
      UInt64.toNat_ofNat_of_lt hoff_lt64
    have hsum_lt : allocId.value.toNat * 2 ^ 32 + offsetBytes < 2 ^ 64 := by omega
    rw [UInt64.toNat_add, hbase, hoff_u64, Nat.mod_eq_of_lt hsum_lt]
  have check_align : ∀ (k : Nat) (mask : UInt64),
      (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) →
      mask.toNat = 2 ^ k - 1 →
      (translateTy ty ly).layout.size.bytes.toNat = 2 ^ k →
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes)).isAligned
        (translateTy ty ly).layout.align.abi =
        .ok (((annealStackBaseAddr allocId + UInt64.ofNat offsetBytes) &&& mask) == 0) →
      offsetBytes ≠ 0 ∧
      1 < (translateTy ty ly).layout.size.bytes.toNat ∧
      offsetBytes % (translateTy ty ly).layout.size.bytes.toNat ≠ 0 := by
    intro k mask hmem hmask hsz hisAl
    rw [hsz]
    rw [hisAl] at hmis
    have hand : ((annealStackBaseAddr allocId + UInt64.ofNat offsetBytes) &&& mask).toNat =
        (allocId.value.toNat * 2 ^ 32 + offsetBytes) % (2 ^ k) := by
      rw [UInt64.toNat_and, haddr, hmask, Nat.and_two_pow_sub_one_eq_mod]
    have hmod_ne : (allocId.value.toNat * 2 ^ 32 + offsetBytes) % (2 ^ k) ≠ 0 := by
      intro h0
      have hu : (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes) &&& mask = 0 := by
        apply UInt64.toNat_inj.mp
        rw [hand, h0]
        rfl
      rw [hu] at hmis
      cases hmis
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact absurd (Nat.mod_one _) hmod_ne
    · exact ⟨by omega, by decide, by omega⟩
    · exact ⟨by omega, by decide, by omega⟩
    · exact ⟨by omega, by decide, by omega⟩
    · exact ⟨by omega, by decide, by omega⟩
  rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · exact check_align 0 0 (by decide) rfl (by simp only [translateTy, hk]; rfl)
      (by simp only [translateTy, hk]; rfl)
  · exact check_align 2 3 (by decide) rfl (by simp only [translateTy, hk]; rfl)
      (by simp only [translateTy, hk]; rfl)
  · cases it
    · exact check_align 0 0 (by decide) rfl (by simp only [translateTy, hk]; rfl)
        (by simp only [translateTy, hk]; rfl)
    · exact check_align 1 1 (by decide) rfl (by simp only [translateTy, hk]; rfl)
        (by simp only [translateTy, hk]; rfl)
    · exact check_align 2 3 (by decide) rfl (by simp only [translateTy, hk]; rfl)
        (by simp only [translateTy, hk]; rfl)
    · exact check_align 3 7 (by decide) rfl (by simp only [translateTy, hk]; rfl)
        (by simp only [translateTy, hk]; rfl)
    · exact check_align 4 15 (by decide) rfl (by simp only [translateTy, hk]; rfl)
        (by simp only [translateTy, hk]; rfl)
    · exact check_align 3 7 (by decide) rfl (by simp only [translateTy, hk]; rfl)
        (by simp only [translateTy, hk]; rfl)
  · cases ut
    · exact check_align 0 0 (by decide) rfl (by simp only [translateTy, hk]; rfl)
        (by simp only [translateTy, hk]; rfl)
    · exact check_align 1 1 (by decide) rfl (by simp only [translateTy, hk]; rfl)
        (by simp only [translateTy, hk]; rfl)
    · exact check_align 2 3 (by decide) rfl (by simp only [translateTy, hk]; rfl)
        (by simp only [translateTy, hk]; rfl)
    · exact check_align 3 7 (by decide) rfl (by simp only [translateTy, hk]; rfl)
        (by simp only [translateTy, hk]; rfl)
    · exact check_align 4 15 (by decide) rfl (by simp only [translateTy, hk]; rfl)
        (by simp only [translateTy, hk]; rfl)
    · exact check_align 3 7 (by decide) rfl (by simp only [translateTy, hk]; rfl)
        (by simp only [translateTy, hk]; rfl)

/-- Both-UB core of `step_safeRef_deref_read_oob_simulation`: Anneal's `stepMirFn` fails with `.ub` and
`lean-miri`'s `Miri.Interpreter.Step.step` reports the stated
`StepError.undefinedBehavior`. -/
private theorem step_safeRef_deref_read_oob_both_ub
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
    {dstDecl refDecl allocDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (_hperm : e.perm ≠ .disabled)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hoob : (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat <
      ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat)
    (_hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing a dangling reference")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, halloc, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · have hlookup : lookupBorrow s.memory.borrows ptrVal.tag = some e.toBorrowEntry := by
      rw [← htag]; exact (halloc.borrow_sync e he).2
    obtain ⟨tgtDecl, sc_t, _, hdecl_t, _, hslot_t, hsz_a_nat, _, _⟩ :=
      hstate.alloc_target_init_scalar he (by rw [htarget]; simp) (by rw [htarget]; simp)
    have htgt_eq : tgtDecl = allocDecl := Option.some.inj (hdecl_t.symm.trans hdecl_a)
    have hsc_eq : sc_t = sc := by
      have h := Option.some.inj (hslot_t.symm.trans htarget)
      injection h with h'; injection h'
    subst htgt_eq; subst sc_t
    have hoob_sc :
        sc.sizeBytes <
          ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat := by
      rwa [← hsz_a_nat]
    obtain ⟨accTy, hpt_res, hacc_kind⟩ :=
      placeTyResolved_deref_safeRef_prim (layouts := body.layouts) hdecl_ref href_ty
    let rAccTy := resolveTyWithLocalDecls body.localDecls body.layouts accTy
    have hrAcc_kind : rAccTy.kind = dstDecl.ty.kind :=
      (resolveTyWithLocalDecls_kind body.localDecls body.layouts accTy).trans hacc_kind
    have hrAcc_prim : IsPrimScalarTy rAccTy := hdst_prim.of_kind_eq hrAcc_kind
    have htr_rAcc : translateTy rAccTy body.layouts = translateTy dstDecl.ty body.layouts := by
      rw [← hrAcc_prim.translateTy_layoutIdx body.layouts, hrAcc_kind,
        hdst_prim.translateTy_layoutIdx body.layouts]
    have hts_r : tyScalarBytes rAccTy =
        some (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat := by
      rw [← htr_rAcc]
      exact (IsPrimScalarTy.tyScalarBytes_eq hrAcc_prim body.layouts).1
    have hextract_none :
        extractScalarSlice? sc ptrVal.offsetBytes
          (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat = none := by
      unfold extractScalarSlice?
      have hble_f :
          Nat.ble (Nat.add ptrVal.offsetBytes
            (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat) sc.sizeBytes = false :=
        nat_ble_eq_false_of_lt hoob_sc
      rw [hble_f, Bool.and_false]
    have hop_ub : evalOperand s.frame.locals (opKind ⟨refIdx, .cons .deref .nil⟩)
        s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals body.localDecls =
        .ub := by
      cases hld : body.localDecls with
      | nil => rw [hld] at hdecl_ref; cases hdecl_ref
      | cons d₀ ds =>
        have hd_eq : body.localDecls = d₀ :: ds := hld
        have htl : e.toBorrowEntry.targetLocal = e.localIdx := rfl
        have htp : e.toBorrowEntry.targetProjection = .nil := rfl
        have hperm_eq : e.toBorrowEntry.perm = e.perm := rfl
        have hbody : evalStackThinPtrTypedDerefRead s.frame.locals (.scalar sc) e.toBorrowEntry
            ptrVal .nil body.localDecls body.layouts (some accTy) (some accTy)
            (placeTyResolved body.localDecls body.layouts
              { local_ := e.toBorrowEntry.targetLocal,
                projection := e.toBorrowEntry.targetProjection }) = .ub := by
          unfold evalStackThinPtrTypedDerefRead
          rw [htp, htl]
          dsimp only [stripTransparentProjections]
          change (let resolvedAccTyOpt := some rAccTy; _) = _
          dsimp only []
          cases Bool.and
            (checkDerefAlign body.localDecls body.layouts _ ptrVal.offsetBytes)
            (checkTargetPlaceAlign body.localDecls body.layouts _ e.toBorrowEntry ptrVal
              (some (.scalar sc)))
          · rfl
          · dsimp only [readProjectedForLocal, readProjectedValue]
            rw [hts_r]
            dsimp only []
            rw [hextract_none]
            dsimp only []
            have hdec_fb :
                ∀ targetTyOpt ld ptOpt,
                  decodeAtBorrowTargetOffset? s.frame.locals (.scalar sc) e.toBorrowEntry ptrVal
                    .nil body.layouts (some rAccTy) targetTyOpt ld ptOpt = none := by
              intro targetTyOpt ld ptOpt
              unfold decodeAtBorrowTargetOffset?
              dsimp only [AllocMapEntry.toBorrowEntry, readProjectedForLocal, readProjectedValue]
              exact decodeSubValueAtByteOffset_scalar_oob_none₂ body.layouts targetTyOpt sc
                ptrVal.offsetBytes rAccTy ld hrAcc_prim (htr_rAcc.symm ▸ hoob_sc)
            rw [hdec_fb]
            cases hres :
              resolveStackThinPtrTargetProjWithResidual? s.frame.locals (.scalar sc)
                e.toBorrowEntry ptrVal .nil _ body.layouts _ _ with
            | none => rfl
            | some pr =>
              have hpr_eq : pr = (.nil, 0) ∧ ptrVal.offsetBytes = 0 := by
                unfold resolveStackThinPtrTargetProjWithResidual? at hres
                dsimp only [AllocMapEntry.toBorrowEntry, stripTransparentProjections,
                  normalizeSubsliceProjections, normalizeAdjacentSubslices] at hres
                cases hb0 : Nat.beq ptrVal.offsetBytes 0
                · rw [hb0] at hres
                  dsimp only [splitLastConstantIndex?, splitLastField?, endsWithSubslice,
                    readProjectedValue, resolveStackThinPtrFieldOffsetProj?,
                    splitAfterLastSeqProj] at hres
                  split at hres <;> cases hres
                · rw [hb0] at hres
                  split at hres
                  · exact ⟨Option.some.inj hres.symm, Nat.eq_of_beq_eq_true hb0⟩
                  · dsimp only [splitLastConstantIndex?, splitLastField?, endsWithSubslice,
                      readProjectedValue, resolveStackThinPtrFieldOffsetProj?,
                      splitAfterLastSeqProj] at hres
                    cases hres
              obtain ⟨rfl, hoff0⟩ := hpr_eq
              dsimp only [readProjectedForLocal, readProjectedValue]
              have hoob0 :
                  sc.sizeBytes < (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat := by
                have h := hoob_sc
                rw [hoff0, Nat.zero_add] at h
                exact h
              have hdec0 :
                  ∀ targetTyOpt ld,
                    decodeSubValueAtByteOffset? body.layouts targetTyOpt
                      (.scalar sc) 0 rAccTy ld = none :=
                fun targetTyOpt ld =>
                  decodeSubValueAtByteOffset_scalar_oob_none₂ body.layouts targetTyOpt sc 0 rAccTy ld
                    hrAcc_prim (by rw [htr_rAcc, Nat.zero_add]; exact hoob0)
              have hextract0 :
                  extractScalarSlice? sc 0
                    (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat = none := by
                unfold extractScalarSlice?
                have hble_f :
                    Nat.ble (Nat.add 0
                      (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat) sc.sizeBytes =
                      false :=
                  nat_ble_eq_false_of_lt (by rw [Nat.add_eq, Nat.zero_add]; exact hoob0)
                rw [hble_f, Bool.and_false]
              have hsz_neq :
                  Nat.beq (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat
                    sc.sizeBytes = false :=
                nat_beq_eq_false_of_ne (Nat.ne_of_gt hoob0)
              dsimp only [rAccTy] at hrAcc_prim hdec0
              generalize resolveTyWithLocalDecls body.localDecls body.layouts accTy = rTy
                at hrAcc_prim hdec0 ⊢
              rcases rTy with ⟨rak, rali⟩
              rcases hrAcc_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;>
                (dsimp only at hk; subst hk;
                 simp only [Nat.beq_refl, hsz_neq, Bool.and_false, hextract0, hdec0])
        rcases hopKind with rfl | rfl <;>
        · unfold evalOperand
          dsimp only []
          rw [← hd_eq]
          rw [hpt_res, hslot_r]
          dsimp only []
          rw [hlookup]
          dsimp only []
          rw [htl, htarget, hperm_eq]
          cases e.perm <;> first | rfl | exact hbody
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue; dsimp only []; rw [hop_ub]
  · have himm_r := himm_ref tf hframes
    have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
      ⟨dstIdx, .nil⟩ (opKind ⟨refIdx, .cons .deref .nil⟩) span m
    obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
    obtain ⟨slot_r, mls_r, _, hlt_ra, hslot_ra, hmls_ra, hmls_ra_eq, hloc_r⟩ :=
      (hstate_a.frame_rel_singleton rfl).lookup_local hdecl_ref
    have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
      hloc_r.cachedLayout_eq
    have himm_ra := himm_r.cache_layout hlt_d (translateTy dstDecl.ty body.layouts) mls_r hmls_ra
    have hsr_eq : slot_r = .init (.ptr ptrVal 8) := Option.some.inj (hslot_ra.symm.trans hslot_r)
    subst hsr_eq
    rcases hloc_r.ref_immediate_cases href_ty himm_ra with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmr_ptr⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
      have hmls_ra' : tfa.locals[refIdx]'hlt_ra =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_r.layout⟩ := by
        rw [hmls_ra_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
      let tfb := cacheFrameLocalLayout tfa refIdx hlt_ra (translateTy refDecl.ty body.layouts)
      have hop_ptr := annealEvalOperand_deref_live hopKind
        (known := some (translateTy dstDecl.ty body.layouts)) (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_ra hdecl_ref hmls_ra' hcache_r
      have hprim0 : IsPrimScalarTy { kind := dstDecl.ty.kind, layoutIdx := 0 } := by
        rcases hdst_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
        · exact Or.inl hk
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr (Or.inl ⟨it, hk⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨ut, hk⟩))
      have hlay0_eq : translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts =
          translateTy dstDecl.ty body.layouts := hdst_prim.translateTy_layoutIdx body.layouts
      have hlive_a : get? s.frame.locals e.localIdx ≠ some .dead := by
        rw [htarget]; simp
      have hoob0 : (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat <
          ptrVal.offsetBytes +
            (translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat := by
        rwa [hlay0_eq]
      have hder_err := annealDerefOperandToMemPlace_safeRef_ptr_oob hstate hdecl_ref href_ty
        hprim0 hptrRel he htag hdecl_a hlive_a hoob0 (translateTy refDecl.ty body.layouts)
        (st := { m with stack := ⟨#[tfb]⟩ }) rfl
      have hop_err : annealEvalOperand body.localDecls body.layouts
          (translateOperand (opKind ⟨refIdx, .cons .deref .nil⟩))
          (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
          .error (.undefinedBehavior "dereferencing a dangling reference")
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hop_ptr, EStateM.bind_eq_error hder_err]
      have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
          m =
          ({ m with stack := ⟨#[tfb]⟩ },
            .error (.undefinedBehavior "dereferencing a dangling reference")) := by
        rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hop_err]
      exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **`step_safeRef_deref_read_oob_simulation` (`LM-3.2`, upgraded to UB simulation)**:
closing the `ptrVal.offsetBytes = 0` / pointee-size precondition of
`step_safeRef_deref_read_simulation`: when `_r : &(mut) P` holds a `PtrRel`
pointer into a live stack local `e.localIdx` (holding `.init (.scalar sc)` with
`e.perm ≠ .disabled`), but `ptrVal.offsetBytes + sizeof(P)` exceeds
`sizeof(allocDecl.ty)`, executing `_d = (copy|move) *_r` raises undefined
behavior in BOTH `stepMirFn` (`MirStepNode.fail .ub` via
`evalStackThinPtrTypedDerefRead`) and `Miri.Interpreter.Step.step`
(`annealStepHooks`, `"dereferencing a dangling reference"`). -/
theorem step_safeRef_deref_read_oob_simulation
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
    {dstDecl refDecl allocDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (_hperm : e.perm ≠ .disabled)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hoob : (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat <
      ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat)
    (_hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing a dangling reference")) := by
  obtain ⟨ha, m', hm⟩ := step_safeRef_deref_read_oob_both_ub hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ref href_ty hdst_prim himm_ref hslot_r he htag _hperm hdecl_a htarget hoob _hdst_live
  exact ⟨by rw [ha, hm]; exact .ub m' _, ha, m', hm⟩

/-- Both-UB core of `step_safeRef_deref_write_oob_simulation`: Anneal's `stepMirFn` fails with `.ub` and
`lean-miri`'s `Miri.Interpreter.Step.step` reports the stated
`StepError.undefinedBehavior`. -/
private theorem step_safeRef_deref_write_oob_both_ub
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl allocDecl : LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hop_ok : evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc) s.frame.locals)
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .active ∨ e.perm = .reserved)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    {sl_a : LocalSlot} (hsl_a : get? s.frame.locals e.localIdx = some sl_a)
    (hsl_ne : sl_a ≠ .dead)
    (hoob : (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat <
      ptrVal.offsetBytes +
        (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat)
    (hsl_init : get? s.frame.locals e.localIdx ≠ some .uninit := by intro h; cases h)
    (hsc_sz : sc.sizeBytes =
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat := by rfl) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing a dangling reference")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, hcaller, _, halloc, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · have hlookup : lookupBorrow s.memory.borrows ptrVal.tag = some e.toBorrowEntry := by
      rw [← htag]; exact (halloc.borrow_sync e he).2
    have hlive_a0 : get? s.frame.locals e.localIdx ≠ some .dead :=
      fun hd => hsl_ne (Option.some.inj (hsl_a.symm.trans hd))
    obtain ⟨tgtDecl, sc_a, _, hdecl_t, _, hslot_a, hsz_a_nat, _, _⟩ :=
      hstate.alloc_target_init_scalar he hlive_a0 hsl_init
    have htgt_eq : tgtDecl = allocDecl := Option.some.inj (hdecl_t.symm.trans hdecl_a)
    subst htgt_eq
    have hoob_sc : sc_a.sizeBytes < ptrVal.offsetBytes + sc.sizeBytes := by
      rw [← hsz_a_nat, hsc_sz]
      exact hoob
    obtain ⟨accTy, hpt_res, hacc_kind⟩ :=
      placeTyResolved_deref_safeRef_prim (layouts := body.layouts) hdecl_ref href_ty
    let rAccTy := resolveTyWithLocalDecls body.localDecls body.layouts accTy
    have hrAcc_kind : rAccTy.kind = pointeeKind :=
      (resolveTyWithLocalDecls_kind body.localDecls body.layouts accTy).trans hacc_kind
    have hrAcc_prim : IsPrimScalarTy rAccTy := hpk_prim.of_kind_eq hrAcc_kind
    have hspl_none : spliceScalarSlice? sc_a ptrVal.offsetBytes sc = none := by
      unfold spliceScalarSlice?
      have hble_f : Nat.ble (Nat.add ptrVal.offsetBytes sc.sizeBytes) sc_a.sizeBytes = false :=
        nat_ble_eq_false_of_lt hoob_sc
      rw [hble_f, Bool.and_false]
    have hw_ub :
        writePlaceValue s.frame.locals s.memory.borrows ⟨refIdx, .cons .deref .nil⟩ (.scalar sc)
          body.localDecls body.layouts = .ub := by
      cases hld : body.localDecls with
      | nil => rw [hld] at hdecl_ref; cases hdecl_ref
      | cons d₀ ds =>
        have hd_eq : body.localDecls = d₀ :: ds := hld
        have htl : e.toBorrowEntry.targetLocal = e.localIdx := rfl
        have htp : e.toBorrowEntry.targetProjection = .nil := rfl
        have hperm_eq : e.toBorrowEntry.perm = e.perm := rfl
        have hbody :
            writeStackThinPtrTypedDeref s.frame.locals s.frame.locals e.toBorrowEntry ptrVal .nil
              (.scalar sc) body.localDecls body.layouts (some accTy) (some accTy) = .ub := by
          unfold writeStackThinPtrTypedDeref
          rw [htp, htl]
          dsimp only [stripTransparentProjections]
          change (let resolvedAccTyOpt := some rAccTy; _) = _
          dsimp only []
          cases Bool.and
            (checkDerefAlign body.localDecls body.layouts _ ptrVal.offsetBytes)
            (Bool.and
              (checkTargetPlaceAlign body.localDecls body.layouts _ e.toBorrowEntry ptrVal _)
              (validateValueForTy? body.layouts (some rAccTy) (.scalar sc)))
          · rfl
          · dsimp only [readProjectedForLocal, readProjectedValue]
            rw [hslot_a]
            dsimp only []
            rw [hspl_none]
            dsimp only []
            cases hres :
              resolveStackThinPtrTargetProjWithResidual? s.frame.locals (.scalar sc_a)
                e.toBorrowEntry ptrVal .nil _ body.layouts _ _ with
            | none =>
              dsimp only [readProjectedForLocal, readProjectedValue]
              rw [spliceSubValueAtByteOffset_scalar_oob_none _ _ _ _ _ sc_a sc
                ptrVal.offsetBytes hoob_sc]
            | some pr =>
              have hpr_eq : pr = (.nil, 0) ∧ ptrVal.offsetBytes = 0 := by
                unfold resolveStackThinPtrTargetProjWithResidual? at hres
                dsimp only [AllocMapEntry.toBorrowEntry, stripTransparentProjections,
                  normalizeSubsliceProjections, normalizeAdjacentSubslices] at hres
                cases hb0 : Nat.beq ptrVal.offsetBytes 0
                · rw [hb0] at hres
                  dsimp only [splitLastConstantIndex?, splitLastField?, endsWithSubslice,
                    readProjectedValue, resolveStackThinPtrFieldOffsetProj?,
                    splitAfterLastSeqProj] at hres
                  split at hres <;> cases hres
                · rw [hb0] at hres
                  split at hres
                  · exact ⟨Option.some.inj hres.symm, Nat.eq_of_beq_eq_true hb0⟩
                  · dsimp only [splitLastConstantIndex?, splitLastField?, endsWithSubslice,
                      readProjectedValue, resolveStackThinPtrFieldOffsetProj?,
                      splitAfterLastSeqProj] at hres
                    cases hres
              obtain ⟨rfl, hoff0⟩ := hpr_eq
              dsimp only [readProjectedForLocal, readProjectedValue]
              have hspl0 : spliceScalarSlice? sc_a 0 sc = none := by
                rw [← hoff0]; exact hspl_none
              have hrAcc_def : resolveTyWithLocalDecls body.localDecls body.layouts accTy = rAccTy := rfl
              rw [hrAcc_def]
              rcases rAccTy with ⟨rak, rali⟩
              rcases hrAcc_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;>
                dsimp only at hk <;> subst hk <;>
                simp only [hspl0]
        unfold writePlaceValue
        dsimp only []
        rw [← hd_eq]
        rw [hpt_res, hslot_r]
        dsimp only []
        rw [hlookup]
        dsimp only []
        rw [hperm_eq]
        rcases hperm with hp | hp <;> rw [hp] <;> exact hbody
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt; dsimp only []
    rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes (hop tf hframes), hop_ok]
    dsimp only [evalPlaceWrite]; rw [hprot, hw_ub, hcaller]
  · have himm_r := himm_ref tf hframes
    have hlive_a0 : get? s.frame.locals e.localIdx ≠ some .dead :=
      fun hd => hsl_ne (Option.some.inj (hsl_a.symm.trans hd))
    have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
      ⟨refIdx, .cons .deref .nil⟩ op span m
    obtain ⟨slot_r, mls_r, _, hlt_r, hslot_rf, hmls_r, hmls_r_eq, hloc_r⟩ :=
      hfr.lookup_local hdecl_ref
    have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
      hloc_r.cachedLayout_eq
    let tfa := cacheFrameLocalLayout tf refIdx hlt_r (translateTy refDecl.ty body.layouts)
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
      have hder_err := annealDerefOperandToMemPlace_safeRef_ptr_oob hstate hdecl_ref href_ty
        hpk_prim hptrRel he htag hdecl_a hlive_a0 hoob (translateTy refDecl.ty body.layouts)
        (st := { m with stack := ⟨#[tfa]⟩ }) rfl
      have hdst_err : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨refIdx, .cons .deref .nil⟩) m =
          .error (.undefinedBehavior "dereferencing a dangling reference")
            { m with stack := ⟨#[tfa]⟩ } := by
        rw [hdst_live, EStateM.bind_eq_error hder_err]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
          ({ m with stack := ⟨#[tfa]⟩ },
            .error (.undefinedBehavior "dereferencing a dangling reference")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hdst_err]
      exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **`step_safeRef_deref_write_oob_simulation` (`LM-3.2`, upgraded to UB simulation)**:
closing the `ptrVal.offsetBytes = 0` / pointee-size precondition of
`step_safeRef_deref_write_simulation`: when `_r : &(mut) P` holds a `PtrRel`
pointer into a live stack local `e.localIdx` with writable borrow
(`e.perm ∈ {.active, .reserved}`), `op` evaluates to `.scalar sc` in Anneal, and
`ptrVal.offsetBytes + sizeof(P)` exceeds `sizeof(allocDecl.ty)`, executing
`*_r = .use op` raises undefined behavior in BOTH `stepMirFn`
(`MirStepNode.fail .ub` via `writeStackThinPtrTypedDeref`) and
`Miri.Interpreter.Step.step` (`annealStepHooks`,
`"dereferencing a dangling reference"`). -/
theorem step_safeRef_deref_write_oob_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl allocDecl : LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hop_ok : evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc) s.frame.locals)
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .active ∨ e.perm = .reserved)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    {sl_a : LocalSlot} (hsl_a : get? s.frame.locals e.localIdx = some sl_a)
    (hsl_ne : sl_a ≠ .dead)
    (hoob : (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat <
      ptrVal.offsetBytes +
        (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat)
    (hsl_init : get? s.frame.locals e.localIdx ≠ some .uninit := by intro h; cases h)
    (hsc_sz : sc.sizeBytes =
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat := by rfl) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing a dangling reference")) := by
  obtain ⟨ha, m', hm⟩ := step_safeRef_deref_write_oob_both_ub hstate hphase hbb hstmt hdecl_ref href_ty hpk_prim hop himm_ref hop_ok hslot_r he htag hperm hdecl_a hsl_a hsl_ne hoob hsl_init hsc_sz
  exact ⟨by rw [ha, hm]; exact .ub m' _, ha, m', hm⟩

/-- Both-UB core of `step_safeRef_deref_read_misaligned_simulation`: Anneal's `stepMirFn` fails with `.ub` and
`lean-miri`'s `Miri.Interpreter.Step.step` reports the stated
`StepError.undefinedBehavior`. -/
private theorem step_safeRef_deref_read_misaligned_both_ub
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
    {dstDecl refDecl allocDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (_hperm : e.perm ≠ .disabled)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hinbounds : ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat ≤
      (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat)
    {mis : Miri.Memory.Misalignment}
    (hmis : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
      (translateTy dstDecl.ty body.layouts).layout.align.abi = .ok (some mis))
    (_hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing an unaligned reference")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, halloc, _⟩ := id hstate
  have himm_r := himm_ref tf hframes
  refine ⟨?_, ?_⟩
  · obtain ⟨slot_r, mls_r, _, _, hslot_rf, hmls_r, _, hloc_r⟩ := hfr.lookup_local hdecl_ref
    have hsr_eq : slot_r = .init (.ptr ptrVal 8) := Option.some.inj (hslot_rf.symm.trans hslot_r)
    subst hsr_eq
    rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, _⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
      obtain ⟨_, _, _, hid_lt, hoff_lt, _, ⟨e', he', htag', rfl⟩⟩ := hptrRel
      have he_eq : e' = e :=
        mem_eq_of_map_nodup halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst he_eq
      have hisAl : (Miri.ABI.Size.ofBytes
          (annealStackBaseAddr e'.allocId + UInt64.ofNat ptrVal.offsetBytes)).isAligned
          (translateTy dstDecl.ty body.layouts).layout.align.abi = .ok false := by
        unfold annealOffsetMisalignment at hmis
        cases h_al : (Miri.ABI.Size.ofBytes
            (annealStackBaseAddr e'.allocId + UInt64.ofNat ptrVal.offsetBytes)).isAligned
            (translateTy dstDecl.ty body.layouts).layout.align.abi with
        | error _ => rw [h_al] at hmis; cases hmis
        | ok b =>
          cases b
          · rfl
          · rw [h_al] at hmis; cases hmis
      obtain ⟨hoff_nz, hal_gt1, hmod_nz⟩ :=
        PrimScalar_misaligned_offset_mod_ne_zero₂ hdst_prim body.layouts hid_lt hoff_lt hisAl
      have hlookup : lookupBorrow s.memory.borrows ptrVal.tag = some e'.toBorrowEntry := by
        rw [← htag]; exact (halloc.borrow_sync e' he').2
      obtain ⟨accTy, hpt_res, hacc_kind⟩ :=
        placeTyResolved_deref_safeRef_prim (layouts := body.layouts) hdecl_ref href_ty
      let rPt := resolveTyWithLocalDecls body.localDecls body.layouts accTy
      have hrPt_kind : rPt.kind = dstDecl.ty.kind :=
        (resolveTyWithLocalDecls_kind body.localDecls body.layouts accTy).trans hacc_kind
      have hrPt_prim : IsPrimScalarTy rPt := hdst_prim.of_kind_eq hrPt_kind
      have htr_rPt : translateTy rPt body.layouts = translateTy dstDecl.ty body.layouts := by
        rw [← hrPt_prim.translateTy_layoutIdx body.layouts, hrPt_kind,
          hdst_prim.translateTy_layoutIdx body.layouts]
      have hal_rPt : tyByteAlign body.localDecls body.layouts rPt =
          (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat := by
        rw [(hrPt_prim.tyByteAlign_eq body.localDecls hlay_coh).1, htr_rPt]
      have hcda_false : checkDerefAlign body.localDecls body.layouts (some rPt) ptrVal.offsetBytes =
          false := by
        unfold checkDerefAlign
        rw [nat_beq_eq_false_of_ne hoff_nz]
        dsimp only []
        rw [hal_rPt, nat_ble_eq_false_of_lt hal_gt1]
        have hdm := divModBytesAux_snd_mod₂ ptrVal.offsetBytes ptrVal.offsetBytes
          (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat 0
          (by omega) (Nat.le_refl _)
        rcases hdm_eq : divModBytesAux ptrVal.offsetBytes ptrVal.offsetBytes
            (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat 0 with ⟨q, r⟩
        rw [hdm_eq] at hdm
        dsimp only [] at hdm ⊢
        rw [hdm]
        exact nat_beq_eq_false_of_ne hmod_nz
      have hop_ub : evalOperand s.frame.locals (opKind ⟨refIdx, .cons .deref .nil⟩)
          s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals body.localDecls =
          .ub := by
        cases hld : body.localDecls with
        | nil => rw [hld] at hdecl_ref; cases hdecl_ref
        | cons d₀ ds =>
          have hd_eq : body.localDecls = d₀ :: ds := hld
          have htl : e'.toBorrowEntry.targetLocal = e'.localIdx := rfl
          have htp : e'.toBorrowEntry.targetProjection = .nil := rfl
          have hperm_eq : e'.toBorrowEntry.perm = e'.perm := rfl
          have hbody : evalStackThinPtrTypedDerefRead s.frame.locals (.scalar sc) e'.toBorrowEntry
              ptrVal .nil body.localDecls body.layouts (some accTy) (some accTy)
              (placeTyResolved body.localDecls body.layouts
                { local_ := e'.toBorrowEntry.targetLocal,
                  projection := e'.toBorrowEntry.targetProjection }) = .ub := by
            unfold evalStackThinPtrTypedDerefRead
            rw [htp, htl]
            dsimp only [stripTransparentProjections]
            change (let resolvedAccTyOpt := some rPt; _) = _
            dsimp only []
            rw [hcda_false, Bool.false_and]
          rcases hopKind with rfl | rfl <;>
          · unfold evalOperand
            dsimp only []
            rw [← hd_eq]
            rw [hpt_res, hslot_r]
            dsimp only []
            rw [hlookup]
            dsimp only []
            rw [htl, htarget, hperm_eq]
            cases e'.perm <;> first | rfl | exact hbody
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]
      unfold evalStmt evalRvalue; dsimp only []; rw [hop_ub]
  · have himm_r := himm_ref tf hframes
    have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
      ⟨dstIdx, .nil⟩ (opKind ⟨refIdx, .cons .deref .nil⟩) span m
    obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
    obtain ⟨slot_r, mls_r, _, hlt_ra, hslot_ra, hmls_ra, hmls_ra_eq, hloc_r⟩ :=
      (hstate_a.frame_rel_singleton rfl).lookup_local hdecl_ref
    have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
      hloc_r.cachedLayout_eq
    have himm_ra := himm_r.cache_layout hlt_d (translateTy dstDecl.ty body.layouts) mls_r hmls_ra
    have hsr_eq : slot_r = .init (.ptr ptrVal 8) := Option.some.inj (hslot_ra.symm.trans hslot_r)
    subst hsr_eq
    rcases hloc_r.ref_immediate_cases href_ty himm_ra with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmr_ptr⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
      have hmls_ra' : tfa.locals[refIdx]'hlt_ra =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_r.layout⟩ := by
        rw [hmls_ra_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
      let tfb := cacheFrameLocalLayout tfa refIdx hlt_ra (translateTy refDecl.ty body.layouts)
      have hop_ptr := annealEvalOperand_deref_live hopKind
        (known := some (translateTy dstDecl.ty body.layouts)) (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_ra hdecl_ref hmls_ra' hcache_r
      have hprim0 : IsPrimScalarTy { kind := dstDecl.ty.kind, layoutIdx := 0 } := by
        rcases hdst_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
        · exact Or.inl hk
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr (Or.inl ⟨it, hk⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨ut, hk⟩))
      have hlay0_eq : translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts =
          translateTy dstDecl.ty body.layouts := hdst_prim.translateTy_layoutIdx body.layouts
      have hlive_a : get? s.frame.locals e.localIdx ≠ some .dead := by
        rw [htarget]; simp
      have hin0 : ptrVal.offsetBytes +
          (translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat ≤
          (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat := by
        rwa [hlay0_eq]
      have hmis0 : annealOffsetMisalignment
          (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
          (translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts).layout.align.abi =
          .ok (some mis) := by
        rwa [hlay0_eq]
      have hder_err := annealDerefOperandToMemPlace_safeRef_ptr_misaligned hstate hdecl_ref href_ty
        hprim0 hptrRel he htag hdecl_a hlive_a hin0 hmis0 (translateTy refDecl.ty body.layouts)
        (st := { m with stack := ⟨#[tfb]⟩ }) rfl
      have hop_err : annealEvalOperand body.localDecls body.layouts
          (translateOperand (opKind ⟨refIdx, .cons .deref .nil⟩))
          (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
          .error (.undefinedBehavior "dereferencing an unaligned reference")
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hop_ptr, EStateM.bind_eq_error hder_err]
      have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
          m =
          ({ m with stack := ⟨#[tfb]⟩ },
            .error (.undefinedBehavior "dereferencing an unaligned reference")) := by
        rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hop_err]
      exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **`step_safeRef_deref_read_misaligned_simulation` (`LM-3.2`, upgraded to UB simulation)**:
when `_r : &(mut) P` holds an in-bounds `PtrRel` pointer into a live stack local
`e.localIdx` (`ptrVal.offsetBytes + sizeof(P) ≤ sizeof(allocDecl.ty)`) whose
address is misaligned for `P` (`annealOffsetMisalignment ... = .ok (some mis)`,
e.g. `offsetBytes = 1` on `&u16` into an 8-byte `u64` stack local), executing
`_d = (copy|move) *_r` raises undefined behavior in BOTH `stepMirFn`
(`MirStepNode.fail .ub` via `checkDerefAlign`) and `Miri.Interpreter.Step.step`
(`annealStepHooks`, `"dereferencing an unaligned reference"`). -/
theorem step_safeRef_deref_read_misaligned_simulation
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
    {dstDecl refDecl allocDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (_hperm : e.perm ≠ .disabled)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hinbounds : ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat ≤
      (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat)
    {mis : Miri.Memory.Misalignment}
    (hmis : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
      (translateTy dstDecl.ty body.layouts).layout.align.abi = .ok (some mis))
    (_hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing an unaligned reference")) := by
  obtain ⟨ha, m', hm⟩ := step_safeRef_deref_read_misaligned_both_ub hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ref href_ty hdst_prim himm_ref hslot_r he htag _hperm hdecl_a htarget hinbounds hmis _hdst_live hlay_coh
  exact ⟨by rw [ha, hm]; exact .ub m' _, ha, m', hm⟩

/-- Both-UB core of `step_safeRef_deref_write_misaligned_simulation`: Anneal's `stepMirFn` fails with `.ub` and
`lean-miri`'s `Miri.Interpreter.Step.step` reports the stated
`StepError.undefinedBehavior`. -/
private theorem step_safeRef_deref_write_misaligned_both_ub
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl allocDecl : LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hop_ok : evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc) s.frame.locals)
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .active ∨ e.perm = .reserved)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    {sl_a : LocalSlot} (hsl_a : get? s.frame.locals e.localIdx = some sl_a)
    (hsl_ne : sl_a ≠ .dead)
    (hinbounds : ptrVal.offsetBytes +
        (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat ≤
      (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat)
    {mis : Miri.Memory.Misalignment}
    (hmis : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.align.abi =
      .ok (some mis))
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing an unaligned reference")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, hcaller, _, halloc, _⟩ := id hstate
  have himm_r := himm_ref tf hframes
  refine ⟨?_, ?_⟩
  · obtain ⟨slot_r, mls_r, _, _, hslot_rf, hmls_r, _, hloc_r⟩ := hfr.lookup_local hdecl_ref
    have hsr_eq : slot_r = .init (.ptr ptrVal 8) := Option.some.inj (hslot_rf.symm.trans hslot_r)
    subst hsr_eq
    rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, _⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
      obtain ⟨_, _, _, hid_lt, hoff_lt, _, ⟨e', he', htag', rfl⟩⟩ := hptrRel
      have he_eq : e' = e :=
        mem_eq_of_map_nodup halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst he_eq
      have hisAl : (Miri.ABI.Size.ofBytes
          (annealStackBaseAddr e'.allocId + UInt64.ofNat ptrVal.offsetBytes)).isAligned
          (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.align.abi =
          .ok false := by
        unfold annealOffsetMisalignment at hmis
        cases h_al : (Miri.ABI.Size.ofBytes
            (annealStackBaseAddr e'.allocId + UInt64.ofNat ptrVal.offsetBytes)).isAligned
            (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.align.abi with
        | error _ => rw [h_al] at hmis; cases hmis
        | ok b =>
          cases b
          · rfl
          · rw [h_al] at hmis; cases hmis
      obtain ⟨hoff_nz, hal_gt1, hmod_nz⟩ :=
        PrimScalar_misaligned_offset_mod_ne_zero₂ hpk_prim body.layouts hid_lt hoff_lt hisAl
      have hlookup : lookupBorrow s.memory.borrows ptrVal.tag = some e'.toBorrowEntry := by
        rw [← htag]; exact (halloc.borrow_sync e' he').2
      obtain ⟨accTy, hpt_res, hacc_kind⟩ :=
        placeTyResolved_deref_safeRef_prim (layouts := body.layouts) hdecl_ref href_ty
      let rPt := resolveTyWithLocalDecls body.localDecls body.layouts accTy
      have hrPt_kind : rPt.kind = pointeeKind :=
        (resolveTyWithLocalDecls_kind body.localDecls body.layouts accTy).trans hacc_kind
      have hrPt_prim : IsPrimScalarTy rPt := hpk_prim.of_kind_eq hrPt_kind
      have htr_rPt : translateTy rPt body.layouts =
          translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts := by
        rw [← hrPt_prim.translateTy_layoutIdx body.layouts, hrPt_kind]
      have hal_rPt : tyByteAlign body.localDecls body.layouts rPt =
          (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat := by
        rw [(hrPt_prim.tyByteAlign_eq body.localDecls hlay_coh).1, htr_rPt]
      have hcda_false : checkDerefAlign body.localDecls body.layouts (some rPt) ptrVal.offsetBytes =
          false := by
        unfold checkDerefAlign
        rw [nat_beq_eq_false_of_ne hoff_nz]
        dsimp only []
        rw [hal_rPt, nat_ble_eq_false_of_lt hal_gt1]
        have hdm := divModBytesAux_snd_mod₂ ptrVal.offsetBytes ptrVal.offsetBytes
          (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat 0
          (by omega) (Nat.le_refl _)
        rcases hdm_eq : divModBytesAux ptrVal.offsetBytes ptrVal.offsetBytes
            (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat 0 with ⟨q, r⟩
        rw [hdm_eq] at hdm
        dsimp only [] at hdm ⊢
        rw [hdm]
        exact nat_beq_eq_false_of_ne hmod_nz
      have hw_ub :
          writePlaceValue s.frame.locals s.memory.borrows ⟨refIdx, .cons .deref .nil⟩ (.scalar sc)
            body.localDecls body.layouts = .ub := by
        cases hld : body.localDecls with
        | nil => rw [hld] at hdecl_ref; cases hdecl_ref
        | cons d₀ ds =>
          have hd_eq : body.localDecls = d₀ :: ds := hld
          have htl : e'.toBorrowEntry.targetLocal = e'.localIdx := rfl
          have htp : e'.toBorrowEntry.targetProjection = .nil := rfl
          have hperm_eq : e'.toBorrowEntry.perm = e'.perm := rfl
          have hbody :
              writeStackThinPtrTypedDeref s.frame.locals s.frame.locals e'.toBorrowEntry ptrVal .nil
                (.scalar sc) body.localDecls body.layouts (some accTy) (some accTy) = .ub := by
            unfold writeStackThinPtrTypedDeref
            rw [htp, htl]
            dsimp only [stripTransparentProjections]
            change (let resolvedAccTyOpt := some rPt; _) = _
            dsimp only []
            rw [hcda_false, Bool.false_and]
          unfold writePlaceValue
          dsimp only []
          rw [← hd_eq]
          rw [hpt_res, hslot_r]
          dsimp only []
          rw [hlookup]
          dsimp only []
          rw [hperm_eq]
          rcases hperm with hp | hp <;> rw [hp] <;> exact hbody
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]
      unfold evalStmt; dsimp only []
      rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes (hop tf hframes), hop_ok]
      dsimp only [evalPlaceWrite]; rw [hprot, hw_ub, hcaller]
  · have hlive_a0 : get? s.frame.locals e.localIdx ≠ some .dead :=
      fun hd => hsl_ne (Option.some.inj (hsl_a.symm.trans hd))
    have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
      ⟨refIdx, .cons .deref .nil⟩ op span m
    obtain ⟨slot_r, mls_r, _, hlt_r, hslot_rf, hmls_r, hmls_r_eq, hloc_r⟩ :=
      hfr.lookup_local hdecl_ref
    have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
      hloc_r.cachedLayout_eq
    let tfa := cacheFrameLocalLayout tf refIdx hlt_r (translateTy refDecl.ty body.layouts)
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
      have hder_err := annealDerefOperandToMemPlace_safeRef_ptr_misaligned hstate hdecl_ref href_ty
        hpk_prim hptrRel he htag hdecl_a hlive_a0 hinbounds hmis (translateTy refDecl.ty body.layouts)
        (st := { m with stack := ⟨#[tfa]⟩ }) rfl
      have hdst_err : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨refIdx, .cons .deref .nil⟩) m =
          .error (.undefinedBehavior "dereferencing an unaligned reference")
            { m with stack := ⟨#[tfa]⟩ } := by
        rw [hdst_live, EStateM.bind_eq_error hder_err]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
          ({ m with stack := ⟨#[tfa]⟩ },
            .error (.undefinedBehavior "dereferencing an unaligned reference")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hdst_err]
      exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **`step_safeRef_deref_write_misaligned_simulation` (`LM-3.2`, upgraded to UB simulation)**:
when `_r : &(mut) P` holds an in-bounds `PtrRel` pointer into a live stack local
`e.localIdx` with writable borrow (`e.perm ∈ {.active, .reserved}`), `op`
evaluates to `.scalar sc` in Anneal, and `ptrVal.offsetBytes` is misaligned for
`P` (`annealOffsetMisalignment ... = .ok (some mis)`), executing `*_r = .use op`
raises undefined behavior in BOTH `stepMirFn` (`MirStepNode.fail .ub` via
`checkDerefAlign`) and `Miri.Interpreter.Step.step` (`annealStepHooks`,
`"dereferencing an unaligned reference"`). -/
theorem step_safeRef_deref_write_misaligned_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl allocDecl : LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hop_ok : evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc) s.frame.locals)
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .active ∨ e.perm = .reserved)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    {sl_a : LocalSlot} (hsl_a : get? s.frame.locals e.localIdx = some sl_a)
    (hsl_ne : sl_a ≠ .dead)
    (hinbounds : ptrVal.offsetBytes +
        (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat ≤
      (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat)
    {mis : Miri.Memory.Misalignment}
    (hmis : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.align.abi =
      .ok (some mis))
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing an unaligned reference")) := by
  obtain ⟨ha, m', hm⟩ := step_safeRef_deref_write_misaligned_both_ub hstate hphase hbb hstmt hdecl_ref href_ty hpk_prim hop himm_ref hop_ok hslot_r he htag hperm hdecl_a hsl_a hsl_ne hinbounds hmis hlay_coh
  exact ⟨by rw [ha, hm]; exact .ub m' _, ha, m', hm⟩

/-! ## 7. Tree Borrows Permission Divergences on Safe References (`LM-3.2` vs `LM-3.3`) -/

/-- **`step_safeRef_deref_write_perm_divergence` (`LM-3.2`, genuine divergence)**:
when `_r : &(mut) P` holds an offset-`0` `PtrRel` pointer into a live stack local
`e.localIdx` (`tgtDecl.ty.kind = pointeeKind`) whose borrow permission forbids
mutation (`e.perm = .frozen ∨ e.perm = .disabled`, e.g. writing through a shared
reference after transmuting `&T -> &mut T` or writing through a disabled `&mut T`),
and `op` evaluates to `.scalar sc`, executing `*_r = .use op` diverges:
1. Anneal's `stepMirFn` rejects the write with `MirStepNode.fail .ub`;
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`, before `LM-3.3`
   borrow-tracker hooks are wired) steps `(m', .ok true)` and overwrites
   `e.allocId`'s live stack allocation with `sc`. -/
theorem step_safeRef_deref_write_perm_divergence
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
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hop_ok : evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc) s.frame.locals)
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hperm : e.perm = .frozen ∨ e.perm = .disabled)
    (hlive_t : get? s.frame.locals e.localIdx ≠ some .dead)
    (htgt_kind : ∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
      tgtDecl.ty.kind = pointeeKind) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' msc alloc' memKind,
      ScalarRel sc msc ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.machine.memory.live.find? (fun x => x.1 == e.allocId) =
        some (e.allocId, ⟨memKind, alloc'⟩) ∧
      alloc'.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
        .ok (.fromScalarInt msc) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, hcaller, _, halloc, _⟩ := id hstate
  have hop_tf := hop tf hframes
  refine ⟨?_, ?_⟩
  · have hlookup := (halloc.borrow_sync e he).2
    rw [htag] at hlookup
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt; dsimp only []
    rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes hop_tf, hop_ok]
    dsimp only [evalPlaceWrite, writePlaceValue]
    rw [hprot]; dsimp only []
    cases body.localDecls <;>
    · simp only [hslot_r, hlookup]
      rcases hperm with hp | hp <;> simp [hp, hcaller]
  · have himm_r := himm_ref tf hframes
    have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
      ⟨refIdx, .cons .deref .nil⟩ op span m
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
        translateTy valTy body.layouts := by
      have h1 := hval_prim.translateTy_layoutIdx body.layouts
      rw [hval_kind] at h1; exact h1
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
      obtain ⟨id₀, borTag, hprov_eq, hid_lt, _, hmptr_off, ⟨e', he', htag', hid_eq⟩⟩ := id hptrRel
      have he_eq : e' = e :=
        mem_eq_of_map_nodup halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst e'; subst id₀
      obtain ⟨tgtDecl, hdecl_tgt, htgt_prim⟩ := halloc.target_decl e he
      obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
      obtain ⟨slot_t, _, _, _, hslot_t, _, _, _⟩ := hfr.lookup_local hdecl_tgt
      have ht_ne_dead : slot_t ≠ .dead := fun hd => hlive_t (hslot_t.trans (congrArg some hd))
      have hder_ok := annealDerefOperandToMemPlace_safeRef_ptr_live hstate hdecl_ref href_ty
        hpt_prim hprov_eq hmptr_off he hoff0 hlive_t htgt_kind
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
        ⟨_, _, hop_ub, _⟩ | ⟨sc₁, msc, tf', hop_ok₁, hm_op_ok, hstate_tf', himm_sc, _⟩
      · rw [hop_ok] at hop_ub; cases hop_ub
      · rw [hop_ok] at hop_ok₁
        injection hop_ok₁ with hv_sc _
        injection hv_sc with hsc_eq1
        subst hsc_eq1
        rcases id hstate_tf' with ⟨tf₀', hframes_tf', _, _, hfr_tf', _, _, _, _, _, halloc_tf', _⟩
        injection hframes_tf' with h1_tf; injection h1_tf with h2_tf; subst h2_tf
        obtain ⟨hlive_sync, _⟩ := halloc_tf'.local_alloc_sync tf' rfl e he
        have htr_tgt : translateTy tgtDecl.ty body.layouts = translateTy valTy body.layouts := by
          rw [← htgt_prim.translateTy_layoutIdx body.layouts,
            ← hval_prim.translateTy_layoutIdx body.layouts, htgt_kind tgtDecl hdecl_tgt, hval_kind]
        obtain ⟨_, _, hshape_fn⟩ := hlive_sync slot_t hslot_t ht_ne_dead
        obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hshape_fn tgtDecl hdecl_tgt
        obtain ⟨sc', msc', hsc_eq, hmsc_eq, hrel_sc, hsz_sc, hbool_val, hchar_val⟩ :=
          himm_sc.of_primitive_scalar hval_prim
        injection hsc_eq with hsc_eq'; subst hsc_eq'
        have hmsc_eq' : msc = msc' := by
          injection hmsc_eq with h1
          unfold Miri.Memory.Scalar.fromScalarInt at h1
          injection h1 with h2; injection h2
        subst hmsc_eq'
        have hshape_sc : StackScalarAllocShape (translateSizeBytes sc.sizeBytes)
            localAlloc.allocation := by
          rw [← hsz_sc, ← htr_tgt]; exact hshape_la
        obtain ⟨alloc', hw_alloc, _, _, _, hread_alloc'⟩ :=
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
        refine ⟨_, msc, alloc', localAlloc.kind, hrel_sc,
          miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok
            rfl hfr_tf'.location_eq,
          live_find_filter_push_self₂ m.machine.memory.live e.allocId _, hread_alloc'⟩

/-- **`step_safeRef_deref_read_disabled_divergence` (`LM-3.2`, genuine divergence)**:
when `_r : &(mut) P` holds an offset-`0` `PtrRel` pointer into a live initialized
stack local `e.localIdx` (`get? s.frame.locals e.localIdx = some (.init (.scalar sc))`,
`tgtDecl.ty.kind = dstDecl.ty.kind`), `_d` is a live immediate local, and `e.perm = .disabled`
(for example after a conflicting direct write to `e.localIdx` invalidated `_r`'s
borrow tag), executing `_d = (copy|move) *_r` diverges:
1. Anneal's `stepMirFn` rejects the read with `MirStepNode.fail .ub`;
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`, before `LM-3.3`
   borrow-tracker hooks are wired) steps `(m', .ok true)` and stores
   `.scalar (.fromScalarInt msc)` (`ScalarRel sc msc`) into `dstIdx`. -/
theorem step_safeRef_deref_read_disabled_divergence
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
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hperm : e.perm = .disabled)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (htgt_kind : ∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
      tgtDecl.ty.kind = dstDecl.ty.kind)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' msc,
      ScalarRel sc msc ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc)))) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, hcaller, _, halloc, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · have hlookup := (halloc.borrow_sync e he).2
    rw [htag] at hlookup
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    rcases hopKind with rfl | rfl <;>
    · unfold evalStmt evalRvalue evalOperand readProjectedValue; dsimp only []
      cases body.localDecls <;>
        simp [hslot_r, hlookup, hperm]
  · obtain ⟨himm_dst, himm_ref⟩ := himm tf hframes
    have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
      ⟨dstIdx, .nil⟩ (opKind ⟨refIdx, .cons .deref .nil⟩) span m
    have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
    rw [htr_dst] at hm_stmt
    obtain ⟨slot_d, mls_d, _, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
      hfr.lookup_local hdecl_dst
    have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
    have hfra := hstate_a.frame_rel_singleton rfl
    obtain ⟨slot_r, mls_r, _, hlt_ra, hslot_ra, hmls_r, hmls_r_eq, hloc_r⟩ :=
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
    have hsr_eq : slot_r = .init (.ptr ptrVal 8) := Option.some.inj (hslot_ra.symm.trans hslot_r)
    subst hsr_eq
    rcases hloc_r.ref_immediate_cases href_ty himm_ra with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmr_ptr⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
      have hmls_r' : tfa.locals[refIdx]'hlt_ra =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_r.layout⟩ := by
        rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
      have hop_ptr := annealEvalOperand_deref_live hopKind
        (known := some (translateTy dstDecl.ty body.layouts)) (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_ra hdecl_ref hmls_r' hcache_r
      obtain ⟨id₀, borTag, hprov_eq, hid_lt, _, hmptr_off, ⟨e', he', htag', hid_eq⟩⟩ := id hptrRel
      have he_eq : e' = e :=
        mem_eq_of_map_nodup halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst e'; subst id₀
      obtain ⟨tgtDecl, hdecl_tgt, htgt_prim⟩ := halloc.target_decl e he
      obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
      have ht_ne_some_dead : get? s.frame.locals e.localIdx ≠ some .dead := by
        rw [htarget]; simp
      have htgt_kind_eq : tgtDecl.ty.kind = dstDecl.ty.kind := htgt_kind tgtDecl hdecl_tgt
      have htr_tgt : translateTy tgtDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
        rw [← htgt_prim.translateTy_layoutIdx body.layouts, htgt_kind_eq, hlay0_eq]
      obtain ⟨_, _, _, halloc_a⟩ : ∃ a b c, AllocMapRel body s { m with stack := ⟨#[tfa]⟩ } allocMap := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc_a, _⟩ := id hstate_a
        exact ⟨(), (), (), halloc_a⟩
      obtain ⟨slot_t, mls_t, _, _, hslot_t, hmls_t, _, hloc_t⟩ := hfra.lookup_local hdecl_tgt
      have hst_eq : slot_t = .init (.scalar sc) := Option.some.inj (hslot_t.symm.trans htarget)
      subst hst_eq
      obtain ⟨⟨lay_t, hlay_t⟩, _, hshape_f⟩ :=
        (halloc_a.local_alloc_sync tfa rfl e he).1 _ hslot_t (by simp)
      obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hshape_f tgtDecl hdecl_tgt
      rw [htr_tgt] at hshape_la
      obtain ⟨_, _, _, _, _, hnz_sz⟩ := hdst_prim.size_align_ok body.layouts
      have hder_ok := annealDerefOperandToMemPlace_safeRef_ptr_live hstate hdecl_ref href_ty
        hprim0 hprov_eq hmptr_off he hoff0 ht_ne_some_dead htgt_kind
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
      have hloc_t_1 : LocalRelLM3_1 m.machine allocMap tgtDecl body.layouts
          (.init (.scalar sc)) mls_t := by
        rw [hmls_t_eq'] at hloc_t ⊢; exact hloc_t.indirect_base
      obtain ⟨_, hsc_la'⟩ := hloc_t_1.indirect_stackAllocPlace_spec hmls_t_eq' hbase
        hfind_la (halloc_a.live_key_unique e he) (htr_tgt ▸ hnz_sz)
      obtain ⟨_, hbool_t, hchar_t, msc_t, hrel_t, hread_ok⟩ := hsc_la' sc rfl
      rw [htr_tgt] at hread_ok
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
      have hrd_ne : refIdx ≠ dstIdx := by
        intro hrd; subst hrd
        rw [hdecl_dst] at hdecl_ref; injection hdecl_ref with hd_eq; subst hd_eq
        rcases hdst_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at href_ty <;> cases href_ty
      have hlt_db : dstIdx < tfb.locals.size := by
        simp only [tfb, tfa, cacheFrameLocalLayout_size]; exact hlt_d
      have hdb_get : tfb.locals[dstIdx]? =
          some { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } := by
        simp only [tfb, tfa, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ hrd_ne, Array.getElem?_set_self, hmls_d_eq]
      obtain ⟨oldImm, hmd_imm⟩ : ∃ oldImm, mls_d.value = .live (.immediate oldImm) := by
        rcases hloc_d with hloc_d_1 | ⟨_, _, _, _, _, _, _, _⟩
        rotate_left
        · exact ⟨_, rfl⟩
        cases hloc_d_1 with
        | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
        | base hb =>
          cases hb with
          | dead _ _ => exact absurd rfl hsd_ne
          | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst _ hmls_d mp)
          | immediate _ _ _ _ _ => exact ⟨_, rfl⟩
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
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
          m =
          ({ m with stack := ⟨#[{ tfb with
              locals := tfb.locals.set dstIdx
                { tfb.locals[dstIdx]'hlt_db with
                  value := .live (.immediate (.scalar (.fromScalarInt msc_t))) }
                hlt_db }]⟩ }, .ok ()) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_ok]
        rw [annealReadImmediate_indirect_prim_eq₂ hdst_prim]
        rw [EStateM.bind_eq_ok hread_m, hw_ok]
      refine ⟨_, _, msc_t, hrel_t,
        miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok
          rfl hfrb.location_eq, rfl, ?_⟩
      simp [Array.getElem?_set_self]

/-- **`evalRvalue_reborrow_safeRef_perm_divergence` (`LM-3.2`, genuine divergence)**:
complement to `evalRvalue_reborrow_safeRef_simulation`: when `_r : &(mut) P`
holds an offset-`0` `PtrRel` pointer into a live stack local `e.localIdx`
(`tgtDecl.ty.kind = pointeeKind`), `_d` is a live immediate safe-reference
local, and `_r`'s borrow permission forbids the reborrow
(`e.perm = .disabled ∨ (e.perm = .frozen ∧ bk ≠ .shared)`, e.g. mutable reborrow
`&mut *_r` of a frozen borrow or any reborrow `&*_r` of a disabled borrow),
executing `_d = &(mut) *_r` diverges:
1. Anneal's `stepMirFn` rejects the reborrow with `MirStepNode.fail .ub`;
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`, before `LM-3.3`
   borrow-tracker hooks are wired) steps `(m', .ok true)` and writes a pointer
   to `e.allocId` into `dstIdx`. -/
theorem evalRvalue_reborrow_safeRef_perm_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {dstDecl refDecl : LocalDecl}
    {bk : BorrowKind} {refMut dstMut : Mutability}
    {pointeeKind dstPointee : RigidTy} {span : String}
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
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hperm : e.perm = .disabled ∨ (e.perm = .frozen ∧ bk ≠ .shared))
    (hlive_t : get? s.frame.locals e.localIdx ≠ some .dead)
    (htgt_kind : ∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
      tgtDecl.ty.kind = pointeeKind)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              .concrete e.allocId borTag⟩)))) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, halloc, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · have hlookup := (halloc.borrow_sync e he).2
    rw [htag] at hlookup
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []
    rw [hslot_r]; dsimp only []
    cases Bool.and (Nat.beq 8 (layoutPointerBytes body.layouts))
        (checkDerefAlign body.localDecls body.layouts _ ptrVal.offsetBytes) with
    | false => rfl
    | true =>
      dsimp only []
      rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry]
      rcases hperm with hp | ⟨hp, hm⟩
      · rw [hp]
      · rw [hp]
        rcases bk with _ | _
        · exact absurd rfl hm
        · rfl
  · obtain ⟨himm_d, himm_r⟩ := himm tf hframes
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
          (.Ref .Erased (translateBorrowKind bk) (translatePlace ⟨refIdx, .cons .deref .nil⟩))
          ⟨dstIdx, #[]⟩) m := rfl
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
    obtain ⟨slot_r, mls_r, _, hlt_ra, hslot_ra, hmls_ra, hmls_ra_eq, hloc_r⟩ :=
      hfra.lookup_local hdecl_ref
    have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
      hloc_r.cachedLayout_eq
    have himm_ra : ∀ mp, mls_r.value ≠ .live (.indirect mp) :=
      himm_r.cache_layout hlt_d _ mls_r hmls_ra
    have hsr_eq : slot_r = .init (.ptr ptrVal 8) := Option.some.inj (hslot_ra.symm.trans hslot_r)
    subst hsr_eq
    rcases hloc_r.ref_immediate_cases href_ty himm_ra with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmr_ptr⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
      obtain ⟨id₀, borTag, hprov_eq, _, _, hmptr_off, ⟨e', he', htag', hid_eq⟩⟩ := hptrRel
      have he_eq : e' = e :=
        mem_eq_of_map_nodup halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst e'; subst id₀
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
      obtain ⟨oldImm, hmdb_imm⟩ : ∃ oldImm, mls_db.value = .live (.immediate oldImm) := by
        rcases hloc_db.ref_immediate_cases hdst_ty himm_db with
          ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
        · exact absurd h hsd_ne
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
      refine ⟨_, _, borTag,
        miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok
          rfl hfrb.location_eq, rfl, ?_⟩
      rw [hmptr_eq]; simp [Array.getElem?_set_self]

/-! ## 8. `PlaceMention` Under `StateRelLM3_2` -/

/-- **`step_placeMention_local_lm3_2_simulation`**: `PlaceMention(_x)` on a live
unprojected local `_x` (`get? s.frame.locals loc ≠ some .dead`) — whether `_x`
is a safe-reference local, raw-pointer local, scalar local, or borrowed
memory-backed local — steps in lockstep under `StepRelLM3_2`, memoizing `_x`'s
layout in `lean-miri` without altering `allocMap` or any local value. -/
theorem step_placeMention_local_lm3_2_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.placeMention ⟨loc, .nil⟩, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hlive : get? s.frame.locals loc ≠ some .dead) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨slot, _, _, hlt_mf, hslot, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hslot_ne : slot ≠ .dead := fun hd => hlive (hslot.trans (congrArg some hd))
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have ha : evalStmt s ⟨.placeMention ⟨loc, .nil⟩, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s s.frame.locals) := by
    unfold evalStmt; dsimp only []; rw [hslot]
    cases slot with
    | dead => exact absurd rfl hslot_ne
    | uninit => rfl
    | init _ => rfl
  have hcache : ∀ l, (tf.locals[loc]'hlt_mf).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls_eq]; exact hloc.cachedLayout_eq
  have hm := evalStatement_placeMention_eq (span := span) hframes hlt_mf hdecl hcache
  have hstate' := hstate.cache_layout hframes hdecl hlt_mf
  rcases hstate' with
    ⟨tfa, hframes_a, hretCont, hretPlace, hfra, _, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  injection hframes_a with h1; injection h1 with h2; subst tfa
  rw [ha, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfra.location_eq]
  apply StepRelLM3_2.step
  refine .mk _ rfl hretCont hretPlace hfra.advance hcal hstack hprot hcaller hbor ?_ hdisj
  refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
    halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
  intro tf' htf' e he
  injection htf' with h3; injection h3 with h4; subst tf'
  exact halloc.local_alloc_sync _ rfl e he

/-- **`step_placeMention_safeRef_deref_simulation` (`LM-3.2` `PlaceMention(*_r)` Agreement)**:
for an immediate safe-reference local `_r : &(mut) P` (`IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 }`),
executing `PlaceMention(*_r)` (`let _ = *_r;`) steps in lockstep under `StepRelLM3_2`
across the valid safe-reference regime:
1. If `_r` is `.dead`, both machines report undefined behavior (`StepRelLM3_2.ub`).
2. If `_r` holds `.init (.ptr ptrVal 8)` at offset `0` into a live stack local
   `e.localIdx` (`get? s.frame.locals e.localIdx ≠ some .dead`) of matching type
   `pointeeKind` — **even when `e.localIdx` is uninitialized (`.uninit`) or
   `e.perm = .disabled`** — both machines step normally without reading pointee
   memory (`StepRelLM3_2.step`), preserving `StateRelLM3_2` across `allocMap`. -/
theorem step_placeMention_safeRef_deref_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {refDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hvalid_or_dead :
      get? s.frame.locals refIdx = some .dead ∨
      ∃ ptrVal e,
        get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) ∧
        e ∈ allocMap ∧ e.tag = ptrVal.tag ∧ ptrVal.offsetBytes = 0 ∧
        get? s.frame.locals e.localIdx ≠ some .dead ∧
        (∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
          tgtDecl.ty.kind = pointeeKind)) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, halloc, _⟩ := id hstate
  have himm_r := himm_ref tf hframes
  obtain ⟨slot_r, mls_r, _, hlt_r, hslot_r, hmls_r, hmls_r_eq, hloc_r⟩ :=
    hfr.lookup_local hdecl_ref
  have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
    hloc_r.cachedLayout_eq
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  rcases hvalid_or_dead with hdead | ⟨ptrVal, e, hptr, he, htag, hoff0, hlive_t, htgt_kind⟩
  · have hsr_eq : slot_r = .dead := Option.some.inj (hslot_r.symm.trans hdead)
    subst hsr_eq
    rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
      ⟨_, hmr_dead⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩
    · have hmls_dead : tf.locals[refIdx]'hlt_r = ⟨.dead, mls_r.layout⟩ := by
        rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_dead; subst hmr_dead; rfl
      have hdead_ev := annealEvalPlace_deref_dead hframes hlt_r hdecl_ref hmls_dead hcache_r
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩) m =
          ({ m with stack := ⟨#[cacheFrameLocalLayout tf refIdx hlt_r
              (translateTy refDecl.ty body.layouts)]⟩ },
            .error (.undefinedBehavior "read of dead local")) := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt translateStmtKind annealStepHooks
        dsimp only [Miri.Interpreter.runRvalue]; rw [hdead_ev]; rfl
      have ha_err : evalStmt s ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only []; rw [hslot_r]
      rw [ha_err, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      exact .ub _ _
    · cases h
    · cases h
    · cases h
  · have hsr_eq : slot_r = .init (.ptr ptrVal 8) := Option.some.inj (hslot_r.symm.trans hptr)
    subst hsr_eq
    rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmr_ptr⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
      obtain ⟨id₀, borTag, hprov_eq, _, _, hmptr_off, ⟨e', he', htag', hid_eq⟩⟩ := hptrRel
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
      have hp_ok : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨refIdx, .cons .deref .nil⟩) m =
          .ok ⟨.memory ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
                some (.concrete e.allocId borTag)⟩, .none, none⟩,
              translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts⟩
            { m with stack := ⟨#[cacheFrameLocalLayout tf refIdx hlt_r
                (translateTy refDecl.ty body.layouts)]⟩ } := by
        rw [hlive_ev, EStateM.bind_eq_ok hder_ptr]; rfl
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩) m =
          ({ m with stack := ⟨#[cacheFrameLocalLayout tf refIdx hlt_r
              (translateTy refDecl.ty body.layouts)]⟩ }, .ok ()) := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt translateStmtKind annealStepHooks
        dsimp only [Miri.Interpreter.runRvalue]; rw [hp_ok]; rfl
      have ha_ok : evalStmt s ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩
          body.localDecls body.layouts = MirStepNode.step (advanceStmt s s.frame.locals) := by
        unfold evalStmt; dsimp only []; rw [hslot_r]; rfl
      have hstate' := hstate.cache_layout hframes hdecl_ref hlt_r
      rcases hstate' with
        ⟨tfa, hframes_a, hretCont, hretPlace, hfra, _, hstack, hprot, hcaller, hbor, halloc_a, hdisj⟩
      injection hframes_a with h1; injection h1 with h2; subst tfa
      rw [ha_ok, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_ok rfl hfra.location_eq]
      apply StepRelLM3_2.step
      refine .mk _ rfl hretCont hretPlace hfra.advance hcal hstack hprot hcaller hbor ?_ hdisj
      refine ⟨halloc_a.tags_nodup, halloc_a.local_to_alloc_unique, halloc_a.alloc_to_local_injective,
        halloc_a.target_decl, halloc_a.base_addr_valid, halloc_a.borrow_sync,
        halloc_a.live_key_unique, ?_⟩
      intro tf' htf' e₀ he₀
      injection htf' with h3; injection h3 with h4; subst tf'
      exact halloc_a.local_alloc_sync _ rfl e₀ he₀

/-- **`step_placeMention_safeRef_deref_uninit_simulation` (`LM-3.2` `PlaceMention(*_r)` Uninitialized Reference UB)**:
when `_r : &(mut) P` is `.uninit`, executing `PlaceMention(*_r)` raises undefined
behavior in BOTH `stepMirFn` (`MirStepNode.fail .ub`) and
`Miri.Interpreter.Step.step` (`annealStepHooks`,
`"read of uninitialized local"`). -/
theorem step_placeMention_safeRef_deref_uninit_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {refDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hun : get? s.frame.locals refIdx = some .uninit) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "read of uninitialized local")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have himm_r := himm_ref tf hframes
  obtain ⟨slot_r, mls_r, _, hlt_r, hslot_r, hmls_r, hmls_r_eq, hloc_r⟩ :=
    hfr.lookup_local hdecl_ref
  have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
    hloc_r.cachedLayout_eq
  let tfa := cacheFrameLocalLayout tf refIdx hlt_r (translateTy refDecl.ty body.layouts)
  have hsr_eq : slot_r = .uninit := Option.some.inj (hslot_r.symm.trans hun)
  subst hsr_eq
  refine ⟨?_, ?_⟩
  · rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]; unfold evalStmt; dsimp only []; rw [hslot_r]; rfl
  · rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
      ⟨h, _⟩ | ⟨_, hmr_un⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩
    · cases h
    · have hmls_un : tf.locals[refIdx]'hlt_r = ⟨.live (.immediate .uninit), mls_r.layout⟩ := by
        rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_un; subst hmr_un; rfl
      have hlive_ev := annealEvalPlace_deref_live hframes hlt_r hdecl_ref hmls_un hcache_r
      have hder_err := annealDerefOperandToMemPlace_safeRef_uninit (ly := body.layouts)
        hdecl_ref href_ty hpk_prim (translateTy refDecl.ty body.layouts)
        { m with stack := ⟨#[tfa]⟩ }
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩) m =
          ({ m with stack := ⟨#[tfa]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt translateStmtKind annealStepHooks
        dsimp only [Miri.Interpreter.runRvalue]; rw [hlive_ev, EStateM.bind_eq_error hder_err]; rfl
      exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩
    · cases h
    · cases h

/-- **`step_placeMention_safeRef_deref_divergence` (`LM-3.2` `PlaceMention(*_r)` Divergence)**:
complement to `step_placeMention_safeRef_deref_simulation`: because Anneal's
`evalStmt` (`Statements.lean`) evaluates `.placeMention ⟨refIdx, .cons .deref .nil⟩`
by checking `get? s.frame.locals refIdx = some (.init _)` without validating the
dereferenced reference target, while `lean-miri`'s `evalStatement` evaluates
`evalPlace(*_r)` through `PointerPlaceMachine.dereference`
(`annealSafeRefDerefCheck`), `PlaceMention(*_r)` diverges across all four
initialized invalid safe-reference states:
1. `_r` holds an integer scalar `.init (.scalar sc)` (null or provenance-less),
2. `_r` holds `.init (.ptr ptrVal 8)` whose target local `e.localIdx` is `.dead`,
3. `_r` holds an out-of-bounds `.init (.ptr ptrVal 8)` into a live `e.localIdx`, or
4. `_r` holds a misaligned `.init (.ptr ptrVal 8)` into a live `e.localIdx`.

In every case, Anneal steps `stepMirFn body s = .step (advanceStmt s s.frame.locals)`
while `lean-miri` raises `.error (.undefinedBehavior msg)`. -/
theorem step_placeMention_safeRef_deref_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {refDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hbad :
      (∃ sc, get? s.frame.locals refIdx = some (.init (.scalar sc))) ∨
      (∃ ptrVal e,
        get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) ∧
        e ∈ allocMap ∧ e.tag = ptrVal.tag ∧
        get? s.frame.locals e.localIdx = some .dead) ∨
      (∃ ptrVal e allocDecl,
        get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) ∧
        e ∈ allocMap ∧ e.tag = ptrVal.tag ∧
        get? body.localDecls e.localIdx = some allocDecl ∧
        get? s.frame.locals e.localIdx ≠ some .dead ∧
        (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat <
          ptrVal.offsetBytes +
            (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat) ∨
      (∃ ptrVal e allocDecl mis,
        get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) ∧
        e ∈ allocMap ∧ e.tag = ptrVal.tag ∧
        get? body.localDecls e.localIdx = some allocDecl ∧
        get? s.frame.locals e.localIdx ≠ some .dead ∧
        ptrVal.offsetBytes +
          (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat ≤
          (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat ∧
        annealOffsetMisalignment
          (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
          (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.align.abi =
          .ok (some mis))) :
    stepMirFn body s = .step (advanceStmt s s.frame.locals) ∧
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have himm_r := himm_ref tf hframes
  obtain ⟨slot_r, mls_r, _, hlt_r, hslot_r, hmls_r, hmls_r_eq, hloc_r⟩ :=
    hfr.lookup_local hdecl_ref
  have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
    hloc_r.cachedLayout_eq
  let tfa := cacheFrameLocalLayout tf refIdx hlt_r (translateTy refDecl.ty body.layouts)
  have hm_err_of_place : ∀ msg,
      annealEvalPlace body.localDecls body.layouts
        (translatePlace ⟨refIdx, .cons .deref .nil⟩) m =
        .error (.undefinedBehavior msg) { m with stack := ⟨#[tfa]⟩ } →
      ∃ m' msg',
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg')) := by
    intro msg hp_err
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩) m =
        ({ m with stack := ⟨#[tfa]⟩ }, .error (.undefinedBehavior msg)) := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt translateStmtKind annealStepHooks
      dsimp only [Miri.Interpreter.runRvalue]; rw [hp_err]; rfl
    exact ⟨_, msg, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩
  rcases hbad with ⟨sc, hsc⟩ | ⟨ptrVal, e, hptr, he, htag, hdead_t⟩ |
    ⟨ptrVal, e, allocDecl, hptr, he, htag, hdecl_a, hlive_t, hoob⟩ |
    ⟨ptrVal, e, allocDecl, mis, hptr, he, htag, hdecl_a, hlive_t, hinb, hmis⟩
  · have hsr_eq : slot_r = .init (.scalar sc) := Option.some.inj (hslot_r.symm.trans hsc)
    subst hsr_eq
    refine ⟨?_, ?_⟩
    · rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt; dsimp only []; rw [hslot_r]; rfl
    · rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
        ⟨h, _⟩ | ⟨h, _⟩ | ⟨sc', msc, hs_eq, hsz8, hrel, hmr_sc⟩ | ⟨_, _, h, _⟩
      · cases h
      · cases h
      · injection hs_eq with hv_eq; injection hv_eq with hsc_eq; subst hsc_eq
        have hmls_sc : tf.locals[refIdx]'hlt_r =
            ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_r.layout⟩ := by
          rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_sc; subst hmr_sc; rfl
        have hlive_ev := annealEvalPlace_deref_live hframes hlt_r hdecl_ref hmls_sc hcache_r
        have hsc_chk := annealDerefOperandToMemPlace_safeRef_scalarInt (ly := body.layouts)
          hdecl_ref href_ty hpk_prim hrel hsz8 (translateTy refDecl.ty body.layouts)
          { m with stack := ⟨#[tfa]⟩ }
        by_cases h0 : sc.bits = 0
        · exact hm_err_of_place _ (by rw [hlive_ev, EStateM.bind_eq_error (hsc_chk.1 h0)])
        · exact hm_err_of_place _ (by rw [hlive_ev, EStateM.bind_eq_error (hsc_chk.2 h0)])
      · cases h
  · have hsr_eq : slot_r = .init (.ptr ptrVal 8) := Option.some.inj (hslot_r.symm.trans hptr)
    subst hsr_eq
    refine ⟨?_, ?_⟩
    · rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt; dsimp only []; rw [hslot_r]; rfl
    · rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
        ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmr_ptr⟩
      · cases h
      · cases h
      · cases h
      · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
        have hmls_ptr : tf.locals[refIdx]'hlt_r =
            ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
              mls_r.layout⟩ := by
          rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
        have hlive_ev := annealEvalPlace_deref_live hframes hlt_r hdecl_ref hmls_ptr hcache_r
        have hder_err := annealDerefOperandToMemPlace_safeRef_ptr_dead hstate hdecl_ref href_ty
          hpk_prim hptrRel he htag hdead_t (translateTy refDecl.ty body.layouts)
          (st := { m with stack := ⟨#[tfa]⟩ }) rfl
        exact hm_err_of_place _ (by rw [hlive_ev, EStateM.bind_eq_error hder_err])
  · have hsr_eq : slot_r = .init (.ptr ptrVal 8) := Option.some.inj (hslot_r.symm.trans hptr)
    subst hsr_eq
    refine ⟨?_, ?_⟩
    · rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt; dsimp only []; rw [hslot_r]; rfl
    · rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
        ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmr_ptr⟩
      · cases h
      · cases h
      · cases h
      · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
        have hmls_ptr : tf.locals[refIdx]'hlt_r =
            ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
              mls_r.layout⟩ := by
          rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
        have hlive_ev := annealEvalPlace_deref_live hframes hlt_r hdecl_ref hmls_ptr hcache_r
        have hder_err := annealDerefOperandToMemPlace_safeRef_ptr_oob hstate hdecl_ref href_ty
          hpk_prim hptrRel he htag hdecl_a hlive_t hoob (translateTy refDecl.ty body.layouts)
          (st := { m with stack := ⟨#[tfa]⟩ }) rfl
        exact hm_err_of_place _ (by rw [hlive_ev, EStateM.bind_eq_error hder_err])
  · have hsr_eq : slot_r = .init (.ptr ptrVal 8) := Option.some.inj (hslot_r.symm.trans hptr)
    subst hsr_eq
    refine ⟨?_, ?_⟩
    · rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt; dsimp only []; rw [hslot_r]; rfl
    · rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
        ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmr_ptr⟩
      · cases h
      · cases h
      · cases h
      · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
        have hmls_ptr : tf.locals[refIdx]'hlt_r =
            ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
              mls_r.layout⟩ := by
          rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
        have hlive_ev := annealEvalPlace_deref_live hframes hlt_r hdecl_ref hmls_ptr hcache_r
        have hder_err := annealDerefOperandToMemPlace_safeRef_ptr_misaligned hstate hdecl_ref href_ty
          hpk_prim hptrRel he htag hdecl_a hlive_t hinb hmis (translateTy refDecl.ty body.layouts)
          (st := { m with stack := ⟨#[tfa]⟩ }) rfl
        exact hm_err_of_place _ (by rw [hlive_ev, EStateM.bind_eq_error hder_err])

/-! ## 9. Unified `LM-3.2` Statement and Terminator Simulation -/

/-- **`step_nop_lm3_2_simulation`**: `StatementKind.nop` steps in lockstep across
any `StateRelLM3_2`-related state (including states with live safe references,
raw pointers, and promoted stack allocations), preserving `allocMap`. -/
theorem step_nop_lm3_2_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.nop, span⟩) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have ha : evalStmt s ⟨.nop, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s s.frame.locals) := rfl
  have hm : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.nop, span⟩) m =
      (m, .ok ()) := rfl
  rw [ha, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm hframes
    hfr.location_eq]
  apply StepRelLM3_2.step
  refine .mk _ rfl hretCont hretPlace hfr.advance hcal hstack hprot hcaller hbor ?_ hdisj
  refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
    halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
  intro tf' htf' e he
  injection htf' with h1
  injection h1 with h2
  subst h2
  exact halloc.local_alloc_sync tf hframes e he

/-- **`step_scalar_use_lm3_2_simulation`**: scalar assignment `_d = .use op`
into an immediate primitive-scalar local `_d` from any `StateRelLM3_2`-related
state (including non-empty `allocMap` with live safe references, raw pointers,
and promoted stack allocations) steps in lockstep preserving `allocMap` (or
reports UB in both machines if `op` or `_d` is dead/uninitialized). -/
theorem step_scalar_use_lm3_2_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩)
    {dstDecl : LocalDecl} {valTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hval_kind : valTy.kind = dstDecl.ty.kind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, hstack, hprot, hcaller, hbor, _, _⟩ := id hstate
  have himm_d := himm_dst tf hframes
  have hop_tf := hop tf hframes
  have hval_prim : IsPrimScalarTy valTy := by
    rcases hdst_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact Or.inl (hval_kind.trans hk)
    · exact Or.inr (Or.inl (hval_kind.trans hk))
    · exact Or.inr (Or.inr (Or.inl ⟨it, hval_kind.trans hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ut, hval_kind.trans hk⟩))
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts ⟨dstIdx, .nil⟩ op span m
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval : annealEvalPlace body.localDecls body.layouts (translatePlace ⟨dstIdx, .nil⟩) m =
      .ok ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d
            (translateTy dstDecl.ty body.layouts)]⟩ } :=
    annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a : StateRelLM3_2 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_dst hlt_d
  have hop_tfa : WellTypedScalarOperand body tfa op valTy :=
    hop_tf.of_cacheFrameLocalLayout dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  rcases evalOperand_scalar_lm3_2_simulation hstate_a rfl hop_tfa hval_prim
      (some (translateTy dstDecl.ty body.layouts)) with
    ⟨m_op, msg_op, hop_ub, hm_op_ub⟩ |
    ⟨sc, msc, tf', hop_ok, hm_op_ok, hstate_tf', himm_sc, _, htf'_preserve⟩
  · have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes hop_tf, hop_ub]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
        (m_op, .error (.undefinedBehavior msg_op)) := by
      rw [hm_stmt]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval]
      dsimp only []
      rw [estate_bind_assoc₂, EStateM.bind_eq_error hm_op_ub]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · have himm_dst_rel : ImmediateRel dstDecl.ty body.layouts (.scalar sc)
        (.scalar (.fromScalarInt msc)) :=
      himm_sc.of_ty_kind_eq hval_prim hval_kind
    have hfr_tf' := hstate_tf'.frame_rel_singleton rfl
    obtain ⟨_, mls_dc, _, hlt_dc, _, hmls_dc, hmls_dc_eq, hloc_dc⟩ :=
      hfr_tf'.lookup_local hdecl_dst
    have hd_tfa : (tfa.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some mls_d.value := by
      simp [tfa, cacheFrameLocalLayout, Array.getElem?_set_self, hmls_d_eq]
    have hd_Val : mls_dc.value = mls_d.value := by
      have hp := htf'_preserve dstIdx
      rw [hd_tfa, hmls_dc] at hp
      injection hp
    have hnot_ind_d := himm_d mls_d hmls_d
    cases hloc_d with
    | ref _ _ _ _ _ _ hty_ref _ =>
      exfalso
      rcases hdst_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hty_ref <;> cases hty_ref
    | lm3_1 hloc_d_1 =>
      cases hloc_d_1 with
      | rawPtr _ _ _ _ _ _ hty_raw _ =>
        exfalso
        rcases hdst_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hty_raw <;> cases hty_raw
      | base hloc_d_b =>
        cases hloc_d_b with
        | indirect _ mp _ _ _ _ => exact absurd rfl (hnot_ind_d mp)
        | dead _ _ =>
          have hdc_dead : tf'.locals[dstIdx]? = some ⟨.dead, mls_dc.layout⟩ := by
            rw [hmls_dc]; rcases mls_dc with ⟨vd, ld⟩; dsimp only at hd_Val; rw [hd_Val]
          have hget_dc := frame_getLocal_of_getElem? tf' dstIdx _ hdc_dead
          have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
              body.localDecls body.layouts = MirStepNode.fail .ub := by
            unfold evalStmt; dsimp only []
            rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes hop_tf, hop_ok]
            dsimp only []; rw [hslot_d]
          have hm_err : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) ()
              (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
              ({ m with stack := ⟨#[tf']⟩ }, .error (.undefinedBehavior "write to dead local")) := by
            rw [hm_stmt]
            unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok hdst_eval]
            dsimp only []
            rw [estate_bind_assoc₂, EStateM.bind_eq_ok hm_op_ok,
              annealWriteImmediate_dead (m := { m with stack := ⟨#[tf']⟩ }) (id0 := tf.localsIdentity)
                rfl hget_dc]
          rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
            hm_err]
          exact .ub _ _
        | immediate _ oldImm _ _ hvald =>
          have hsd_ne : slot_d ≠ .dead := by
            rcases hvald with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> simp
          have hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx :=
            hstate.immediate_not_in_allocMap hframes hslot_d hsd_ne himm_d
          have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor dstIdx none hnot_dst
          have hdc_live : tf'.locals[dstIdx]? =
              some ⟨.live (.immediate oldImm), mls_dc.layout⟩ := by
            rw [hmls_dc]; rcases mls_dc with ⟨vd, ld⟩; dsimp only at hd_Val; rw [hd_Val]
          have hget_dc := frame_getLocal_of_getElem? tf' dstIdx _ hdc_live
          have hw_ok := annealWriteImmediate_live
            (val := .scalar (.fromScalarInt msc))
            (m := { m with stack := ⟨#[tf']⟩ }) (id0 := tf.localsIdentity)
            (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dc hget_dc
          have hm_ok : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) ()
              (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
              ({ m with stack := ⟨#[{ tf' with
                  locals := tf'.locals.set dstIdx
                    { tf'.locals[dstIdx]'hlt_dc with
                      value := .live (.immediate (.scalar (.fromScalarInt msc))) }
                    hlt_dc }]⟩ },
                .ok ()) := by
            rw [hm_stmt]
            unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok hdst_eval]
            dsimp only []
            rw [estate_bind_assoc₂, EStateM.bind_eq_ok hm_op_ok, hw_ok]
          rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
            hfr_tf'.location_eq]
          have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
              body.localDecls body.layouts =
              MirStepNode.step
                (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc))) s.memory) := by
            unfold evalStmt; dsimp only []
            rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes hop_tf, hop_ok]
            dsimp only []; rw [hslot_d]
            cases slot_d with
            | dead => exact absurd rfl hsd_ne
            | uninit =>
              simp only [set?_eq_some_set hlt_af_d, hprot, hbor_inv]
              congr 2; generalize s.memory = mem at hprot ⊢; cases mem; dsimp at hprot ⊢; subst hprot; rfl
            | init _ =>
              simp only [set?_eq_some_set hlt_af_d, hprot, hbor_inv]
              congr 2; generalize s.memory = mem at hprot ⊢; cases mem; dsimp at hprot ⊢; subst hprot; rfl
          rw [ha_ok]
          refine .step _ _ ?_
          have hnew_d : LocalRelLM3_2 m.machine (allocMap.map id) dstDecl body.layouts
              (.init (.scalar sc))
              { tf'.locals[dstIdx]'hlt_dc with
                value := .live (.immediate (.scalar (.fromScalarInt msc))) } := by
            rw [List.map_id]
            exact .lm3_1 (.base (.immediate (.init (.scalar sc)) (.scalar (.fromScalarInt msc)) _
              (by rw [hmls_dc_eq]; exact hloc_dc.cachedLayout_eq)
              (Or.inr ⟨_, rfl, himm_dst_rel⟩)))
          have hval_dc : (tf'.locals[dstIdx]'hlt_dc).value = .live (.immediate oldImm) := by
            rw [hmls_dc_eq, hd_Val]
          have hstep_rel := hstate_tf'.advance_write_immediate_perm_map rfl id
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            hdecl_dst hnot_dst hval_dc hnew_d
            hcal hstack hprot hcaller (by rw [List.map_id]; exact hbor) rfl
          rw [List.map_id] at hstep_rel
          exact hstep_rel

/-- **`step_direct_write_promoted_lm3_2_simulation`**: direct scalar assignment
`_d = .use op` into a borrowed / promoted primitive-scalar local `_d`
(`∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx`) from any `StateRelLM3_2`-related state
steps in lockstep under `Miri.Interpreter.Step.step` (`annealStepHooks`) and
Anneal's `stepMirFn`, overwriting `_d`'s backing stack allocation in `lean-miri`,
invalidating conflicting Tree Borrows permissions in Anneal (`updateAllocMapOnWrite
allocMap dstIdx none` — disabling active `&mut _d` and freezing `& _d`!), and
reporting UB in both machines if `op` or `_d` is dead. -/
theorem step_direct_write_promoted_lm3_2_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩)
    {dstDecl : LocalDecl} {valTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hval_kind : valTy.kind = dstDecl.ty.kind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (hmem_dst : ∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx) :
    StepRelLM3_2 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨e₀, he₀, he₀_loc⟩ := hmem_dst
  cases he₀_loc
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, hbor, _, _⟩ := id hstate
  have hop_tf := hop tf hframes
  have hval_prim : IsPrimScalarTy valTy := by
    rcases hdst_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact Or.inl (hval_kind.trans hk)
    · exact Or.inr (Or.inl (hval_kind.trans hk))
    · exact Or.inr (Or.inr (Or.inl ⟨it, hval_kind.trans hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ut, hval_kind.trans hk⟩))
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨e₀.localIdx, .nil⟩ op span m
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[e₀.localIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval : annealEvalPlace body.localDecls body.layouts
      (translatePlace ⟨e₀.localIdx, .nil⟩) m =
      .ok ⟨.local 0 e₀.localIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[cacheFrameLocalLayout tf e₀.localIdx hlt_d
            (translateTy dstDecl.ty body.layouts)]⟩ } :=
    annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf e₀.localIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a : StateRelLM3_2 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_dst hlt_d
  have hop_tfa : WellTypedScalarOperand body tfa op valTy :=
    hop_tf.of_cacheFrameLocalLayout e₀.localIdx hlt_d (translateTy dstDecl.ty body.layouts)
  rcases evalOperand_scalar_lm3_2_simulation hstate_a rfl hop_tfa hval_prim
      (some (translateTy dstDecl.ty body.layouts)) with
    ⟨m_op, msg_op, hop_ub, hm_op_ub⟩ |
    ⟨sc, msc, tf', hop_ok, hm_op_ok, hstate_tf', himm_sc, _, htf'_preserve⟩
  · have ha_ub : evalStmt s ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes hop_tf, hop_ub]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use op), span⟩) m =
        (m_op, .error (.undefinedBehavior msg_op)) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval]; dsimp only []
      rw [estate_bind_assoc₂, EStateM.bind_eq_error hm_op_ub]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · obtain ⟨tf₀', hframes_tf', _, _, hfr_tf', _, _, _, _, _, halloc_tf', _⟩ := id hstate_tf'
    injection hframes_tf' with h₁
    injection h₁ with htf'
    subst htf'
    obtain ⟨_, mls_dc, _, _, _, hmls_dc, _, _⟩ := hfr_tf'.lookup_local hdecl_dst
    have hd_tfa : (tfa.locals[e₀.localIdx]?).map Miri.Interpreter.LocalState.value =
        some mls_d.value := by
      simp [tfa, cacheFrameLocalLayout, Array.getElem?_set_self, hmls_d_eq]
    have hd_Val : mls_dc.value = mls_d.value := by
      have hp := htf'_preserve e₀.localIdx
      rw [hd_tfa, hmls_dc] at hp
      injection hp
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
      have ha_ub : evalStmt s ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use op), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only []
        rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes hop_tf, hop_ok]
        dsimp only []; rw [hslot_d]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use op), span⟩) m =
          ({ m with stack := ⟨#[tf']⟩ }, .error (.undefinedBehavior "write to dead local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; dsimp only []
        rw [estate_bind_assoc₂, EStateM.bind_eq_ok hm_op_ok,
          annealWriteImmediate_dead (m := { m with stack := ⟨#[tf']⟩ }) (id0 := tf.localsIdentity)
            rfl hget_dc]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
    · obtain ⟨⟨lay_e, hlay_e⟩, _, hsh_e⟩ :=
        (halloc_tf'.local_alloc_sync tf' rfl e₀ he₀).1 slot_d hslot_d hsd_dead
      obtain ⟨localAlloc, hfind_la, hkind_la, halign_la, hshape_la⟩ := hsh_e dstDecl hdecl_dst
      obtain ⟨hid_lt, _, hbase_e⟩ := halloc_tf'.base_addr_valid e₀ he₀
      obtain ⟨sc', msc', hsc_eq, hmsc_eq, hrel_sc, hsz_sc, hbool_val, hchar_val⟩ :=
        (himm_sc.of_ty_kind_eq hval_prim hval_kind).of_primitive_scalar hdst_prim
      injection hsc_eq with hsc'; subst hsc'
      have hmsc' : msc = msc' := by
        injection hmsc_eq with h1
        unfold Miri.Memory.Scalar.fromScalarInt at h1
        injection h1 with h2
        injection h2 with h3
      subst hmsc'
      have hshape_sc : StackScalarAllocShape (translateSizeBytes sc.sizeBytes)
          localAlloc.allocation := hsz_sc ▸ hshape_la
      obtain ⟨alloc', hw_alloc, halign_alloc', hshape_alloc', hinit_alloc', hread_alloc'⟩ :=
        hshape_sc.writeScalar_readScalar hrel_sc
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
          (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use op), span⟩) m =
          ({ stack := ⟨#[tf']⟩
             machine := { m.machine with
               memory := { m.machine.memory with
                 live := (m.machine.memory.live.filter (fun x => x.1 != e₀.allocId)).push
                   (e₀.allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; dsimp only []
        rw [estate_bind_assoc₂, EStateM.bind_eq_ok hm_op_ok, hw_ind, stackAllocPlace, hw_m]
      rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
        hfr_tf'.location_eq]
      have ha_ok : evalStmt s ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use op), span⟩
          body.localDecls body.layouts =
          MirStepNode.step
            (advanceStmt s (s.frame.locals.set e₀.localIdx (.init (.scalar sc)))
              { s.memory with
                borrows := (updateAllocMapOnWrite allocMap e₀.localIdx none).map
                  AllocMapEntry.toBorrowEntry }) := by
        unfold evalStmt; dsimp only []
        rw [evalRvalue_use_scalarOperand_eq_lm3_2 hstate hframes hop_tf, hop_ok]
        dsimp only []; rw [hslot_d]
        cases slot_d with
        | dead => exact absurd rfl hsd_dead
        | uninit =>
          simp only [set?_eq_some_set hlt_af_d, hprot, hbor,
            invalidateConflictingBorrows_map_toBorrowEntry]
        | init _ =>
          simp only [set?_eq_some_set hlt_af_d, hprot, hbor,
            invalidateConflictingBorrows_map_toBorrowEntry]
      rw [ha_ok]
      apply StepRelLM3_2.step
      exact hstate_tf'.advance_write_deref_scalar rfl
        (fun x => x.updateOnWrite e₀.localIdx none)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        he₀ hdecl_dst hdst_prim hslot_d hsd_dead hfind_la hkind_la halign_la
        hrel_sc hsz_sc hbool_val hchar_val halign_alloc' hshape_alloc' hinit_alloc' hread_alloc'

/-- Observation- and safe-reference-return-aware one-step outcome correspondence
extending `StepRelLM3_2` to:
1. intra-frame transitions emitting a `MirObs` observation (`MirObs.silent` or
   `MirObs.event tag` for `SwitchInt` branch-tag observations) across
   `StateRelLM3_2`, and
2. root-frame `Return` carrying `ImmediateRelLM3_2`-related values (covering
   scalars, scalar pairs, raw pointers, AND safe references `&T` / `&mut T`). -/
inductive StepObsRelLM3_2 (body : CapturedMir) (m : AnnealStepState)
    (allocMap : List AllocMapEntry) :
    MirStepNode → Miri.Interpreter.StepResult AnnealStepState Bool → Prop where
  | emitStep (obs : MirObs) (s' : MachineState) (m' : AnnealStepState) :
      StateRelLM3_2 body s' m' allocMap →
      StepObsRelLM3_2 body m allocMap (MirStepNode.emitStep obs s') (m', .ok true)
  | retRoot (decl0 : LocalDecl) (retVal : Value)
      (imm0 : Miri.Interpreter.Immediate AnnealProv)
      (mem' : Memory) (m' : AnnealStepState) :
      get? body.localDecls 0 = some decl0 →
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) →
      ImmediateRelLM3_2 allocMap decl0.ty body.layouts retVal imm0 →
      m' = { m with stack := ⟨#[]⟩ } →
      StepObsRelLM3_2 body m allocMap (MirStepNode.retNormal retVal mem') (m', .ok true)
  | ub (m' : AnnealStepState) (msg : String) :
      StepObsRelLM3_2 body m allocMap (MirStepNode.fail .ub)
        (m', .error (.undefinedBehavior msg))

/-- Lift any silent-fragment `StepRelLM3_2` proof into `StepObsRelLM3_2`. -/
theorem StepRelLM3_2.toStepObsRelLM3_2
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM3_2 body m allocMap aRes mRes) :
    StepObsRelLM3_2 body m allocMap aRes mRes := by
  cases h with
  | step s' m' hrel => exact .emitStep .silent s' m' hrel
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    exact .retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm'
  | ub m' msg => exact .ub m' msg

/-- Lift any `StepObsRelLM3_1` proof into `StepObsRelLM3_2`. -/
theorem StepObsRelLM3_1.toLM3_2
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRelLM3_1 body m allocMap aRes mRes) :
    StepObsRelLM3_2 body m allocMap aRes mRes := by
  cases h with
  | emitStep obs s' m' hrel => exact .emitStep obs s' m' hrel.toLM3_2
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    exact .retRoot decl0 retVal imm0 mem' m' hdecl hop (.lm3_1 himm) hm'
  | ub m' msg => exact .ub m' msg

namespace StepObsRelLM3_2

/-- Bidirectional intra-frame `emitStep` equivalence under `StepObsRelLM3_2`. -/
theorem emitStep_iff
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRelLM3_2 body m allocMap aRes mRes) :
    (∃ obs s', aRes = .emitStep obs s' ∧ StateRelLM3_2 body s' mRes.1 allocMap) ↔
      (mRes.2 = .ok true ∧ mRes.1.stack.frames ≠ #[]) := by
  cases h with
  | emitStep obs s' m' hrel =>
    obtain ⟨tf, hf, hrc, hrp, hfr, hcal, hst, hprot, hcaller, hbor, halloc, hd⟩ := hrel
    constructor
    · intro _
      refine ⟨rfl, ?_⟩
      rw [hf]
      intro hemp
      have hsz := congrArg Array.size hemp
      contradiction
    · intro _
      exact ⟨obs, s', rfl,
        StateRelLM3_2.mk tf hf hrc hrp hfr hcal hst hprot hcaller hbor halloc hd⟩
  | retRoot _ _ _ _ _ _ _ _ hm' =>
    subst hm'
    constructor
    · rintro ⟨obs, _, h, _⟩
      cases obs <;> cases h
    · rintro ⟨_, hne⟩; exact False.elim (hne rfl)
  | ub _ _ =>
    constructor
    · rintro ⟨obs, _, h, _⟩
      cases obs <;> cases h
    · rintro ⟨hok, _⟩; cases hok

/-- Bidirectional normal root-frame return equivalence under
`StepObsRelLM3_2`. -/
theorem retNormal_iff
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRelLM3_2 body m allocMap aRes mRes) :
    (∃ retVal mem', aRes = .retNormal retVal mem') ↔
      (mRes.2 = .ok true ∧ mRes.1.stack.frames = #[]) := by
  cases h with
  | emitStep obs _ _ hst =>
    obtain ⟨tf, hfr, _, _, _, _, _, _, _, _, _, _⟩ := hst
    constructor
    · rintro ⟨_, _, h⟩
      cases obs <;> cases h
    · rintro ⟨_, hempty⟩
      rw [hfr] at hempty
      have hsz := congrArg Array.size hempty
      contradiction
  | retRoot _ retVal _ mem' _ _ _ _ hm' =>
    subst hm'
    exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨retVal, mem', rfl⟩⟩
  | ub _ _ =>
    constructor
    · rintro ⟨_, _, h⟩; cases h
    · rintro ⟨hok, _⟩; cases hok

/-- Extract the `ImmediateRelLM3_2` return-value correspondence from a normal
root-frame return under `StepObsRelLM3_2`. -/
theorem retNormal_rel
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {retVal : Value} {mem' : Memory}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRelLM3_2 body m allocMap (.retNormal retVal mem') mRes) :
    ∃ decl0 imm0,
      get? body.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) ∧
      ImmediateRelLM3_2 allocMap decl0.ty body.layouts retVal imm0 ∧
      mRes = ({ m with stack := ⟨#[]⟩ }, .ok true) := by
  generalize ha : MirStepNode.retNormal retVal mem' = aNode at h
  cases h with
  | emitStep obs _ _ _ => cases obs <;> cases ha
  | retRoot decl0 rv imm0 mm _ hdecl hop himm hm' =>
    injection ha with h1
    injection h1 with h2
    injection h2 with hrv hmem
    subst hrv hmem hm'
    exact ⟨decl0, imm0, hdecl, hop, himm, rfl⟩
  | ub _ _ => cases ha

/-- Bidirectional undefined-behavior equivalence under `StepObsRelLM3_2`. -/
theorem ub_iff
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRelLM3_2 body m allocMap aRes mRes) :
    (aRes = .fail .ub) ↔ (∃ msg, mRes.2 = .error (.undefinedBehavior msg)) := by
  cases h with
  | emitStep obs _ _ _ =>
    constructor
    · intro h; cases obs <;> cases h
    · rintro ⟨_, h⟩; cases h
  | retRoot _ _ _ _ _ _ _ _ _ =>
    constructor
    · intro h; cases h
    · rintro ⟨_, h⟩; cases h
  | ub _ msg =>
    exact ⟨fun _ => ⟨msg, rfl⟩, fun _ => rfl⟩

end StepObsRelLM3_2

/-- **`step_terminator_goto_return_lm3_2_simulation`**: root-frame basic-block
terminators `Goto`, `Return` (for **any** non-zero-sized immediate `_0`,
unifying primitive scalars, scalar pairs, `.rawPtr`, AND safe references `.ref`
in one `StepRelLM3_2` theorem), and `Unreachable` step in lockstep across
`StateRelLM3_2` under `stepMirFn` and `Miri.Interpreter.Step.step`
(`annealStepHooks`). -/
theorem step_terminator_goto_return_lm3_2_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hterm :
      (∃ target, bb.terminator.kind = .goto target) ∨
      (bb.terminator.kind = .return_ ∧
        ∃ decl0,
          get? body.localDecls 0 = some decl0 ∧
          (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO ∧
          ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 0) ∨
      bb.terminator.kind = .unreachable) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hprot, hcaller, hbor, halloc, hd_tf⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
    simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  rcases hterm with ⟨target, hgoto⟩ | ⟨hret, decl0, hdecl0, hsz0, himm0⟩ | hunreach
  · unfold evalTerminator translateTerminator
      Miri.Interpreter.ControlFlow.evalTerminator
      Miri.Interpreter.ControlFlow.goToBlock
      Miri.Interpreter.ControlFlow.setLocation
    rw [hgoto, stack_currentFrame?_singleton m.stack topFrame hframes, hframes]
    dsimp only [translateTerminatorKind, Except.map, Id.run]
    apply StepRelLM3_2.step
    refine StateRelLM3_2.mk
      { topFrame with location := .mir ⟨target, 0⟩ }
      rfl hretCont ⟨retLay, hretPlace⟩
      ⟨hframe.body_eq, rfl, hframe.af_locals_len, hframe.mf_locals_size, hframe.locals_rel⟩
      hcal hstack hprot hcaller hbor ?_ hd_tf
    refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro tf' htf' e he
    injection htf' with h1; injection h1 with h2; subst tf'
    exact halloc.local_alloc_sync topFrame hframes e he
  · obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, hloc0⟩ := hframe.lookup_local hdecl0
    have hget0 := frame_getLocal_of_getElem? topFrame 0 mls0 hmls0
    have himm0' := himm0 topFrame hframes mls0 hmls0
    unfold evalTerminator translateTerminator
      Miri.Interpreter.ControlFlow.evalTerminator
    rw [hret, hstack, annealTerminatorHooks_toControlHooks, hslot0]
    dsimp only [translateTerminatorKind, Id.run, Pure.pure]
    cases hloc0 with
    | ref ptrVal mptr _ mutability pk _ hty0 hptrRel =>
      have hop0 := annealControlHooks_returnOperand_scalar hframes hget0
      rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
        hframe.location_eq hbb hcleanup hretCont hop0
        (annealControlHooks_popFrame_singleton hframes)
        (annealControlHooks_copyReturn_empty _ hretPlace)
        (annealControlHooks_cleanupFrame_eq false topFrame _)]
      exact StepRelLM3_2.retRoot decl0 (.ptr ptrVal 8)
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
        s.memory _ hdecl0 hop0 (.ref mutability pk ptrVal mptr hty0 hptrRel) rfl
    | lm3_1 hloc0_1 =>
      cases hloc0_1 with
      | rawPtr ptrVal mptr _ mutability pk _ hty0 hptrRel =>
        have hop0 := annealControlHooks_returnOperand_scalar hframes hget0
        rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
          hframe.location_eq hbb hcleanup hretCont hop0
          (annealControlHooks_popFrame_singleton hframes)
          (annealControlHooks_copyReturn_empty _ hretPlace)
          (annealControlHooks_cleanupFrame_eq false topFrame _)]
        exact StepRelLM3_2.retRoot decl0 (.ptr ptrVal 8)
          (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          s.memory _ hdecl0 hop0 (.lm3_1 (.rawPtr mutability pk ptrVal mptr hty0 hptrRel)) rfl
      | base hbase0 =>
        cases hbase0 with
        | dead _ _ =>
          rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
            hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_dead hframes hget0)]
          exact StepRelLM3_2.ub _ _
        | indirect _ mp _ _ _ _ =>
          exact False.elim (himm0' mp rfl)
        | immediate _ imm _ _ hval =>
          rcases hval with ⟨rfl, rfl⟩ | ⟨retVal, rfl, himmRel⟩
          · rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
              hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_uninit hframes hget0)]
            exact StepRelLM3_2.ub _ _
          · cases himmRel with
            | unit hzero =>
              exact False.elim (hsz0 hzero)
            | scalar sc msc hsc hsz_sc hbool_sc hchar_sc =>
              have hop0 := annealControlHooks_returnOperand_scalar hframes hget0
              rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
                hframe.location_eq hbb hcleanup hretCont hop0
                (annealControlHooks_popFrame_singleton hframes)
                (annealControlHooks_copyReturn_empty _ hretPlace)
                (annealControlHooks_cleanupFrame_eq false topFrame _)]
              exact StepRelLM3_2.retRoot decl0 _ _ s.memory _ hdecl0 hop0
                (.lm3_1 (.of_immediateRel (.scalar sc msc hsc hsz_sc hbool_sc hchar_sc))) rfl
            | scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair =>
              have hop0 := annealControlHooks_returnOperand_scalarPair hframes hget0
              rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
                hframe.location_eq hbb hcleanup hretCont hop0
                (annealControlHooks_popFrame_singleton hframes)
                (annealControlHooks_copyReturn_empty _ hretPlace)
                (annealControlHooks_cleanupFrame_eq false topFrame _)]
              exact StepRelLM3_2.retRoot decl0 _ _ s.memory _ hdecl0 hop0
                (.lm3_1 (.of_immediateRel (.scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair))) rfl
  · unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
    rw [hunreach]
    dsimp only [translateTerminatorKind, Except.map, Id.run]
    exact StepRelLM3_2.ub _ _

/-- **`step_terminator_switchInt_lm3_2_simulation`**: `SwitchInt` terminator
simulation across `StateRelLM3_2` (including states with live safe references,
raw pointers, and promoted stack allocations in `allocMap`), stepping both
machines in lockstep to `lookupSwitchTarget sc.bits targets.branches targets.otherwise`
(emitting `MirObs.event sc.bits` in Anneal) or raising UB in both when `discr`
is `.dead` or `.uninit`. -/
theorem step_terminator_switchInt_lm3_2_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {discr : MirAst.Operand} {targets : SwitchTargets} {ty : Ty}
    (hterm : bb.terminator.kind = .switchInt discr targets)
    (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hdiscr : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame discr ty)
    (hcases : SwitchCasesFit ty targets) :
    StepObsRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨topFrame, hframes, _, _, hframe, hcal, _, _, _, _, _, _⟩ := id hstate
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  have hprim : IsPrimScalarTy ty := by
    rcases hty with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hm_term : translateTerminator bb.terminator =
      { sourceInfo := defaultSourceInfo,
        kind := .SwitchInt (translateOperand discr) (translateSwitchTargets targets) } := by
    unfold translateTerminator; rw [hterm]; rfl
  have hdisc_eq : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
      (translateOperand discr) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperand body.localDecls body.layouts (translateOperand discr) none >>=
          annealReadImmediate) m := rfl
  unfold evalTerminator
  rw [hterm, hm_term]
  dsimp only []
  rcases evalOperand_scalar_lm3_2_simulation hstate hframes (hdiscr topFrame hframes) hprim none with
    ⟨m', msg, ha_ub, hm_ub⟩ |
    ⟨sc, msc, tf', ha_ok, hm_ok, hstate', himm, _, _⟩
  · rw [ha_ub]
    have hdisc : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
        (translateOperand discr) m = (m', .error (.undefinedBehavior msg)) := by
      rw [hdisc_eq]; unfold Miri.Interpreter.runRvalue; rw [hm_ub]
    rw [evalTerminator_switchInt_error _ () _ _ _ m m' _ hdisc]
    exact .ub m' msg
  · rw [ha_ok]
    obtain ⟨sc₀, msc₀, hsc_eq, hmsc_eq, hrel, hsz, hbool, _⟩ := himm.of_primitive_scalar hprim
    injection hsc_eq with hsc_eq'; subst hsc_eq'
    have hmsc_eq' : msc = msc₀ := by cases hmsc_eq; rfl
    subst hmsc_eq'
    have hdisc : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
        (translateOperand discr) m =
        ({ m with stack := ⟨#[tf']⟩ },
          .ok ⟨.scalar (.fromScalarInt msc), translateTy ty body.layouts⟩) := by
      rw [hdisc_eq]; unfold Miri.Interpreter.runRvalue; rw [hm_ok]
    obtain ⟨hwsz, hwvalid⟩ := boolOrInt_translateTy_size hty body.layouts
    have hwidth : sc.sizeBytes = boolOrIntByteWidth ty :=
      translateSizeBytes_inj hrel.validBytes hwvalid (by rw [← hsz, hwsz])
    have hsz_ty : sc.sizeBytes = match ty.kind with
        | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc.sizeBytes := by
      rw [hwidth]
      rcases ty with ⟨tk, tIdx⟩
      rcases hty with h | ⟨k, h⟩ | ⟨k, h⟩ <;> dsimp only at h <;> subst h <;> rfl
    have hbits : ty.kind = .bool → sc.bits = 0 ∨ sc.bits = 1 := fun h => (hbool h).2
    have hcmp : ∀ v b, (v, b) ∈ targets.branches →
        (annealTerminatorHooks body.localDecls body.layouts).compareSwitchCase ()
          ⟨.scalar (.fromScalarInt msc), translateTy ty body.layouts⟩ v
          { m with stack := ⟨#[tf']⟩ } =
        ({ m with stack := ⟨#[tf']⟩ }, .ok (Nat.beq sc.bits v)) := by
      intro v b hmem
      obtain ⟨hlt, hcase_bool⟩ := hcases v b hmem
      rw [← hwidth] at hlt
      exact compareSwitchCase_simulation hrel body.localDecls body.layouts ty hty hsz_ty hbits
        v hlt hcase_bool _
    rw [evalTerminator_switchInt_ok _ () _ _ _ m _ _ sc.bits hdisc hcmp]
    unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
    rw [stack_currentFrame?_singleton _ tf' rfl]
    dsimp only [Except.map]
    apply StepObsRelLM3_2.emitStep
    rcases hstate' with
      ⟨tf'', htf'', hretCont', ⟨retLay', hretPlace'⟩, hfr',
        hcal', hstack', hprot', hcaller', hbor', halloc', hd_tf'⟩
    injection htf'' with h1; injection h1 with h2; subst h2
    let tgtBlk := lookupSwitchTarget sc.bits targets.branches targets.otherwise
    have hs_frame_id :
        ({ s with frame := { blockIdx := tgtBlk, stmtIdx := 0, locals := s.frame.locals } } :
          MachineState) =
        { s with frame := { s.frame with blockIdx := tgtBlk, stmtIdx := 0 } } := rfl
    rw [hs_frame_id]
    refine StateRelLM3_2.mk
      { tf' with location := .mir (Miri.MIR.Location.mk tgtBlk 0) }
      rfl hretCont' ⟨retLay', hretPlace'⟩
      ⟨hfr'.body_eq, rfl, hfr'.af_locals_len, hfr'.mf_locals_size, hfr'.locals_rel⟩
      hcal' hstack' hprot' hcaller' hbor' ?_ hd_tf'
    refine ⟨halloc'.tags_nodup, halloc'.local_to_alloc_unique, halloc'.alloc_to_local_injective,
      halloc'.target_decl, halloc'.base_addr_valid, halloc'.borrow_sync, halloc'.live_key_unique, ?_⟩
    intro tf_q htf_q e he
    injection htf_q with hq1; injection hq1 with hq2; subst hq2
    exact halloc'.local_alloc_sync tf' rfl e he

/-- **`step_terminator_assert_lm3_2_simulation`**: `Assert` terminator
(`TerminatorKind.assert cond expected target .unreachable`) simulation across
`StateRelLM3_2`:
1. If `cond` is `.dead` or `.uninit`, both machines raise UB (`StepRelLM3_2.ub`).
2. If `cond` evaluates to `b ≠ expected`, both machines raise UB (`StepRelLM3_2.ub`).
3. If `cond` evaluates to `b = expected`, both machines jump in lockstep to
   `target` (`StepRelLM3_2.step`), preserving `StateRelLM3_2` across `allocMap`. -/
theorem step_terminator_assert_lm3_2_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {cond : MirAst.Operand} {condTy : Ty} {expected : Bool} {target : BasicBlockIdx}
    (hterm : bb.terminator.kind = .assert cond expected target .unreachable)
    (hbool : condTy.kind = .bool)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame cond condTy) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨topFrame, hframes, _, _, hframe, hcal, _, _, _, _, _, _⟩ := id hstate
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  have hm_term : translateTerminator bb.terminator =
      { sourceInfo := defaultSourceInfo,
        kind := .Assert (translateOperand cond) expected
          (.BoundsCheck (translateOperand cond) (translateOperand cond))
          target .Unreachable } := by
    unfold translateTerminator; rw [hterm]; rfl
  unfold evalTerminator
  rw [hterm, hm_term]
  dsimp only [Miri.Interpreter.ControlFlow.evalTerminator]
  rcases evalOperand_scalar_lm3_2_simulation hstate hframes (hop topFrame hframes)
      (Or.inl hbool) none with
    ⟨m', msg, ha_ub, hm_ub⟩ |
    ⟨sc, msc, tf', ha_ok, hm_ok, hstate', himm, _, _⟩
  · rw [ha_ub]
    have hread_err : (annealTerminatorHooks body.localDecls body.layouts).readAssertCondition ()
        (translateOperand cond) m = (m', .error (.undefinedBehavior msg)) := by
      dsimp only [annealTerminatorHooks, Miri.Interpreter.TerminatorHooks.readAssertCondition]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_assoc_apply, EStateM.bind_eq_error hm_ub]
    have h8 := readAssertCondition_to_8 hread_err
    simp only [h8, Except.map]
    exact .ub m' msg
  · rw [ha_ok]
    obtain ⟨sc₀, msc₀, hsc_eq, hmsc_eq, hsc_rel, _, hsc_bool, _⟩ :=
      himm.of_primitive_scalar (Or.inl hbool)
    injection hsc_eq with hsc_eq'; subst hsc_eq'
    have hmsc_eq' : msc = msc₀ := by cases hmsc_eq; rfl
    subst hmsc_eq'
    rcases hsc_bool hbool with ⟨hsc_sz1, hsc_bits⟩
    obtain ⟨b, hb_sc, hb_toB⟩ : ∃ b : Bool,
        sc = boolToScalar b ∧
        (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBool = .ok b := by
      have hmsc_sz : msc.size = Miri.ABI.Size.ofBytes 1 := by
        rw [hsc_rel.size_eq, hsc_sz1]; rfl
      have hmsc_data : msc.data = sc.bits := hsc_rel.data_eq
      rcases sc with ⟨sc_b, sc_sz⟩
      rcases msc with ⟨msc_d, msc_s⟩
      dsimp only at hsc_sz1 hsc_bits hmsc_sz hmsc_data
      subst hsc_sz1 hmsc_sz
      rcases hsc_bits with h0 | h1
      · subst h0 hmsc_data
        refine ⟨false, rfl, ?_⟩
        with_unfolding_all rfl
      · subst h1 hmsc_data
        refine ⟨true, rfl, ?_⟩
        with_unfolding_all rfl
    subst hb_sc
    have hread_ok : (annealTerminatorHooks body.localDecls body.layouts).readAssertCondition ()
        (translateOperand cond) m = ({ m with stack := ⟨#[tf']⟩ }, .ok b) := by
      dsimp only [annealTerminatorHooks, Miri.Interpreter.TerminatorHooks.readAssertCondition]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_assoc_apply, EStateM.bind_eq_ok hm_ok]
      dsimp only [Miri.Interpreter.Immediate.toScalar, bind, EStateM.bind, pure, EStateM.pure]
      rw [hb_toB]
      rfl
    have h8 := readAssertCondition_to_8 hread_ok
    simp only [h8]
    dsimp only [Id.run, bind, Except.bind, pure, Except.pure,
      Miri.Interpreter.TerminatorHooks.ignoreOptionalOverflowChecks,
      Miri.Interpreter.ControlFlow.isOptionalOverflowCheck]
    by_cases h_eq : expected = b
    · subst h_eq
      have hbeq_self : (expected == expected) = true := beq_self_eq_true expected
      simp only [Bool.and_false, Bool.false_or, hbeq_self, ↓reduceIte]
      unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
      rw [stack_currentFrame?_singleton _ tf' rfl]
      dsimp only [Except.map]
      split
      · apply StepRelLM3_2.step
        rcases hstate' with
          ⟨tf'', htf'', hretCont', ⟨retLay', hretPlace'⟩, hfr',
            hcal', hstack', hprot', hcaller', hbor', halloc', hd_tf'⟩
        injection htf'' with h1; injection h1 with h2; subst h2
        have hs_frame_id :
            ({ s with frame := { blockIdx := target, stmtIdx := 0, locals := s.frame.locals } } :
              MachineState) =
            { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } } := rfl
        rw [hs_frame_id]
        refine StateRelLM3_2.mk
          { tf' with location := .mir (Miri.MIR.Location.mk target 0) }
          rfl hretCont' ⟨retLay', hretPlace'⟩
          ⟨hfr'.body_eq, rfl, hfr'.af_locals_len, hfr'.mf_locals_size, hfr'.locals_rel⟩
          hcal' hstack' hprot' hcaller' hbor' ?_ hd_tf'
        refine ⟨halloc'.tags_nodup, halloc'.local_to_alloc_unique, halloc'.alloc_to_local_injective,
          halloc'.target_decl, halloc'.base_addr_valid, halloc'.borrow_sync, halloc'.live_key_unique,
          ?_⟩
        intro tf_q htf_q e he
        injection htf_q with hq1; injection hq1 with hq2; subst hq2
        exact halloc'.local_alloc_sync tf' rfl e he
      · next h_contra =>
        exfalso
        cases expected <;> cases h_contra
    · have hbeq_ne : (expected == b) = false := beq_false_of_ne h_eq
      simp only [Bool.and_false, Bool.false_or, hbeq_ne, Bool.false_eq_true, ↓reduceIte]
      dsimp only [annealTerminatorHooks, applyUnwindAction, Except.map]
      split
      · next h_contra =>
        exfalso
        cases expected <;> cases b <;> first | exact h_eq rfl | cases h_contra
      · exact .ub _ "assert panic"

/-- State-dependent well-typedness predicate for the `LM-3.2` lockstep statement
fragment across `StateRelLM3_2` states (covering `nop`, `StorageLive`,
`StorageDead`, immediate and promoted direct scalar writes, `& _t` / `&mut _t`
on immediate and already-promoted locals, safe-reference copy/move, safe-reference
dereference reads `copy *_r` / `move *_r` and writes `*_r = op`, `PlaceMention(_x)`,
and `PlaceMention(*_r)` in its valid/dead agreement regime; every complementary
dangling, OOB, misaligned, or Tree Borrows permission divergence is paired with
an explicit divergence theorem in Sections 3–8). -/
inductive WellTypedLM3_2StateStmt
    (body : CapturedMir) (s : MachineState) (m : AnnealStepState)
    (allocMap : List AllocMapEntry) : Statement → Prop where
  | nop (span : String) :
      WellTypedLM3_2StateStmt body s m allocMap ⟨.nop, span⟩
  | storageLive (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      (∀ e ∈ allocMap, e.localIdx ≠ loc) →
      WellTypedLM3_2StateStmt body s m allocMap ⟨.storageLive loc, span⟩
  | storageDead (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      loc ≠ 0 →
      WellTypedLM3_2StateStmt body s m allocMap ⟨.storageDead loc, span⟩
  | scalarUse
      (dstIdx : Local) (op : MirAst.Operand) (dstDecl : LocalDecl) (valTy : Ty) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      IsPrimScalarTy dstDecl.ty →
      valTy.kind = dstDecl.ty.kind →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        WellTypedScalarOperand body topFrame op valTy) →
      (∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) →
      WellTypedLM3_2StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
  | directWritePromoted
      (dstIdx : Local) (op : MirAst.Operand) (dstDecl : LocalDecl) (valTy : Ty) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      IsPrimScalarTy dstDecl.ty →
      valTy.kind = dstDecl.ty.kind →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        WellTypedScalarOperand body topFrame op valTy) →
      (∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx) →
      WellTypedLM3_2StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
  | refAddrOf
      (dstIdx targetIdx : Local) (bk : BorrowKind)
      (dstDecl targetDecl : LocalDecl) (refMut : Mutability) (pointeeKind : RigidTy)
      (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls targetIdx = some targetDecl →
      dstDecl.ty.kind = .ref refMut pointeeKind →
      IsPrimScalarTy targetDecl.ty →
      dstIdx ≠ targetIdx →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame targetIdx) →
      WellTypedLM3_2StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩
  | refIndirect
      (dstIdx targetIdx : Local) (bk : BorrowKind)
      (dstDecl targetDecl : LocalDecl) (refMut : Mutability) (pointeeKind : RigidTy)
      (e₀ : AllocMapEntry) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls targetIdx = some targetDecl →
      dstDecl.ty.kind = .ref refMut pointeeKind →
      IsPrimScalarTy targetDecl.ty →
      dstIdx ≠ targetIdx →
      (∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) →
      e₀ ∈ allocMap →
      e₀.localIdx = targetIdx →
      WellTypedLM3_2StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩
  | safeRefUse
      (dstIdx srcIdx : Local) (opKind : Place → MirAst.Operand)
      (dstDecl srcDecl : LocalDecl) (srcMut dstMut : Mutability)
      (srcPointee dstPointee : RigidTy) (span : String) :
      (opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move) →
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls srcIdx = some srcDecl →
      srcDecl.ty.kind = .ref srcMut srcPointee →
      dstDecl.ty.kind = .ref dstMut dstPointee →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) →
      WellTypedLM3_2StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨srcIdx, .nil⟩)), span⟩
  | safeRefDerefRead
      (dstIdx refIdx : Local) (opKind : Place → MirAst.Operand)
      (dstDecl refDecl : LocalDecl) (mutability : Mutability) (span : String) :
      (opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move) →
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls refIdx = some refDecl →
      refDecl.ty.kind = .ref mutability dstDecl.ty.kind →
      IsPrimScalarTy dstDecl.ty →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx) →
      (∀ ptrVal, get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
        ∀ e ∈ allocMap, e.tag = ptrVal.tag →
          get? s.frame.locals e.localIdx ≠ some .dead →
            ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
            (∀ decl, get? body.localDecls e.localIdx = some decl →
              decl.ty.kind = dstDecl.ty.kind)) →
      WellTypedLM3_2StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩
  | safeRefDerefWrite
      (refIdx : Local) (op : MirAst.Operand) (refDecl : LocalDecl)
      (mutability : Mutability) (pointeeKind : RigidTy) (valTy : Ty) (span : String) :
      get? body.localDecls refIdx = some refDecl →
      refDecl.ty.kind = .ref mutability pointeeKind →
      IsPrimScalarTy valTy →
      valTy.kind = pointeeKind →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        WellTypedScalarOperand body topFrame op valTy) →
      (∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx) →
      (∀ ptrVal e tgtDecl,
        get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
        e ∈ allocMap → e.tag = ptrVal.tag →
        get? body.localDecls e.localIdx = some tgtDecl →
        get? s.frame.locals e.localIdx ≠ some .dead →
        ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
          tgtDecl.ty.kind = pointeeKind) →
      WellTypedLM3_2StateStmt body s m allocMap
        ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩
  | placeMentionLocal
      (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      get? s.frame.locals loc ≠ some .dead →
      WellTypedLM3_2StateStmt body s m allocMap
        ⟨.placeMention ⟨loc, .nil⟩, span⟩
  | placeMentionSafeRefDeref
      (refIdx : Local) (refDecl : LocalDecl)
      (mutability : Mutability) (pointeeKind : RigidTy) (span : String) :
      get? body.localDecls refIdx = some refDecl →
      refDecl.ty.kind = .ref mutability pointeeKind →
      IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 } →
      (∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx) →
      (get? s.frame.locals refIdx = some .dead ∨
        ∃ ptrVal e,
          get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) ∧
          e ∈ allocMap ∧ e.tag = ptrVal.tag ∧ ptrVal.offsetBytes = 0 ∧
          get? s.frame.locals e.localIdx ≠ some .dead ∧
          (∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
            tgtDecl.ty.kind = pointeeKind)) →
      WellTypedLM3_2StateStmt body s m allocMap
        ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩

/-- **`step_stmt_lm3_2_state_simulation` (`LM-3.2` Composed Statement Simulation)**:
every statement satisfying `WellTypedLM3_2StateStmt body s m allocMap stmt` in a
`StateRelLM3_2`-related state steps in lockstep (`StepRelLM3_2`) under Anneal's
`stepMirFn` and `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`)
across an updated `allocMap'`. -/
theorem step_stmt_lm3_2_state_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : WellTypedLM3_2StateStmt body s m allocMap stmt)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    ∃ allocMap' : List AllocMapEntry,
      StepRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  cases hwt with
  | nop =>
    exact ⟨allocMap, step_nop_lm3_2_simulation hstate hphase hbb hstmt⟩
  | storageLive _ _ _ hdecl hnot_mapped =>
    exact ⟨allocMap, step_storageLive_lm3_2_simulation hstate hphase hbb hstmt hdecl hnot_mapped⟩
  | storageDead _ _ _ hdecl hne0 =>
    exact ⟨disableAllocMapLocal allocMap _,
      step_storageDead_lm3_2_simulation hstate hphase hbb hstmt hdecl hne0⟩
  | scalarUse _ _ _ _ _ hdecl hprim hkind hop himm =>
    exact ⟨allocMap,
      step_scalar_use_lm3_2_simulation hstate hphase hbb hstmt hdecl hprim hkind hop himm⟩
  | directWritePromoted _ _ _ _ _ hdecl hprim hkind hop hmem =>
    exact ⟨_,
      step_direct_write_promoted_lm3_2_simulation hstate hphase hbb hstmt hdecl hprim hkind hop hmem⟩
  | refAddrOf _ _ _ _ _ _ _ _ hdecl_d hdecl_t hdst_ty htgt_ty hne himm =>
    exact ⟨_,
      evalRvalue_ref_simulation hstate hphase hbb hstmt hdecl_d hdecl_t hdst_ty htgt_ty hne
        himm hsupply⟩
  | refIndirect _ _ _ _ _ _ _ e₀ _ hdecl_d hdecl_t hdst_ty htgt_ty hne himm_d he₀ he₀_loc =>
    exact ⟨_,
      evalRvalue_ref_indirect_simulation hstate hphase hbb hstmt hdecl_d hdecl_t hdst_ty htgt_ty
        hne himm_d he₀ he₀_loc⟩
  | safeRefUse _ _ _ _ _ _ _ _ _ _ hopKind hdecl_d hdecl_s hsrc_ty hdst_ty himm =>
    exact ⟨allocMap,
      step_safeRef_use_simulation hstate hphase hopKind hbb hstmt hdecl_d hdecl_s hsrc_ty hdst_ty
        himm⟩
  | safeRefDerefRead _ _ _ _ _ _ _ hopKind hdecl_d hdecl_r href_ty hprim himm hlive =>
    exact step_safeRef_deref_read_simulation hstate hphase hopKind hbb hstmt hdecl_d hdecl_r
      href_ty hprim himm hlive hlay_coh
  | safeRefDerefWrite _ _ _ _ _ _ _ hdecl_r href_ty hprim hkind hop himm hlive =>
    exact step_safeRef_deref_write_simulation hstate hphase hbb hstmt hdecl_r href_ty hprim hkind
      hop himm hlive hlay_coh
  | placeMentionLocal _ _ _ hdecl hlive =>
    exact ⟨allocMap, step_placeMention_local_lm3_2_simulation hstate hphase hbb hstmt hdecl hlive⟩
  | placeMentionSafeRefDeref _ _ _ _ _ hdecl_r href_ty hprim himm hval =>
    exact ⟨allocMap,
      step_placeMention_safeRef_deref_simulation hstate hphase hbb hstmt hdecl_r href_ty hprim
        himm hval⟩

/-- State-dependent well-typedness predicate for `LM-3.2` root-frame basic-block
terminators (`Goto`, `Return` for any non-zero-sized immediate `_0` including
scalars, scalar pairs, `.rawPtr`, and safe references `.ref`, `Unreachable`,
`SwitchInt`, and `Assert`) across `StateRelLM3_2` states. -/
inductive WellTypedLM3_2StateTerminator
    (body : CapturedMir) (m : AnnealStepState) (bb : BasicBlockData) : Prop where
  | goto (target : BasicBlockIdx) :
      bb.isCleanup = false →
      bb.terminator.kind = .goto target →
      WellTypedLM3_2StateTerminator body m bb
  | return_ (decl0 : LocalDecl) :
      bb.isCleanup = false →
      bb.terminator.kind = .return_ →
      get? body.localDecls 0 = some decl0 →
      (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO →
      (∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 0) →
      WellTypedLM3_2StateTerminator body m bb
  | unreachable :
      bb.isCleanup = false →
      bb.terminator.kind = .unreachable →
      WellTypedLM3_2StateTerminator body m bb
  | switchInt (discr : MirAst.Operand)
      (targets : SwitchTargets) (ty : Ty) :
      bb.terminator.kind = .switchInt discr targets →
      (ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k)) →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        WellTypedScalarOperand body topFrame discr ty) →
      SwitchCasesFit ty targets →
      WellTypedLM3_2StateTerminator body m bb
  | assert_ (cond : MirAst.Operand) (condTy : Ty)
      (expected : Bool) (target : BasicBlockIdx) :
      bb.terminator.kind = .assert cond expected target .unreachable →
      condTy.kind = .bool →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        WellTypedScalarOperand body topFrame cond condTy) →
      WellTypedLM3_2StateTerminator body m bb

/-- **`step_terminator_lm3_2_state_simulation` (`LM-3.2` Composed Terminator
Simulation)**: every basic-block terminator satisfying
`WellTypedLM3_2StateTerminator body m bb` at the end of a basic block in a
`StateRelLM3_2`-related state steps in lockstep (`StepObsRelLM3_2`) under
Anneal's `stepMirFn` and `lean-miri`'s `Miri.Interpreter.Step.step`
(`annealStepHooks`). -/
theorem step_terminator_lm3_2_state_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hwt : WellTypedLM3_2StateTerminator body m bb) :
    StepObsRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  cases hwt with
  | goto target hcleanup hgoto =>
    exact (step_terminator_goto_return_lm3_2_simulation hstate hphase hbb hstmt_none
      hstmt_len hcleanup (Or.inl ⟨target, hgoto⟩)).toStepObsRelLM3_2
  | return_ decl0 hcleanup hret hdecl0 hsz0 himm0 =>
    exact (step_terminator_goto_return_lm3_2_simulation hstate hphase hbb hstmt_none
      hstmt_len hcleanup
      (Or.inr (Or.inl ⟨hret, decl0, hdecl0, hsz0, himm0⟩))).toStepObsRelLM3_2
  | unreachable hcleanup hunreach =>
    exact (step_terminator_goto_return_lm3_2_simulation hstate hphase hbb hstmt_none
      hstmt_len hcleanup (Or.inr (Or.inr hunreach))).toStepObsRelLM3_2
  | switchInt discr targets ty hterm hty hdiscr hcases =>
    exact step_terminator_switchInt_lm3_2_simulation hstate hphase hbb hstmt_none
      hstmt_len hterm hty hdiscr hcases
  | assert_ cond condTy expected target hterm hbool hop =>
    exact (step_terminator_assert_lm3_2_simulation hstate hphase hbb hstmt_none
      hstmt_len hterm hbool hop).toStepObsRelLM3_2

/-- **`step_mir_lm3_2_state_simulation` (`LM-3.2` Unified Statement + Terminator
Step Simulation)**: at any location of a `StateRelLM3_2`-related state, if
either the current statement satisfies `WellTypedLM3_2StateStmt` or `stmtIdx` is
at the end of the basic block (`s.frame.stmtIdx = length bb.statements`) and the
terminator satisfies `WellTypedLM3_2StateTerminator`, then Anneal's `stepMirFn`
and `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) step in
lockstep under `StepObsRelLM3_2` across an updated `allocMap'`. -/
theorem step_mir_lm3_2_state_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hloc :
      (∃ stmt, get? bb.statements s.frame.stmtIdx = some stmt ∧
        WellTypedLM3_2StateStmt body s m allocMap stmt) ∨
      (get? bb.statements s.frame.stmtIdx = none ∧
        s.frame.stmtIdx = length bb.statements ∧
        WellTypedLM3_2StateTerminator body m bb))
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    ∃ allocMap' : List AllocMapEntry,
      StepObsRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hloc with ⟨stmt, hstmt, hwt_stmt⟩ | ⟨hstmt_none, hstmt_len, hwt_term⟩
  · obtain ⟨allocMap', hstep⟩ :=
      step_stmt_lm3_2_state_simulation hstate hphase hbb hstmt hwt_stmt hsupply hlay_coh
    exact ⟨allocMap', hstep.toStepObsRelLM3_2⟩
  · exact ⟨allocMap,
      step_terminator_lm3_2_state_simulation hstate hphase hbb hstmt_none hstmt_len hwt_term⟩

/-! ## 9. Multi-Step `StateRelLM3_2Tree` Hierarchy Simulations (`LM-3.2`) -/

/-- Same `(tag, localIdx, allocId)` skeleton between two `AllocMapEntry` lists. -/
inductive SameAllocSkeleton : List AllocMapEntry → List AllocMapEntry → Prop where
  | nil : SameAllocSkeleton [] []
  | cons {a b : AllocMapEntry} {am₁ am₂ : List AllocMapEntry}
      (h : a.tag = b.tag ∧ a.localIdx = b.localIdx ∧ a.allocId = b.allocId)
      (htl : SameAllocSkeleton am₁ am₂) :
      SameAllocSkeleton (a :: am₁) (b :: am₂)

private theorem SameAllocSkeleton.refl (am : List AllocMapEntry) : SameAllocSkeleton am am := by
  induction am with
  | nil => exact .nil
  | cons hd tl ih => exact .cons ⟨rfl, rfl, rfl⟩ ih

private theorem SameAllocSkeleton.symm {am₁ am₂ : List AllocMapEntry}
    (h : SameAllocSkeleton am₁ am₂) : SameAllocSkeleton am₂ am₁ := by
  induction h with
  | nil => exact .nil
  | cons hhd _ ih => exact .cons ⟨hhd.1.symm, hhd.2.1.symm, hhd.2.2.symm⟩ ih

private theorem SameAllocSkeleton.mem_left {am₁ am₂ : List AllocMapEntry}
    (h : SameAllocSkeleton am₁ am₂) {a : AllocMapEntry} (ha : a ∈ am₁) :
    ∃ b ∈ am₂, a.tag = b.tag ∧ a.localIdx = b.localIdx ∧ a.allocId = b.allocId := by
  induction h with
  | nil => cases ha
  | @cons x y xs ys hxy _ ih =>
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact ⟨y, List.Mem.head _, hxy⟩
    · obtain ⟨b, hb, hrel⟩ := ih hmem
      exact ⟨b, List.mem_cons_of_mem y hb, hrel⟩

private theorem SameAllocSkeleton.tags_eq {am₁ am₂ : List AllocMapEntry}
    (h : SameAllocSkeleton am₁ am₂) :
    am₁.map AllocMapEntry.tag = am₂.map AllocMapEntry.tag := by
  induction h with
  | nil => rfl
  | cons hxy _ ih => simp only [List.map_cons, hxy.1, ih]

private theorem SameAllocSkeleton.of_tree_maps
    (treeMap : List ReborrowMapEntry)
    (f : AllocMapEntry → AllocMapEntry)
    (hf_tag : ∀ x, (f x).tag = x.tag)
    (hf_loc : ∀ x, (f x).localIdx = x.localIdx)
    (hf_aid : ∀ x, (f x).allocId = x.allocId)
    (g : ReborrowMapEntry → ReborrowMapEntry)
    (hg_tag : ∀ x, (g x).tag = x.tag)
    (hg_loc : ∀ x, (g x).localIdx = x.localIdx)
    (hg_aid : ∀ x, (g x).allocId = x.allocId) :
    SameAllocSkeleton
      ((treeMap.map ReborrowMapEntry.toAllocMapEntry).map f)
      ((treeMap.map g).map ReborrowMapEntry.toAllocMapEntry) := by
  induction treeMap with
  | nil => exact .nil
  | cons hd tl ih =>
    simp only [List.map_cons]
    refine .cons ⟨?_, ?_, ?_⟩ ih
    · rw [hf_tag]; simp [ReborrowMapEntry.toAllocMapEntry, hg_tag]
    · rw [hf_loc]; simp [ReborrowMapEntry.toAllocMapEntry, hg_loc]
    · rw [hf_aid]; simp [ReborrowMapEntry.toAllocMapEntry, hg_aid]

private theorem SameAllocSkeleton.of_map_right
    (xs : List ReborrowMapEntry)
    (g : ReborrowMapEntry → ReborrowMapEntry)
    (hg_tag : ∀ x, (g x).tag = x.tag)
    (hg_loc : ∀ x, (g x).localIdx = x.localIdx)
    (hg_aid : ∀ x, (g x).allocId = x.allocId) :
    SameAllocSkeleton
      (xs.map ReborrowMapEntry.toAllocMapEntry)
      ((xs.map g).map ReborrowMapEntry.toAllocMapEntry) := by
  induction xs with
  | nil => exact .nil
  | cons hd tl ih =>
    refine .cons ⟨?_, ?_, ?_⟩ ih
    · dsimp only [ReborrowMapEntry.toAllocMapEntry]; exact (hg_tag hd).symm
    · dsimp only [ReborrowMapEntry.toAllocMapEntry]; exact (hg_loc hd).symm
    · dsimp only [ReborrowMapEntry.toAllocMapEntry]; exact (hg_aid hd).symm

private theorem PtrRel.of_skeleton {am₁ am₂ : List AllocMapEntry}
    (hskel : SameAllocSkeleton am₁ am₂) {p : ProvenancePtr}
    {mptr : Miri.Memory.Pointer AnnealProv}
    (h : PtrRel am₁ p mptr) : PtrRel am₂ p mptr := by
  rcases h with ⟨allocId, borTag, hprov, hid, hoff, haddr, ⟨e₁, he₁, htag₁, haid₁⟩⟩
  obtain ⟨e₂, he₂, htag_eq, _, haid_eq⟩ := hskel.mem_left he₁
  exact .mk allocId borTag hprov hid hoff haddr
    ⟨e₂, he₂, htag_eq.symm.trans htag₁, haid_eq.symm.trans haid₁⟩

private theorem LocalRelLM3_2.of_skeleton {mach : AnnealMachine}
    {am₁ am₂ : List AllocMapEntry} (hskel : SameAllocSkeleton am₁ am₂)
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_2 mach am₁ decl layouts slot mls) :
    LocalRelLM3_2 mach am₂ decl layouts slot mls := by
  cases h with
  | lm3_1 h1 =>
    cases h1 with
    | base hb => exact .lm3_1 (.base hb)
    | rawPtr p mptr cl mutability pk hc hty hptr =>
      exact .lm3_1 (.rawPtr p mptr cl mutability pk hc hty (hptr.of_skeleton hskel))
  | ref p mptr cl mutability pk hc hty hptr =>
    exact .ref p mptr cl mutability pk hc hty (hptr.of_skeleton hskel)

/-- Replacing `am₁` with `am₂` of the same `(tag, localIdx, allocId)` skeleton
and updating `s.memory.borrows := am₂.map AllocMapEntry.toBorrowEntry` preserves
`StateRelLM3_2`. -/
theorem StateRelLM3_2.replace_borrows_skeleton
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {am₁ am₂ : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m am₁)
    (hskel : SameAllocSkeleton am₁ am₂) :
    StateRelLM3_2 body
      { s with memory := { s.memory with borrows := am₂.map AllocMapEntry.toBorrowEntry } }
      m am₂ := by
  rcases hstate with
    ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, _, halloc, hdisj⟩
  have hnodup₂ : (am₂.map AllocMapEntry.tag).Nodup := by
    rw [← hskel.tags_eq]; exact halloc.tags_nodup
  have hfr₂ : FrameRelLM3_2 body m.machine am₂ s.frame tf :=
    ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size,
      fun i decl slot mls hd hs hm =>
        (hfr.locals_rel i decl slot mls hd hs hm).of_skeleton hskel⟩
  refine .mk tf hframes hretCont hretPlace hfr₂ hcal hstack hprot hcaller rfl ?_ hdisj
  refine ⟨hnodup₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b₁ hb₁ b₂ hb₂ hloc
    obtain ⟨a₁, ha₁, _, hl₁, hid₁⟩ := hskel.symm.mem_left hb₁
    obtain ⟨a₂, ha₂, _, hl₂, hid₂⟩ := hskel.symm.mem_left hb₂
    rw [hid₁, hid₂]
    exact halloc.local_to_alloc_unique a₁ ha₁ a₂ ha₂ (hl₁.symm.trans (hloc.trans hl₂))
  · intro b₁ hb₁ b₂ hb₂ hid
    obtain ⟨a₁, ha₁, _, hl₁, hid₁⟩ := hskel.symm.mem_left hb₁
    obtain ⟨a₂, ha₂, _, hl₂, hid₂⟩ := hskel.symm.mem_left hb₂
    rw [hl₁, hl₂]
    exact halloc.alloc_to_local_injective a₁ ha₁ a₂ ha₂ (hid₁.symm.trans (hid.trans hid₂))
  · intro b hb
    obtain ⟨a, ha, _, hl, _⟩ := hskel.symm.mem_left hb
    rw [hl]; exact halloc.target_decl a ha
  · intro b hb
    obtain ⟨a, ha, _, _, hid⟩ := hskel.symm.mem_left hb
    rw [hid]; exact halloc.base_addr_valid a ha
  · intro b hb
    obtain ⟨a, ha, ht, _, _⟩ := hskel.symm.mem_left hb
    refine ⟨?_, ?_⟩
    · dsimp only []; rw [ht]; exact (halloc.borrow_sync a ha).1
    · dsimp only []; exact lookupBorrow_map_toBorrowEntry_of_nodup hnodup₂ hb
  · intro b hb
    obtain ⟨a, ha, _, _, hid⟩ := hskel.symm.mem_left hb
    rw [hid]; exact halloc.live_key_unique a ha
  · intro tf' htf' b hb
    obtain ⟨a, ha, _, hl, hid⟩ := hskel.symm.mem_left hb
    dsimp only []; rw [hl, hid]
    exact halloc.local_alloc_sync tf' htf' a ha

/-- Build `StateRelLM3_2Tree` directly from a parent-erased `StateRelLM3_2` state
`s_e` whose borrow skeleton matches `treeMap'`. -/
theorem StateRelLM3_2Tree.of_erased_skeleton
    {body : CapturedMir} {s_e : MachineState} {m : AnnealStepState}
    {am₁ : List AllocMapEntry} {treeMap' : List ReborrowMapEntry}
    (hrel : StateRelLM3_2 body s_e m am₁)
    (hskel : SameAllocSkeleton am₁ (treeMap'.map ReborrowMapEntry.toAllocMapEntry)) :
    StateRelLM3_2Tree body
      { s_e with memory := { s_e.memory with borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry } }
      m treeMap' :=
  ⟨hrel.replace_borrows_skeleton hskel, rfl⟩

theorem lookupAllocMapByTag_map_toAllocMapEntry
    (treeMap : List ReborrowMapEntry) (tag : Nat) :
    lookupAllocMapByTag (treeMap.map ReborrowMapEntry.toAllocMapEntry) tag =
      (lookupTreeMapByTag treeMap tag).map ReborrowMapEntry.toAllocMapEntry := by
  induction treeMap with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, lookupAllocMapByTag, lookupTreeMapByTag,
      ReborrowMapEntry.toAllocMapEntry]
    cases Nat.beq hd.tag tag
    · exact ih
    · rfl

private theorem evalStackThinPtrTypedDerefRead_locals_eq
    {locals locals' : List LocalSlot} {rootVal val : Value}
    {entry : BorrowEntry} {ptrVal : ProvenancePtr}
    {localDecls : List LocalDecl}
    {layouts : LayoutTable}
    {pointeeTyOpt accessedTyOpt targetTyOpt : Option Ty}
    {targetDecls : List LocalDecl}
    (h : evalStackThinPtrTypedDerefRead locals rootVal entry ptrVal .nil
      localDecls layouts pointeeTyOpt accessedTyOpt targetTyOpt targetDecls = .ok val locals') :
    locals' = locals := by
  unfold evalStackThinPtrTypedDerefRead at h
  have hstrip : stripTransparentProjections (.nil : List ProjectionElem) = .nil := rfl
  rw [hstrip] at h
  dsimp only [] at h
  split at h
  · cases h
  · split at h
    · rename_i res hfast
      revert hfast
      split <;>
      · intro hfast
        first
        | cases hfast
        | (split at hfast
           · split at hfast
             · split at hfast
               · split at hfast
                 · injection hfast with hres; rw [← hres] at h; injection h with _ hl; exact hl.symm
                 · injection hfast with hres; rw [← hres] at h; cases h
               · cases hfast
             · cases hfast
           · cases hfast)
    · split at h
      · split at h
        · split at h
          · injection h with _ hl; exact hl.symm
          · cases h
        · cases h
      · split at h
        · split at h
          · cases h
          · split at h
            · injection h with _ hl; exact hl.symm
            · cases h
        · cases h
        · cases h

private theorem evalOperand_deref_ptr_treeMap_eq
    {locals : List LocalSlot} {refIdx : Local} {ptrVal : ProvenancePtr} {sz : Nat}
    {opKind : Place → MirAst.Operand}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hget : get? locals refIdx = some (.init (.ptr ptrVal sz)))
    (treeMap : List ReborrowMapEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl) :
    evalOperand locals (opKind ⟨refIdx, .cons .deref .nil⟩)
        (treeMap.map ReborrowMapEntry.toBorrowEntry) globals layouts callerLocals localDecls =
      evalOperand locals (opKind ⟨refIdx, .cons .deref .nil⟩)
        ((treeMap.map ReborrowMapEntry.toAllocMapEntry).map AllocMapEntry.toBorrowEntry)
        globals layouts callerLocals localDecls := by
  rcases hopKind with rfl | rfl <;>
  · unfold evalOperand
    cases localDecls with
    | nil =>
      dsimp only []; rw [hget]; dsimp only []
      rw [lookupBorrow_map_toBorrowEntry_treeMap, lookupBorrow_erased_treeMap]
      cases lookupTreeMapByTag treeMap ptrVal.tag with
      | none => rfl
      | some e =>
        rcases e with ⟨_, _, _, _, _⟩
        dsimp only [Option.map, ReborrowMapEntry.toBorrowEntry,
          ReborrowMapEntry.toAllocMapEntry, AllocMapEntry.toBorrowEntry]
    | cons _ _ =>
      dsimp only []; rw [hget]; dsimp only []
      rw [lookupBorrow_map_toBorrowEntry_treeMap, lookupBorrow_erased_treeMap]
      cases lookupTreeMapByTag treeMap ptrVal.tag with
      | none => rfl
      | some e =>
        rcases e with ⟨_, _, _, _, _⟩
        dsimp only [Option.map, ReborrowMapEntry.toBorrowEntry,
          ReborrowMapEntry.toAllocMapEntry, AllocMapEntry.toBorrowEntry]
        rfl

private theorem evalOperand_scalarOperand_borrows_eq
    {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {valTy : Ty}
    (hop : WellTypedScalarOperand body tf op valTy)
    (locals : List LocalSlot) (b₁ b₂ : List BorrowEntry)
    (globals : List CapturedAllocation) (callerLocals : List LocalSlot) :
    evalOperand locals op b₁ globals body.layouts callerLocals =
      evalOperand locals op b₂ globals body.layouts callerLocals := by
  cases hop with
  | constScalar _ _ _ _ _ _ _ _ _ => rfl
  | copyLocal _ _ _ _ _ => rfl

private theorem writePlaceValue_deref_ptr_treeMap_eq
    {locals : List LocalSlot} {refIdx : Local} {ptrVal : ProvenancePtr} {sz : Nat}
    (hget : get? locals refIdx = some (.init (.ptr ptrVal sz)))
    (treeMap : List ReborrowMapEntry)
    (val : Value) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    writePlaceValue locals (treeMap.map ReborrowMapEntry.toBorrowEntry)
        ⟨refIdx, .cons .deref .nil⟩ val localDecls layouts =
      writePlaceValue locals
        ((treeMap.map ReborrowMapEntry.toAllocMapEntry).map AllocMapEntry.toBorrowEntry)
        ⟨refIdx, .cons .deref .nil⟩ val localDecls layouts := by
  unfold writePlaceValue
  cases localDecls with
  | nil =>
    dsimp only []; rw [hget]; dsimp only []
    rw [lookupBorrow_map_toBorrowEntry_treeMap, lookupBorrow_erased_treeMap]
    cases lookupTreeMapByTag treeMap ptrVal.tag with
    | none => rfl
    | some e =>
      rcases e with ⟨_, _, _, _, _⟩
      dsimp only [Option.map, ReborrowMapEntry.toBorrowEntry,
        ReborrowMapEntry.toAllocMapEntry, AllocMapEntry.toBorrowEntry]
  | cons _ _ =>
    dsimp only []; rw [hget]; dsimp only []
    rw [lookupBorrow_map_toBorrowEntry_treeMap, lookupBorrow_erased_treeMap]
    cases lookupTreeMapByTag treeMap ptrVal.tag with
    | none => rfl
    | some e =>
      rcases e with ⟨_, _, _, _, _⟩
      dsimp only [Option.map, ReborrowMapEntry.toBorrowEntry,
        ReborrowMapEntry.toAllocMapEntry, AllocMapEntry.toBorrowEntry]
      rfl

private theorem invalidateConflictingBorrows_treeMap_eq_of_not_mem
    (treeMap : List ReborrowMapEntry) (targetLocal : Local)
    (hnot : ∀ e ∈ treeMap, e.localIdx ≠ targetLocal) :
    invalidateConflictingBorrows (treeMap.map ReborrowMapEntry.toBorrowEntry)
        targetLocal none =
      treeMap.map ReborrowMapEntry.toBorrowEntry := by
  induction treeMap with
  | nil => rfl
  | cons hd tl ih =>
    have hne : Nat.beq hd.localIdx targetLocal = false := by
      cases h : Nat.beq hd.localIdx targetLocal
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) (hnot hd (List.Mem.head tl))
    simp only [List.map_cons, invalidateConflictingBorrows, updateBorrowPerm,
      ReborrowMapEntry.toBorrowEntry, hne,
      ih (fun e he => hnot e (List.mem_cons_of_mem hd he))]

private theorem freezeDerefRead_treeMap_eq
    (locals : List LocalSlot) (treeMap : List ReborrowMapEntry)
    (hnodup : (treeMap.map ReborrowMapEntry.tag).Nodup)
    (ptrIdx : Local) (ptrVal : ProvenancePtr)
    {e : ReborrowMapEntry} (he : e ∈ treeMap) (htag : e.tag = ptrVal.tag)
    (hget : get? locals ptrIdx = some (.init (.ptr ptrVal 8))) :
    (match treeMap.map ReborrowMapEntry.toBorrowEntry with
     | b₁ :: b₂ :: restBorrows =>
       freezeDerefReadBorrowsAt locals ptrIdx .nil (b₁ :: b₂ :: restBorrows)
     | other => other) =
      (derefReadNextTreeMap locals treeMap ptrIdx).map ReborrowMapEntry.toBorrowEntry := by
  have hlook_tm := lookupTreeMapByTag_of_mem_nodup hnodup he htag
  have hlook_bor :
      lookupBorrow (treeMap.map ReborrowMapEntry.toBorrowEntry) ptrVal.tag =
        some e.toBorrowEntry := by
    rw [lookupBorrow_map_toBorrowEntry_treeMap, hlook_tm]; rfl
  have hdr :
      derefReadNextTreeMap locals treeMap ptrIdx =
        treeMap.map (derefReadMapFnTree treeMap e.localIdx ptrVal.tag) := by
    simp [derefReadNextTreeMap, hget, hlook_tm]
  rw [hdr]
  cases treeMap with
  | nil => cases he
  | cons x₁ rest =>
    cases rest with
    | nil =>
      simp [derefReadMapFnTree]
    | cons x₂ rest₂ =>
      simp only [List.map_cons] at hlook_bor ⊢
      unfold freezeDerefReadBorrowsAt
      rw [hget]; dsimp only []
      rw [hlook_bor]; dsimp only []
      have hproj : appendProjections e.toBorrowEntry.targetProjection .nil = .nil := rfl
      have hro : e.toBorrowEntry.rangeOffset = 0 := rfl
      have hrl : e.toBorrowEntry.rangeLen = 0 := rfl
      have htl : e.toBorrowEntry.targetLocal = e.localIdx := rfl
      rw [hproj, hro, hrl, htl]
      have hfrz := freezeTreeBorrowsOnReadAtProj_map_toBorrowEntry_tree
        ((x₁ :: x₂ :: rest₂).map ReborrowMapEntry.toBorrowEntry)
        (x₁ :: x₂ :: rest₂) e.localIdx ptrVal.tag
      dsimp only [List.map_cons, derefReadMapFnTree] at hfrz ⊢
      exact hfrz

/-- In a `treeMap` hierarchy with distinct tags, if the reader's entry `e` is not
`.disabled` and no strict ancestor of `e` forbids a child read
(`treeBorrowAncestorsChildAccessUB .read`), then no ancestor-or-self of the
reader tag (`isBorrowDescendantOrSelf`) is `.disabled`. -/
theorem treeMap_ancestorOrSelf_not_disabled
    {treeMap : List ReborrowMapEntry}
    (hnodup : (treeMap.map ReborrowMapEntry.tag).Nodup)
    {e : ReborrowMapEntry} (he : e ∈ treeMap)
    (hperm : e.perm ≠ .disabled)
    (hanc : treeBorrowAncestorsChildAccessUB .read
      (treeMap.map ReborrowMapEntry.toBorrowEntry) e.parentTag = false) :
    ∀ y ∈ treeMap,
      isBorrowDescendantOrSelf (treeMap.map ReborrowMapEntry.toBorrowEntry) e.tag y.tag =
        true →
      y.perm ≠ .disabled := by
  have hlook : ∀ y ∈ treeMap,
      lookupBorrow (treeMap.map ReborrowMapEntry.toBorrowEntry) y.tag =
        some y.toBorrowEntry := by
    intro y hy
    rw [lookupBorrow_map_toBorrowEntry_treeMap, lookupTreeMapByTag_of_mem_nodup hnodup hy rfl]
    rfl
  have key : ∀ (n : Nat) (c : Nat),
      (∀ z, lookupBorrow (treeMap.map ReborrowMapEntry.toBorrowEntry) c = some z →
        z.perm ≠ .disabled ∧
        treeBorrowChainChildAccessUBAux .read n
          (treeMap.map ReborrowMapEntry.toBorrowEntry) z.parentTag = false) →
      ∀ y ∈ treeMap,
        isBorrowDescendantOrSelfAux n (treeMap.map ReborrowMapEntry.toBorrowEntry) c y.tag =
          true →
        y.perm ≠ .disabled := by
    intro n
    induction n with
    | zero =>
      intro c hc y hy hdesc
      have hceq : c = y.tag := Nat.eq_of_beq_eq_true hdesc
      have hly := hlook y hy
      rw [← hceq] at hly
      exact (hc _ hly).1
    | succ n ih =>
      intro c hc y hy hdesc
      unfold isBorrowDescendantOrSelfAux at hdesc
      cases hbeq : Nat.beq c y.tag with
      | true =>
        have hly := hlook y hy
        rw [← Nat.eq_of_beq_eq_true hbeq] at hly
        exact (hc _ hly).1
      | false =>
        cases hl : lookupBorrow (treeMap.map ReborrowMapEntry.toBorrowEntry) c with
        | none =>
          simp only [hbeq, hl] at hdesc
          cases hdesc
        | some z =>
          have hz := (hc z hl).2
          cases hp : z.parentTag with
          | none =>
            simp only [hbeq, hl, hp] at hdesc
            cases hdesc
          | some p =>
            simp only [hbeq, hl, hp] at hdesc
            rw [hp] at hz
            refine ih p ?_ y hy hdesc
            intro z' hz'
            unfold treeBorrowChainChildAccessUBAux at hz
            simp only [hz'] at hz
            cases hub : treeBorrowTransitionIsUB
                (treeBorrowPermTransition .read .localAccess z'.perm false) with
            | true =>
              simp only [hub] at hz
              cases hz
            | false =>
              simp only [hub] at hz
              refine ⟨?_, hz⟩
              intro hdis
              rw [hdis] at hub
              cases hub
  intro y hy hdesc
  refine key _ e.tag ?_ y hy hdesc
  intro z hz
  rw [hlook e he] at hz
  injection hz with hz
  subst hz
  exact ⟨hperm, hanc⟩

/-- On a `treeMap` hierarchy without protectors, a read through tag `rTag` is
undefined behavior only at a `.disabled` ancestor-or-self of `rTag`. -/
theorem hasTreeReadUB_treeMap_eq_false
    (treeMap subMap : List ReborrowMapEntry) (targetLocal : Local) (rTag : Nat)
    (hgood : ∀ y ∈ subMap,
      isBorrowDescendantOrSelf (treeMap.map ReborrowMapEntry.toBorrowEntry) rTag y.tag =
        true →
      y.perm ≠ .disabled) :
    hasTreeReadUB (treeMap.map ReborrowMapEntry.toBorrowEntry)
      (subMap.map ReborrowMapEntry.toBorrowEntry) .nil targetLocal (some rTag) .nil 0 0 =
      false := by
  induction subMap with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : borrowEntryReadUB (treeMap.map ReborrowMapEntry.toBorrowEntry) .nil
        hd.toBorrowEntry targetLocal (some rTag) .nil 0 0 = false := by
      have hne := hgood hd (List.Mem.head _)
      unfold borrowEntryReadUB
      have hoverlap : borrowEntryOverlapsWrite hd.toBorrowEntry .nil 0 0 = true := rfl
      have htl_eq : hd.toBorrowEntry.targetLocal = hd.localIdx := rfl
      have htag_eq : hd.toBorrowEntry.tag = hd.tag := rfl
      rw [htl_eq]
      cases Nat.beq hd.localIdx targetLocal with
      | false => rfl
      | true =>
        dsimp only
        rw [hoverlap]
        dsimp only
        rw [htag_eq]
        cases hb : isBorrowDescendantOrSelf (treeMap.map ReborrowMapEntry.toBorrowEntry)
            rTag hd.tag with
        | true =>
          have hne' := hne hb
          rcases hd with ⟨_, _, _, perm, _⟩
          cases perm <;> first | rfl | exact absurd rfl hne'
        | false =>
          rcases hd with ⟨_, _, _, perm, _⟩
          cases perm <;> rfl
    rw [List.map_cons]
    unfold hasTreeReadUB
    rw [hhd]
    exact ih (fun y hy => hgood y (List.mem_cons_of_mem _ hy))

/-- A dereference read through the pointer in `ptrIdx`, whose tag belongs to the
non-`.disabled` entry `e` of a `treeMap` hierarchy without protectors, is not
undefined behavior when no strict ancestor of `e` forbids a child read. -/
theorem derefReadTreeUB_treeMap_eq_false
    (locals : List LocalSlot) (treeMap : List ReborrowMapEntry)
    (hnodup : (treeMap.map ReborrowMapEntry.tag).Nodup)
    (ptrIdx : Local) (ptrVal : ProvenancePtr)
    {e : ReborrowMapEntry} (he : e ∈ treeMap) (htag : e.tag = ptrVal.tag)
    (hget : get? locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hperm : e.perm ≠ .disabled)
    (hanc : treeBorrowAncestorsChildAccessUB .read
      (treeMap.map ReborrowMapEntry.toBorrowEntry) e.parentTag = false) :
    derefReadTreeUB locals ptrIdx .nil (treeMap.map ReborrowMapEntry.toBorrowEntry) .nil =
      false := by
  have hlook_tm := lookupTreeMapByTag_of_mem_nodup hnodup he htag
  have hlook_bor :
      lookupBorrow (treeMap.map ReborrowMapEntry.toBorrowEntry) ptrVal.tag =
        some e.toBorrowEntry := by
    rw [lookupBorrow_map_toBorrowEntry_treeMap, hlook_tm]; rfl
  have hgood := treeMap_ancestorOrSelf_not_disabled hnodup he hperm hanc
  rw [htag] at hgood
  unfold derefReadTreeUB
  rw [hget]
  dsimp only
  rw [hlook_bor]
  dsimp only [ReborrowMapEntry.toBorrowEntry, appendProjections]
  exact hasTreeReadUB_treeMap_eq_false treeMap treeMap e.localIdx ptrVal.tag hgood

/-- A dereference write through the pointer in `ptrIdx`, whose tag belongs to the
entry `e` of a `treeMap` hierarchy, is not undefined behavior at a strict
ancestor when no strict ancestor of `e` forbids a child write. -/
theorem derefWriteTreeUB_treeMap_eq_false
    (locals : List LocalSlot) (treeMap : List ReborrowMapEntry)
    (hnodup : (treeMap.map ReborrowMapEntry.tag).Nodup)
    (ptrIdx : Local) (ptrVal : ProvenancePtr)
    {e : ReborrowMapEntry} (he : e ∈ treeMap) (htag : e.tag = ptrVal.tag)
    (hget : get? locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hanc : treeBorrowAncestorsChildAccessUB .write
      (treeMap.map ReborrowMapEntry.toBorrowEntry) e.parentTag = false) :
    derefWriteTreeUB locals (treeMap.map ReborrowMapEntry.toBorrowEntry)
      ⟨ptrIdx, .cons .deref .nil⟩ = false := by
  have hlook_tm := lookupTreeMapByTag_of_mem_nodup hnodup he htag
  have hlook_bor :
      lookupBorrow (treeMap.map ReborrowMapEntry.toBorrowEntry) ptrVal.tag =
        some e.toBorrowEntry := by
    rw [lookupBorrow_map_toBorrowEntry_treeMap, hlook_tm]; rfl
  cases treeMap with
  | nil => rfl
  | cons x₁ rest =>
    cases rest with
    | nil => rfl
    | cons x₂ rest₂ =>
      simp only [List.map_cons] at hlook_bor hanc ⊢
      unfold derefWriteTreeUB
      dsimp only
      rw [hget]
      dsimp only
      rw [hlook_bor]
      exact hanc

/-- **`step_reborrow_safeRef_tree_simulation_explicit` (`LM-3.2` Tree Borrows Reborrow)**:
computable `StepRelLM3_2Tree` step simulation for reborrowing `_d = &bk (*_r)`
with post-step borrow hierarchy `reborrowTreeMapNext body.localDecls body.layouts bk s.frame.locals treeMap refIdx s.memory.nextTag`
recording `parentTag = some ptrVal.tag` on the newly minted child tag `nextTag`. -/
theorem step_reborrow_safeRef_tree_simulation_explicit
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {dstDecl refDecl : LocalDecl}
    {bk : BorrowKind} {refMut dstMut : Trusted.Rustc.V2026_06_01.MirAst.Mutability}
    {pointeeKind dstPointee : RigidTy}
    {span : String}
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : Trusted.Sequence.get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : Trusted.Sequence.get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref refMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_zero_perm : ∀ ptrVal e,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      Trusted.Sequence.get? s.frame.locals e.localIdx ≠ some .dead ∧
      Trusted.Sequence.get? s.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, Trusted.Sequence.get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind))
    (hanc_read : ∀ ptrVal e,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      treeBorrowAncestorsChildAccessUB .read s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    StepRelLM3_2Tree body m
      (reborrowTreeMapNext body.localDecls body.layouts bk s.frame.locals treeMap refIdx
        s.memory.nextTag)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  let s_e := eraseBorrowParents s treeMap
  let am := treeMap.map ReborrowMapEntry.toAllocMapEntry
  let treeMap' :=
    reborrowTreeMapNext body.localDecls body.layouts bk s.frame.locals treeMap refIdx
      s.memory.nextTag
  have hstate_e : StateRelLM3_2 body s_e m am := htree.erased_rel
  have hbor_s : s.memory.borrows = treeMap.map ReborrowMapEntry.toBorrowEntry := htree.borrows_eq
  obtain ⟨tf, hframes, hretCont, hretPlace, hfr, hcal_e, hstack_e, hprot_e, hcaller_e,
    hbor_e, halloc_e, hdisj⟩ := id hstate_e
  have hcal : s.memory.activeCallee = none := hcal_e
  have hstack : s.memory.callStack = .nil := hstack_e
  have hprot : s.memory.activeProtectors = .nil := hprot_e
  have hcaller : s.memory.callerLocals = .nil := hcaller_e
  have hnodup_tm : (treeMap.map ReborrowMapEntry.tag).Nodup := by
    have htags : am.map AllocMapEntry.tag = treeMap.map ReborrowMapEntry.tag := by
      dsimp only [am]; rw [List.map_map]; rfl
    rw [← htags]; exact halloc_e.tags_nodup
  have hflat_ub := (evalRvalue_reborrow_safeRef_simulation hstate_e hphase hbb hstmt
    hdecl_dst hdecl_ref href_ty hdst_ty hpk_prim himm (by
      intro ptrVal e' hget he' htag'
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      exact hlive_zero_perm ptrVal e hget he htag') hlay_coh).1
  obtain ⟨himm_d, himm_r⟩ := himm tf hframes
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate_e.cache_layout hframes hdecl_dst hlt_d
  have hfra := hstate_a.frame_rel_singleton rfl
  obtain ⟨slot_r, mls_r, _, hlt_ra, hslot_ra, hmls_ra, hmls_ra_eq, hloc_r⟩ :=
    hfra.lookup_local hdecl_ref
  have hcache_r : ∀ l, mls_r.layout = some l → l = translateTy refDecl.ty body.layouts :=
    hloc_r.cachedLayout_eq
  have himm_ra : ∀ mp, mls_r.value ≠ .live (.indirect mp) :=
    himm_r.cache_layout hlt_d _ mls_r hmls_ra
  have hslot_d_s : get? s.frame.locals dstIdx = some slot_d := hslot_d
  have hslot_ra_s : get? s.frame.locals refIdx = some slot_r := hslot_ra
  rcases hloc_r.ref_immediate_cases href_ty himm_ra with
    ⟨hsr_dead, _⟩ | ⟨hsr_un, _⟩ | ⟨sc_r, _, hsr_sc, _⟩ |
    ⟨ptrVal, mptr, hsr_ptr, hptrRel, hmr_ptr⟩
  · have ha_s : stepMirFn body s = MirStepNode.fail .ub := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []
      rw [hslot_ra_s, hsr_dead]
    have ha_e : stepMirFn body s_e = MirStepNode.fail .ub := by
      rw [stepMirFn_eq_of_not_other body s_e hcal_e hphase]
      dsimp only [s_e, eraseBorrowParents]
      simp only [hbb, hstmt]; unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []
      rw [hslot_ra_s, hsr_dead]
    obtain ⟨m', msg, hm_err⟩ := hflat_ub.mp ha_e
    rw [ha_s, hm_err]; exact .ub _ _ _
  · have ha_s : stepMirFn body s = MirStepNode.fail .ub := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []
      rw [hslot_ra_s, hsr_un]
    have ha_e : stepMirFn body s_e = MirStepNode.fail .ub := by
      rw [stepMirFn_eq_of_not_other body s_e hcal_e hphase]
      dsimp only [s_e, eraseBorrowParents]
      simp only [hbb, hstmt]; unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []
      rw [hslot_ra_s, hsr_un]
    obtain ⟨m', msg, hm_err⟩ := hflat_ub.mp ha_e
    rw [ha_s, hm_err]; exact .ub _ _ _
  · have ha_s : stepMirFn body s = MirStepNode.fail .ub := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []
      rw [hslot_ra_s, hsr_sc]
    have ha_e : stepMirFn body s_e = MirStepNode.fail .ub := by
      rw [stepMirFn_eq_of_not_other body s_e hcal_e hphase]
      dsimp only [s_e, eraseBorrowParents]
      simp only [hbb, hstmt]; unfold evalStmt evalRvalue evalRvalueRefDeref; dsimp only []
      rw [hslot_ra_s, hsr_sc]
    obtain ⟨m', msg, hm_err⟩ := hflat_ub.mp ha_e
    rw [ha_s, hm_err]; exact .ub _ _ _
  · have hsr_full : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) :=
      hslot_ra_s.trans (congrArg some hsr_ptr)
    have hsr_full_e : get? s_e.frame.locals refIdx = some (.init (.ptr ptrVal 8)) := hsr_full
    obtain ⟨_, borTag, hprov_eq, hid_lt, _, hmptr_off, ⟨e_am, he_am, htag_am, rfl⟩⟩ := id hptrRel
    obtain ⟨e, he, he_to⟩ := List.mem_map.mp he_am
    subst he_to
    have htag : e.tag = ptrVal.tag := htag_am
    obtain ⟨hlive_t, hun_t, hoff0, hne_dis, hnot_fmut, htgt_kind⟩ :=
      hlive_zero_perm ptrVal e hsr_full he htag
    obtain ⟨tgtDecl, sc_t, _, hdecl_t, _, hslot_t, hsz_sc, _⟩ :=
      hstate_e.alloc_target_init_scalar he_am hlive_t hun_t
    obtain ⟨accTy, hpt_res, hacc_kind⟩ :=
      placeTyResolved_deref_safeRef_prim (layouts := body.layouts) hdecl_ref href_ty
    have hacc_prim : IsPrimScalarTy accTy := hpk_prim.of_kind_eq hacc_kind
    have htgt_acc_kind : tgtDecl.ty.kind = accTy.kind :=
      (htgt_kind tgtDecl hdecl_t).trans hacc_kind.symm
    have hlook_tm := lookupTreeMapByTag_of_mem_nodup hnodup_tm he htag
    have hlook_s : lookupBorrow s.memory.borrows ptrVal.tag = some e.toBorrowEntry := by
      rw [hbor_s, lookupBorrow_map_toBorrowEntry_treeMap, hlook_tm]; rfl
    have htm'_eq :
        treeMap' =
          { tag := s.memory.nextTag
            localIdx := e.localIdx
            allocId := e.allocId
            perm := reborrowPermOf body.localDecls body.layouts bk refIdx
            parentTag := some ptrVal.tag } ::
            treeMap.map
              (ReborrowMapEntry.updateOnRead (treeMap.map ReborrowMapEntry.toBorrowEntry)
                e.localIdx ptrVal.tag) := by
      dsimp only [treeMap']; simp [reborrowTreeMapNext, hsr_full, hlook_tm]
    have hnf : e.perm = .frozen → bk = .shared := fun hfz => by
      rcases hbk : bk with _ | _
      · rfl
      · exact absurd ⟨hfz, by rw [hbk]; exact fun h => BorrowKind.noConfusion h⟩ hnot_fmut
    have hrv_s :
        evalRvalue s.frame.locals (.ref bk ⟨refIdx, .cons .deref .nil⟩)
          s.memory body.localDecls body.layouts =
          .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals
            { s.memory with
              borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry
              nextTag := s.memory.nextTag + 1 } := by
      have hfrz := freezeTreeBorrowsOnReadAtProj_map_toBorrowEntry_tree
        (treeMap.map ReborrowMapEntry.toBorrowEntry) treeMap e.localIdx ptrVal.tag
      have hrd : hasTreeReadUB (treeMap.map ReborrowMapEntry.toBorrowEntry)
          (treeMap.map ReborrowMapEntry.toBorrowEntry) .nil e.localIdx (some ptrVal.tag)
          .nil 0 0 = false := by
        have hgood := treeMap_ancestorOrSelf_not_disabled hnodup_tm he hne_dis
          (by rw [← hbor_s]; exact hanc_read ptrVal e hsr_full he htag)
        rw [htag] at hgood
        exact hasTreeReadUB_treeMap_eq_false treeMap treeMap e.localIdx ptrVal.tag hgood
      have hsh_perm :
          sharedBorrowPerm body.localDecls body.layouts ⟨refIdx, .cons .deref .nil⟩ = .frozen := by
        rcases hpk_prim with hpk | hpk | ⟨_, hpk⟩ | ⟨_, hpk⟩ <;>
          (dsimp only at hpk;
           unfold sharedBorrowPerm placeTy resolveProjectedTy pointeeTyOf tyIsFreeze rigidTyIsFreeze;
           dsimp only []; rw [hdecl_ref]; dsimp only []; rw [href_ty]; dsimp only []; rw [hpk])
      have hmut_perm :
          mutableBorrowPerm body.localDecls body.layouts ⟨refIdx, .cons .deref .nil⟩ =
            .reservedFrz false := by
        rcases hpk_prim with hpk | hpk | ⟨_, hpk⟩ | ⟨_, hpk⟩ <;>
          (dsimp only at hpk;
           unfold mutableBorrowPerm placeTy resolveProjectedTy pointeeTyOf tyIsFreeze rigidTyIsFreeze;
           dsimp only []; rw [hdecl_ref]; dsimp only []; rw [href_ty]; dsimp only []; rw [hpk])
      have hzst :
          placeIsZeroSized body.localDecls body.layouts ⟨refIdx, .cons .deref .nil⟩ = false := by
        rcases hpk_prim with hpk | hpk | ⟨w, hpk⟩ | ⟨w, hpk⟩ <;>
          (dsimp only at hpk;
           unfold placeIsZeroSized placeTy resolveProjectedTy pointeeTyOf tyIsZeroSized
             rigidTyIsZeroSized;
           dsimp only []; rw [hdecl_ref]; dsimp only []; rw [href_ty]; dsimp only []; rw [hpk];
           try cases w <;> rfl)
      have hcda :
          checkDerefAlign body.localDecls body.layouts (some accTy) ptrVal.offsetBytes = true := by
        rw [hoff0]
      have hres_tgt :
          resolveRefDerefTarget? s.frame.locals (.scalar sc_t) e.toBorrowEntry ptrVal .nil
            body.localDecls body.layouts (some accTy) (some accTy) false body.localDecls =
            .some (.some (.nil, 0)) :=
        resolveRefDerefTarget?_prim_scalar_zero s.frame.locals hlay_coh hacc_prim hdecl_t rfl
          htgt_acc_kind hoff0 hsz_sc
      have htl : e.toBorrowEntry.targetLocal = e.localIdx := rfl
      have hro : e.toBorrowEntry.rangeOffset = 0 := rfl
      have hrl : e.toBorrowEntry.rangeLen = 0 := rfl
      have hperm_eq : e.toBorrowEntry.perm = e.perm := rfl
      unfold evalRvalue evalRvalueRefDeref
      dsimp only [stripTransparentProjections]
      rw [hlay_coh.1, hpt_res, hsr_full]
      dsimp only [Nat.beq]
      have hslot_t' : get? s.frame.locals e.localIdx = some (.init (.scalar sc_t)) := hslot_t
      rw [hcda, Bool.true_and, hlook_s]
      dsimp only []
      rw [htl, hslot_t']
      dsimp only []
      rw [hro, hrl, hperm_eq, hres_tgt]
      dsimp only [resolveBorrowProjectionElems]
      rw [hbor_s, hprot, htm'_eq]
      dsimp only [List.map_cons, ReborrowMapEntry.toBorrowEntry, reborrowPermOf]
      rw [hsh_perm, hmut_perm, hzst, hfrz]
      generalize treeMap.map ReborrowMapEntry.toBorrowEntry = B at hrd ⊢
      cases B with
      | nil =>
        cases hp : e.perm <;> rcases hm : bk with _ | ⟨_ | _⟩
        all_goals first
          | exact absurd hp hne_dis
          | exact BorrowKind.noConfusion (hm.symm.trans (hnf hp))
          | rfl
      | cons b₁ rest =>
        cases rest with
        | nil =>
          cases hp : e.perm <;> rcases hm : bk with _ | ⟨_ | _⟩
          all_goals first
            | exact absurd hp hne_dis
            | exact BorrowKind.noConfusion (hm.symm.trans (hnf hp))
            | rfl
        | cons b₂ rest₂ =>
          cases hp : e.perm <;> rcases hm : bk with _ | ⟨_ | _⟩
          all_goals first
            | exact absurd hp hne_dis
            | exact BorrowKind.noConfusion (hm.symm.trans (hnf hp))
            | (dsimp only []; rw [hrd]; rfl)
    by_cases hsd_dead : slot_d = .dead
    · have ha_s : stepMirFn body s = MirStepNode.fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]; unfold evalStmt; dsimp only []
        rw [hrv_s]; dsimp only []
        rw [hslot_d_s, hsd_dead]
      have hrv_e :
          ∃ mem₁, evalRvalue s_e.frame.locals (.ref bk ⟨refIdx, .cons .deref .nil⟩)
            s_e.memory body.localDecls body.layouts =
            .ok (.ptr { allocId := s_e.memory.nextTag, offsetBytes := 0 } 8) s_e.frame.locals mem₁ := by
        obtain ⟨mem₁, hrv, _⟩ := evalRvalue_reborrow_root_ok halloc_e.tags_nodup hbor_e hprot_e
          hsr_full_e he_am htag_am hne_dis hnot_fmut hlay_coh hpt_res hacc_prim hdecl_t
          htgt_acc_kind hoff0 hslot_t hsz_sc
        exact ⟨mem₁, hrv⟩
      obtain ⟨mem₁, hrv_e_eq⟩ := hrv_e
      have ha_e : stepMirFn body s_e = MirStepNode.fail .ub := by
        rw [stepMirFn_eq_of_not_other body s_e hcal_e hphase]
        dsimp only [s_e, eraseBorrowParents] at hrv_e_eq ⊢
        simp only [hbb, hstmt]; unfold evalStmt; dsimp only []
        rw [hrv_e_eq]; dsimp only []; rw [hslot_d_s, hsd_dead]
      obtain ⟨m', msg, hm_err⟩ := hflat_ub.mp ha_e
      rw [ha_s, hm_err]; exact .ub _ _ _
    · -- Live immediate `dstIdx`: both machines step cleanly!
      have hnot_dst_am : ∀ x ∈ am, x.localIdx ≠ dstIdx :=
        hstate_e.immediate_not_in_allocMap hframes hslot_d hsd_dead himm_d
      have hnot_dst_tm : ∀ x ∈ treeMap, x.localIdx ≠ dstIdx :=
        fun x hx => hnot_dst_am x.toAllocMapEntry (List.mem_map_of_mem hx)
      have hnot_dst_tm' : ∀ x ∈ treeMap', x.localIdx ≠ dstIdx := by
        rw [htm'_eq]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact hnot_dst_tm e he
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hmem
          rw [ReborrowMapEntry.updateOnRead_localIdx]
          exact hnot_dst_tm y hy
      have hinv_tm' := invalidateConflictingBorrows_treeMap_eq_of_not_mem treeMap' dstIdx hnot_dst_tm'
      have hlt_af_d_s : dstIdx < s.frame.locals.length := hlt_af_d
      have ha_s :
          stepMirFn body s =
            MirStepNode.step
              (advanceStmt s
                (s.frame.locals.set dstIdx
                  (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)))
                { s.memory with
                  borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry
                  nextTag := s.memory.nextTag + 1 }) := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]; unfold evalStmt; dsimp only []
        rw [hrv_s]; dsimp only []
        rw [hslot_d_s]
        cases slot_d with
        | dead => exact absurd rfl hsd_dead
        | uninit => simp only [set?_eq_some_set hlt_af_d_s, hprot, hinv_tm']
        | init _ => simp only [set?_eq_some_set hlt_af_d_s, hprot, hinv_tm']
      have hmls_ra' : tfa.locals[refIdx]'hlt_ra =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_r.layout⟩ := by
        rw [hmls_ra_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr_ptr; subst hmr_ptr; rfl
      let tfb := cacheFrameLocalLayout tfa refIdx hlt_ra (translateTy refDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_ra hdecl_ref hmls_ra' hcache_r
      have hder_ptr := annealDerefOperandToMemPlace_safeRef_ptr_live hstate_e hdecl_ref href_ty
        hpk_prim hprov_eq hmptr_off he_am hoff0 hlive_t htgt_kind
        (translateTy refDecl.ty body.layouts) (st := { m with stack := ⟨#[tfb]⟩ }) rfl
      dsimp only [ReborrowMapEntry.toAllocMapEntry] at hder_ptr hid_lt hmptr_off hprov_eq
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
      have hrv_m := evalRvalueIntoPlace_ref_ok (region := .Erased)
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
      have hex_old : ∃ oldImm, mls_db.value = .live (.immediate oldImm) := by
        rcases hloc_db.ref_immediate_cases hdst_ty himm_db with
          ⟨hsd, _⟩ | ⟨_, hmd⟩ | ⟨_, _, _, _, _, hmd⟩ | ⟨_, _, _, _, hmd⟩
        · exact absurd hsd hsd_dead
        · exact ⟨_, hmd⟩
        · exact ⟨_, hmd⟩
        · exact ⟨_, hmd⟩
      obtain ⟨oldImm, hmdb_imm⟩ := hex_old
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
            (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩) m =
          Miri.Interpreter.runRvalue
            (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts)
              () (.Ref .Erased (translateBorrowKind bk)
                (translatePlace ⟨refIdx, .cons .deref .nil⟩)) ⟨dstIdx, #[]⟩) m := rfl
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
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv_m, hw]
      rw [ha_s, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok
        rfl hfrb.location_eq]
      apply StepRelLM3_2Tree.step
      -- Build `StateRelLM3_2Tree` on `(advanceStmt s ..., m', treeMap')`:
      let am_read :=
        (treeMap.map
          (ReborrowMapEntry.updateOnRead (treeMap.map ReborrowMapEntry.toBorrowEntry)
            e.localIdx ptrVal.tag)).map ReborrowMapEntry.toAllocMapEntry
      let newAllocEntry : AllocMapEntry :=
        { tag := s.memory.nextTag
          localIdx := e.localIdx
          allocId := e.allocId
          perm := reborrowPermOf body.localDecls body.layouts bk refIdx }
      have ham'_eq : treeMap'.map ReborrowMapEntry.toAllocMapEntry = newAllocEntry :: am_read := by
        rw [htm'_eq]; rfl
      have hskel_read : SameAllocSkeleton am am_read :=
        SameAllocSkeleton.of_map_right treeMap
          (ReborrowMapEntry.updateOnRead (treeMap.map ReborrowMapEntry.toBorrowEntry)
            e.localIdx ptrVal.tag)
          (fun x => ReborrowMapEntry.updateOnRead_tag _ _ _ x)
          (fun x => ReborrowMapEntry.updateOnRead_localIdx _ _ _ x)
          (fun x => ReborrowMapEntry.updateOnRead_allocId _ _ _ x)
      have hstate_read := hstate_b.replace_borrows_skeleton hskel_read
      obtain ⟨tfb', hfb', hretCont_b, hretPlace_b, hfr_read, _, _, _, _, _, halloc_read, hdisj_b⟩ :=
        id hstate_read
      injection hfb' with h₁; injection h₁ with h₂; subst h₂
      obtain ⟨e_r, he_r, _, hl_er, ha_er⟩ := hskel_read.mem_left he_am
      have he_r_loc : e_r.localIdx = e.localIdx := hl_er.symm
      have he_r_aid : e_r.allocId = e.allocId := ha_er.symm
      have hptr_new :
          PtrRel (newAllocEntry :: am_read)
            { allocId := s.memory.nextTag, offsetBytes := 0 } mptr :=
        .mk e.allocId borTag hprov_eq hid_lt (show (0 : Nat) < 2 ^ 32 by decide)
          (by rw [hmptr_eq]; simp)
          ⟨newAllocEntry, List.Mem.head _, rfl, rfl⟩
      have hdb_elem : tfb.locals[dstIdx]'hlt_db = ⟨.live (.immediate oldImm), mls_db.layout⟩ :=
        Option.some.inj ((Array.getElem?_eq_getElem hlt_db).symm.trans hdb_imm)
      have hnew_d :
          LocalRelLM3_2 m.machine (newAllocEntry :: am_read) dstDecl body.layouts
            (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
            { tfb.locals[dstIdx]'hlt_db with
              value := .live (.immediate (.scalar
                (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) } := by
        rw [hdb_elem]
        exact .ref _ _ _ dstMut dstPointee hloc_db.cachedLayout_eq hdst_ty hptr_new
      have hfr_final := ((hfr_read.mono_cons newAllocEntry).update_local hdecl_dst _ _ hnew_d).advance
      have hnodup_new : ((newAllocEntry :: am_read).map AllocMapEntry.tag).Nodup := by
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, halloc_read.tags_nodup⟩
        intro hmem
        obtain ⟨x, hx, htag_eq⟩ := List.mem_map.mp hmem
        have hlt_tag : x.tag < s.memory.nextTag := (halloc_read.borrow_sync x hx).1
        dsimp only [newAllocEntry] at htag_eq
        omega
      refine ⟨?_, rfl⟩
      rw [ham'_eq]
      refine .mk _ rfl hretCont_b hretPlace_b hfr_final hcal hstack hprot hcaller
        (by dsimp only [eraseBorrowParents, advanceStmt]; rw [ham'_eq]) ?_ ?_
      · refine ⟨hnodup_new, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x₁ hx₁ x₂ hx₂ hloc_eq
          rcases List.mem_cons.mp hx₁ with rfl | hm₁ <;>
            rcases List.mem_cons.mp hx₂ with rfl | hm₂
          · rfl
          · dsimp only [newAllocEntry]; rw [← he_r_aid]
            exact halloc_read.local_to_alloc_unique e_r he_r x₂ hm₂ (he_r_loc.trans hloc_eq)
          · symm; dsimp only [newAllocEntry]; rw [← he_r_aid]
            exact halloc_read.local_to_alloc_unique e_r he_r x₁ hm₁
              (he_r_loc.trans hloc_eq.symm)
          · exact halloc_read.local_to_alloc_unique x₁ hm₁ x₂ hm₂ hloc_eq
        · intro x₁ hx₁ x₂ hx₂ hid_eq
          rcases List.mem_cons.mp hx₁ with rfl | hm₁ <;>
            rcases List.mem_cons.mp hx₂ with rfl | hm₂
          · rfl
          · exact he_r_loc.symm.trans (halloc_read.alloc_to_local_injective e_r he_r x₂ hm₂
              (he_r_aid.trans hid_eq))
          · exact (halloc_read.alloc_to_local_injective x₁ hm₁ e_r he_r
              (hid_eq.trans he_r_aid.symm)).trans he_r_loc
          · exact halloc_read.alloc_to_local_injective x₁ hm₁ x₂ hm₂ hid_eq
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hm
          · dsimp only [newAllocEntry]; rw [← he_r_loc]; exact halloc_read.target_decl e_r he_r
          · exact halloc_read.target_decl x hm
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hm
          · dsimp only [newAllocEntry]; rw [← he_r_aid]; exact halloc_read.base_addr_valid e_r he_r
          · exact halloc_read.base_addr_valid x hm
        · intro x hx
          have hlook_all := lookupBorrow_map_toBorrowEntry_of_nodup hnodup_new hx
          rcases List.mem_cons.mp hx with rfl | hm
          · refine ⟨Nat.lt_succ_self _, ?_⟩
            dsimp only [eraseBorrowParents, advanceStmt]; rw [ham'_eq]; exact hlook_all
          · have hlt_x : x.tag < s.memory.nextTag := (halloc_read.borrow_sync x hm).1
            refine ⟨Nat.lt_trans hlt_x (Nat.lt_succ_self _), ?_⟩
            dsimp only [eraseBorrowParents, advanceStmt]; rw [ham'_eq]; exact hlook_all
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hm
          · dsimp only [newAllocEntry]; rw [← he_r_aid]; exact halloc_read.live_key_unique e_r he_r
          · exact halloc_read.live_key_unique x hm
        · intro tf' htf' x hx
          injection htf' with h₁'; injection h₁' with h₂'; subst h₂'
          have hex_orig : ∃ x₀ ∈ am_read, x.localIdx = x₀.localIdx ∧ x.allocId = x₀.allocId := by
            rcases List.mem_cons.mp hx with rfl | hm
            · exact ⟨e_r, he_r, he_r_loc.symm, he_r_aid.symm⟩
            · exact ⟨x, hm, rfl, rfl⟩
          obtain ⟨x₀, hx₀, hx_loc, hx_aid⟩ := hex_orig
          rw [hx_loc, hx_aid]
          obtain ⟨a₀, ha₀, _, hl₀, _⟩ := hskel_read.symm.mem_left hx₀
          have hne_d : dstIdx ≠ x₀.localIdx :=
            Ne.symm (hl₀ ▸ hnot_dst_am a₀ ha₀)
          obtain ⟨hlive_x, hdead_x⟩ := halloc_read.local_alloc_sync tfb rfl x₀ hx₀
          have hslot_after :
              get? (eraseBorrowParents
                (advanceStmt s
                  (s.frame.locals.set dstIdx
                    (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)))
                  { s.memory with
                    borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry
                    nextTag := s.memory.nextTag + 1 }) treeMap').frame.locals x₀.localIdx =
              get? s.frame.locals x₀.localIdx := by
            dsimp only [eraseBorrowParents, advanceStmt]
            rw [get?_eq_getElem?, List.getElem?_set_ne hne_d, ← get?_eq_getElem?]
          refine ⟨fun slot hslot hne_dead => ?_, fun hdead => ?_⟩
          · rw [hslot_after] at hslot
            obtain ⟨⟨lay_x, hlay_x⟩, hsc_x, hshape_x⟩ := hlive_x slot hslot hne_dead
            refine ⟨⟨lay_x, ?_⟩, hsc_x, hshape_x⟩
            show (tfb.locals.set dstIdx _ hlt_db)[x₀.localIdx]? = _
            rw [Array.getElem?_set_ne _ hne_d]
            exact hlay_x
          · rw [hslot_after] at hdead
            exact hdead_x hdead
      · apply MemoryAllocDisjoint.mono_immediate hdisj_b
        intro k
        by_cases hk : k = dstIdx
        · subst hk
          right
          refine ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
            mls_db.layout, ?_⟩
          show (tfb.locals.set k _ hlt_db)[k]? = _
          rw [Array.getElem?_set_self, hdb_elem]
        · left
          show (tfb.locals.set dstIdx _ hlt_db)[k]? = _
          rw [Array.getElem?_set_ne _ (Ne.symm hk)]

theorem evalRvalue_reborrow_safeRef_tree_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {dstDecl refDecl : LocalDecl}
    {bk : BorrowKind} {refMut dstMut : Trusted.Rustc.V2026_06_01.MirAst.Mutability}
    {pointeeKind dstPointee : RigidTy}
    {span : String}
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : Trusted.Sequence.get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : Trusted.Sequence.get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref refMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_zero_perm : ∀ ptrVal e,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      Trusted.Sequence.get? s.frame.locals e.localIdx ≠ some .dead ∧
      Trusted.Sequence.get? s.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, Trusted.Sequence.get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind))
    (hanc_read : ∀ ptrVal e,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      treeBorrowAncestorsChildAccessUB .read s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    ((stepMirFn body s = MirStepNode.fail .ub) ↔
      ∃ m' msg,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg))) ∧
    (∀ s' m',
      stepMirFn body s = MirStepNode.step s' →
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) →
      ∃ (treeMap' : List ReborrowMapEntry),
        StepRelLM3_2Tree body m treeMap' (MirStepNode.step s') (m', .ok true)) := by
  have hsim := step_reborrow_safeRef_tree_simulation_explicit htree hphase hbb hstmt
    hdecl_dst hdecl_ref href_ty hdst_ty hpk_prim himm hlive_zero_perm hanc_read hlay_coh
  generalize ha : stepMirFn body s = an at hsim ⊢
  generalize hm : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
    mr at hsim ⊢
  refine ⟨⟨fun hub => ?_, fun ⟨m', msg, herr⟩ => ?_⟩, fun s' m' hs' hm' => ?_⟩
  · subst hub; cases hsim; exact ⟨_, _, rfl⟩
  · subst herr; cases hsim; rfl
  · subst hs' hm'; exact ⟨_, hsim⟩

theorem step_safeRef_deref_read_tree_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {opKind : Place → Operand} {span : String}
    (hopKind : opKind = Operand.copy ∨ opKind = Operand.move)
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl refDecl : LocalDecl} {mutability : Trusted.Rustc.V2026_06_01.MirAst.Mutability}
    (hdecl_dst : Trusted.Sequence.get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : Trusted.Sequence.get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal, Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ treeMap, e.tag = ptrVal.tag →
        Trusted.Sequence.get? s.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, Trusted.Sequence.get? body.localDecls e.localIdx = some decl →
            decl.ty.kind = dstDecl.ty.kind))
    (hanc_read : ∀ ptrVal,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ treeMap, e.tag = ptrVal.tag →
        treeBorrowAncestorsChildAccessUB .read s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    StepRelLM3_2Tree body m (derefReadNextTreeMap s.frame.locals treeMap refIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  let s_e := eraseBorrowParents s treeMap
  let am := treeMap.map ReborrowMapEntry.toAllocMapEntry
  let treeMap' := derefReadNextTreeMap s.frame.locals treeMap refIdx
  have hsim := step_safeRef_deref_read_simulation_explicit htree.erased_rel hphase hopKind
    hbb hstmt hdecl_dst hdecl_ref href_ty hdst_prim himm (by
      intro ptrVal hget e' he' htag' hdead
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      exact hlive_ref ptrVal hget e he htag' hdead) hlay_coh
  obtain ⟨tf, hframes, _, _, hfr, hcal_e, _, hprot_e, hcaller_e, hbor_e, halloc_e, _⟩ :=
    id htree.erased_rel
  have hcal : s.memory.activeCallee = none := hcal_e
  have hprot : s.memory.activeProtectors = .nil := hprot_e
  have hbor_s : s.memory.borrows = treeMap.map ReborrowMapEntry.toBorrowEntry := htree.borrows_eq
  have hnodup_tm : (treeMap.map ReborrowMapEntry.tag).Nodup := by
    have htags : am.map AllocMapEntry.tag = treeMap.map ReborrowMapEntry.tag := by
      dsimp only [am]; rw [List.map_map]; rfl
    rw [← htags]; exact halloc_e.tags_nodup
  have hskel : SameAllocSkeleton (derefReadNextAllocMap s.frame.locals am refIdx)
      (treeMap'.map ReborrowMapEntry.toAllocMapEntry) := by
    dsimp only [derefReadNextAllocMap, derefReadNextTreeMap, am, treeMap']
    cases hgr : get? s.frame.locals refIdx with
    | none => exact .refl _
    | some slot =>
      cases slot with
      | dead => exact .refl _
      | uninit => exact .refl _
      | init val =>
        cases val with
        | unit => exact .refl _
        | scalar _ => exact .refl _
        | aggregate _ _ => exact .refl _
        | ptr ptrVal sz =>
          by_cases hsz : sz = 8
          · subst hsz
            simp only [lookupAllocMapByTag_map_toAllocMapEntry]
            cases lookupTreeMapByTag treeMap ptrVal.tag with
            | none => exact .refl _
            | some e =>
              dsimp only [Option.map, ReborrowMapEntry.toAllocMapEntry]
              exact SameAllocSkeleton.of_tree_maps treeMap
                (derefReadMapFn (treeMap.map ReborrowMapEntry.toAllocMapEntry) e.localIdx ptrVal.tag)
                (fun x => derefReadMapFn_tag _ _ _ x)
                (fun x => derefReadMapFn_localIdx _ _ _ x)
                (fun x => derefReadMapFn_allocId _ _ _ x)
                (derefReadMapFnTree treeMap e.localIdx ptrVal.tag)
                (fun x => derefReadMapFnTree_tag _ _ _ x)
                (fun x => derefReadMapFnTree_localIdx _ _ _ x)
                (fun x => derefReadMapFnTree_allocId _ _ _ x)
          · simp [hsz]; exact .refl _
  obtain ⟨himm_d, himm_r⟩ := himm tf hframes
  obtain ⟨slot_r, mls_r, _, _, hslot_r, hmls_r, _, hloc_r⟩ := hfr.lookup_local hdecl_ref
  obtain ⟨slot_d, _, hlt_af_d, _, hslot_d, _, _, _⟩ := hfr.lookup_local hdecl_dst
  have hslot_r_s : get? s.frame.locals refIdx = some slot_r := hslot_r
  have hslot_d_s : get? s.frame.locals dstIdx = some slot_d := hslot_d
  have hlt_af_d_s : dstIdx < s.frame.locals.length := hlt_af_d
  have hcaller_s : s.memory.callerLocals = .nil := hcaller_e
  have hfe : s_e.frame = s.frame := rfl
  have hs_step := stepMirFn_eq_of_not_other body s hcal hphase
  have he_step := stepMirFn_eq_of_not_other body s_e hcal_e hphase
  simp only [hbb, hstmt] at hs_step
  simp only [hfe, hbb, hstmt] at he_step
  generalize hm_res :
    Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = mRes at hsim ⊢
  change StepRelLM3_2 body m _ (stepMirFn body s_e) mRes at hsim
  rcases hloc_r.ref_immediate_cases href_ty (himm_r mls_r hmls_r) with
    ⟨hsr, _⟩ | ⟨hsr, _⟩ | ⟨_, _, hsr, _⟩ | ⟨ptrVal, _, hsr, hptrRel, _⟩
  · have ha_s : stepMirFn body s = .fail .ub := by
      rw [hs_step]; rcases hopKind with rfl | rfl <;>
      · unfold evalStmt evalRvalue evalOperand; dsimp only []
        cases body.localDecls <;> simp only [hslot_r_s, hsr]
    have ha_e : stepMirFn body s_e = .fail .ub := by
      rw [he_step]; rcases hopKind with rfl | rfl <;>
      · unfold evalStmt; rw [hfe]; unfold evalRvalue evalOperand; dsimp only []
        cases body.localDecls <;> simp only [hslot_r_s, hsr]
    rw [ha_e] at hsim; rw [ha_s]
    cases hsim with | ub m' msg => exact .ub _ m' msg
  · have ha_s : stepMirFn body s = .fail .ub := by
      rw [hs_step]; rcases hopKind with rfl | rfl <;>
      · unfold evalStmt evalRvalue evalOperand; dsimp only []
        cases body.localDecls <;> simp only [hslot_r_s, hsr]
    have ha_e : stepMirFn body s_e = .fail .ub := by
      rw [he_step]; rcases hopKind with rfl | rfl <;>
      · unfold evalStmt; rw [hfe]; unfold evalRvalue evalOperand; dsimp only []
        cases body.localDecls <;> simp only [hslot_r_s, hsr]
    rw [ha_e] at hsim; rw [ha_s]
    cases hsim with | ub m' msg => exact .ub _ m' msg
  · have ha_s : stepMirFn body s = .fail .ub := by
      rw [hs_step]; rcases hopKind with rfl | rfl <;>
      · unfold evalStmt evalRvalue evalOperand; dsimp only []
        cases body.localDecls <;> simp only [hslot_r_s, hsr]
    have ha_e : stepMirFn body s_e = .fail .ub := by
      rw [he_step]; rcases hopKind with rfl | rfl <;>
      · unfold evalStmt; rw [hfe]; unfold evalRvalue evalOperand; dsimp only []
        cases body.localDecls <;> simp only [hslot_r_s, hsr]
    rw [ha_e] at hsim; rw [ha_s]
    cases hsim with | ub m' msg => exact .ub _ m' msg
  · have hsr_full : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) :=
      hslot_r_s.trans (congrArg some hsr)
    have hop_eq :
        evalOperand s.frame.locals (opKind ⟨refIdx, .cons .deref .nil⟩)
          s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals body.localDecls =
        evalOperand s.frame.locals (opKind ⟨refIdx, .cons .deref .nil⟩)
          s_e.memory.borrows s_e.memory.globals body.layouts s_e.memory.callerLocals
          body.localDecls := by
      dsimp only [s_e, eraseBorrowParents]
      rw [hbor_s]
      exact evalOperand_deref_ptr_treeMap_eq hopKind hsr_full treeMap s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls
    obtain ⟨_, _, _, _, _, _, ⟨e_am, he_am, htag_am, _⟩⟩ := hptrRel
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp he_am
    cases hop_res : evalOperand s.frame.locals (opKind ⟨refIdx, .cons .deref .nil⟩)
        s_e.memory.borrows s_e.memory.globals body.layouts s_e.memory.callerLocals
        body.localDecls with
    | ub =>
      have hop_s : evalOperand s.frame.locals (opKind ⟨refIdx, .cons .deref .nil⟩)
          s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals body.localDecls =
          .ub :=
        hop_eq.trans hop_res
      have ha_s : stepMirFn body s = .fail .ub := by
        rw [hs_step]; unfold evalStmt evalRvalue; dsimp only []; rw [hop_s]
      have ha_e : stepMirFn body s_e = .fail .ub := by
        rw [he_step]; unfold evalStmt; rw [hfe]; unfold evalRvalue; dsimp only []; rw [hop_res]
      rw [ha_e] at hsim; rw [ha_s]
      cases hsim with | ub m' msg => exact .ub _ m' msg
    | unsupported =>
      have ha_e : stepMirFn body s_e = .unsupported := by
        rw [he_step]; unfold evalStmt; rw [hfe]; unfold evalRvalue; dsimp only []; rw [hop_res]
      rw [ha_e] at hsim; cases hsim
    | ok val locals₁ =>
      have hop_s : evalOperand s.frame.locals (opKind ⟨refIdx, .cons .deref .nil⟩)
          s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals body.localDecls =
          .ok val locals₁ :=
        hop_eq.trans hop_res
      have hlb_e : lookupBorrow s_e.memory.borrows ptrVal.tag =
          some e.toAllocMapEntry.toBorrowEntry := by
        have h := (halloc_e.borrow_sync e.toAllocMapEntry he_am).2
        dsimp only [AllocMapEntry.toBorrowEntry] at h ⊢
        rw [htag_am] at h ⊢
        exact h
      have hloc₁_eq : locals₁ = s.frame.locals := by
        rcases hopKind with rfl | rfl <;>
        · unfold evalOperand at hop_res
          cases hld : body.localDecls <;> rw [hld] at hop_res
          · rw [hld] at hdecl_ref; cases hdecl_ref
          · dsimp only [] at hop_res
            rw [hsr_full] at hop_res; dsimp only [] at hop_res
            rw [hlb_e] at hop_res
            dsimp only [ReborrowMapEntry.toAllocMapEntry, AllocMapEntry.toBorrowEntry] at hop_res
            cases hbp : e.perm <;> (rw [hbp] at hop_res; try cases hop_res) <;>
            · dsimp only [] at hop_res
              cases hgt : get? s.frame.locals e.localIdx with
              | none =>
                rw [hgt, hcaller_e] at hop_res
                simp [get?] at hop_res
              | some tslot =>
                rw [hgt] at hop_res
                cases tslot with
                | dead => cases hop_res
                | uninit => cases hop_res
                | init rootVal =>
                  exact evalStackThinPtrTypedDerefRead_locals_eq hop_res
      subst hloc₁_eq
      have hperm_e : e.perm ≠ .disabled := by
        intro hdis
        rcases hopKind with rfl | rfl <;>
        · unfold evalOperand at hop_res
          cases hld : body.localDecls <;> rw [hld] at hop_res <;>
          · dsimp only [] at hop_res
            rw [hsr_full] at hop_res; dsimp only [] at hop_res
            rw [hlb_e] at hop_res
            dsimp only [ReborrowMapEntry.toAllocMapEntry, AllocMapEntry.toBorrowEntry] at hop_res
            rw [hdis] at hop_res
            cases hop_res
      cases hval_load :
          validateLoadedValue body.layouts body.localDecls
            (opKind ⟨refIdx, .cons .deref .nil⟩) val with
      | false =>
        have ha_s : stepMirFn body s = .fail .ub := by
          rw [hs_step]; unfold evalStmt evalRvalue; dsimp only []
          rw [hop_s]; dsimp only []; rw [hval_load]
        have ha_e : stepMirFn body s_e = .fail .ub := by
          rw [he_step]; unfold evalStmt; rw [hfe]; unfold evalRvalue; dsimp only []
          rw [hop_res]; dsimp only []; rw [hval_load]
        rw [ha_e] at hsim; rw [ha_s]
        cases hsim with | ub m' msg => exact .ub _ m' msg
      | true =>
        have hub_e : derefReadTreeUB s.frame.locals refIdx .nil s_e.memory.borrows
            s_e.memory.activeProtectors = false := by
          rw [hprot_e, hbor_e]
          exact derefReadTreeUB_map_toBorrowEntry_eq_false _ am halloc_e.tags_nodup refIdx ptrVal
            8 e.toAllocMapEntry he_am htag_am hsr_full hperm_e
        have hrv_s :
            evalRvalue s.frame.locals (.use (opKind ⟨refIdx, .cons .deref .nil⟩))
              s.memory body.localDecls body.layouts =
            .ok val s.frame.locals
              { s.memory with borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry } := by
          have hfrz := freezeDerefRead_treeMap_eq s.frame.locals treeMap hnodup_tm
            refIdx ptrVal he htag_am hsr_full
          have hub_s := derefReadTreeUB_treeMap_eq_false s.frame.locals treeMap hnodup_tm refIdx
            ptrVal he htag_am hsr_full hperm_e
            (by rw [← hbor_s]; exact hanc_read ptrVal hsr_full e he htag_am)
          unfold evalRvalue; dsimp only []; rw [hop_s]; dsimp only []; rw [hval_load]
          rcases hopKind with rfl | rfl <;>
          · rw [hbor_s]
            cases hbm : treeMap.map ReborrowMapEntry.toBorrowEntry with
            | nil =>
              exact False.elim (List.not_mem_nil (hbm ▸ List.mem_map_of_mem he))
            | cons b₁ rest =>
              cases rest with
              | nil =>
                rw [hbm] at hfrz; dsimp only [] at hfrz ⊢
                rw [← hfrz, ← hbm, ← hbor_s]
              | cons b₂ rest₂ =>
                rw [hbm] at hfrz hub_s; dsimp only [] at hfrz ⊢
                rw [hprot]
                simp only [hub_s]
                rw [hfrz]
        by_cases hsd_dead : slot_d = .dead
        · have ha_s : stepMirFn body s = .fail .ub := by
            rw [hs_step]; unfold evalStmt; dsimp only []; rw [hrv_s]; dsimp only []
            rw [hslot_d_s, hsd_dead]
          have ha_e : stepMirFn body s_e = .fail .ub := by
            rw [he_step]; unfold evalStmt; rw [hfe]; unfold evalRvalue; dsimp only []
            rw [hop_res]; dsimp only []; rw [hval_load]
            rcases hopKind with rfl | rfl <;>
            · cases hb : s_e.memory.borrows with
              | nil => dsimp only []; rw [hslot_d_s, hsd_dead]
              | cons _ r =>
                cases r with
                | nil => dsimp only []; rw [hslot_d_s, hsd_dead]
                | cons _ _ =>
                  rw [hb] at hub_e
                  dsimp only []
                  simp only [hub_e]
                  rw [hslot_d_s, hsd_dead]
          rw [ha_e] at hsim; rw [ha_s]
          cases hsim with | ub m' msg => exact .ub _ m' msg
        · have hnot_dst_am : ∀ x ∈ am, x.localIdx ≠ dstIdx :=
            htree.erased_rel.immediate_not_in_allocMap hframes hslot_d hsd_dead himm_d
          have hnot_dst_tm' : ∀ x ∈ treeMap', x.localIdx ≠ dstIdx := by
            intro x hx
            have hx_am : x.toAllocMapEntry ∈ treeMap'.map ReborrowMapEntry.toAllocMapEntry :=
              List.mem_map_of_mem hx
            obtain ⟨a, ha, _, hl, _⟩ := hskel.symm.mem_left hx_am
            have ha_orig : ∃ a₀ ∈ am, a.localIdx = a₀.localIdx := by
              dsimp only [derefReadNextAllocMap] at ha
              simp only [hsr_full] at ha
              cases hlk : lookupAllocMapByTag am ptrVal.tag <;> simp only [hlk] at ha
              · exact ⟨a, ha, rfl⟩
              · obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
                exact ⟨a₀, ha₀, derefReadMapFn_localIdx ..⟩
            obtain ⟨a₀, ha₀, hl₀⟩ := ha_orig
            intro hd
            exact hnot_dst_am a₀ ha₀ (hl₀.symm.trans (hl.symm.trans hd))
          have hinv_s := invalidateConflictingBorrows_treeMap_eq_of_not_mem treeMap' dstIdx hnot_dst_tm'
          have ha_s :
              stepMirFn body s =
                .step (advanceStmt s (s.frame.locals.set dstIdx (.init val))
                  { s.memory with borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry }) := by
            rw [hs_step]; unfold evalStmt; dsimp only []; rw [hrv_s]; dsimp only []
            rw [hslot_d_s]
            cases slot_d with
            | dead => exact absurd rfl hsd_dead
            | uninit => simp only [set?_eq_some_set hlt_af_d_s, hprot, hinv_s]
            | init _ => simp only [set?_eq_some_set hlt_af_d_s, hprot, hinv_s]
          have hprot_se : s_e.memory.activeProtectors = .nil := hprot_e
          have hex_be : ∃ b_e,
              stepMirFn body s_e =
                .step (advanceStmt s_e (s.frame.locals.set dstIdx (.init val))
                  { s_e.memory with borrows := b_e }) := by
            rw [he_step]; unfold evalStmt; rw [hfe]; unfold evalRvalue; dsimp only []
            rw [hop_res]; dsimp only []; rw [hval_load]
            rcases hopKind with rfl | rfl <;>
            · cases hb : s_e.memory.borrows with
              | nil =>
                dsimp only []; rw [hslot_d_s]
                cases slot_d with
                | dead => exact absurd rfl hsd_dead
                | uninit => simp only [set?_eq_some_set hlt_af_d_s, hprot_se]; exact ⟨_, rfl⟩
                | init _ => simp only [set?_eq_some_set hlt_af_d_s, hprot_se]; exact ⟨_, rfl⟩
              | cons _ r =>
                cases r with
                | nil =>
                  dsimp only []; rw [hslot_d_s]
                  cases slot_d with
                  | dead => exact absurd rfl hsd_dead
                  | uninit => simp only [set?_eq_some_set hlt_af_d_s, hprot_se]; exact ⟨_, rfl⟩
                  | init _ => simp only [set?_eq_some_set hlt_af_d_s, hprot_se]; exact ⟨_, rfl⟩
                | cons _ _ =>
                  rw [hb] at hub_e
                  dsimp only []
                  simp only [hub_e]
                  rw [hslot_d_s]
                  cases slot_d with
                  | dead => exact absurd rfl hsd_dead
                  | uninit => simp only [set?_eq_some_set hlt_af_d_s, hprot_se]; exact ⟨_, rfl⟩
                  | init _ => simp only [set?_eq_some_set hlt_af_d_s, hprot_se]; exact ⟨_, rfl⟩
          obtain ⟨b_e, ha_e⟩ := hex_be
          rw [ha_e] at hsim; rw [ha_s]
          cases hsim with
          | step s'_e m' hrel_e =>
            have hs_eq :
                advanceStmt s (s.frame.locals.set dstIdx (.init val))
                  { s.memory with borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry } =
                { advanceStmt s_e (s.frame.locals.set dstIdx (.init val))
                    { s_e.memory with borrows := b_e } with
                  memory :=
                    { (advanceStmt s_e (s.frame.locals.set dstIdx (.init val))
                        { s_e.memory with borrows := b_e }).memory with
                      borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry } } := by
              dsimp only [s_e, eraseBorrowParents, advanceStmt]
            rw [hs_eq]
            exact .step _ _ treeMap' (StateRelLM3_2Tree.of_erased_skeleton hrel_e hskel)

theorem step_safeRef_deref_write_tree_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : Operand} {span : String}
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl : LocalDecl} {mutability : Trusted.Rustc.V2026_06_01.MirAst.Mutability}
    {pointeeKind : RigidTy} {valTy : Ty}
    (hdecl_ref : Trusted.Sequence.get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hval_prim : IsPrimScalarTy valTy)
    (hval_kind : valTy.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal e tgtDecl,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      Trusted.Sequence.get? body.localDecls e.localIdx = some tgtDecl →
      Trusted.Sequence.get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
        tgtDecl.ty.kind = pointeeKind)
    (hanc_write : ∀ ptrVal e,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      treeBorrowAncestorsChildAccessUB .write s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts := by exact ⟨rfl, fun _ _ h => nomatch h⟩) :
    StepRelLM3_2Tree body m (derefWriteNextTreeMap s.frame.locals treeMap refIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  let s_e := eraseBorrowParents s treeMap
  let am := treeMap.map ReborrowMapEntry.toAllocMapEntry
  let treeMap' := derefWriteNextTreeMap s.frame.locals treeMap refIdx
  have hsim := step_safeRef_deref_write_simulation_explicit htree.erased_rel hphase hbb hstmt
    hdecl_ref href_ty hval_prim hval_kind hop himm_ref (by
      intro ptrVal e' tgtDecl hget he' htag' hdecl_t hdead
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      exact hlive_ref ptrVal e tgtDecl hget he htag' hdecl_t hdead) hlay_coh
  obtain ⟨tf, hframes, _, _, hfr, hcal_e, _, hprot_e, hcaller_e, hbor_e, halloc_e, _⟩ :=
    id htree.erased_rel
  have hcal : s.memory.activeCallee = none := hcal_e
  have hprot : s.memory.activeProtectors = .nil := hprot_e
  have hcaller : s.memory.callerLocals = .nil := hcaller_e
  have hbor_s : s.memory.borrows = treeMap.map ReborrowMapEntry.toBorrowEntry := htree.borrows_eq
  have hnodup_tm : (treeMap.map ReborrowMapEntry.tag).Nodup := by
    have htags : am.map AllocMapEntry.tag = treeMap.map ReborrowMapEntry.tag := by
      dsimp only [am]; rw [List.map_map]; rfl
    rw [← htags]; exact halloc_e.tags_nodup
  have hskel : SameAllocSkeleton (derefWriteNextAllocMap s.frame.locals am refIdx)
      (treeMap'.map ReborrowMapEntry.toAllocMapEntry) := by
    dsimp only [derefWriteNextAllocMap, derefWriteNextTreeMap, am, treeMap']
    cases hgr : get? s.frame.locals refIdx with
    | none => exact .refl _
    | some slot =>
      cases slot with
      | dead => exact .refl _
      | uninit => exact .refl _
      | init val =>
        cases val with
        | unit => exact .refl _
        | scalar _ => exact .refl _
        | aggregate _ _ => exact .refl _
        | ptr ptrVal sz =>
          by_cases hsz : sz = 8
          · subst hsz
            simp only [lookupAllocMapByTag_map_toAllocMapEntry]
            cases lookupTreeMapByTag treeMap ptrVal.tag with
            | none => exact .refl _
            | some e =>
              dsimp only [Option.map, ReborrowMapEntry.toAllocMapEntry, updateAllocMapOnWrite]
              exact SameAllocSkeleton.of_tree_maps treeMap
                (fun x => x.updateOnWrite e.localIdx (some ptrVal.tag))
                (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                (ReborrowMapEntry.updateOnWrite (treeMap.map ReborrowMapEntry.toBorrowEntry)
                  e.localIdx ptrVal.tag)
                (fun x => ReborrowMapEntry.updateOnWrite_tag _ _ _ x)
                (fun x => ReborrowMapEntry.updateOnWrite_localIdx _ _ _ x)
                (fun x => ReborrowMapEntry.updateOnWrite_allocId _ _ _ x)
          · simp [hsz]; exact .refl _
  have hop_tf := hop tf hframes
  have hfe : s_e.frame = s.frame := rfl
  have hs_step := stepMirFn_eq_of_not_other body s hcal hphase
  have he_step := stepMirFn_eq_of_not_other body s_e hcal_e hphase
  simp only [hbb, hstmt] at hs_step
  simp only [hfe, hbb, hstmt] at he_step
  generalize hm_res :
    Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = mRes at hsim ⊢
  change StepRelLM3_2 body m _ (stepMirFn body s_e) mRes at hsim
  have hop_eq :
      evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals =
      evalOperand s.frame.locals op s_e.memory.borrows s_e.memory.globals body.layouts
        s_e.memory.callerLocals :=
    evalOperand_scalarOperand_borrows_eq hop_tf s.frame.locals s.memory.borrows
      s_e.memory.borrows s.memory.globals s.memory.callerLocals
  have hrv_s := evalRvalue_use_scalarOperand_eq_lm3_2 htree.erased_rel hframes hop_tf s.memory
  have hrv_e := evalRvalue_use_scalarOperand_eq_lm3_2 htree.erased_rel hframes hop_tf s_e.memory
  rw [hfe] at hrv_s hrv_e
  cases hop_res : evalOperand s.frame.locals op s_e.memory.borrows s_e.memory.globals
      body.layouts s_e.memory.callerLocals with
  | ub =>
    have ha_s : stepMirFn body s = .fail .ub := by
      rw [hs_step]; unfold evalStmt; dsimp only []; rw [hrv_s, hop_eq.trans hop_res]
    have ha_e : stepMirFn body s_e = .fail .ub := by
      rw [he_step]; unfold evalStmt; rw [hfe]; dsimp only []; rw [hrv_e, hop_res]
    rw [ha_e] at hsim; rw [ha_s]
    cases hsim with | ub m' msg => exact .ub _ m' msg
  | unsupported =>
    have ha_e : stepMirFn body s_e = .unsupported := by
      rw [he_step]; unfold evalStmt; rw [hfe]; dsimp only []; rw [hrv_e, hop_res]
    rw [ha_e] at hsim; cases hsim
  | ok val locals₁ =>
    have hloc₁_eq : locals₁ = s.frame.locals := by
      cases hop_tf with
      | constScalar c sc hcv _ _ _ _ _ _ =>
        unfold evalOperand at hop_res; dsimp only [] at hop_res
        rw [hcv] at hop_res; injection hop_res with _ hl; exact hl.symm
      | copyLocal idx _ _ _ _ =>
        unfold evalOperand at hop_res; dsimp only [] at hop_res
        cases hgi : get? s.frame.locals idx with
        | none => rw [hgi] at hop_res; cases hop_res
        | some sl =>
          rw [hgi] at hop_res
          cases sl with
          | dead => cases hop_res
          | uninit => cases hop_res
          | init _ =>
            simp only [readProjectedValue] at hop_res
            injection hop_res with _ hl; exact hl.symm
    subst hloc₁_eq
    obtain ⟨slot_r, mls_r, _, _, hslot_r, hmls_r, _, hloc_r⟩ := hfr.lookup_local hdecl_ref
    have hslot_r_s : get? s.frame.locals refIdx = some slot_r := hslot_r
    rcases hloc_r.ref_immediate_cases href_ty ((himm_ref tf hframes) mls_r hmls_r) with
      ⟨hsr, _⟩ | ⟨hsr, _⟩ | ⟨_, _, hsr, _⟩ | ⟨ptrVal, _, hsr, hptrRel, _⟩
    · have ha_s : stepMirFn body s = .fail .ub := by
        rw [hs_step]; unfold evalStmt; dsimp only []
        rw [hrv_s, hop_eq.trans hop_res]; dsimp only [evalPlaceWrite]
        rw [hprot, hcaller]; unfold writePlaceValue; dsimp only []
        cases body.localDecls <;> simp only [hslot_r_s, hsr]
      have ha_e : stepMirFn body s_e = .fail .ub := by
        rw [he_step]; unfold evalStmt; rw [hfe]; dsimp only []
        rw [hrv_e, hop_res]; dsimp only [evalPlaceWrite]
        rw [hprot_e, hcaller_e]; unfold writePlaceValue; dsimp only []
        cases body.localDecls <;> simp only [hslot_r_s, hsr]
      rw [ha_e] at hsim; rw [ha_s]
      cases hsim with | ub m' msg => exact .ub _ m' msg
    · have ha_s : stepMirFn body s = .fail .ub := by
        rw [hs_step]; unfold evalStmt; dsimp only []
        rw [hrv_s, hop_eq.trans hop_res]; dsimp only [evalPlaceWrite]
        rw [hprot, hcaller]; unfold writePlaceValue; dsimp only []
        cases body.localDecls <;> simp only [hslot_r_s, hsr]
      have ha_e : stepMirFn body s_e = .fail .ub := by
        rw [he_step]; unfold evalStmt; rw [hfe]; dsimp only []
        rw [hrv_e, hop_res]; dsimp only [evalPlaceWrite]
        rw [hprot_e, hcaller_e]; unfold writePlaceValue; dsimp only []
        cases body.localDecls <;> simp only [hslot_r_s, hsr]
      rw [ha_e] at hsim; rw [ha_s]
      cases hsim with | ub m' msg => exact .ub _ m' msg
    · have ha_s : stepMirFn body s = .fail .ub := by
        rw [hs_step]; unfold evalStmt; dsimp only []
        rw [hrv_s, hop_eq.trans hop_res]; dsimp only [evalPlaceWrite]
        rw [hprot, hcaller]; unfold writePlaceValue; dsimp only []
        cases body.localDecls <;> simp only [hslot_r_s, hsr]
      have ha_e : stepMirFn body s_e = .fail .ub := by
        rw [he_step]; unfold evalStmt; rw [hfe]; dsimp only []
        rw [hrv_e, hop_res]; dsimp only [evalPlaceWrite]
        rw [hprot_e, hcaller_e]; unfold writePlaceValue; dsimp only []
        cases body.localDecls <;> simp only [hslot_r_s, hsr]
      rw [ha_e] at hsim; rw [ha_s]
      cases hsim with | ub m' msg => exact .ub _ m' msg
    · have hsr_full : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) :=
        hslot_r_s.trans (congrArg some hsr)
      have hwp_eq :
          writePlaceValue s.frame.locals s.memory.borrows ⟨refIdx, .cons .deref .nil⟩ val
            body.localDecls body.layouts =
          writePlaceValue s.frame.locals s_e.memory.borrows ⟨refIdx, .cons .deref .nil⟩ val
            body.localDecls body.layouts := by
        dsimp only [s_e, eraseBorrowParents]; rw [hbor_s]
        exact writePlaceValue_deref_ptr_treeMap_eq hsr_full treeMap val body.localDecls body.layouts
      cases hwp_res : writePlaceValue s.frame.locals s_e.memory.borrows ⟨refIdx, .cons .deref .nil⟩ val
          body.localDecls body.layouts with
      | ub =>
        have ha_s : stepMirFn body s = .fail .ub := by
          rw [hs_step]; unfold evalStmt; dsimp only []
          rw [hrv_s, hop_eq.trans hop_res]; dsimp only [evalPlaceWrite]
          rw [hprot]; dsimp only []; rw [hwp_eq.trans hwp_res, hcaller]
        have ha_e : stepMirFn body s_e = .fail .ub := by
          rw [he_step]; unfold evalStmt; rw [hfe]; dsimp only []
          rw [hrv_e, hop_res]; dsimp only [evalPlaceWrite]
          rw [hprot_e]; dsimp only []; rw [hwp_res, hcaller_e]
        rw [ha_e] at hsim; rw [ha_s]
        cases hsim with | ub m' msg => exact .ub _ m' msg
      | unsupported =>
        have ha_e : stepMirFn body s_e = .unsupported := by
          rw [he_step]; unfold evalStmt; rw [hfe]; dsimp only []
          rw [hrv_e, hop_res]; dsimp only [evalPlaceWrite]
          rw [hprot_e]; dsimp only []; rw [hwp_res]
        rw [ha_e] at hsim; cases hsim
      | ok locals₂ =>
        obtain ⟨_, _, _, _, _, _, ⟨e_am, he_am, htag_am, _⟩⟩ := hptrRel
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp he_am
        have hinv_s := invalidateDerefWriteBorrows_map_toBorrowEntry_tree
          s.frame.locals treeMap hnodup_tm refIdx ptrVal he htag_am hsr_full
        rw [← hbor_s] at hinv_s
        have hwub_s : derefWriteTreeUB s.frame.locals s.memory.borrows
            ⟨refIdx, .cons .deref .nil⟩ = false := by
          rw [hbor_s]
          exact derefWriteTreeUB_treeMap_eq_false s.frame.locals treeMap hnodup_tm refIdx ptrVal
            he htag_am hsr_full (by rw [← hbor_s]; exact hanc_write ptrVal e hsr_full he htag_am)
        have hwub_e : derefWriteTreeUB s.frame.locals s_e.memory.borrows
            ⟨refIdx, .cons .deref .nil⟩ = false := by
          rw [hbor_e]
          exact derefWriteTreeUB_map_toBorrowEntry_eq_false _ _ _
        have ha_s :
            stepMirFn body s =
              .step (advanceStmt s locals₂
                { s.memory with borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry }) := by
          rw [hs_step]; unfold evalStmt; dsimp only []
          rw [hrv_s, hop_eq.trans hop_res]; dsimp only [evalPlaceWrite]
          rw [hprot]; dsimp only []; rw [hwp_eq.trans hwp_res]
          simp only [hwub_s, hcaller]
          rw [hinv_s]
        have ha_e :
            stepMirFn body s_e =
              .step (advanceStmt s_e locals₂
                { s_e.memory with
                  borrows := invalidateDerefWriteBorrows s.frame.locals s_e.memory.borrows
                    ⟨refIdx, .cons .deref .nil⟩ .nil }) := by
          rw [he_step]; unfold evalStmt; rw [hfe]; dsimp only []
          rw [hrv_e, hop_res]; dsimp only [evalPlaceWrite]
          rw [hprot_e]; dsimp only []; rw [hwp_res]
          simp only [hwub_e]
        rw [ha_e] at hsim; rw [ha_s]
        cases hsim with
        | step s'_e m' hrel_e =>
          have hs_eq :
              advanceStmt s locals₂
                { s.memory with borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry } =
              { advanceStmt s_e locals₂
                  { s_e.memory with
                    borrows := invalidateDerefWriteBorrows s_e.frame.locals s_e.memory.borrows
                      ⟨refIdx, .cons .deref .nil⟩ .nil } with
                memory :=
                  { (advanceStmt s_e locals₂
                      { s_e.memory with
                        borrows := invalidateDerefWriteBorrows s_e.frame.locals s_e.memory.borrows
                          ⟨refIdx, .cons .deref .nil⟩ .nil }).memory with
                    borrows := treeMap'.map ReborrowMapEntry.toBorrowEntry } } := by
            dsimp only [s_e, eraseBorrowParents, advanceStmt]
          rw [hs_eq]
          exact .step _ _ treeMap' (StateRelLM3_2Tree.of_erased_skeleton hrel_e hskel)

theorem step_terminator_goto_return_tree_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : Trusted.Sequence.get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = bb.statements.length)
    (hwt_term : WellTypedLM3_2StateTerminator body m bb)
    (hgoto_ret : (∃ target, bb.terminator.kind = .goto target) ∨ bb.terminator.kind = .return_ ∨ bb.terminator.kind = .unreachable) :
    StepRelLM3_2Tree body m treeMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  have ⟨hcleanup, hret_decl0⟩ : bb.isCleanup = false ∧ (bb.terminator.kind = .return_ → ∃ d, get? body.localDecls 0 = some d ∧
          (translateTy d.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO ∧
          ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 0) := by
    rcases hgoto_ret with ⟨target, hgoto⟩ | hret | hunreach
    · cases hwt_term
      · exact ⟨by assumption, fun h => by rw [hgoto] at h; contradiction⟩
      · rw [hgoto] at *; contradiction
      · rw [hgoto] at *; contradiction
      · rw [hgoto] at *; contradiction
      · rw [hgoto] at *; contradiction
    · cases hwt_term
      · rw [hret] at *; contradiction
      · refine ⟨by assumption, fun _ => ⟨_, by assumption, by assumption, by assumption⟩⟩
      · rw [hret] at *; contradiction
      · rw [hret] at *; contradiction
      · rw [hret] at *; contradiction
    · cases hwt_term
      · rw [hunreach] at *; contradiction
      · rw [hunreach] at *; contradiction
      · exact ⟨by assumption, fun h => by rw [hunreach] at h; contradiction⟩
      · rw [hunreach] at *; contradiction
      · rw [hunreach] at *; contradiction
  rcases htree.erased_rel with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hprot, hcaller, hbor, halloc, hd_tf⟩
  have hcal' : s.memory.activeCallee = none := hcal
  have hstack' : s.memory.callStack = [] := hstack
  rw [stepMirFn_eq_of_not_other body s hcal' hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
    simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  rcases hgoto_ret with ⟨target, hgoto⟩ | hret | hunreach
  · unfold evalTerminator translateTerminator
      Miri.Interpreter.ControlFlow.evalTerminator
      Miri.Interpreter.ControlFlow.goToBlock
      Miri.Interpreter.ControlFlow.setLocation
    rw [hgoto, stack_currentFrame?_singleton m.stack topFrame hframes, hframes]
    dsimp only [translateTerminatorKind, Except.map, Id.run]
    apply StepRelLM3_2Tree.step
    refine StateRelLM3_2Tree.mk (StateRelLM3_2.mk
      { topFrame with location := .mir ⟨target, 0⟩ }
      rfl hretCont ⟨retLay, hretPlace⟩
      ⟨hframe.body_eq, rfl, hframe.af_locals_len, hframe.mf_locals_size, hframe.locals_rel⟩
      hcal hstack hprot hcaller hbor ?_ hd_tf) htree.borrows_eq
    refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro tf' htf' e he
    injection htf' with h1; injection h1 with h2; subst tf'
    exact halloc.local_alloc_sync topFrame hframes e he
  · unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
    rw [hret, hstack', annealTerminatorHooks_toControlHooks]
    dsimp only [translateTerminatorKind, Id.run, Pure.pure]
    obtain ⟨decl0, hdecl0, hsz0, himm0⟩ := hret_decl0 hret
    obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, hloc0⟩ := hframe.lookup_local hdecl0
    have hslot0' : get? s.frame.locals 0 = some slot0 := hslot0
    rw [hslot0']
    have hget0 := frame_getLocal_of_getElem? topFrame 0 mls0 hmls0
    have himm0' := himm0 topFrame hframes mls0 hmls0
    cases hloc0 with
    | ref ptrVal mptr _ mutability pk _ hty0 hptrRel =>
      have hop0 := annealControlHooks_returnOperand_scalar hframes hget0
      rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
        hframe.location_eq hbb hcleanup hretCont hop0
        (annealControlHooks_popFrame_singleton hframes)
        (annealControlHooks_copyReturn_empty _ hretPlace)
        (annealControlHooks_cleanupFrame_eq false topFrame _)]
      exact StepRelLM3_2Tree.retRoot treeMap decl0 (.ptr ptrVal 8)
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
        s.memory _ hdecl0 hop0 (.ref mutability pk ptrVal mptr hty0 hptrRel) rfl
    | lm3_1 hloc0_1 =>
      cases hloc0_1 with
      | rawPtr ptrVal mptr _ mutability pk _ hty0 hptrRel =>
        have hop0 := annealControlHooks_returnOperand_scalar hframes hget0
        rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
          hframe.location_eq hbb hcleanup hretCont hop0
          (annealControlHooks_popFrame_singleton hframes)
          (annealControlHooks_copyReturn_empty _ hretPlace)
          (annealControlHooks_cleanupFrame_eq false topFrame _)]
        exact StepRelLM3_2Tree.retRoot treeMap decl0 (.ptr ptrVal 8)
          (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          s.memory _ hdecl0 hop0 (.lm3_1 (.rawPtr mutability pk ptrVal mptr hty0 hptrRel)) rfl
      | base hbase0 =>
        cases hbase0 with
        | dead _ _ =>
          rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
            hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_dead hframes hget0)]
          exact StepRelLM3_2Tree.ub _ _ _
        | indirect _ mp _ _ _ _ =>
          exact False.elim (himm0' mp rfl)
        | immediate _ imm _ _ hval =>
          rcases hval with ⟨rfl, rfl⟩ | ⟨retVal, rfl, himmRel⟩
          · rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
              hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_uninit hframes hget0)]
            exact StepRelLM3_2Tree.ub _ _ _
          · cases himmRel with
            | unit hzero =>
              exact False.elim (hsz0 hzero)
            | scalar sc msc hsc hsz_sc hbool_sc hchar_sc =>
              have hop0 := annealControlHooks_returnOperand_scalar hframes hget0
              rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
                hframe.location_eq hbb hcleanup hretCont hop0
                (annealControlHooks_popFrame_singleton hframes)
                (annealControlHooks_copyReturn_empty _ hretPlace)
                (annealControlHooks_cleanupFrame_eq false topFrame _)]
              exact StepRelLM3_2Tree.retRoot treeMap decl0 _ _ s.memory _ hdecl0 hop0
                (.lm3_1 (.of_immediateRel (.scalar sc msc hsc hsz_sc hbool_sc hchar_sc))) rfl
            | scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair =>
              have hop0 := annealControlHooks_returnOperand_scalarPair hframes hget0
              rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
                hframe.location_eq hbb hcleanup hretCont hop0
                (annealControlHooks_popFrame_singleton hframes)
                (annealControlHooks_copyReturn_empty _ hretPlace)
                (annealControlHooks_cleanupFrame_eq false topFrame _)]
              exact StepRelLM3_2Tree.retRoot treeMap decl0 _ _ s.memory _ hdecl0 hop0
                (.lm3_1 (.of_immediateRel (.scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair))) rfl
  · unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
    rw [hunreach]
    dsimp only [translateTerminatorKind, Except.map, Id.run]
    exact StepRelLM3_2Tree.ub _ _ _

end LeanMiriSpec.Correspondence
