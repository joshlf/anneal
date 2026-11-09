/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Pointers

/-!
# Raw pointer and reference statements in both semantics (MR-3.1, MR-3.2)

The statement-level facts on which `step_correspondence_N` rests for the raw
pointer and safe reference statements that `inFragment` admits:

* Direct borrows `_i = &raw const q`, `_i = &raw mut q`, `_i = &q`, and
  `_i = &mut q` (`evalStmt_assign_rawPtr`, `evalStmt_assign_ref`,
  `evalStatement_assign_rawPtr_mr`, `evalStatement_assign_ref_mr`): Anneal
  pushes a fresh Tree Borrows entry (`Frozen` for shared `Freeze` targets,
  `Active` for mutable borrows) and stores its tag; MiniRust stores the address
  of `q`'s bytes, enforcing non-null, alignment, and dereferenceability for
  `PtrType::Ref`. `BorrowsOk.directBorrow` / `BorrowsOk.rawPtr` and
  `LocalsOk.rawPtr_extend` maintain the flow-sensitive borrow invariant.
* Reborrows `_i = &*_p`, `_i = &mut *_p`, `_i = &raw const *_p`, and
  `_i = &raw mut *_p` (`evalStmt_assign_rawPtr_reborrow`,
  `evalStmt_assign_ref_reborrow`, `evalStatement_assign_reborrow_mr`,
  `BorrowsOk.reborrow`).
* Tag-preserving copies `_i = copy _p` / `move _p` / `CopyForDeref(_p)`,
  `_i = PtrToPtr(copy _p)`, and `_i = Offset(copy _p, 0)`
  (`evalRvalue_ptrRvalue`, `evalStatement_assign_ptrRvalue_mr`,
  `BorrowsOk.ptrCopy`).
* Dereference reads `_i = copy (*_p)` / `move (*_p)` / `CopyForDeref(*_p)`
  (`evalRvalue_derefRead_eq`, `evalPlace_deref`).
* Dereference writes `(*_p) = rv` (`evalStmt_assign_derefWrite`,
  `derefWrite_target`, `BorrowsOk.derefWrite`), tracking Tree Borrows sibling/parent
  invalidation (`invalidateDerefWriteBorrows`) via the flow-sensitive CFG
  lattice `ptrAliasingOk`.
* Fragment-check inversions (`statementOk_rawPtr_spec`, `statementOk_ref_spec`,
  `statementOk_rawPtr_reborrow_spec`, `statementOk_ref_reborrow_spec`,
  `statementOk_derefRead`, `ptrTargetSpec_cases`).
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open Trusted.Sequence

/-! ## The borrow table -/

theorem lookupBorrow_cons_self (e : BorrowEntry) (rest : List BorrowEntry) :
    lookupBorrow (e :: rest) e.tag = some e := by
  simp [lookupBorrow, Nat.beq_refl]

theorem lookupBorrow_cons_ne (e : BorrowEntry) (rest : List BorrowEntry) (tag : Nat)
    (h : e.tag ≠ tag) : lookupBorrow (e :: rest) tag = lookupBorrow rest tag := by
  have hb : Nat.beq e.tag tag = false := by
    cases hb : Nat.beq e.tag tag with
    | false => rfl
    | true => exact absurd (Nat.beq_eq.mp hb) h
  simp only [lookupBorrow, hb]

theorem BorrowsOk.perm_eq {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    {e : BorrowEntry} (he : e ∈ s.memory.borrows) :
    ∃ mutbl, (e.perm = rawPtrPerm mutbl ∨ (mutbl = .mut ∧ e.perm = .reserved) ∨
      e.perm = .disabled) ∧ e.protector = none ∧ e.rangeOffset = 0 ∧ e.rangeLen = 0 := by
  obtain ⟨mutbl, _, _, heq | ⟨hm, heq⟩ | heq, _, _⟩ := hb.entries_ok e he
  · exact ⟨mutbl, .inl (congrArg BorrowEntry.perm heq),
      congrArg BorrowEntry.protector heq,
      congrArg BorrowEntry.rangeOffset heq, congrArg BorrowEntry.rangeLen heq⟩
  · exact ⟨mutbl, .inr (.inl ⟨hm, congrArg BorrowEntry.perm heq⟩),
      congrArg BorrowEntry.protector heq,
      congrArg BorrowEntry.rangeOffset heq, congrArg BorrowEntry.rangeLen heq⟩
  · exact ⟨mutbl, .inr (.inr (congrArg BorrowEntry.perm heq)),
      congrArg BorrowEntry.protector heq,
      congrArg BorrowEntry.rangeOffset heq, congrArg BorrowEntry.rangeLen heq⟩

theorem borrowEntry_form_of_unranged (e : BorrowEntry)
    (hprot : e.protector = none) (hroff : e.rangeOffset = 0) (hrlen : e.rangeLen = 0) :
    ∃ mutbl : MirAst.Mutability,
      e = { rawPtrEntry e.tag mutbl ⟨e.targetLocal, e.targetProjection⟩ with
            parentTag := e.parentTag } ∨
      (mutbl = .mut ∧ e = { rawPtrEntry e.tag .mut ⟨e.targetLocal, e.targetProjection⟩ with
                            perm := .reserved, parentTag := e.parentTag }) ∨
      e = { rawPtrEntry e.tag mutbl ⟨e.targetLocal, e.targetProjection⟩ with
            perm := .disabled, parentTag := e.parentTag } := by
  rcases e with ⟨tag, tloc, tproj, perm, prot, roff, rlen, ptag⟩
  dsimp only at hprot hroff hrlen ⊢
  subst hprot hroff hrlen
  cases perm with
  | active => exact ⟨.mut, .inl rfl⟩
  | frozen => exact ⟨.not, .inl rfl⟩
  | reserved => exact ⟨.mut, .inr (.inl ⟨rfl, rfl⟩)⟩
  | disabled => exact ⟨.mut, .inr (.inr rfl)⟩

/-- Updating local `i` to `slot'` and its abstract state to `st'` while extending
the borrow table monotonically on existing tags preserves `PtrEnvOk`. -/
theorem PtrEnvOk.setPtrLocal {body : CapturedMir} {view : List LocalSlot}
    {borrows borrows' : List BorrowEntry} {env : List PtrLocalState}
    (hok : PtrEnvOk body view borrows env)
    (hext_lk : ∀ tag e, lookupBorrow borrows tag = some e → lookupBorrow borrows' tag = some e)
    (i : Nat) (slot' : LocalSlot) (st' : PtrLocalState)
    (hi_ok : i < body.localDecls.length → PtrLocalOk body (view.set i slot') borrows' i st') :
    PtrEnvOk body (view.set i slot') borrows'
      (Correspondence.setPtrLocal body.localDecls.length env i st') := by
  intro p hp
  unfold Correspondence.setPtrLocal
  rw [getD_map_range _ _ _ hp]
  by_cases hpi : p = i
  · subst hpi
    simpa using hi_ok hp
  · have hb_pi : (p == i) = false := beq_false_of_ne hpi
    simp only [hb_pi, Bool.false_eq_true, ↓reduceIte]
    have hp_ok := hok p hp
    cases hst : env.getD p .disabled with
    | empty =>
      rw [hst] at hp_ok
      dsimp only [removePeerFromState, PtrLocalOk]
      intro dp pv hdp hpty hv
      rw [List.getElem?_set_ne (Ne.symm hpi)] at hv
      exact hp_ok dp pv hdp hpty hv
    | disabled =>
      trivial
    | live target peers =>
      rw [hst] at hp_ok
      dsimp only [removePeerFromState, PtrLocalOk]
      intro dp pv hdp hpty hv
      rw [List.getElem?_set_ne (Ne.symm hpi)] at hv
      obtain ⟨⟨entry, hlk, hndis, hnf, ht⟩, hpeers⟩ := hp_ok dp pv hdp hpty hv
      refine ⟨⟨entry, hext_lk pv.tag entry hlk, hndis, hnf, ht⟩, ?_⟩
      intro r hr dr pv_r hdr hptr hvr
      simp only [List.mem_filter, bne_iff_ne, ne_eq] at hr
      rw [List.getElem?_set_ne (Ne.symm hr.2)] at hvr
      exact hpeers r hr.1 dr pv_r hdr hptr hvr

/-- `BorrowsOk` after `StorageLive(_i)`, `StorageDead(_i)`, or `Deinit(_i)` on a
non-address-taken local `_i` (scalar or pointer/reference), under a locals map
that agrees with the old one on address-taken locals. -/
theorem BorrowsOk.advance_storage {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm lm' : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    {bb : BasicBlockData} {st : MirAst.Statement}
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    {locals' : List LocalSlot} (i : Nat) (slot' : LocalSlot)
    (hkind : st.kind = .storageLive i ∨ st.kind = .storageDead i ∨ st.kind = .deinit ⟨i, []⟩)
    (hi_addr : i ∉ bodyAddrTakenLocals body)
    (hnp : ∀ (dp : LocalDecl) (pv : ProvenancePtr),
      body.localDecls[i]? = some dp → isPtrTy dp.ty = true → slot' ≠ .init (.ptr pv 8))
    (hlm : ∀ k ∈ bodyAddrTakenLocals body, mapGet lm' (localName k) = mapGet lm (localName k)) :
    BorrowsOk body ctx (view.set i slot') (advanceStmt s locals' s.memory) lm' := by
  have hb0 := hb.with_lm hlm
  cases hptr : isDeclPtrLocal body.localDecls i with
  | false =>
    have hstep :
        let env := ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx
        ptrStmtStep body.localDecls env st =
          (List.range body.localDecls.length).map (fun q => env.getD q .disabled) := by
      rcases hkind with hk | hk | hk <;> simp [ptrStmtStep, hk, hptr]
    exact hb0.advance_set_nonptr hbb hst hstep i slot' (fun hk => absurd hk hi_addr) hnp
  | true =>
    have hstep :
        let env := ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx
        ptrStmtStep body.localDecls env st =
          setPtrLocal body.localDecls.length env i .empty := by
      rcases hkind with hk | hk | hk <;> simp [ptrStmtStep, hk, hptr]
    refine {
      tags_lt := hb0.tags_lt
      entries_ok := hb0.entries_ok
      target_ptrs := fun hfrag k hk => by
        obtain ⟨hnd, hlmk, hd⟩ := hb0.target_ptrs hfrag k hk
        refine ⟨?_, hlmk, hd⟩
        have hik : i ≠ k := fun h => hi_addr (h ▸ hk)
        rw [List.getElem?_set_ne hik]
        exact hnd
      alias_ok := by
        simp only [advanceStmt]
        rw [Nat.add_eq, ptrEnvBefore_succ hbb hst, hstep]
        refine hb0.alias_ok.setPtrLocal (fun _ _ h => h) i slot' .empty (fun _ dp pv hdp hpty hv => ?_)
        by_cases hlt : i < view.length
        · rw [List.getElem?_set_self hlt] at hv
          injection hv with hs
          exact hnp dp pv hdp hpty hs
        · rw [List.getElem?_eq_none (by simp; omega)] at hv
          cases hv
      ptr_slots := fun p dp mutbl pointeeIt ptrVal hdp hpt hv => by
        by_cases hip : i = p
        · subst hip
          have hp_ty : isPtrTy dp.ty = true := by simp [isPtrTy, hpt]
          by_cases hlt : i < view.length
          · rw [List.getElem?_set_self hlt] at hv
            injection hv with hs
            exact False.elim (hnp dp ptrVal hdp hp_ty hs)
          · rw [List.getElem?_eq_none (by simp; omega)] at hv
            cases hv
        · rw [List.getElem?_set_ne hip] at hv
          exact hb0.ptr_slots p dp mutbl pointeeIt ptrVal hdp hpt hv }

theorem borrowTargets_cons_ne (body : CapturedMir) (ctx : Ctx) (e : BorrowEntry)
    (borrows : List BorrowEntry) (tag : Nat) (h : e.tag ≠ tag) :
    borrowTargets body ctx (e :: borrows) tag = borrowTargets body ctx borrows tag := by
  unfold borrowTargets
  rw [lookupBorrow_cons_ne e borrows tag h]

theorem borrowTargets_rawPtr_self (body : CapturedMir) (ctx : Ctx) (tag : Nat)
    (mutbl : MirAst.Mutability) (q : Place) (borrows : List BorrowEntry)
    (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff)) :
    borrowTargets body ctx (rawPtrEntry tag mutbl q :: borrows) tag =
      some ((ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat,
        some (⟨((ctx.base.length + q.local_ : Nat) : Int)⟩, ())) := by
  have hl := lookupBorrow_cons_self (rawPtrEntry tag mutbl q) borrows
  simp only [rawPtrEntry] at hl
  obtain ⟨k, projs⟩ := q
  unfold borrowTargets
  simp only [rawPtrEntry] at hspec ⊢
  rw [hl]
  simp [hspec]

theorem ctxWithBorrows_refBorrowEntry_eq (body : CapturedMir) (ctx : Ctx) (tag : Nat)
    (bkind : MirAst.BorrowKind) (q : Place) (borrows : List BorrowEntry) :
    ctxWithBorrows body ctx (refBorrowEntry tag bkind q :: borrows) =
      ctxWithBorrows body ctx (rawPtrEntry tag (borrowKindMutbl bkind) q :: borrows) := by
  unfold ctxWithBorrows
  congr 1
  funext t
  unfold borrowTargets lookupBorrow refBorrowEntry rawPtrEntry
  cases Nat.beq tag t <;> rfl

/-- The pointer bytes of every initialized pointer local stay in sync after
`&raw` or `&` / `&mut` pushes an entry with a fresh tag. -/
theorem LocalsOk.rawPtr_extend {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hlo : LocalsOk body (ctxWithBorrows body ctx s.memory.borrows) view lm A)
    (hb : BorrowsOk body ctx view s lm) (e : BorrowEntry) (he : e.tag = s.memory.nextTag) :
    LocalsOk body (ctxWithBorrows body ctx (e :: s.memory.borrows)) view lm A := by
  refine LocalsOkA.extend_ptrTargets (ctx1 := ctxWithBorrows body ctx s.memory.borrows)
    (ctx2 := ctxWithBorrows body ctx (e :: s.memory.borrows)) rfl hlo ?_
  intro i d pv a pr hd hpty hv h2
  obtain ⟨⟨mutbl, pointeeIt⟩, hpt⟩ : ∃ r, ptrPointeeOf d.ty = some r := by
    unfold isPtrTy at hpty
    exact Option.isSome_iff_exists.mp hpty
  obtain ⟨entry, _, _, hlookup, _⟩ := hb.ptr_slots i d mutbl pointeeIt pv hd hpt hv
  obtain ⟨hmem, htag⟩ := lookupBorrow_mem_and_tag hlookup
  have hlt := hb.tags_lt entry hmem
  have hne : e.tag ≠ pv.allocId := by
    rw [he]
    have : entry.tag = pv.allocId := htag
    omega
  simp only [ctxWithBorrows] at h2 ⊢
  rw [borrowTargets_cons_ne body ctx e s.memory.borrows pv.allocId hne] at h2
  exact h2

/-- `BorrowsOk` after a direct borrow `_i = &raw mutbl q`, `_i = &q`,
`_i = &mut q`, or `_i = &two_phase mut q` pushed `entry` and stored its tag in `_i`. -/
theorem BorrowsOk.directBorrow {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    (hlen : view.length = body.localDecls.length)
    {bb : BasicBlockData} (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    {st : MirAst.Statement} (hst : bb.statements[s.frame.stmtIdx]? = some st)
    {i : Nat} {d : LocalDecl} (hdi : body.localDecls[i]? = some d)
    {rv : Rvalue} {mutbl : MirAst.Mutability} {q : Place}
    (hkind : st.kind = .assign ⟨i, []⟩ rv)
    (hdb : directBorrowOf rv = some (mutbl, q))
    (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    (hpt_i : ptrPointeeOf d.ty = some (mutbl, pointeeIt))
    (hi_addr : i ∉ bodyAddrTakenLocals body) (locals' : List LocalSlot)
    {entry : BorrowEntry}
    (hentry : entry = rawPtrEntry s.memory.nextTag mutbl q ∨
      (mutbl = .mut ∧ entry = { rawPtrEntry s.memory.nextTag .mut q with perm := .reserved })) :
    BorrowsOk body ctx (view.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8)))
      (advanceStmt s locals' { s.memory with
        borrows := entry :: s.memory.borrows,
        nextTag := s.memory.nextTag + 1 }) lm := by
  have hbbmem : bb ∈ body.basicBlocks := List.mem_of_getElem? hbb
  have hstmem : st ∈ bb.statements := List.mem_of_getElem? hst
  have hq_addr : q.local_ ∈ bodyAddrTakenLocals body :=
    mem_bodyAddrTakenLocals_of_directBorrow hbbmem hstmem hkind hdb
  obtain ⟨k, projs⟩ := q
  simp only at hq_addr
  have hentry_fields :
      entry.tag = s.memory.nextTag ∧ entry.targetLocal = k ∧
      entry.targetProjection = projs ∧ entry.perm ≠ .disabled := by
    rcases hentry with rfl | ⟨_, rfl⟩
    · refine ⟨rfl, rfl, rfl, by cases mutbl <;> simp [rawPtrEntry, rawPtrPerm]⟩
    · exact ⟨rfl, rfl, rfl, by simp⟩
  have hself_lk : lookupBorrow (entry :: s.memory.borrows) s.memory.nextTag = some entry := by
    have hl := lookupBorrow_cons_self entry s.memory.borrows
    rwa [hentry_fields.1] at hl
  have hfresh : ∀ e' ∈ s.memory.borrows, e'.tag ≠ s.memory.nextTag :=
    fun e' he' h => by have := hb.tags_lt e' he'; omega
  have hisPtr_i : isPtrTy d.ty = true := by simp [isPtrTy, hpt_i]
  have hdecl_ptr : isDeclPtrLocal body.localDecls i = true := by
    simp [isDeclPtrLocal, hdi, hisPtr_i]
  have hext_lk : ∀ tag e, lookupBorrow s.memory.borrows tag = some e →
      lookupBorrow (entry :: s.memory.borrows) tag = some e := by
    intro tag e hlk
    obtain ⟨hmem, htag⟩ := lookupBorrow_mem_and_tag hlk
    rw [lookupBorrow_cons_ne _ s.memory.borrows tag (by
      rw [hentry_fields.1, ← htag]
      exact (hfresh e hmem).symm)]
    exact hlk
  refine {
    tags_lt := ?_
    entries_ok := ?_
    target_ptrs := ?_
    alias_ok := ?_
    ptr_slots := ?_ }
  · intro e' he'
    simp only [advanceStmt, List.mem_cons] at he' ⊢
    rcases he' with rfl | he'
    · rw [hentry_fields.1]; omega
    · have := hb.tags_lt e' he'; omega
  · intro e' he'
    simp only [advanceStmt, List.mem_cons] at he'
    rcases he' with rfl | he'
    · refine ⟨mutbl, pointeeIt, relOff, ?_, hentry_fields.2.1 ▸ hq_addr, ?_⟩
      · rw [hentry_fields.1, hentry_fields.2.1, hentry_fields.2.2.1]
        rcases hentry with rfl | ⟨hm, rfl⟩
        · exact .inl rfl
        · exact .inr (.inl ⟨hm, rfl⟩)
      · rwa [hentry_fields.2.1, hentry_fields.2.2.1]
    · exact hb.entries_ok e' he'
  · intro hfrag k' hk'
    obtain ⟨hnd, hlm, hd⟩ := hb.target_ptrs hfrag k' hk'
    refine ⟨?_, hlm, hd⟩
    have hik : i ≠ k' := fun h => hi_addr (h ▸ hk')
    rw [List.getElem?_set_ne hik]
    exact hnd
  · simp only [advanceStmt]
    rw [Nat.add_eq, ptrEnvBefore_succ hbb hst]
    have hstep :
        ptrStmtStep body.localDecls (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx) st =
          setPtrLocal body.localDecls.length
            (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx) i
            (.live (some (k, borrowProjSteps projs)) [i]) := by
      simp [ptrStmtStep, hkind, hdecl_ptr, hdb]
    rw [hstep]
    refine hb.alias_ok.setPtrLocal hext_lk i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8))
      (.live (some (k, borrowProjSteps projs)) [i]) (fun hi_lt _ pv _ _ hv => ?_)
    have hi_vlt : i < view.length := by rw [hlen]; exact hi_lt
    rw [List.getElem?_set_self hi_vlt] at hv
    simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hv
    obtain ⟨rfl, -⟩ := hv
    have hnf_i : isMutPtrLocal body.localDecls i = true → entry.perm ≠ .frozen := by
      intro hmut_i
      have hmut : mutbl = .mut := by
        unfold isMutPtrLocal at hmut_i
        rw [hdi] at hmut_i
        dsimp only [Option.bind_eq_bind, Option.bind_some] at hmut_i
        rw [hpt_i] at hmut_i
        cases mutbl <;> simp at hmut_i <;> rfl
      subst hmut
      rcases hentry with rfl | ⟨_, rfl⟩ <;> simp [rawPtrEntry, rawPtrPerm]
    refine ⟨⟨entry, hself_lk, hentry_fields.2.2.2, hnf_i,
      fun q' hq' => by
        injection hq' with hq'
        rw [← hq', hentry_fields.2.1, hentry_fields.2.2.1]⟩, ?_⟩
    intro r hr _ pv_r _ _ hvr
    simp only [List.mem_singleton] at hr
    subst hr
    rw [List.getElem?_set_self hi_vlt] at hvr
    simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hvr
    obtain ⟨rfl, -⟩ := hvr
    rfl
  · intro p dp mutbl' pointeeIt' ptrVal hdp hpt hv
    by_cases hip : i = p
    · subst hip
      rw [hdi] at hdp; injection hdp with hdp_eq; subst hdp_eq
      have hi_lt : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdi).1
      have hi_vlt : i < view.length := by rw [hlen]; exact hi_lt
      rw [List.getElem?_set_self hi_vlt] at hv
      simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hv
      obtain ⟨rfl, -⟩ := hv
      rw [hpt_i] at hpt
      simp only [Option.some.injEq, Prod.mk.injEq] at hpt
      obtain ⟨rfl, rfl⟩ := hpt
      refine ⟨entry, relOff, rfl, hself_lk, ?_⟩
      rwa [hentry_fields.2.1, hentry_fields.2.2.1]
    · rw [List.getElem?_set_ne hip] at hv
      obtain ⟨entry', relOff', hoff, hlookup, htspec⟩ :=
        hb.ptr_slots p dp mutbl' pointeeIt' ptrVal hdp hpt hv
      exact ⟨entry', relOff', hoff, hext_lk ptrVal.tag entry' hlookup, htspec⟩

/-- `BorrowsOk` after `_i = &raw mutbl q` pushed the entry
`rawPtrEntry nextTag mutbl q` and stored its tag in the pointer local `_i`. -/
theorem BorrowsOk.rawPtr {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    (hlen : view.length = body.localDecls.length)
    {bb : BasicBlockData} (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    {st : MirAst.Statement} (hst : bb.statements[s.frame.stmtIdx]? = some st)
    {i : Nat} {d : LocalDecl} (hdi : body.localDecls[i]? = some d)
    {mutbl : MirAst.Mutability} {q : Place}
    (hkind : st.kind = .assign ⟨i, []⟩ (.rawPtr mutbl q))
    (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    (hpt_i : ptrPointeeOf d.ty = some (mutbl, pointeeIt))
    (hi_addr : i ∉ bodyAddrTakenLocals body) (locals' : List LocalSlot) :
    BorrowsOk body ctx (view.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8)))
      (advanceStmt s locals' { s.memory with
        borrows := rawPtrEntry s.memory.nextTag mutbl q :: s.memory.borrows,
        nextTag := s.memory.nextTag + 1 }) lm := by
  have hnd : ∀ rest, q.projection ≠ .deref :: rest := by
    intro rest hr
    obtain ⟨k, projs⟩ := q
    simp only at hr
    subst hr
    simp [ptrTargetSpec] at hspec
  exact hb.directBorrow hlen hbb hst hdi hkind (directBorrowOf_rawPtr_of_nonDeref hnd)
    pointeeIt relOff hspec hpt_i hi_addr locals' (.inl rfl)

theorem directBorrowOf_eq_none_of_reborrowParentOf {rv : Rvalue} {p : Nat}
    (hrb : reborrowParentOf rv = some p) : directBorrowOf rv = none := by
  cases rv with
  | rawPtr m q =>
    rcases q with ⟨k, projs⟩
    cases projs with
    | nil => simp [reborrowParentOf] at hrb
    | cons ph pt =>
      cases ph <;> first | rfl | (simp [reborrowParentOf] at hrb)
  | ref bk q =>
    rcases q with ⟨k, projs⟩
    cases projs with
    | nil => simp [reborrowParentOf] at hrb
    | cons ph pt =>
      cases ph <;> first | rfl | (simp [reborrowParentOf] at hrb)
  | _ => simp [reborrowParentOf] at hrb

theorem BorrowsOk.freezeRead {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    (targetLocal : Nat) (readerTag : Option Nat) (targetProjection : List ProjectionElem)
    (rangeOffset rangeLen : Nat) :
    let borrows' := MirSemantics.freezeTreeBorrowsOnReadAtProj s.memory.borrows s.memory.borrows
      targetLocal readerTag targetProjection rangeOffset rangeLen
    (∀ e' ∈ borrows', e'.tag < s.memory.nextTag) ∧
    (∀ e' ∈ borrows',
      ∃ (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType) (relOff : Nat),
        (e' = { rawPtrEntry e'.tag mutbl ⟨e'.targetLocal, e'.targetProjection⟩ with
                parentTag := e'.parentTag } ∨
          (mutbl = .mut ∧
            e' = { rawPtrEntry e'.tag .mut ⟨e'.targetLocal, e'.targetProjection⟩ with
                   perm := .reserved, parentTag := e'.parentTag }) ∨
          e' = { rawPtrEntry e'.tag mutbl ⟨e'.targetLocal, e'.targetProjection⟩ with
                 perm := .disabled, parentTag := e'.parentTag }) ∧
        e'.targetLocal ∈ bodyAddrTakenLocals body ∧
        ptrTargetSpec body.layouts body.localDecls ⟨e'.targetLocal, e'.targetProjection⟩ =
          some (pointeeIt, relOff)) ∧
    (∀ (p : Nat) (dp : LocalDecl) (mutbl : MirAst.Mutability)
       (pointeeIt : Gen.IntType) (ptrVal : ProvenancePtr),
      body.localDecls[p]? = some dp →
      ptrPointeeOf dp.ty = some (mutbl, pointeeIt) →
      view[p]? = some (.init (.ptr ptrVal 8)) →
      ∃ (entry : BorrowEntry) (relOff : Nat),
        ptrVal.offsetBytes = 0 ∧
        lookupBorrow borrows' ptrVal.tag = some entry ∧
        ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
          some (pointeeIt, relOff)) := by
  intro borrows'
  have hmap : borrows' = s.memory.borrows.map
      (fun e => MirSemantics.updateBorrowPermOnReadAtProj s.memory.borrows e targetLocal readerTag
        targetProjection rangeOffset rangeLen) :=
    freezeTreeBorrowsOnReadAtProj_eq_map _ _ _ _ _ _ _
  have hf := updateBorrowPermOnReadAtProj_freezeOrSelf s.memory.borrows targetLocal readerTag
    targetProjection rangeOffset rangeLen
  refine ⟨?_, ?_, ?_⟩
  · intro e' he'
    rw [hmap, List.mem_map] at he'
    obtain ⟨e, he, rfl⟩ := he'
    rw [hf.tag]
    exact hb.tags_lt e he
  · intro e' he'
    rw [hmap, List.mem_map] at he'
    obtain ⟨e, he, rfl⟩ := he'
    obtain ⟨_, pointeeIt, relOff, _, hk_addr, htspec⟩ := hb.entries_ok e he
    obtain ⟨_, _, hprot, hroff, hrlen⟩ := hb.perm_eq he
    obtain ⟨mutbl', hform'⟩ := borrowEntry_form_of_unranged _
      ((hf.protector e).trans hprot) ((hf.rangeOffset e).trans hroff)
      ((hf.rangeLen e).trans hrlen)
    refine ⟨mutbl', pointeeIt, relOff, hform', ?_, ?_⟩
    · rw [hf.targetLocal]; exact hk_addr
    · rw [hf.targetLocal, hf.targetProjection]; exact htspec
  · intro p dp mutbl pointeeIt ptrVal hdp hpt hv
    obtain ⟨e, relOff, hoff, hlk, htspec⟩ := hb.ptr_slots p dp mutbl pointeeIt ptrVal hdp hpt hv
    refine ⟨MirSemantics.updateBorrowPermOnReadAtProj s.memory.borrows e targetLocal readerTag
      targetProjection rangeOffset rangeLen, relOff, hoff, ?_, ?_⟩
    · rw [hmap, hf.lookupBorrow_map, hlk]; rfl
    · rw [hf.targetLocal, hf.targetProjection]; exact htspec

theorem stepForeignRead_getD_self (decls : List LocalDecl) (env : List PtrLocalState)
    (p : Nat) (hp : p < decls.length) :
    (stepForeignRead decls decls.length env p).getD p .disabled = env.getD p .disabled := by
  rw [stepForeignRead_getD hp]
  have hkeep : foreignReadKeeps env p p = true := by
    simp [foreignReadKeeps]
  simp [hkeep]

/-- `BorrowsOk` after a reborrow statement (`&*_p`, `&mut *_p`,
`&two_phase mut *_p`, `&raw const *_p`, `&raw mut *_p`) pushed a child entry
inheriting `parentEntry`'s target place and stored its fresh tag in `_i`. -/
theorem BorrowsOk.reborrow {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    (hlen : view.length = body.localDecls.length)
    {bb : BasicBlockData} (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    {st : MirAst.Statement} (hst : bb.statements[s.frame.stmtIdx]? = some st)
    {i p : Nat} {d dp : LocalDecl} (hdi : body.localDecls[i]? = some d)
    (hdp : body.localDecls[p]? = some dp) (hp_ptr : isPtrTy dp.ty = true)
    {rv : Rvalue} (hkind : st.kind = .assign ⟨i, []⟩ rv)
    (hrb : reborrowParentOf rv = some p)
    {mutbl : MirAst.Mutability}
    (parentPtr : ProvenancePtr) (hvp : view[p]? = some (.init (.ptr parentPtr 8)))
    (parentEntry : BorrowEntry)
    (hlk_parent : lookupBorrow s.memory.borrows parentPtr.tag = some parentEntry)
    (hparent_ndis : parentEntry.perm ≠ .disabled)
    (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec body.layouts body.localDecls
      ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ = some (pointeeIt, relOff))
    (hpt_i : ptrPointeeOf d.ty = some (mutbl, pointeeIt))
    (hi_addr : i ∉ bodyAddrTakenLocals body) (locals' : List LocalSlot)
    {borrowsAfterRead : List BorrowEntry}
    (hread : (refReborrowParentOf rv = none ∧ borrowsAfterRead = s.memory.borrows) ∨
      (refReborrowParentOf rv = some p ∧
        borrowsAfterRead = MirSemantics.freezeTreeBorrowsOnReadAtProj s.memory.borrows
          s.memory.borrows parentEntry.targetLocal (some parentPtr.tag)
          parentEntry.targetProjection parentEntry.rangeOffset parentEntry.rangeLen))
    {entry : BorrowEntry}
    (hentry : entry = rawReborrowEntry s.memory.nextTag mutbl parentEntry parentPtr.tag ∨
      ∃ bkind, borrowKindMutbl bkind = mutbl ∧
        entry = refReborrowEntry s.memory.nextTag bkind parentEntry parentPtr.tag) :
    BorrowsOk body ctx (view.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8)))
      (advanceStmt s locals' { s.memory with
        borrows := entry :: borrowsAfterRead,
        nextTag := s.memory.nextTag + 1 }) lm := by
  have hparent_mem := (lookupBorrow_mem_and_tag hlk_parent).1
  obtain ⟨_, _, _, hparent_roff, hparent_rlen⟩ := hb.perm_eq hparent_mem
  have hentry_fields :
      entry.tag = s.memory.nextTag ∧ entry.targetLocal = parentEntry.targetLocal ∧
      entry.targetProjection = parentEntry.targetProjection ∧ entry.perm ≠ .disabled ∧
      entry.protector = none ∧ entry.rangeOffset = 0 ∧ entry.rangeLen = 0 ∧
      (mutbl = .mut → entry.perm = .active ∨ entry.perm = .reserved) := by
    rcases hentry with rfl | ⟨bkind, hbm, rfl⟩
    · refine ⟨rfl, rfl, rfl, ?_, rfl, hparent_roff, hparent_rlen, fun hm => ?_⟩
      · cases mutbl <;> cases hpe : parentEntry.perm <;>
          simp [rawReborrowEntry, rawReborrowPerm]
      · subst hm; exact .inl rfl
    · subst hbm
      cases bkind <;> refine ⟨rfl, rfl, rfl, ?_, rfl, hparent_roff, hparent_rlen, ?_⟩ <;>
        simp [refReborrowEntry, refReborrowPerm, borrowKindMutbl]
  have hself_lk : lookupBorrow (entry :: borrowsAfterRead) s.memory.nextTag = some entry := by
    have hl := lookupBorrow_cons_self entry borrowsAfterRead
    rwa [hentry_fields.1] at hl
  have hAfter :
      (∀ e' ∈ borrowsAfterRead, e'.tag < s.memory.nextTag) ∧
      (∀ e' ∈ borrowsAfterRead,
        ∃ (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType) (relOff : Nat),
          (e' = { rawPtrEntry e'.tag mutbl ⟨e'.targetLocal, e'.targetProjection⟩ with
                  parentTag := e'.parentTag } ∨
            (mutbl = .mut ∧
              e' = { rawPtrEntry e'.tag .mut ⟨e'.targetLocal, e'.targetProjection⟩ with
                     perm := .reserved, parentTag := e'.parentTag }) ∨
            e' = { rawPtrEntry e'.tag mutbl ⟨e'.targetLocal, e'.targetProjection⟩ with
                   perm := .disabled, parentTag := e'.parentTag }) ∧
          e'.targetLocal ∈ bodyAddrTakenLocals body ∧
          ptrTargetSpec body.layouts body.localDecls ⟨e'.targetLocal, e'.targetProjection⟩ =
            some (pointeeIt, relOff)) ∧
      (∀ (q : Nat) (dq : LocalDecl) (mutbl' : MirAst.Mutability)
         (pointeeIt' : Gen.IntType) (ptrVal : ProvenancePtr),
        body.localDecls[q]? = some dq →
        ptrPointeeOf dq.ty = some (mutbl', pointeeIt') →
        view[q]? = some (.init (.ptr ptrVal 8)) →
        ∃ (entry' : BorrowEntry) (relOff' : Nat),
          ptrVal.offsetBytes = 0 ∧
          lookupBorrow borrowsAfterRead ptrVal.tag = some entry' ∧
          ptrTargetSpec body.layouts body.localDecls ⟨entry'.targetLocal, entry'.targetProjection⟩ =
            some (pointeeIt', relOff')) := by
    rcases hread with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨hb.tags_lt, hb.entries_ok, hb.ptr_slots⟩
    · exact hb.freezeRead parentEntry.targetLocal (some parentPtr.tag)
        parentEntry.targetProjection parentEntry.rangeOffset parentEntry.rangeLen
  have hfresh : ∀ e' ∈ borrowsAfterRead, e'.tag ≠ s.memory.nextTag :=
    fun e' he' h => by have := hAfter.1 e' he'; omega
  obtain ⟨_, _, _, _, hq_addr, _⟩ := hb.entries_ok parentEntry hparent_mem
  have hisPtr_i : isPtrTy d.ty = true := by simp [isPtrTy, hpt_i]
  have hdecl_ptr : isDeclPtrLocal body.localDecls i = true := by
    simp [isDeclPtrLocal, hdi, hisPtr_i]
  have hdb_none := directBorrowOf_eq_none_of_reborrowParentOf hrb
  have hext_lk : ∀ tag e, lookupBorrow borrowsAfterRead tag = some e →
      lookupBorrow (entry :: borrowsAfterRead) tag = some e := by
    intro tag e hlk
    obtain ⟨hmem, htag⟩ := lookupBorrow_mem_and_tag hlk
    rw [lookupBorrow_cons_ne _ borrowsAfterRead tag (by
      rw [hentry_fields.1, ← htag]
      exact (hfresh e hmem).symm)]
    exact hlk
  refine {
    tags_lt := ?_
    entries_ok := ?_
    target_ptrs := ?_
    alias_ok := ?_
    ptr_slots := ?_ }
  · intro e' he'
    simp only [advanceStmt, List.mem_cons] at he' ⊢
    rcases he' with rfl | he'
    · rw [hentry_fields.1]; omega
    · have := hAfter.1 e' he'; omega
  · intro e' he'
    simp only [advanceStmt, List.mem_cons] at he'
    rcases he' with rfl | he'
    · obtain ⟨mutbl_e, hform_e⟩ := borrowEntry_form_of_unranged entry
        hentry_fields.2.2.2.2.1 hentry_fields.2.2.2.2.2.1 hentry_fields.2.2.2.2.2.2.1
      refine ⟨mutbl_e, pointeeIt, relOff, hform_e, hentry_fields.2.1 ▸ hq_addr, ?_⟩
      rwa [hentry_fields.2.1, hentry_fields.2.2.1]
    · exact hAfter.2.1 e' he'
  · intro hfrag k' hk'
    obtain ⟨hnd, hlm, hd⟩ := hb.target_ptrs hfrag k' hk'
    refine ⟨?_, hlm, hd⟩
    have hik : i ≠ k' := fun h => hi_addr (h ▸ hk')
    rw [List.getElem?_set_ne hik]
    exact hnd
  · simp only [advanceStmt]
    rw [Nat.add_eq, ptrEnvBefore_succ hbb hst]
    let env := ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx
    have hstep : ptrStmtStep body.localDecls env st =
        stepReborrow body.localDecls.length
          (stepReborrowRead body.localDecls body.localDecls.length env rv) i p := by
      simp [ptrStmtStep, hkind, hdecl_ptr, hdb_none, hrb]
    rw [hstep]
    let envRead := stepReborrowRead body.localDecls body.localDecls.length env rv
    have hranges : ∀ e ∈ s.memory.borrows, e.rangeLen = 0 :=
      fun e he => (hb.perm_eq he).2.2.2.2
    have henvRead_ok : PtrEnvOk body view borrowsAfterRead envRead ∧
        envRead.getD p .disabled = env.getD p .disabled := by
      rcases hread with ⟨href_none, rfl⟩ | ⟨href_p, rfl⟩
      · refine ⟨?_, ?_⟩
        · dsimp only [envRead, stepReborrowRead]
          rw [href_none]
          exact hb.alias_ok
        · dsimp only [envRead, stepReborrowRead]
          rw [href_none]
      · dsimp only [envRead, stepReborrowRead]
        rw [href_p]
        refine ⟨hb.alias_ok.foreignRead hranges hdp hp_ptr hvp hlk_parent, ?_⟩
        exact stepForeignRead_getD_self body.localDecls env p
          (List.getElem?_eq_some_iff.mp hdp).1
    unfold stepReborrow
    have hp_lt : p < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdp).1
    have hp_ok := henvRead_ok.1 p hp_lt
    refine henvRead_ok.1.setPtrLocal hext_lk i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8)) _
      (fun hi_lt => ?_)
    cases hst_p : envRead.getD p .disabled with
    | empty =>
      rw [hst_p] at hp_ok
      exact False.elim (hp_ok dp parentPtr hdp hp_ptr hvp)
    | disabled =>
      trivial
    | live target peers =>
      rw [hst_p] at hp_ok
      have hp_ok_orig := hb.alias_ok p hp_lt
      rw [← henvRead_ok.2, hst_p] at hp_ok_orig
      obtain ⟨⟨entry', hlk', _, _, ht_parent⟩, _⟩ := hp_ok_orig dp parentPtr hdp hp_ptr hvp
      rw [hlk_parent] at hlk'
      injection hlk' with heq
      subst heq
      intro _ pv _ _ hv
      have hi_vlt : i < view.length := by rw [hlen]; exact hi_lt
      rw [List.getElem?_set_self hi_vlt] at hv
      simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hv
      obtain ⟨rfl, -⟩ := hv
      have hnf_i : isMutPtrLocal body.localDecls i = true → entry.perm ≠ .frozen := by
        intro hmut_i
        have hmut : mutbl = .mut := by
          unfold isMutPtrLocal at hmut_i
          rw [hdi] at hmut_i
          dsimp only [Option.bind_eq_bind, Option.bind_some] at hmut_i
          rw [hpt_i] at hmut_i
          cases mutbl <;> simp at hmut_i <;> rfl
        rcases hentry_fields.2.2.2.2.2.2.2 hmut with hperm | hperm <;> simp [hperm]
      refine ⟨⟨entry, hself_lk, hentry_fields.2.2.2.1, hnf_i,
        fun q' hq' => by
          rw [hentry_fields.2.1, hentry_fields.2.2.1]
          exact ht_parent q' hq'⟩, ?_⟩
      intro r hr _ pv_r _ _ hvr
      simp only [List.mem_singleton] at hr
      subst hr
      rw [List.getElem?_set_self hi_vlt] at hvr
      simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hvr
      obtain ⟨rfl, -⟩ := hvr
      rfl
  · intro q dq mutbl' pointeeIt' ptrVal hdq hpt hv
    by_cases hiq : i = q
    · subst hiq
      rw [hdi] at hdq; injection hdq with hdq_eq; subst hdq_eq
      have hi_lt : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdi).1
      have hi_vlt : i < view.length := by rw [hlen]; exact hi_lt
      rw [List.getElem?_set_self hi_vlt] at hv
      simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hv
      obtain ⟨rfl, -⟩ := hv
      rw [hpt_i] at hpt
      simp only [Option.some.injEq, Prod.mk.injEq] at hpt
      obtain ⟨rfl, rfl⟩ := hpt
      refine ⟨entry, relOff, rfl, hself_lk, ?_⟩
      rwa [hentry_fields.2.1, hentry_fields.2.2.1]
    · rw [List.getElem?_set_ne hiq] at hv
      obtain ⟨entry', relOff', hoff, hlookup, htspec⟩ :=
        hAfter.2.2 q dq mutbl' pointeeIt' ptrVal hdq hpt hv
      exact ⟨entry', relOff', hoff, hext_lk ptrVal.tag entry' hlookup, htspec⟩

theorem ptrCopySrcOf_of_ptrRvalueOk {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType} {isRef : Bool} {rv : Rvalue}
    {p : Nat} {dp : LocalDecl}
    (hok : ptrRvalueOk layouts decls mutbl pointeeIt isRef (copyRv rv) = true)
    (hnraw : ∀ m q, rv ≠ .rawPtr m q) (hnref : ∀ bk q, rv ≠ .ref bk q)
    (hp : Operand.copy ⟨p, []⟩ ∈ rvOperands (copyRv rv))
    (hdp : decls[p]? = some dp) (hisPtr : isPtrTy dp.ty = true) :
    directBorrowOf rv = none ∧ reborrowParentOf rv = none ∧ ptrCopySrcOf decls rv = some p := by
  have hdb : directBorrowOf rv = none := by
    cases rv with
    | rawPtr m q => exact absurd rfl (hnraw m q)
    | ref bk q => exact absurd rfl (hnref bk q)
    | _ => rfl
  have hrb : reborrowParentOf rv = none := by
    cases rv with
    | rawPtr m q => exact absurd rfl (hnraw m q)
    | ref bk q => exact absurd rfl (hnref bk q)
    | _ => rfl
  refine ⟨hdb, hrb, ?_⟩
  unfold ptrCopySrcOf
  have hnrawC : ∀ m q, copyRv rv ≠ .rawPtr m q := by
    intro m q h; cases rv with | rawPtr m' q' => exact hnraw m' q' rfl | _ => simp [copyRv] at h
  have hnrefC : ∀ bk q, copyRv rv ≠ .ref bk q := by
    intro bk q h; cases rv with | ref bk' q' => exact hnref bk' q' rfl | _ => simp [copyRv] at h
  cases hcrv : copyRv rv with
  | rawPtr m q => exact absurd hcrv (hnrawC m q)
  | ref bk q => exact absurd hcrv (hnrefC bk q)
  | use op =>
    rw [hcrv] at hok hp
    cases op with
    | copy pl =>
      rcases pl with ⟨p', projs⟩
      cases projs with
      | nil =>
        simp only [rvOperands, List.mem_singleton, Operand.copy.injEq, Place.mk.injEq, and_true] at hp
        subst hp
        simp [hdp, hisPtr]
      | cons _ _ => simp [ptrRvalueOk] at hok
    | _ => simp [ptrRvalueOk] at hok
  | cast k op castTy =>
    rw [hcrv] at hok hp
    cases k with
    | ptrToPtr | transmute =>
      cases op with
      | copy pl =>
        rcases pl with ⟨p', projs⟩
        cases projs with
        | nil =>
          simp only [rvOperands, List.mem_singleton, Operand.copy.injEq, Place.mk.injEq, and_true] at hp
          subst hp
          simp [hdp, hisPtr]
        | cons _ _ => simp [ptrRvalueOk] at hok
      | _ => simp [ptrRvalueOk] at hok
    | _ => simp [ptrRvalueOk] at hok
  | binaryOp bop l r =>
    rw [hcrv] at hok hp
    cases bop with
    | offset =>
      cases l with
      | copy pl =>
        rcases pl with ⟨p', projs⟩
        cases projs with
        | nil =>
          cases r with
          | constant _ =>
            simp only [rvOperands, List.mem_cons, List.not_mem_nil, or_false,
              Operand.copy.injEq, Place.mk.injEq, and_true, reduceCtorEq] at hp
            subst hp
            simp [hdp, hisPtr]
          | _ => simp [ptrRvalueOk] at hok
        | cons _ _ => simp [ptrRvalueOk] at hok
      | _ => simp [ptrRvalueOk] at hok
    | _ => simp [ptrRvalueOk] at hok
  | _ => rw [hcrv] at hok; simp [ptrRvalueOk] at hok

/-- `PtrEnvOk` preservation for a tag-preserving copy `stepPtrCopy`. -/
theorem PtrEnvOk.stepPtrCopy {body : CapturedMir} {view : List LocalSlot}
    {borrows : List BorrowEntry} {env : List PtrLocalState}
    (hok : PtrEnvOk body view borrows env)
    (hlen : view.length = body.localDecls.length)
    (i p : Nat) (pv : ProvenancePtr) {dp : LocalDecl}
    (hdp : body.localDecls[p]? = some dp) (hp_ptr : isPtrTy dp.ty = true)
    (hvp : view[p]? = some (.init (.ptr pv 8)))
    (hmut_ip : isMutPtrLocal body.localDecls i = true → isMutPtrLocal body.localDecls p = true) :
    PtrEnvOk body (view.set i (.init (.ptr pv 8))) borrows
      (Correspondence.stepPtrCopy body.localDecls.length env i p) := by
  have hp_lt : p < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdp).1
  unfold Correspondence.stepPtrCopy
  by_cases hip : i = p
  · subst hip
    simp only [beq_self_eq_true, ↓reduceIte]
    obtain ⟨hp_vlt, hp_get⟩ := List.getElem?_eq_some_iff.mp hvp
    have hset : view.set i (.init (.ptr pv 8)) = view := by
      rw [← hp_get, List.set_getElem_self]
    rw [hset]
    exact hok.of_map_range
  · have hb_ip : (i == p) = false := beq_false_of_ne hip
    simp only [hb_ip, Bool.false_eq_true, ↓reduceIte]
    intro q hq
    rw [getD_map_range _ _ _ hq]
    by_cases hqi : q = i
    · subst hqi
      simp only [beq_self_eq_true, ↓reduceIte]
      have hq_vlt : q < view.length := by rw [hlen]; exact hq
      have hp_ok := hok p hp_lt
      cases hst_p : env.getD p .disabled with
      | empty =>
        rw [hst_p] at hp_ok
        exact False.elim (hp_ok dp pv hdp hp_ptr hvp)
      | disabled =>
        trivial
      | live target peers =>
        rw [hst_p] at hp_ok
        obtain ⟨⟨entry_p, hlk_p, hndis_p, hnf_p, ht_p⟩, hpeers_p⟩ := hp_ok dp pv hdp hp_ptr hvp
        dsimp only [addPeerToState, PtrLocalOk]
        intro _ pv_q _ _ hvq
        rw [List.getElem?_set_self hq_vlt] at hvq
        simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hvq
        obtain ⟨rfl, -⟩ := hvq
        refine ⟨⟨entry_p, hlk_p, hndis_p, fun hm => hnf_p (hmut_ip hm), ht_p⟩,
          fun r hr dr pv_r hdr hptr hvr => ?_⟩
        by_cases hri : r = q
        · subst hri
          rw [List.getElem?_set_self hq_vlt] at hvr
          simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hvr
          obtain ⟨rfl, -⟩ := hvr
          rfl
        · have hr_mem : r ∈ peers := by
            split at hr
            · exact hr
            · simp only [List.mem_cons] at hr
              exact hr.resolve_left hri
          rw [List.getElem?_set_ne (Ne.symm hri)] at hvr
          exact hpeers_p r hr_mem dr pv_r hdr hptr hvr
    · have hb_qi : (q == i) = false := beq_false_of_ne hqi
      simp only [hb_qi, Bool.false_eq_true, ↓reduceIte]
      have hq_ok := hok q hq
      cases hst_q : env.getD q .disabled with
      | empty =>
        rw [hst_q] at hq_ok
        dsimp only [removePeerFromState, PtrLocalOk]
        intro dq pv_q hdq hq_ptr hvq
        rw [List.getElem?_set_ne (Ne.symm hqi)] at hvq
        exact hq_ok dq pv_q hdq hq_ptr hvq
      | disabled =>
        trivial
      | live t ps =>
        rw [hst_q] at hq_ok
        dsimp only [removePeerFromState]
        let ps' := ps.filter (· != i)
        change PtrLocalOk body (view.set i (.init (.ptr pv 8))) borrows q
          (if ps'.contains p then .live t (if ps'.contains i then ps' else i :: ps') else .live t ps')
        by_cases hcp : ps'.contains p = true
        · simp only [hcp, ↓reduceIte]
          have hp_ps : p ∈ ps := by
            have hp_ps' : p ∈ ps' := List.contains_iff_mem.mp hcp
            exact (List.mem_filter.mp hp_ps').1
          intro dq pv_q hdq hq_ptr hvq
          rw [List.getElem?_set_ne (Ne.symm hqi)] at hvq
          obtain ⟨hent_q, hpeers_q⟩ := hq_ok dq pv_q hdq hq_ptr hvq
          have hp_tag : pv.tag = pv_q.tag := hpeers_q p hp_ps dp pv hdp hp_ptr hvp
          refine ⟨hent_q, fun r hr dr pv_r hdr hptr hvr => ?_⟩
          by_cases hri : r = i
          · subst hri
            have hi_lt : r < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdr).1
            have hi_vlt : r < view.length := by rw [hlen]; exact hi_lt
            rw [List.getElem?_set_self hi_vlt] at hvr
            simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hvr
            obtain ⟨rfl, -⟩ := hvr
            exact hp_tag
          · have hr_ps' : r ∈ ps' := by
              split at hr
              · exact hr
              · simp only [List.mem_cons] at hr
                exact hr.resolve_left hri
            have hr_ps : r ∈ ps := (List.mem_filter.mp hr_ps').1
            rw [List.getElem?_set_ne (Ne.symm hri)] at hvr
            exact hpeers_q r hr_ps dr pv_r hdr hptr hvr
        · simp only [hcp, Bool.false_eq_true, ↓reduceIte]
          intro dq pv_q hdq hq_ptr hvq
          rw [List.getElem?_set_ne (Ne.symm hqi)] at hvq
          obtain ⟨hent_q, hpeers_q⟩ := hq_ok dq pv_q hdq hq_ptr hvq
          refine ⟨hent_q, fun r hr dr pv_r hdr hptr hvr => ?_⟩
          simp only [ps', List.mem_filter, bne_iff_ne, ne_eq] at hr
          rw [List.getElem?_set_ne (Ne.symm hr.2)] at hvr
          exact hpeers_q r hr.1 dr pv_r hdr hptr hvr

/-- `BorrowsOk` after a tag-preserving copy (`_i = copy _p`, `move _p`,
`CopyForDeref(_p)`, `PtrToPtr`, `Transmute`, or `Offset(_p, 0)`). -/
theorem BorrowsOk.ptrCopy {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    (hlen : view.length = body.localDecls.length)
    {bb : BasicBlockData} (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    {st : MirAst.Statement} (hst : bb.statements[s.frame.stmtIdx]? = some st)
    {i p : Nat} {d dp : LocalDecl} (hdi : body.localDecls[i]? = some d)
    (hi_ptr : isPtrTy d.ty = true)
    (hdp : body.localDecls[p]? = some dp) (hp_ptr : isPtrTy dp.ty = true)
    (hmut_ip : isMutPtrLocal body.localDecls i = true → isMutPtrLocal body.localDecls p = true)
    {rv : Rvalue} (hkind : st.kind = .assign ⟨i, []⟩ rv)
    (hdb_none : directBorrowOf rv = none) (hrb_none : reborrowParentOf rv = none)
    (hsrc_p : ptrCopySrcOf body.localDecls rv = some p)
    {locals' : List LocalSlot} (pv : ProvenancePtr)
    (hvp : view[p]? = some (.init (.ptr pv 8)))
    (hi_addr : i ∉ bodyAddrTakenLocals body)
    (hpv : ∀ (dp' : LocalDecl) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType),
      body.localDecls[i]? = some dp' → ptrPointeeOf dp'.ty = some (mutbl, pointeeIt) →
      ∃ (entry : BorrowEntry) (relOff : Nat),
        pv.offsetBytes = 0 ∧
        lookupBorrow s.memory.borrows pv.tag = some entry ∧
        ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
          some (pointeeIt, relOff)) :
    BorrowsOk body ctx (view.set i (.init (.ptr pv 8))) (advanceStmt s locals' s.memory) lm where
  tags_lt := hb.tags_lt
  entries_ok := hb.entries_ok
  target_ptrs hfrag k hk := by
    obtain ⟨hnd, hlmk, hd⟩ := hb.target_ptrs hfrag k hk
    refine ⟨?_, hlmk, hd⟩
    have hik : i ≠ k := fun h => hi_addr (h ▸ hk)
    rw [List.getElem?_set_ne hik]
    exact hnd
  alias_ok := by
    have hi_decl : isDeclPtrLocal body.localDecls i = true := by
      simp [isDeclPtrLocal, hdi, hi_ptr]
    simp only [advanceStmt]
    rw [Nat.add_eq, ptrEnvBefore_succ hbb hst]
    simp only [ptrStmtStep, hkind, hi_decl, ↓reduceIte, hdb_none, hrb_none, hsrc_p]
    exact hb.alias_ok.stepPtrCopy hlen i p pv hdp hp_ptr hvp hmut_ip
  ptr_slots q dq mutbl pointeeIt ptrVal hdq hpt hv := by
    by_cases hiq : i = q
    · subst hiq
      have hi_lt : i < view.length := by
        rw [hlen]
        exact (List.getElem?_eq_some_iff.mp hdq).1
      rw [List.getElem?_set_self hi_lt] at hv
      simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hv
      obtain ⟨rfl, -⟩ := hv
      exact hpv dq mutbl pointeeIt hdq hpt
    · rw [List.getElem?_set_ne hiq] at hv
      exact hb.ptr_slots q dq mutbl pointeeIt ptrVal hdq hpt hv

/-- `BorrowsOk` after a dereference read `_i = *_r`, where Anneal freezes
foreign active borrows via `freezeDerefReadBorrowsAt` and writes a non-dead,
non-pointer value `slot'` to `_i`. -/
theorem BorrowsOk.derefRead {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    {bb : BasicBlockData} (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    {st : MirAst.Statement} (hst : bb.statements[s.frame.stmtIdx]? = some st)
    {i r : Nat} {rv : Rvalue} (hkind : st.kind = .assign ⟨i, []⟩ rv)
    (hnd_i : isDeclPtrLocal body.localDecls i = false)
    (hi_addr : i ∉ bodyAddrTakenLocals body)
    (hsrc : ptrDerefReadSrc rv = some r)
    {dr : LocalDecl} (hdr : body.localDecls[r]? = some dr) (hr_ptr : isPtrTy dr.ty = true)
    (ptrVal : ProvenancePtr) (entry : BorrowEntry)
    (hvr : view[r]? = some (.init (.ptr ptrVal 8)))
    (hrA : s.frame.locals[r]? = some (.init (.ptr ptrVal 8)))
    (hlookup : lookupBorrow s.memory.borrows ptrVal.tag = some entry)
    {locals' : List LocalSlot} (slot' : LocalSlot)
    (hnp : ∀ dp pv, body.localDecls[i]? = some dp → isPtrTy dp.ty = true →
      slot' ≠ .init (.ptr pv 8)) :
    BorrowsOk body ctx (view.set i slot')
      (advanceStmt s locals'
        { s.memory with
          borrows := MirSemantics.freezeDerefReadBorrowsAt s.frame.locals r [] s.memory.borrows })
      lm := by
  have hfrz_eq :
      MirSemantics.freezeDerefReadBorrowsAt s.frame.locals r [] s.memory.borrows =
        MirSemantics.freezeTreeBorrowsOnReadAtProj s.memory.borrows s.memory.borrows
          entry.targetLocal (some ptrVal.tag) entry.targetProjection
          entry.rangeOffset entry.rangeLen := by
    cases hbs : s.memory.borrows with
    | nil => rw [hbs] at hlookup; simp [lookupBorrow] at hlookup
    | cons b1 rest =>
      cases rest with
      | nil =>
        rw [hbs] at hlookup
        obtain ⟨hmem, htag⟩ := lookupBorrow_mem_and_tag hlookup
        have hb1 : entry = b1 := by simpa using hmem
        subst hb1
        rw [freezeDerefReadBorrowsAt_singleton, freezeTreeBorrowsOnReadAtProj_eq_map,
          List.map_singleton, updateBorrowPermOnReadAtProj_of_descendant _ _ _ _
            (by rw [htag]; exact isBorrowDescendantOrSelf_self _ _)]
      | cons b2 bs =>
        unfold MirSemantics.freezeDerefReadBorrowsAt
        dsimp only []
        rw [← hbs]
        simp [get?, hrA, hlookup, appendProjections_nil_right]
  have hAfter := hb.freezeRead entry.targetLocal (some ptrVal.tag) entry.targetProjection
    entry.rangeOffset entry.rangeLen
  have hranges : ∀ e ∈ s.memory.borrows, e.rangeLen = 0 :=
    fun e he => (hb.perm_eq he).2.2.2.2
  refine {
    tags_lt := fun e' he' => by
      simp only [advanceStmt, hfrz_eq] at he' ⊢
      exact hAfter.1 e' he'
    entries_ok := fun e' he' => by
      simp only [advanceStmt, hfrz_eq] at he' ⊢
      exact hAfter.2.1 e' he'
    target_ptrs := fun hfrag k hk => by
      obtain ⟨hnd, hlmk, hd⟩ := hb.target_ptrs hfrag k hk
      refine ⟨?_, hlmk, hd⟩
      have hik : i ≠ k := fun h => hi_addr (h ▸ hk)
      rw [List.getElem?_set_ne hik]
      exact hnd
    alias_ok := by
      simp only [advanceStmt, hfrz_eq]
      rw [Nat.add_eq, ptrEnvBefore_succ hbb hst]
      simp only [ptrStmtStep, hkind, hnd_i, Bool.false_eq_true, ↓reduceIte, hsrc]
      exact (hb.alias_ok.foreignRead hranges hdr hr_ptr hvr hlookup).set_nonptr i slot' hnp
    ptr_slots := fun p dp mutbl pointeeIt pv hdp hpt hv => by
      have hp_ptr : isPtrTy dp.ty = true := by simp [isPtrTy, hpt]
      have hv_old : view[p]? = some (.init (.ptr pv 8)) := by
        by_cases hip : i = p
        · subst hip
          by_cases hlt : i < view.length
          · rw [List.getElem?_set_self hlt] at hv
            injection hv with hs
            exact False.elim (hnp dp pv hdp hp_ptr hs)
          · rwa [List.set_eq_of_length_le (Nat.not_lt.mp hlt)] at hv
        · rwa [List.getElem?_set_ne hip] at hv
      simp only [advanceStmt, hfrz_eq]
      exact hAfter.2.2 p dp mutbl pointeeIt pv hdp hpt hv_old }

/-- `BorrowsOk` after a dereference write `(*_w) = rv`, where Anneal updates the
borrow table via `invalidateDerefWriteBorrows` and writes a non-dead,
non-pointer value `slot'` to `entry.targetLocal`. -/
theorem BorrowsOk.derefWrite {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    {bb : BasicBlockData} (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    {st : MirAst.Statement} (hst : bb.statements[s.frame.stmtIdx]? = some st)
    {w : Nat} {rv : Rvalue} (hkind : st.kind = .assign ⟨w, [.deref]⟩ rv)
    (hsrc_none : ptrDerefReadSrc rv = none)
    {dw : LocalDecl} (hdw : body.localDecls[w]? = some dw) (hw_ptr : isPtrTy dw.ty = true)
    (ptrVal : ProvenancePtr) (entry : BorrowEntry)
    (hvw : view[w]? = some (.init (.ptr ptrVal 8)))
    (hwA : s.frame.locals[w]? = some (.init (.ptr ptrVal 8)))
    (hlookup : lookupBorrow s.memory.borrows ptrVal.tag = some entry)
    {locals' : List LocalSlot} (slot' : LocalSlot)
    (hndead : slot' ≠ .dead)
    (hnp : ∀ dp pv, body.localDecls[entry.targetLocal]? = some dp → isPtrTy dp.ty = true →
      slot' ≠ .init (.ptr pv 8)) :
    BorrowsOk body ctx (view.set entry.targetLocal slot')
      (advanceStmt s locals'
        { s.memory with
          borrows := invalidateDerefWriteBorrows s.frame.locals s.memory.borrows ⟨w, [.deref]⟩ [] })
      lm := by
  have hentry_mem : entry ∈ s.memory.borrows := (lookupBorrow_mem_and_tag hlookup).1
  obtain ⟨_, _, _, hroff, hrlen⟩ := hb.perm_eq hentry_mem
  obtain ⟨wMutbl, wIt, hw_pt⟩ : ∃ m it, ptrPointeeOf dw.ty = some (m, it) := by
    unfold isPtrTy at hw_ptr
    obtain ⟨⟨m, it⟩, h⟩ := Option.isSome_iff_exists.mp hw_ptr
    exact ⟨m, it, h⟩
  obtain ⟨entry_slot, relOff_w, hoff0_w, hlk_slot, htspec_w⟩ :=
    hb.ptr_slots w dw wMutbl wIt ptrVal hdw hw_pt hvw
  rw [hlookup] at hlk_slot
  injection hlk_slot with heq_slot
  subst heq_slot
  have hfull :
      MirSemantics.resolveDerefWriteFullProj s.frame.locals s.frame.locals
        (.ptr ptrVal 8) entry [] = entry.targetProjection :=
    resolveDerefWriteFullProj_of_ptrTargetSpec s.frame.locals ptrVal entry wIt relOff_w
      htspec_w hoff0_w
  let upd : BorrowEntry → BorrowEntry := fun e =>
    MirSemantics.updateBorrowPermTreeAtProj s.memory.borrows e entry.targetLocal
      (some ptrVal.tag) entry.targetProjection 0 0
  have hmap :
      invalidateDerefWriteBorrows s.frame.locals s.memory.borrows ⟨w, [.deref]⟩ [] =
        s.memory.borrows.map upd :=
    invalidateDerefWriteBorrows_eq_map s.frame.locals s.memory.borrows w ptrVal entry
      hwA hlookup hrlen hroff hfull
  have hupd_fields : ∀ e,
      (upd e).tag = e.tag ∧ (upd e).targetLocal = e.targetLocal ∧
      (upd e).targetProjection = e.targetProjection ∧
      (upd e).rangeOffset = e.rangeOffset ∧ (upd e).rangeLen = e.rangeLen ∧
      (upd e).protector = e.protector ∧ (upd e).parentTag = e.parentTag := fun e => by
    exact updateBorrowPermTreeAtProj_fields s.memory.borrows e entry.targetLocal
      (some ptrVal.tag) entry.targetProjection 0 0
  refine {
    tags_lt := fun e' he' => by
      simp only [advanceStmt, hmap, List.mem_map] at he' ⊢
      obtain ⟨e, he, rfl⟩ := he'
      rw [(hupd_fields e).1]
      exact hb.tags_lt e he
    entries_ok := fun e' he' => by
      simp only [advanceStmt, hmap, List.mem_map] at he' ⊢
      obtain ⟨e, he, rfl⟩ := he'
      obtain ⟨_, pointeeIt, relOff, _, hk_addr, htspec⟩ := hb.entries_ok e he
      obtain ⟨_, _, hprot_e, hroff_e, hrlen_e⟩ := hb.perm_eq he
      obtain ⟨_, hloc, hproj, hroff_u, hrlen_u, hprot_u, _⟩ := hupd_fields e
      obtain ⟨mutbl', hform'⟩ := borrowEntry_form_of_unranged (upd e)
        (hprot_u.trans hprot_e) (hroff_u.trans hroff_e) (hrlen_u.trans hrlen_e)
      refine ⟨mutbl', pointeeIt, relOff, hform', hloc ▸ hk_addr, ?_⟩
      rwa [hloc, hproj]
    target_ptrs := fun hfrag k hk => by
      obtain ⟨hnd, hlmk, hd⟩ := hb.target_ptrs hfrag k hk
      refine ⟨?_, hlmk, hd⟩
      by_cases htk : entry.targetLocal = k
      · subst htk
        by_cases hlt : entry.targetLocal < view.length
        · rw [List.getElem?_set_self hlt]
          intro h
          injection h with hs
          exact hndead hs
        · rw [List.set_eq_of_length_le (Nat.not_lt.mp hlt)]
          exact hnd
      · rw [List.getElem?_set_ne htk]
        exact hnd
    alias_ok := ?_
    ptr_slots := fun p dp mutbl pointeeIt pv hdp hpt hv => by
      have hp_ptr : isPtrTy dp.ty = true := by simp [isPtrTy, hpt]
      have hv_old : view[p]? = some (.init (.ptr pv 8)) := by
        by_cases htp : entry.targetLocal = p
        · subst htp
          by_cases hlt : entry.targetLocal < view.length
          · rw [List.getElem?_set_self hlt] at hv
            injection hv with hs
            exact False.elim (hnp dp pv hdp hp_ptr hs)
          · rwa [List.set_eq_of_length_le (Nat.not_lt.mp hlt)] at hv
        · rwa [List.getElem?_set_ne htp] at hv
      obtain ⟨e_p, relOff, hoff0, hlk_p, htspec_p⟩ :=
        hb.ptr_slots p dp mutbl pointeeIt pv hdp hpt hv_old
      obtain ⟨_, hloc_p, hproj_p, _⟩ := hupd_fields e_p
      refine ⟨upd e_p, relOff, hoff0, ?_, ?_⟩
      · simp only [advanceStmt, hmap]
        rw [lookupBorrow_map_eq (fun e => (hupd_fields e).1) pv.tag, hlk_p]
        rfl
      · rwa [hloc_p, hproj_p] }
  simp only [advanceStmt, hmap]
  rw [Nat.add_eq, ptrEnvBefore_succ hbb hst]
  simp only [ptrStmtStep, hkind, hsrc_none]
  apply PtrEnvOk.set_nonptr _ entry.targetLocal slot' hnp
  let env := ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx
  have hw_lt : w < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdw).1
  have hw_ok := hb.alias_ok w hw_lt
  unfold stepDerefWrite
  cases hst_w : env.getD w .disabled with
  | empty =>
    rw [hst_w] at hw_ok
    exact False.elim (hw_ok dw ptrVal hdw hw_ptr hvw)
  | disabled =>
    intro q hq
    rw [getD_map_range _ _ _ hq]
    trivial
  | live wTarget wPeers =>
    rw [hst_w] at hw_ok
    obtain ⟨⟨entry_w, hlk_w, _, _, hw_tgt⟩, hw_peers⟩ := hw_ok dw ptrVal hdw hw_ptr hvw
    rw [hlookup] at hlk_w
    injection hlk_w with heq_w
    subst heq_w
    intro q hq
    rw [getD_map_range _ _ _ hq]
    have hq_ok := hb.alias_ok q hq
    cases hst_q : env.getD q .disabled with
    | empty =>
      rw [hst_q] at hq_ok
      exact hq_ok
    | disabled =>
      trivial
    | live qTarget qPeers =>
      rw [hst_q] at hq_ok
      by_cases hkeep : (wPeers.contains q || targetsDefinitelyDisjoint qTarget wTarget) = true
      · simp only [hkeep, ↓reduceIte]
        intro dq pv_q hdq hq_ptr hvq
        obtain ⟨⟨e_q, hlk_q, hndis_q, hnf_q, hq_tgt⟩, hq_peers⟩ := hq_ok dq pv_q hdq hq_ptr hvq
        obtain ⟨_, he_q_tag⟩ := lookupBorrow_mem_and_tag hlk_q
        have hkeep_q : upd e_q = e_q ∨ upd e_q = { e_q with perm := .active } := by
          apply updateBorrowPermTreeAtProj_self_or_disjoint_keep
          intro hloc
          have hkeep' : wPeers.contains q = true ∨ targetsDefinitelyDisjoint qTarget wTarget = true := by
            simpa only [Bool.or_eq_true] using hkeep
          rcases hkeep' with hpeer | hdisj
          · have htag_eq := hw_peers q (List.contains_iff_mem.mp hpeer) dq pv_q hdq hq_ptr hvq
            exact .inl (he_q_tag.trans htag_eq)
          · by_cases htag_eq : e_q.tag = ptrVal.tag
            · exact .inl htag_eq
            · right
              refine ⟨htag_eq, ?_⟩
              cases qTarget with
              | none => simp [targetsDefinitelyDisjoint] at hdisj
              | some qp =>
                cases wTarget with
                | none => simp [targetsDefinitelyDisjoint] at hdisj
                | some wp =>
                  obtain ⟨k1, p1⟩ := qp
                  obtain ⟨k2, p2⟩ := wp
                  have h1 := hq_tgt (k1, p1) rfl
                  have h2 := hw_tgt (k2, p2) rfl
                  simp only [Prod.mk.injEq] at h1 h2
                  obtain ⟨rfl, rfl⟩ := h1
                  obtain ⟨rfl, rfl⟩ := h2
                  simp only [targetsDefinitelyDisjoint, hloc, ne_eq, not_true_eq_false,
                    decide_false, Bool.false_or, Bool.not_eq_true'] at hdisj
                  rwa [← borrowProjOverlap_borrowProjSteps]
        refine ⟨⟨upd e_q, ?_, ?_, ?_, ?_⟩, hq_peers⟩
        · rw [lookupBorrow_map_eq (fun e => (hupd_fields e).1) pv_q.tag, hlk_q]
          rfl
        · rcases hkeep_q with hsame | hact_q
          · rwa [hsame]
          · simp [hact_q]
        · intro hmut_q
          rcases hkeep_q with hsame | hact_q
          · rw [hsame]; exact hnf_q hmut_q
          · simp [hact_q]
        · intro qp hqp
          rw [(hupd_fields e_q).2.1, (hupd_fields e_q).2.2.1]
          exact hq_tgt qp hqp
      · simp only [hkeep, Bool.false_eq_true, ↓reduceIte]
        trivial

/-! ## Anneal -/

/-- Anneal's assignment to the root local `_i` (not a borrow target) of an
rvalue that pushes `entry` targeting `q.local_` onto `borrowsAfterRead` and
returns `s.memory.nextTag`. -/
theorem evalStmt_assign_pushBorrow_on (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i : Nat) (rv : Rvalue) (entry : BorrowEntry)
    (borrowsAfterRead : List BorrowEntry) (q : Place)
    (hq_loc : entry.targetLocal = q.local_)
    (span : String)
    (hrv : evalRvalue s.frame.locals rv s.memory decls layouts =
      .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals
        { s.memory with
          borrows := entry :: borrowsAfterRead,
          nextTag := s.memory.nextTag + 1 })
    (hi : i < s.frame.locals.length)
    (hbor : ∀ e ∈ borrowsAfterRead, e.targetLocal ≠ i) (hqi : q.local_ ≠ i)
    (hprot : s.memory.activeProtectors = []) :
    (s.frame.locals[i]? ≠ some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8)))
          { s.memory with
            borrows := entry :: borrowsAfterRead,
            nextTag := s.memory.nextTag + 1 }))) ∧
    (s.frame.locals[i]? = some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hi]
  have hinv : invalidateConflictingBorrows (entry :: borrowsAfterRead)
      i .none = entry :: borrowsAfterRead := by
    apply invalidateConflictingBorrows_of_ne
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · rwa [hq_loc]
    · exact hbor e he'
  refine ⟨fun hlive => ?_, fun hdead => ?_⟩
  · have hlive' : s.frame.locals[i] ≠ .dead := fun h => hlive (by rw [hs, h])
    simp only [evalStmt, hrv, get?, hs, set?, hi, ↓reduceIte, hprot, hinv]
    cases hsl : s.frame.locals[i] with
    | dead => exact absurd hsl hlive'
    | uninit => rfl
    | init v => rfl
  · simp [evalStmt, hrv, get?, hdead]

/-- Anneal's assignment to the root local `_i` (not a borrow target) of an
rvalue that pushes `entry` targeting `q.local_` and returns `s.memory.nextTag`. -/
theorem evalStmt_assign_pushBorrow (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i : Nat) (rv : Rvalue) (entry : BorrowEntry) (q : Place)
    (hq_loc : entry.targetLocal = q.local_)
    (span : String)
    (hrv : evalRvalue s.frame.locals rv s.memory decls layouts =
      .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals
        { s.memory with
          borrows := entry :: s.memory.borrows,
          nextTag := s.memory.nextTag + 1 })
    (hi : i < s.frame.locals.length)
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) (hqi : q.local_ ≠ i)
    (hprot : s.memory.activeProtectors = []) :
    (s.frame.locals[i]? ≠ some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8)))
          { s.memory with
            borrows := entry :: s.memory.borrows,
            nextTag := s.memory.nextTag + 1 }))) ∧
    (s.frame.locals[i]? = some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) :=
  evalStmt_assign_pushBorrow_on s decls layouts i rv entry s.memory.borrows q hq_loc span hrv
    hi hbor hqi hprot

/-- Anneal's `_i = &raw mutbl q` on a live borrow target `q` (neither a
dereference nor indexed): a fresh entry is pushed and its tag stored in `_i`
(UB when `_i` is dead). -/
theorem evalStmt_assign_rawPtr (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i : Nat) (mutbl : MirAst.Mutability) (q : Place)
    (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec layouts decls q = some (pointeeIt, relOff))
    (span : String) (hnd : ∀ rest, q.projection ≠ .deref :: rest)
    (hni : noIndexProj q.projection = true) (slotq : LocalSlot)
    (hsq : s.frame.locals[q.local_]? = some slotq) (hliveq : slotq ≠ .dead)
    (hi : i < s.frame.locals.length)
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) (hqi : q.local_ ≠ i)
    (hprot : s.memory.activeProtectors = []) :
    (s.frame.locals[i]? ≠ some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ (.rawPtr mutbl q), span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8)))
          { s.memory with
            borrows := rawPtrEntry s.memory.nextTag mutbl q :: s.memory.borrows,
            nextTag := s.memory.nextTag + 1 }))) ∧
    (s.frame.locals[i]? = some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ (.rawPtr mutbl q), span⟩ decls layouts = MirStepNode.fail .ub) :=
  evalStmt_assign_pushBorrow s decls layouts i (.rawPtr mutbl q)
    (rawPtrEntry s.memory.nextTag mutbl q) q rfl span
    (evalRvalue_rawPtr_local s.frame.locals mutbl q s.memory decls layouts
      (sharedBorrowPerm_of_ptrTargetSpec hspec) hnd hni slotq hsq hliveq)
    hi hbor hqi hprot

/-- Anneal's `_i = &q` / `_i = &mut q` / `_i = &two_phase mut q` on a live
borrow target `q` in the fragment: pushes `refBorrowEntry nextTag bkind q` and
stores its tag in `_i` (UB when `_i` is dead). -/
theorem evalStmt_assign_ref (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i : Nat) (bkind : MirAst.BorrowKind)
    (q : Place) (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec layouts decls q = some (pointeeIt, relOff))
    (span : String) (hnd : ∀ rest, q.projection ≠ .deref :: rest)
    (hni : noIndexProj q.projection = true) (slotq : LocalSlot)
    (hsq : s.frame.locals[q.local_]? = some slotq) (hliveq : slotq ≠ .dead)
    (hi : i < s.frame.locals.length)
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) (hqi : q.local_ ≠ i)
    (hprot : s.memory.activeProtectors = []) :
    (s.frame.locals[i]? ≠ some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ (.ref bkind q), span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8)))
          { s.memory with
            borrows := refBorrowEntry s.memory.nextTag bkind q :: s.memory.borrows,
            nextTag := s.memory.nextTag + 1 }))) ∧
    (s.frame.locals[i]? = some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ (.ref bkind q), span⟩ decls layouts = MirStepNode.fail .ub) :=
  evalStmt_assign_pushBorrow s decls layouts i (.ref bkind q)
    (refBorrowEntry s.memory.nextTag bkind q) q rfl span
    (evalRvalue_ref_local s.frame.locals bkind q s.memory decls layouts pointeeIt relOff
      hspec hnd hni slotq hsq hliveq)
    hi hbor hqi hprot

/-- Anneal's `_i = &raw mutbl (*_p)` through an initialized pointer/reference
local `_p` whose entry `parentEntry` has compatible permission. -/
theorem evalStmt_assign_rawPtr_reborrow (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i : Nat) (mutbl : MirAst.Mutability) (p : Nat)
    (dp : LocalDecl) (srcMutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (hdp : decls[p]? = some dp) (hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt))
    (span : String)
    (parentPtr : ProvenancePtr) (hp : s.frame.locals[p]? = some (.init (.ptr parentPtr 8)))
    (parentEntry : BorrowEntry) (he : lookupBorrow s.memory.borrows parentPtr.tag = some parentEntry)
    (hthin : needsThinPtrElemResolution parentEntry.targetProjection parentPtr.offsetBytes = false)
    (hndis : parentEntry.perm ≠ .disabled)
    (hmut : mutbl = .mut → parentEntry.perm = .active ∨ parentEntry.perm = .reserved)
    (hi : i < s.frame.locals.length)
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hprot : s.memory.activeProtectors = []) :
    (s.frame.locals[i]? ≠ some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ (.rawPtr mutbl ⟨p, [.deref]⟩), span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8)))
          { s.memory with
            borrows := rawReborrowEntry s.memory.nextTag mutbl parentEntry parentPtr.tag ::
              s.memory.borrows,
            nextTag := s.memory.nextTag + 1 }))) ∧
    (s.frame.locals[i]? = some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ (.rawPtr mutbl ⟨p, [.deref]⟩), span⟩ decls layouts =
        MirStepNode.fail .ub) :=
  evalStmt_assign_pushBorrow s decls layouts i (.rawPtr mutbl ⟨p, [.deref]⟩)
    (rawReborrowEntry s.memory.nextTag mutbl parentEntry parentPtr.tag)
    ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ rfl span
    (evalRvalue_rawPtr_reborrow s.frame.locals mutbl p s.memory decls layouts dp srcMutbl
      pointeeIt hdp hp_ty parentPtr hp parentEntry he hndis hmut hthin)
    hi hbor (hbor parentEntry (lookupBorrow_mem_and_tag he).1) hprot

/-- Anneal's `_i = &(*_p)` / `_i = &mut (*_p)` / `_i = &two_phase mut (*_p)`
through an initialized pointer/reference local `_p` whose entry `parentEntry`
has compatible permission. -/
theorem evalStmt_assign_ref_reborrow (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i : Nat) (bkind : MirAst.BorrowKind)
    (p : Nat)
    (dp : LocalDecl) (srcMutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (hdp : decls[p]? = some dp) (hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt))
    (span : String)
    (parentPtr : ProvenancePtr) (hp : s.frame.locals[p]? = some (.init (.ptr parentPtr 8)))
    (parentEntry : BorrowEntry) (he : lookupBorrow s.memory.borrows parentPtr.tag = some parentEntry)
    (hthin : needsThinPtrElemResolution parentEntry.targetProjection parentPtr.offsetBytes = false)
    (hndis : parentEntry.perm ≠ .disabled)
    (hmut : borrowKindMutbl bkind = .mut → parentEntry.perm = .active ∨ parentEntry.perm = .reserved)
    (hi : i < s.frame.locals.length)
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hprot : s.memory.activeProtectors = []) :
    (s.frame.locals[i]? ≠ some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ (.ref bkind ⟨p, [.deref]⟩), span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8)))
          { s.memory with
            borrows := refReborrowEntry s.memory.nextTag bkind parentEntry parentPtr.tag ::
              MirSemantics.freezeTreeBorrowsOnReadAtProj s.memory.borrows s.memory.borrows
                parentEntry.targetLocal (some parentPtr.tag) parentEntry.targetProjection
                parentEntry.rangeOffset parentEntry.rangeLen,
            nextTag := s.memory.nextTag + 1 }))) ∧
    (s.frame.locals[i]? = some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ (.ref bkind ⟨p, [.deref]⟩), span⟩ decls layouts =
        MirStepNode.fail .ub) := by
  have hbor_frz : ∀ e ∈ MirSemantics.freezeTreeBorrowsOnReadAtProj s.memory.borrows s.memory.borrows
      parentEntry.targetLocal (some parentPtr.tag) parentEntry.targetProjection
      parentEntry.rangeOffset parentEntry.rangeLen, e.targetLocal ≠ i := by
    intro e' he'
    rw [freezeTreeBorrowsOnReadAtProj_eq_map, List.mem_map] at he'
    obtain ⟨e, he_mem, rfl⟩ := he'
    have hf := updateBorrowPermOnReadAtProj_freezeOrSelf s.memory.borrows
      parentEntry.targetLocal (some parentPtr.tag) parentEntry.targetProjection
      parentEntry.rangeOffset parentEntry.rangeLen
    rw [hf.targetLocal]
    exact hbor e he_mem
  exact evalStmt_assign_pushBorrow_on s decls layouts i (.ref bkind ⟨p, [.deref]⟩)
    (refReborrowEntry s.memory.nextTag bkind parentEntry parentPtr.tag)
    (MirSemantics.freezeTreeBorrowsOnReadAtProj s.memory.borrows s.memory.borrows
      parentEntry.targetLocal (some parentPtr.tag) parentEntry.targetProjection
      parentEntry.rangeOffset parentEntry.rangeLen)
    ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ rfl span
    (evalRvalue_ref_reborrow s.frame.locals bkind p s.memory decls layouts dp srcMutbl
      pointeeIt hdp hp_ty parentPtr hp parentEntry he hndis hmut hthin)
    hi hbor_frz (hbor parentEntry (lookupBorrow_mem_and_tag he).1) hprot

theorem evalStmt_assign_ub (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (dst : Place) (rv : Rvalue) (span : String)
    (hu : evalRvalue s.frame.locals rv s.memory decls layouts = .ub) :
    evalStmt s ⟨.assign dst rv, span⟩ decls layouts = MirStepNode.fail .ub := by
  simp [evalStmt, hu]

/-- Anneal's read through a pointer to a live borrow target is a read of the
borrowed place. -/
theorem evalOperand_deref_eq_target (locals : List LocalSlot) (p : Nat)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (layouts : Layout.LayoutTable) (callerLocals : List LocalSlot)
    (ptrVal : ProvenancePtr) (sz : Nat) (hp : locals[p]? = some (.init (.ptr ptrVal sz)))
    (entry : BorrowEntry) (he : lookupBorrow borrows ptrVal.tag = some entry)
    (hthin : needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes = false)
    (hperm : entry.perm ≠ .disabled)
    (hnd : ∀ rest, entry.targetProjection ≠ .deref :: rest)
    (slot : LocalSlot) (ht : locals[entry.targetLocal]? = some slot) :
    evalOperand locals (.copy ⟨p, [.deref]⟩) borrows globals layouts callerLocals =
      evalOperand locals (.copy ⟨entry.targetLocal, entry.targetProjection⟩) borrows globals
        layouts callerLocals := by
  have happ := appendProjections_nil_right
  cases hpe : entry.perm with
  | disabled => exact absurd hpe hperm
  | _ =>
    cases htp : entry.targetProjection with
    | nil =>
      cases slot <;> simp [evalOperand, get?, hp, he, hpe, ht, htp]
    | cons ph pt =>
      have hph : ph ≠ .deref := fun h => hnd pt (by rw [htp, h])
      have hpt : appendProjections pt [] = pt := appendProjections_nil_right pt
      have hthin' : needsThinPtrElemResolution (ph :: pt) ptrVal.offsetBytes = false := by
        rwa [← htp]
      cases ph with
      | deref => exact absurd rfl hph
      | _ => cases slot <;> simp [evalOperand, get?, hp, he, hpe, ht, htp, hpt, hthin']

/-- Anneal's assignment to the root local `_i` (not a borrow target) of an
rvalue that evaluates without changing the slots or the memory. -/
theorem evalStmt_assign_val (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i : Nat) (rv : Rvalue) (span : String)
    (hi : i < s.frame.locals.length)
    (hbor : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i) (hprot : s.memory.activeProtectors = []) :
    (∀ v, evalRvalue s.frame.locals rv s.memory decls layouts = .ok v s.frame.locals s.memory →
      (s.frame.locals[i]? ≠ some .dead →
        evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
          .tau (.running (advanceStmt s (s.frame.locals.set i (.init v)) s.memory))) ∧
      (s.frame.locals[i]? = some .dead →
        evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub)) ∧
    (evalRvalue s.frame.locals rv s.memory decls layouts = .ub →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hi]
  have hinv := invalidateConflictingBorrows_of_ne s.memory.borrows i .none hbor
  refine ⟨fun v hv => ⟨fun hlive => ?_, fun hdead => ?_⟩, fun hu => ?_⟩
  · have hlive' : s.frame.locals[i] ≠ .dead := fun h => hlive (by rw [hs, h])
    simp only [evalStmt, hv, get?, hs, set?, hi, ↓reduceIte, hprot, hinv]
    cases hsl : s.frame.locals[i] with
    | dead => exact absurd hsl hlive'
    | uninit => simp [MirStepNode.step, memory_mk_nil_prot s.memory hprot]
    | init w => simp [MirStepNode.step, memory_mk_nil_prot s.memory hprot]
  · simp [evalStmt, hv, get?, hdead]
  · simp [evalStmt, hu]

theorem ptrPointeeOf_bind_of_rawPtrPointeeOf {decls : List LocalDecl} {p : Nat}
    {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (h : (decls[p]? >>= (rawPtrPointeeOf ·.ty)) = some (mutbl, it)) :
    (decls[p]? >>= (ptrPointeeOf ·.ty)) = some (mutbl, it) := by
  cases hdp : decls[p]? with
  | none => simp [hdp] at h
  | some dp =>
    simp only [hdp, Option.bind_eq_bind, Option.bind_some] at h ⊢
    exact (ptrPointeeOf_of_rawPtrPointeeOf h).1

theorem ptrPointeeOf_bind_of_refPointeeOf {decls : List LocalDecl} {p : Nat}
    {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (h : (decls[p]? >>= (refPointeeOf ·.ty)) = some (mutbl, it)) :
    (decls[p]? >>= (ptrPointeeOf ·.ty)) = some (mutbl, it) := by
  cases hdp : decls[p]? with
  | none => simp [hdp] at h
  | some dp =>
    simp only [hdp, Option.bind_eq_bind, Option.bind_some] at h ⊢
    exact (ptrPointeeOf_of_refPointeeOf h).1

/-- Anneal's evaluation of a pointer- or reference-copying fragment rvalue
(`copy _p`, `PtrToPtr(copy _p)`, `Transmute(copy _p)`, or `Offset(copy _p, 0)`):
the pointer held by `_p`. -/
theorem evalRvalue_ptrRvalue {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType} {isRef : Bool} {rv : Rvalue}
    (hok : ptrRvalueOk layouts decls mutbl pointeeIt isRef rv = true)
    (hnraw : ∀ m q, rv ≠ .rawPtr m q) (hnref : ∀ bk q, rv ≠ .ref bk q) :
    ∃ p, p < decls.length ∧ .copy ⟨p, []⟩ ∈ rvOperands rv ∧
      (∃ srcMutbl, (decls[p]? >>= (ptrPointeeOf ·.ty)) = some (srcMutbl, pointeeIt) ∧
        (mutbl = .mut → srcMutbl = .mut)) ∧
      ∀ (locals : List LocalSlot) (mem : MirSemantics.Memory),
        (∀ pv, pv.offsetBytes = 0 → locals[p]? = some (.init (.ptr pv 8)) →
          (ptrOffsetSrcOf rv = some p →
            ∃ (entry : BorrowEntry) (relOff : Nat),
              lookupBorrow mem.borrows pv.tag = some entry ∧
              entry.perm ≠ .disabled ∧
              ptrTargetSpec layouts decls ⟨entry.targetLocal, entry.targetProjection⟩ =
                some (pointeeIt, relOff) ∧
              ∃ slot, locals[entry.targetLocal]? = some slot ∧ slot ≠ .dead) →
          evalRvalue locals rv mem decls layouts = .ok (.ptr pv 8) locals mem) ∧
        ((locals[p]? = some .uninit ∨ locals[p]? = some .dead) →
          evalRvalue locals rv mem decls layouts = .ub) := by
  cases rv with
  | rawPtr m q => exact absurd rfl (hnraw m q)
  | ref bk q => exact absurd rfl (hnref bk q)
  | use op =>
    cases op with
    | copy pl =>
      obtain ⟨p, projs⟩ := pl
      cases projs with
      | nil =>
        simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        have hpt : (decls[p]? >>= (ptrPointeeOf ·.ty)) = some (mutbl, pointeeIt) := by
          cases isRef with
          | false => exact ptrPointeeOf_bind_of_rawPtrPointeeOf (by simpa using hok.2)
          | true => exact ptrPointeeOf_bind_of_refPointeeOf (by simpa using hok.2)
        refine ⟨p, hok.1, by simp [rvOperands], ⟨mutbl, hpt, fun h => h⟩,
          fun locals mem => ⟨fun pv _ hp _ => ?_, fun hu => ?_⟩⟩
        · simp [evalRvalue, evalOperand, get?, hp, readProjectedValue]
        · rcases hu with hu | hu <;> simp [evalRvalue, evalOperand, get?, hu]
      | cons _ _ => simp [ptrRvalueOk] at hok
    | _ => simp [ptrRvalueOk] at hok
  | cast k op castTy =>
    cases k with
    | ptrToPtr =>
      cases op with
      | copy pl =>
        obtain ⟨p, projs⟩ := pl
        cases projs with
        | nil =>
          simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨⟨⟨_, hp⟩, hcast_raw⟩, hsrc⟩ := hok
          cases hsp : (decls[p]? >>= (rawPtrPointeeOf ·.ty)) with
          | none => simp [hsp] at hsrc
          | some pr =>
            obtain ⟨srcMutbl, srcIt⟩ := pr
            simp only [hsp, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hsrc
            obtain ⟨hit, hm⟩ := hsrc
            subst hit
            have hpt_bind := ptrPointeeOf_bind_of_rawPtrPointeeOf hsp
            cases hdp : decls[p]? with
            | none => simp [hdp] at hpt_bind
            | some dp =>
              have hsrc_pt : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt) := by
                simpa [hdp] using hpt_bind
              refine ⟨p, hp, by simp [rvOperands],
                ⟨srcMutbl, hpt_bind, fun h => ?_⟩,
                fun locals mem => ⟨fun pv _ hpv _ =>
                  (evalRvalue_ptrToPtr_of_rawPtrPointeeOf locals p castTy mem decls layouts
                    hdp hsrc_pt hcast_raw).1 pv 8 hpv,
                  fun hu =>
                  (evalRvalue_ptrToPtr_of_rawPtrPointeeOf locals p castTy mem decls layouts
                    hdp hsrc_pt hcast_raw).2 hu⟩⟩
              rcases hm with hm | hm
              · exact hm
              · subst h; cases hm
        | cons _ _ => simp [ptrRvalueOk] at hok
      | _ => simp [ptrRvalueOk] at hok
    | transmute =>
      cases op with
      | copy pl =>
        obtain ⟨p, projs⟩ := pl
        cases projs with
        | nil =>
          simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨⟨hp, hcast⟩, hsrc⟩ := hok
          have hdst : ptrPointeeOf castTy = some (mutbl, pointeeIt) := by
            cases isRef with
            | false => exact (ptrPointeeOf_of_rawPtrPointeeOf (by simpa using hcast)).1
            | true => exact (ptrPointeeOf_of_refPointeeOf (by simpa using hcast)).1
          cases hsp : (decls[p]? >>= (ptrPointeeOf ·.ty)) with
          | none => simp [hsp] at hsrc
          | some pr =>
            obtain ⟨srcMutbl, srcIt⟩ := pr
            simp only [hsp, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hsrc
            obtain ⟨hit, hm⟩ := hsrc
            subst srcIt
            cases hdp : decls[p]? with
            | none => simp [hdp] at hsp
            | some dp =>
              have hsrc_pt : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt) := by
                simpa [hdp] using hsp
              refine ⟨p, hp, by simp [rvOperands],
                ⟨srcMutbl, hsp, fun h => ?_⟩,
                fun locals mem => ⟨fun pv hoff hpv _ =>
                  (evalRvalue_transmute_ptr locals p castTy mem decls layouts
                    hdp hsrc_pt hdst).1 pv hoff hpv,
                  fun hu =>
                  (evalRvalue_transmute_ptr locals p castTy mem decls layouts
                    hdp hsrc_pt hdst).2 hu⟩⟩
              rcases hm with hm | hm
              · exact hm
              · subst h; cases hm
        | cons _ _ => simp [ptrRvalueOk] at hok
      | _ => simp [ptrRvalueOk] at hok
    | _ => simp [ptrRvalueOk] at hok
  | binaryOp bop l r =>
    cases bop with
    | offset =>
      cases l with
      | copy pl =>
        obtain ⟨p, projs⟩ := pl
        cases projs with
        | nil =>
          cases r with
          | constant c =>
            simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
            obtain ⟨⟨⟨_, hp⟩, hpt⟩, hz⟩ := hok
            obtain ⟨rIt, hval, _, _⟩ := zeroOffsetConstOk_iff.mp hz
            cases hdp : decls[p]? with
            | none => simp [hdp] at hpt
            | some dp =>
              have hpt_raw : rawPtrPointeeOf dp.ty = some (mutbl, pointeeIt) := by
                simpa [hdp] using hpt
              refine ⟨p, hp, by simp [rvOperands],
                ⟨mutbl, ptrPointeeOf_bind_of_rawPtrPointeeOf hpt, fun h => h⟩,
                fun locals mem => ⟨fun pv hoff0 hpv hoff_pre => ?_, fun hu => ?_⟩⟩
              · obtain ⟨entry, relOff, hlk, hndis, htspec, slot, hslot, hndead⟩ :=
                  hoff_pre (by simp [ptrOffsetSrcOf])
                have hop_l : evalOperand locals (.copy ⟨p, []⟩) mem.borrows mem.globals
                    layouts mem.callerLocals = .ok (.ptr pv 8) locals := by
                  simp [evalOperand, get?, hpv, readProjectedValue]
                have hop_r : evalOperand locals (.constant c) mem.borrows mem.globals
                    layouts mem.callerLocals = .ok (.scalar ⟨0, rIt.size.bytes⟩) locals := by
                  simp [evalOperand, hval, evalConstValue]
                have hbin := evalPtrOffsetBinOp_zero locals mem decls layouts p dp mutbl pointeeIt
                  pv entry relOff rIt.size.bytes hdp hpt_raw hoff0 hlk hndis htspec
                  ⟨slot, hslot, hndead⟩
                simp [evalRvalue, hop_l, hop_r, hbin]
              · rcases hu with hu | hu <;> simp [evalRvalue, evalOperand, get?, hu]
          | _ => simp [ptrRvalueOk] at hok
        | cons _ _ => simp [ptrRvalueOk] at hok
      | _ => simp [ptrRvalueOk] at hok
    | _ => simp [ptrRvalueOk] at hok
  | _ => simp [ptrRvalueOk] at hok

/-- Anneal's write `(*_p) = rv` through an initialized pointer or reference:
writes `rv`'s value to the target place and invalidates conflicting borrows via
`invalidateDerefWriteBorrows`. -/
theorem evalStmt_assign_derefWrite (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (p : Nat) (rv : Rvalue) (span : String)
    (hprot : s.memory.activeProtectors = []) (hcl : s.memory.callerLocals = []) :
    (∀ v locals', evalRvalue s.frame.locals rv s.memory decls layouts = .ok v s.frame.locals s.memory →
      writePlaceValue s.frame.locals s.memory.borrows ⟨p, [.deref]⟩ v = .ok locals' →
      evalStmt s ⟨.assign ⟨p, [.deref]⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s locals'
          { s.memory with
            borrows := invalidateDerefWriteBorrows s.frame.locals s.memory.borrows ⟨p, [.deref]⟩ [] }))) ∧
    (∀ v, evalRvalue s.frame.locals rv s.memory decls layouts = .ok v s.frame.locals s.memory →
      writePlaceValue s.frame.locals s.memory.borrows ⟨p, [.deref]⟩ v = .ub →
      evalStmt s ⟨.assign ⟨p, [.deref]⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) ∧
    (evalRvalue s.frame.locals rv s.memory decls layouts = .ub →
      evalStmt s ⟨.assign ⟨p, [.deref]⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  refine ⟨fun v locals' hv hw => ?_, fun v hv hw => ?_, fun hu => ?_⟩
  · simp only [evalStmt, hv, evalPlaceWrite, hprot, hw]
    cases hm : s.memory
    simp_all [MirStepNode.step]
  · simp only [evalStmt, hv, evalPlaceWrite, hprot, hw, hcl]
  · simp [evalStmt, hu]

/-- Anneal's write `(*_p) = rv` through an initialized pointer or reference when
`rv` may move out of source locals (`moveKind rv = true`): evaluates `rv` via
`copyRv rv`, de-initializes moved-out locals in `rvPost s.frame.locals rv`,
writes `v` through `*_p` on `rvPost s.frame.locals rv`, and invalidates
conflicting borrows via `invalidateDerefWriteBorrows`. -/
theorem evalStmt_assign_derefWrite_move (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (p : Nat) (rv : Rvalue) (span : String)
    (hk : moveKind rv = true) (hr : readsOk [] (rvOperands rv) = true)
    (hframe : MoveFrameOk s.frame.locals s.memory.borrows rv)
    (hprot : s.memory.activeProtectors = []) (hcl : s.memory.callerLocals = []) :
    (∀ v locals', evalRvalue s.frame.locals (copyRv rv) s.memory decls layouts =
          .ok v s.frame.locals s.memory →
      writePlaceValue (rvPost s.frame.locals rv) s.memory.borrows ⟨p, [.deref]⟩ v = .ok locals' →
      evalStmt s ⟨.assign ⟨p, [.deref]⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s locals'
          { s.memory with
            borrows := invalidateDerefWriteBorrows (rvPost s.frame.locals rv) s.memory.borrows
              ⟨p, [.deref]⟩ [] }))) ∧
    (∀ v, evalRvalue s.frame.locals (copyRv rv) s.memory decls layouts =
          .ok v s.frame.locals s.memory →
      writePlaceValue (rvPost s.frame.locals rv) s.memory.borrows ⟨p, [.deref]⟩ v = .ub →
      evalStmt s ⟨.assign ⟨p, [.deref]⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) ∧
    (evalRvalue s.frame.locals (copyRv rv) s.memory decls layouts = .ub →
      evalStmt s ⟨.assign ⟨p, [.deref]⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hR := evalRvalue_move s.frame.locals rv hk hr hframe s.memory decls layouts
  refine ⟨fun v locals' hv hw => ?_, fun v hv hw => ?_, fun hu => ?_⟩
  · simp only [evalStmt]
    rw [hR, hv]
    simp only [rvWithLocals, evalPlaceWrite, hprot, hw]
    cases hm : s.memory
    simp_all [MirStepNode.step]
  · simp only [evalStmt]
    rw [hR, hv]
    simp only [rvWithLocals, evalPlaceWrite, hprot, hw, hcl]
  · simp only [evalStmt]
    rw [hR, hu]
    rfl

theorem invalidateDerefWriteBorrows_congr_local {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} (L1 L2 : List LocalSlot)
    (borrows : List BorrowEntry) (p : Nat) (ptrVal : ProvenancePtr) (entry : BorrowEntry)
    {pointeeIt : Gen.IntType} {relOff : Nat}
    (htspec : ptrTargetSpec layouts decls ⟨entry.targetLocal, entry.targetProjection⟩ =
      some (pointeeIt, relOff))
    (hoff0 : ptrVal.offsetBytes = 0)
    (hp1 : L1[p]? = some (.init (.ptr ptrVal 8)))
    (hp2 : L2[p]? = some (.init (.ptr ptrVal 8)))
    (he : lookupBorrow borrows ptrVal.tag = some entry)
    (hrlen : entry.rangeLen = 0) (hroff : entry.rangeOffset = 0) :
    invalidateDerefWriteBorrows L1 borrows ⟨p, [.deref]⟩ [] =
      invalidateDerefWriteBorrows L2 borrows ⟨p, [.deref]⟩ [] := by
  have hfull1 := resolveDerefWriteFullProj_of_ptrTargetSpec L1 ptrVal entry pointeeIt relOff
    htspec hoff0
  have hfull2 := resolveDerefWriteFullProj_of_ptrTargetSpec L2 ptrVal entry pointeeIt relOff
    htspec hoff0
  rw [invalidateDerefWriteBorrows_eq_map L1 borrows p ptrVal entry hp1 he hrlen hroff hfull1,
    invalidateDerefWriteBorrows_eq_map L2 borrows p ptrVal entry hp2 he hrlen hroff hfull2]

/-! ## MiniRust -/

/-- Two place expressions that evaluate to the same place, the second on the
machine the first leaves behind, make the same assignment. -/
theorem evalStatement_assign_place_eq {m m1 : Mach} {pe pe' : Gen.PlaceExpr} {place : Gen.Place BM}
    {ty : Gen.Type} (e : Gen.ValueExpr)
    (h1 : evalPlace m pe = .ok ((place, ty), m1)) (h2 : evalPlace m1 pe' = .ok ((place, ty), m1)) :
    evalStatement m (.Assign pe e) = evalStatement m1 (.Assign pe' e) := by
  simp [evalStatement, h1, h2]

/-- Two place expressions that evaluate to the same place, the second on the
machine the first leaves behind, load the same value. -/
theorem evalValue_load_place_eq {m m1 : Mach} {pe pe' : Gen.PlaceExpr} {place : Gen.Place BM}
    {ty : Gen.Type}
    (h1 : evalPlace m pe = .ok ((place, ty), m1)) (h2 : evalPlace m1 pe' = .ok ((place, ty), m1)) :
    evalValue m (.Load pe) = evalValue m1 (.Load pe') := by
  simp [evalValue, h1, h2]

@[simp] theorem computeAlign_sized (m : Mach) (sz : Size) (al : Align) :
    computeAlign m (.Sized sz al) none = .ok al := rfl

@[simp] theorem computeSize_sized_none (m : Mach) (sz : Size) (al : Align) :
    computeSize m (.Sized sz al) none = .ok sz := rfl

/-- `ValueExpr::AddrOf` of a place expression that evaluates to a valid thin
pointer of `ptrTy` on the resulting machine `m1`. -/
theorem evalValue_addrOf_of {m m1 : Mach} {ctx : Ctx} {A : List Gen.Allocation}
    {f1 f2 : Frame} {rest : List Frame} (hsh : Shape m1 ctx (f1 :: f2 :: rest) A)
    {targetPe : Gen.PlaceExpr} {T : Gen.Type} (ptrTy : Gen.PtrType) (a : Int) (pr : Option Prov)
    (hev : evalPlace m targetPe =
      .ok (({ ptr := { thin_pointer := { addr := a, provenance := pr }, metadata := none },
               aligned := true }, T), m1))
    (hck : checkValue (m := some m1)
      (.Ptr { thin_pointer := { addr := a, provenance := pr }, metadata := none })
      (.Ptr ptrTy) = .ok ()) :
    evalValue m (.AddrOf targetPe ptrTy) =
      .ok ((.Ptr { thin_pointer := { addr := a, provenance := pr }, metadata := none },
            .Ptr ptrTy), m1) := by
  have hrt := retagPtrBM_shape hsh
    { thin_pointer := { addr := a, provenance := pr }, metadata := none }
  rw [evalValue, hev, ok_bind]
  dsimp only []
  rw [hck, ok_bind, hrt, ok_bind]
  rfl

theorem evalValue_addrOf_place_ub {m : Mach} {targetPe : Gen.PlaceExpr} {ptrTy : Gen.PtrType}
    {msg : String} (hev : evalPlace m targetPe = .error (.ub msg)) :
    evalValue m (.AddrOf targetPe ptrTy) = .error (.ub msg) := by
  rw [evalValue, hev]
  rfl

/-- `Machine::eval_statement` on an assignment to a local whose place
evaluates without changing the machine: the store of the source's value. -/
theorem evalStatement_assign_local_eq {m m1 : Mach} {e : Gen.ValueExpr} {p : Ptr}
    {T T' : Gen.Type} (i : Nat) (v : Val)
    (hplace : evalPlace m (.Local (localName i)) =
      .ok (({ ptr := { thin_pointer := p, metadata := none }, aligned := true }, T), m))
    (hm1 : evalValue m e = .ok ((v, T'), m1)) :
    evalStatement m (.Assign (.Local (localName i)) e) = typedStore m1 p v T ⟨1⟩ .None := by
  rw [evalStatement, hplace]
  simp only [ok_bind, hm1, placeStore]
  rfl

/-- `Machine::eval_place` of a dereference `*_p` at the pointee type of the
thin raw pointer or reference local `_p`: it loads `_p`, whose bytes encode the
address of `_p`'s borrow target (`evalPtrLoad`), checks alignment and
dereferenceability for safe reference types, and yields the target's place,
aligned for the pointee type; evaluating the target's own place expression on
the machine after the load yields the same place. -/
theorem evalPlace_deref {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm) (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (p : Nat) (dp : LocalDecl) (srcMutbl : MirAst.Mutability) (it : Gen.IntType)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, it)) :
    (∃ (ptrVal : ProvenancePtr) (entry : BorrowEntry) (relOff : Nat) (m1 : Mach),
      view[p]? = some (.init (.ptr ptrVal 8)) ∧
      ptrVal.offsetBytes = 0 ∧
      lookupBorrow s.memory.borrows ptrVal.tag = some entry ∧
      entry.targetLocal ∈ bodyAddrTakenLocals body ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (it, relOff) ∧
      evalPlace m (.Deref (.Load (.Local (localName p))) (.Int it)) =
        .ok (({ ptr := { thin_pointer := offsetPtr (localPtr ctx entry.targetLocal) relOff,
                         metadata := none }, aligned := true }, .Int it), m1) ∧
      FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m1 blk stmt ∧
      (∀ targetPe, translatePlace body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
          some targetPe →
        evalPlace m1 targetPe =
          .ok (({ ptr := { thin_pointer := offsetPtr (localPtr ctx entry.targetLocal) relOff,
                           metadata := none }, aligned := true }, .Int it), m1))) ∨
    ((view[p]? = some .uninit ∨ view[p]? = some .dead) ∧
      ∃ msg, evalPlace m (.Deref (.Load (.Local (localName p))) (.Int it)) = .error (.ub msg)) := by
  rcases evalPtrLoad h hb hns hfrag p dp srcMutbl it hdp hp_ty with
    ⟨ptrVal, entry, relOff, m1, hv, hoff0, hlookup, hk_addr, htspec, hload, h1⟩ |
      ⟨hnot, msg, hmsg⟩
  · left
    obtain ⟨_, _, hgood, _, _, hal, htgt⟩ :=
      evalTargetPlace h1 hb hns hfrag ⟨entry.targetLocal, entry.targetProjection⟩ it relOff htspec
        hk_addr
    obtain ⟨_, htderef⟩ :=
      evalTargetPlace_deref h1 hb hfrag ⟨entry.targetLocal, entry.targetProjection⟩ it relOff htspec
        hk_addr
    refine ⟨ptrVal, entry, relOff, m1, hv, hoff0, hlookup, hk_addr, htspec, ?_, h1, htgt⟩
    rcases declPtrTy_cases dp.ty with hty | ⟨m', it', href, hty⟩
    · rw [hty] at hload
      rw [evalPlace, hload, ok_bind]
      dsimp only [thinRawPtrTy, PtrType.safe_pointee]
      rw [layout_eq _ hgood, ok_bind, computeAlign_sized, ok_bind, hal]
      rfl
    · obtain ⟨hp', _⟩ := ptrPointeeOf_of_refPointeeOf href
      rw [hp_ty] at hp'
      simp only [Option.some.injEq, Prod.mk.injEq] at hp'
      obtain ⟨rfl, rfl⟩ := hp'
      rw [hty] at hload
      rw [evalPlace, hload, ok_bind]
      dsimp only [refTy, refPtrType, intPointeeInfo, PtrType.safe_pointee]
      have hnot : (!Align.is_aligned ⟨it.size.bytes⟩
          (offsetPtr (localPtr ctx entry.targetLocal) relOff).addr) = false := by
        rw [hal]; rfl
      rw [computeAlign_sized, ok_bind, hnot, ite_eq_right Bool.false_ne_true,
        computeSize_sized_none,
        ok_bind, htderef, ok_bind, layout_eq _ hgood, ok_bind, computeAlign_sized, ok_bind, hal]
      rfl
  · right
    refine ⟨hnot, msg, ?_⟩
    rw [evalPlace, hmsg]
    rfl

theorem ptrPointeeOf_good {t : MirAst.Ty} {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (h : ptrPointeeOf t = some (mutbl, it)) : GoodSize it.size.bytes := by
  unfold ptrPointeeOf at h
  cases hk : t.kind with
  | rawPtr _ pointee | ref _ pointee =>
    rw [hk] at h
    obtain ⟨⟨sg, n⟩, hb, heq⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, rfl⟩ := heq
    exact intTyBytes_good hb
  | _ => rw [hk] at h; cases h

/-- `ValueExpr::AddrOf` of the place of a borrow target at `PtrType::Raw(None)`:
the pointer to the target's bytes, together with its non-null, aligned,
dereferenceable target bounds. -/
theorem evalValue_addrOf {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm) (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (q : Place) (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    (hk_addr : q.local_ ∈ bodyAddrTakenLocals body)
    (targetPe : Gen.PlaceExpr) (hpe : translatePlace body.localDecls q = some targetPe) :
    let tAddr := (ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat
    let tProv : Option Prov := some (⟨((ctx.base.length + q.local_ : Nat) : Int)⟩, ())
    0 < tAddr ∧
    tAddr < 2 ^ 64 ∧
    Align.is_aligned ⟨pointeeIt.size.bytes⟩ (tAddr : Int) = true ∧
    CM.dereferenceable m.mem { addr := (tAddr : Int), provenance := tProv } pointeeIt.size = .ok () ∧
    evalValue m (.AddrOf targetPe (.Raw .None)) =
      .ok ((.Ptr { thin_pointer := { addr := (tAddr : Int), provenance := tProv }, metadata := none },
            .Ptr (.Raw .None)), m) := by
  obtain ⟨_, _, _, htlt, hptrEq, hal, hev⟩ :=
    evalTargetPlace h hb hns hfrag q pointeeIt relOff hspec hk_addr
  obtain ⟨htpos, htderef⟩ := evalTargetPlace_deref h hb hfrag q pointeeIt relOff hspec hk_addr
  rw [← hptrEq] at hal htderef
  have hev' := hev targetPe hpe
  rw [← hptrEq] at hev'
  have hck := checkValue_thinRawPtr (m? := some m) _ htlt
    (some (⟨((ctx.base.length + q.local_ : Nat) : Int)⟩, ()))
  exact ⟨htpos, htlt, hal, htderef, evalValue_addrOf_of h.shape (.Raw .None) _ _ hev' hck⟩

/-- `ValueExpr::AddrOf` of the place of a borrow target at `refPtrType mutbl pointeeIt`:
the pointer to the target's bytes passes all safe-pointer checks (`checkValue_refTy`). -/
theorem evalValue_addrOf_ref {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm) (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (mutbl : MirAst.Mutability) (q : Place) (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    (hk_addr : q.local_ ∈ bodyAddrTakenLocals body)
    (targetPe : Gen.PlaceExpr) (hpe : translatePlace body.localDecls q = some targetPe) :
    let tAddr := (ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat
    let tProv : Option Prov := some (⟨((ctx.base.length + q.local_ : Nat) : Int)⟩, ())
    0 < tAddr ∧
    tAddr < 2 ^ 64 ∧
    Align.is_aligned ⟨pointeeIt.size.bytes⟩ (tAddr : Int) = true ∧
    CM.dereferenceable m.mem { addr := (tAddr : Int), provenance := tProv } pointeeIt.size = .ok () ∧
    evalValue m (.AddrOf targetPe (refPtrType mutbl pointeeIt)) =
      .ok ((.Ptr { thin_pointer := { addr := (tAddr : Int), provenance := tProv }, metadata := none },
            .Ptr (refPtrType mutbl pointeeIt)), m) := by
  obtain ⟨_, _, hgood, htlt, hptrEq, hal, hev⟩ :=
    evalTargetPlace h hb hns hfrag q pointeeIt relOff hspec hk_addr
  obtain ⟨htpos, htderef⟩ := evalTargetPlace_deref h hb hfrag q pointeeIt relOff hspec hk_addr
  rw [← hptrEq] at hal htderef
  have hev' := hev targetPe hpe
  rw [← hptrEq] at hev'
  have hck := checkValue_refTy m mutbl pointeeIt hgood _ htpos htlt
    (some (⟨((ctx.base.length + q.local_ : Nat) : Int)⟩, ())) hal htderef
  exact ⟨htpos, htlt, hal, htderef,
    evalValue_addrOf_of h.shape (refPtrType mutbl pointeeIt) _ _ hev' hck⟩

/-- `Machine::eval_statement` on an assignment to the live pointer or reference
local `_i` whose source evaluates to a valid thin pointer to a live aligned
stack target: the pointer's bytes are stored in `_i`'s allocation. -/
theorem evalStatement_assign_ptr_of {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    (hpt : ptrPointeeOf d.ty = some (mutbl, pointeeIt))
    (hlive : locals[i]? ≠ some .dead) (e : Gen.ValueExpr)
    (tAddr : Nat) (htpos : 0 < tAddr) (htlt : tAddr < 2 ^ 64) (tProv : Option Prov)
    (htal : Align.is_aligned ⟨pointeeIt.size.bytes⟩ (tAddr : Int) = true)
    (T' : Gen.Type) (m1 : Mach)
    (hm1 : evalValue m e =
      .ok ((.Ptr { thin_pointer := { addr := (tAddr : Int), provenance := tProv }, metadata := none },
            T'), m1))
    (h1 : FrameOk body f ctx locals lm m1 blk stmt)
    (htderef : CM.dereferenceable m1.mem { addr := (tAddr : Int), provenance := tProv } pointeeIt.size = .ok ())
    (pv : ProvenancePtr)
    (htgt : ∀ a pr, ctx.ptrTargets pv.allocId = some (a, pr) → tAddr = a ∧ tProv = pr) :
    ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
      FrameOk body f ctx (locals.set i (.init (.ptr pv 8))) lm m' blk stmt := by
  have hp_ty : isPtrTy d.ty = true := by simp [isPtrTy, hpt]
  have hgood : GoodSize pointeeIt.size.bytes := ptrPointeeOf_good hpt
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨hTd, hitd⟩ := tyOf_isPtrTy (layouts := body.layouts) hp_ty
  have hspec := h.hf.2 i d hd
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  have hslive : slot ≠ .dead := fun hc => hlive (hc ▸ hs)
  obtain ⟨p, hp⟩ := h.locs.some_of_live hs hslive
  obtain ⟨k, data, hpk, _, _, _, _, hlen, hA⟩ :=
    h1.locs.storage_any hd hs hp (h.declsOk d (List.mem_of_getElem? hd))
  rw [hTd, tyBytes_declPtrTy] at hlen
  rw [hitd] at hA
  have hplace := evalPlace_local_some h.shape i _ hspec.2 p hp
  rw [hTd] at hplace
  have hst := typedStore_ptr_declPtrTy h1.shape p k hpk d.ty mutbl pointeeIt hpt hgood
    data tAddr htpos htlt tProv htal htderef hA hlen
  have hstmt := evalStatement_assign_local_eq i _ hplace hm1
  refine ⟨_, hstmt.trans hst, ?_⟩
  refine FrameOk.mk' h.hf (withMem_shape h1.shape _) ?_ h.declsOk
    (h1.nonScalar.set_scalar hd (.inr hp_ty) _)
  have hlo' := h1.locs.store_ptr i d hd hp_ty slot hs pv tAddr tProv htlt htgt p hp k hpk
  rw [hitd] at hlo'
  exact hlo'

/-! ## Borrow targets -/

/-- The shapes of a borrow target (`ptrTargetSpec`): an integer local, an
in-bounds constant element of an array local, or a scalar field chain of a
tuple/struct local. -/
theorem ptrTargetSpec_cases {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    (hdeclsOk : ∀ d ∈ decls, localDeclOk layouts d = true)
    {q : Place} {it : Gen.IntType} {relOff : Nat}
    (h : ptrTargetSpec layouts decls q = some (it, relOff)) :
    q.local_ < decls.length ∧
    ((q.projection = [] ∧ ∃ d, decls[q.local_]? = some d ∧ intTypeOf d.ty = some it) ∨
     (∃ offset minLen fromEnd d count,
        q.projection = [.constantIndex offset minLen fromEnd] ∧ decls[q.local_]? = some d ∧
        arrayTypeOf d.ty = some (it, count) ∧
        projOk decls count (.constantIndex offset minLen fromEnd) = true ∧
        (if fromEnd then 1 ≤ offset ∧ offset ≤ count else offset < count)) ∨
     (∃ idx fieldTy rest, q.projection = .field idx fieldTy :: rest ∧
        placeOk layouts decls it q = true ∧
        (decls[q.local_]? >>= (tupleTypeOf layouts ·.ty)).isSome = true ∧
        ∃ d fields size align relOff', decls[q.local_]? = some d ∧
          tupleTypeOf layouts d.ty = some (fields, size, align) ∧
          resolveFieldPath layouts (.tuple fields size align) (.field idx fieldTy :: rest) =
            some (relOff', .scalar it))) := by
  obtain ⟨k, projs⟩ := q
  cases projs with
  | nil =>
    simp only [ptrTargetSpec] at h
    split at h
    · next hr =>
      cases hd : decls[k]? with
      | none => simp [hd] at h
      | some d =>
        simp only [hd, Option.bind_eq_bind, Option.bind_some, Option.map_eq_some_iff] at h
        obtain ⟨it', hit, heq⟩ := h
        injection heq with h1 _
        subst h1
        exact ⟨hr.2, .inl ⟨rfl, d, rfl, hit⟩⟩
    · simp at h
  | cons p1 prest =>
    cases p1 with
    | constantIndex offset minLen fromEnd =>
      cases prest with
      | nil =>
        simp only [ptrTargetSpec] at h
        split at h
        · next hr =>
          cases hd : decls[k]? with
          | none => simp [hd] at h
          | some d =>
            simp only [hd, Option.bind_eq_bind, Option.bind_some] at h
            cases ha : arrayTypeOf d.ty with
            | none => simp [ha] at h
            | some ap =>
              obtain ⟨elemIt, count⟩ := ap
              simp only [ha] at h
              by_cases hc : minLen ≤ count ∧
                  (if fromEnd then 1 ≤ offset ∧ offset ≤ count else offset < count)
              · simp only [hc, and_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨h1, _⟩ := h
                subst h1
                have hgood := arrayTypeOf_good ha
                refine ⟨hr.2, .inr (.inl ⟨offset, minLen, fromEnd, d, count, rfl, rfl, ha, ?_, hc.2⟩)⟩
                have hbound : count < 2 ^ 63 := by
                  have hpos := hgood.pos
                  have hdok := hdeclsOk d (List.mem_of_getElem? hd)
                  have hlt : count * elemIt.size.bytes < 2 ^ 63 := by
                    simpa [localDeclOk, scalarTypeOf_none_of_arrayTypeOf ha, ha,
                      isPtrTy_false_of_arrayTypeOf ha] using hdok
                  have : count * 1 ≤ count * elemIt.size.bytes := Nat.mul_le_mul_left count hpos
                  omega
                cases fromEnd <;> simp_all [projOk] <;> omega
              · simp [hc] at h
        · simp at h
      | cons _ _ => simp [ptrTargetSpec] at h
    | field idx fieldTy =>
      simp only [ptrTargetSpec] at h
      split at h
      · next hr =>
        cases hd : decls[k]? with
        | none => simp [hd] at h
        | some d =>
          simp only [hd, Option.bind_eq_bind, Option.bind_some] at h
          cases ht : tupleTypeOf layouts d.ty with
          | none => simp [ht] at h
          | some tp =>
            obtain ⟨fields, size, align⟩ := tp
            simp only [ht, Option.bind_some] at h
            cases hres : resolveFieldPath layouts (.tuple fields size align)
                (.field idx fieldTy :: prest) with
            | none => simp [hres] at h
            | some rp =>
              obtain ⟨relOff', leafSpec⟩ := rp
              cases leafSpec with
              | tuple _ _ _ => simp [hres] at h
              | scalar leafIt =>
                simp only [hres, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨h1, _⟩ := h
                subst h1
                refine ⟨hr.2, .inr (.inr ⟨idx, fieldTy, prest, rfl, ?_, by simp [ht],
                  d, fields, size, align, relOff', rfl, ht, hres⟩)⟩
                have hnoibt : intBoolTupleOf d.ty = none := (not_scalar_of_tupleTypeOf ht).2.2.1
                obtain ⟨_, hdk⟩ := List.getElem?_eq_some_iff.mp hd
                simp [placeOk, hr.2, hdk, hnoibt, ht, hres]
      · simp at h
    | _ => simp [ptrTargetSpec] at h

theorem translateFieldPlace_isSome_of_resolveFieldPath {layouts : Layout.LayoutTable}
    {spec leafSpec : TupleSpec} {projs : List ProjectionElem} {roff : Nat}
    (h : resolveFieldPath layouts spec projs = some (roff, leafSpec)) (root : Gen.PlaceExpr) :
    (translateFieldPlace root projs).isSome = true := by
  induction projs generalizing spec roff leafSpec root with
  | nil => rfl
  | cons p tl ih =>
    cases p with
    | field idx fty =>
      cases spec with
      | scalar _ => simp [resolveFieldPath] at h
      | tuple fs sz al =>
        simp only [resolveFieldPath] at h
        cases h1 : fs[idx]? with
        | none => simp [h1] at h
        | some fp =>
          cases h2 : specOfRigidTy layouts fty.kind fty.layoutIdx with
          | none => simp [h1, h2] at h
          | some es =>
            simp only [h1, h2, Option.bind_eq_bind, Option.bind_some] at h
            split at h
            · cases hr : resolveFieldPath layouts fp.2 tl with
              | none => simp [hr] at h
              | some rp =>
                simp only [translateFieldPlace]
                exact ih hr _
            · simp at h
    | _ => cases spec <;> simp [resolveFieldPath] at h

/-- A borrow target is a fragment integer operand place. -/
theorem ptrTargetSpec_operandOk {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    (hdeclsOk : ∀ d ∈ decls, localDeclOk layouts d = true)
    {q : Place} {it : Gen.IntType} {relOff : Nat}
    (h : ptrTargetSpec layouts decls q = some (it, relOff)) :
    operandOk layouts decls it (.copy q) = true := by
  obtain ⟨hk, hcases⟩ := ptrTargetSpec_cases hdeclsOk h
  obtain ⟨k, projs⟩ := q
  simp only at hk hcases
  rcases hcases with ⟨hproj, d, hd, hit⟩ | ⟨offset, minLen, fromEnd, d, count, hproj, hd, ha, hpok, -⟩ |
    ⟨idx, fieldTy, rest, hproj, hplace, _, d, fields, size, align, relOff', hd, ht, hres⟩
  · subst hproj
    obtain ⟨_, hdk⟩ := List.getElem?_eq_some_iff.mp hd
    simp [operandOk, placeOk, hk, hdk, hit, translateOperand, translatePlace]
  · subst hproj
    obtain ⟨_, hdk⟩ := List.getElem?_eq_some_iff.mp hd
    have hpok' := hpok
    simp only [projOk, Bool.and_eq_true, decide_eq_true_eq] at hpok'
    have hcond : minLen ≤ count ∧ (fromEnd = false ∨ 1 ≤ offset ∧ offset ≤ count) := by
      refine ⟨hpok'.1.1, ?_⟩
      cases fromEnd <;> simp_all
    simp [operandOk, placeOk, hk, hdk, ha, hpok, translateOperand, translatePlace, hcond]
  · subst hproj
    simp only [operandOk, hplace, Bool.true_and]
    simp only [translateOperand, translatePlace, Option.isSome_map]
    exact translateFieldPlace_isSome_of_resolveFieldPath hres _

/-- `FrameOk` at `ctxWithBorrows` is stable under a change of the borrow table
that keeps `LocalsOk`. -/
theorem FrameOk.ctxWithBorrows_change {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {b1 b2 : List BorrowEntry} {view : List LocalSlot} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx b1) view lm m blk stmt)
    (hlo : LocalsOk body (ctxWithBorrows body ctx b2) view lm m.mem.memory.allocations) :
    FrameOk body f (ctxWithBorrows body ctx b2) view lm m blk stmt :=
  FrameOk.mk' h.hf ⟨h.shape.threads, h.shape.active, h.shape.allocs⟩ hlo h.declsOk h.nonScalar

theorem borrowPlaceIntType_of_ptrTargetSpec {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {q : Place} {pointeeIt : Gen.IntType} {relOff : Nat}
    (hspec : ptrTargetSpec layouts decls q = some (pointeeIt, relOff)) :
    borrowPlaceIntType layouts decls q = some pointeeIt := by
  obtain ⟨k, projs⟩ := q
  cases projs with
  | nil =>
    simp only [ptrTargetSpec] at hspec
    split at hspec
    · cases hd : decls[k]? with
      | none => simp [hd] at hspec
      | some d =>
        simp only [hd, Option.bind_eq_bind, Option.bind_some, Option.map_eq_some_iff] at hspec
        obtain ⟨it', hit, heq⟩ := hspec
        injection heq with h1 _
        subst h1
        simp [borrowPlaceIntType, placeIntType, hd, hit]
    · simp at hspec
  | cons p1 prest =>
    cases p1 with
    | constantIndex offset minLen fromEnd =>
      cases prest with
      | nil =>
        simp only [ptrTargetSpec] at hspec
        split at hspec
        · cases hd : decls[k]? with
          | none => simp [hd] at hspec
          | some d =>
            simp only [hd, Option.bind_eq_bind, Option.bind_some] at hspec
            cases ha : arrayTypeOf d.ty with
            | none => simp [ha] at hspec
            | some ap =>
              obtain ⟨elemIt, count⟩ := ap
              simp only [ha] at hspec
              by_cases hc : minLen ≤ count ∧ (if fromEnd then 1 ≤ offset ∧ offset ≤ count else offset < count)
              · rw [ite_eq_left hc] at hspec
                simp only [Option.some.injEq, Prod.mk.injEq] at hspec
                obtain ⟨h1, _⟩ := hspec
                subst h1
                simp [borrowPlaceIntType, placeIntType, hd, ha]
              · rw [ite_eq_right hc] at hspec
                cases hspec
        · simp at hspec
      | cons _ _ => simp [ptrTargetSpec] at hspec
    | field idx fieldTy =>
      simp only [ptrTargetSpec] at hspec
      split at hspec
      · cases hd : decls[k]? with
        | none => simp [hd] at hspec
        | some d =>
          simp only [hd, Option.bind_eq_bind, Option.bind_some] at hspec
          cases ht : tupleTypeOf layouts d.ty with
          | none => simp [ht] at hspec
          | some tp =>
            obtain ⟨fields, size, align⟩ := tp
            simp only [ht, Option.bind_some] at hspec
            cases hres : resolveFieldPath layouts (.tuple fields size align)
                (.field idx fieldTy :: prest) with
            | none => simp [hres] at hspec
            | some rp =>
              obtain ⟨relOff', leafSpec⟩ := rp
              cases leafSpec with
              | tuple _ _ _ => simp [hres] at hspec
              | scalar leafIt =>
                simp only [hres, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hspec
                obtain ⟨h1, _⟩ := hspec
                subst h1
                have hnoibt : intBoolTupleOf d.ty = none := (not_scalar_of_tupleTypeOf ht).2.2.1
                simp [borrowPlaceIntType, placeIntType, hd, hnoibt, ht, hres]
      · simp at hspec
    | _ => simp [ptrTargetSpec] at hspec

/-- MiniRust's `_i = &raw mutbl q` (`AddrOf`) into a live pointer local: `_i`
holds the address of `q`, which is the target of the fresh borrow that Anneal
pushes. -/
theorem evalStatement_assign_rawPtr_mr {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm) (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (mutbl : MirAst.Mutability) (q : Place) (pointeeIt : Gen.IntType) (relOff : Nat)
    (hpt : ptrPointeeOf d.ty = some (mutbl, pointeeIt))
    (hlive : view[i]? ≠ some .dead)
    (hspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    (hq_addr : q.local_ ∈ bodyAddrTakenLocals body)
    {targetTy : Option MirAst.Ty} (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy (.rawPtr mutbl q) = some e) :
    ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
      FrameOk body f
        (ctxWithBorrows body ctx (rawPtrEntry s.memory.nextTag mutbl q :: s.memory.borrows))
        (view.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8))) lm m' blk stmt := by
  simp only [translateRvalue, Option.bind_eq_bind] at he
  cases hpe : translatePlace body.localDecls q with
  | none => simp [hpe] at he
  | some targetPe =>
    simp [hpe] at he
    subst he
    obtain ⟨htpos, htlt, htal, htderef, hev⟩ :=
      evalValue_addrOf h hb hns hfrag q pointeeIt relOff hspec hq_addr targetPe hpe
    have hlo' := LocalsOk.rawPtr_extend h.locs hb (rawPtrEntry s.memory.nextTag mutbl q) rfl
    have h' := h.ctxWithBorrows_change hlo'
    refine evalStatement_assign_ptr_of h' i d hd hpt hlive _ _ htpos htlt _ htal _ m hev h'
      htderef ⟨s.memory.nextTag, 0⟩ (fun a pr h2 => ?_)
    simp only [ctxWithBorrows] at h2
    rw [borrowTargets_rawPtr_self body ctx s.memory.nextTag mutbl q s.memory.borrows pointeeIt relOff
      hspec] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact ⟨h2.1, h2.2⟩

/-- MiniRust's `_i = &q` / `_i = &mut q` (`AddrOf` at `PtrType::Ref`) into a
live reference local: `_i` holds the non-null, aligned, dereferenceable address
of `q`, matching the fresh borrow that Anneal pushes. -/
theorem evalStatement_assign_ref_mr {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm) (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (bkind : MirAst.BorrowKind) (q : Place) (pointeeIt : Gen.IntType) (relOff : Nat)
    (hpt : ptrPointeeOf d.ty = some (borrowKindMutbl bkind, pointeeIt))
    (hlive : view[i]? ≠ some .dead)
    (hspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    (hq_addr : q.local_ ∈ bodyAddrTakenLocals body)
    {targetTy : Option MirAst.Ty} (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy (.ref bkind q) = some e) :
    ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
      FrameOk body f
        (ctxWithBorrows body ctx
          (refBorrowEntry s.memory.nextTag bkind q :: s.memory.borrows))
        (view.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8))) lm m' blk stmt := by
  rw [ctxWithBorrows_refBorrowEntry_eq]
  have hbpi := borrowPlaceIntType_of_ptrTargetSpec hspec
  simp only [translateRvalue, borrowPlacePointeeInfo, hbpi, Option.bind_eq_bind, Option.bind_some] at he
  cases hpe : translatePlace body.localDecls q with
  | none => simp [hpe] at he
  | some targetPe =>
    simp [hpe] at he
    subst he
    obtain ⟨htpos, htlt, htal, htderef, hev⟩ :=
      evalValue_addrOf_ref h hb hns hfrag (borrowKindMutbl bkind) q pointeeIt relOff hspec hq_addr
        targetPe hpe
    have hlo' := LocalsOk.rawPtr_extend h.locs hb
      (rawPtrEntry s.memory.nextTag (borrowKindMutbl bkind) q) rfl
    have h' := h.ctxWithBorrows_change hlo'
    refine evalStatement_assign_ptr_of h' i d hd hpt hlive _ _ htpos htlt _ htal _ m hev h'
      htderef ⟨s.memory.nextTag, 0⟩ (fun a pr h2 => ?_)
    simp only [ctxWithBorrows] at h2
    rw [borrowTargets_rawPtr_self body ctx s.memory.nextTag (borrowKindMutbl bkind) q
      s.memory.borrows pointeeIt relOff hspec] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact ⟨h2.1, h2.2⟩

/-- An assignment to a local whose source raises UB raises that UB. -/
theorem evalStatement_assign_ub_of {m : Mach} {i : Nat} {e : Gen.ValueExpr} {pl : Gen.Place BM}
    {T : Gen.Type} {msg : String}
    (hpl : evalPlace m (.Local (localName i)) = .ok ((pl, T), m))
    (he : evalValue m e = .error (.ub msg)) :
    evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg) := by
  simp [evalStatement, hpl, he]

/-- MiniRust's reborrow `_i = &raw mutbl (*_p)` or `_i = &(*_p)` / `_i = &mut (*_p)`
into the pointer or reference local `_i`: loads `_p`, evaluates `Deref` (and
safe-pointer `AddrOf` checks for `.ref`), and stores the target's address in
`_i` when `_p` is initialized; raises UB when `_p` is uninitialized or dead. -/
theorem evalStatement_assign_reborrow_mr {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm) (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (hpt : ptrPointeeOf d.ty = some (mutbl, pointeeIt))
    (p : Nat) (dp : LocalDecl) (srcMutbl : MirAst.Mutability)
    (hdp : body.localDecls[p]? = some dp)
    (hp_pt : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt))
    {rv : Rvalue}
    (hrv : rv = .rawPtr mutbl ⟨p, [.deref]⟩ ∨
      ∃ bkind, borrowKindMutbl bkind = mutbl ∧ rv = .ref bkind ⟨p, [.deref]⟩)
    {targetTy : Option MirAst.Ty} (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    (∃ (parentPtr : ProvenancePtr) (parentEntry : BorrowEntry) (relOff : Nat),
      view[p]? = some (.init (.ptr parentPtr 8)) ∧
      parentPtr.offsetBytes = 0 ∧
      lookupBorrow s.memory.borrows parentPtr.tag = some parentEntry ∧
      ptrTargetSpec body.layouts body.localDecls
        ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ = some (pointeeIt, relOff) ∧
      (view[i]? ≠ some .dead →
        ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
          FrameOk body f
            (ctxWithBorrows body ctx
              (rawPtrEntry s.memory.nextTag mutbl
                ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ :: s.memory.borrows))
            (view.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8))) lm m' blk stmt)) ∨
    ((view[p]? = some .uninit ∨ view[p]? = some .dead) ∧
      (view[i]? ≠ some .dead →
        ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg))) := by
  have htpe : translatePlace body.localDecls ⟨p, [.deref]⟩ =
      some (.Deref (.Load (.Local (localName p))) (.Int pointeeIt)) := by
    have hder := derefPointeeTy_of_ptrPointeeOf hp_pt
    simp [translatePlace, hdp, hder, translateFieldPlace]
  have he_form : e = .AddrOf (.Deref (.Load (.Local (localName p))) (.Int pointeeIt)) (.Raw .None) ∨
      e = .AddrOf (.Deref (.Load (.Local (localName p))) (.Int pointeeIt))
            (refPtrType mutbl pointeeIt) := by
    rcases hrv with rfl | ⟨bkind, hbm, rfl⟩
    · left
      simp [translateRvalue, htpe] at he
      exact he.symm
    · right
      have hbpi : borrowPlaceIntType body.layouts body.localDecls ⟨p, [.deref]⟩ = some pointeeIt := by
        simp [borrowPlaceIntType, hdp, hp_pt]
      simp [translateRvalue, borrowPlacePointeeInfo, hbpi, htpe, hbm] at he
      exact he.symm
  rcases evalPlace_deref h hb hns hfrag p dp srcMutbl pointeeIt hdp hp_pt with
    ⟨parentPtr, parentEntry, relOff, m1, hv, hoff0, hlookup, hk_addr, htspec, hderefPl, h1, _⟩ |
      ⟨hnot, msg, hmsg⟩
  · left
    refine ⟨parentPtr, parentEntry, relOff, hv, hoff0, hlookup, htspec, fun hlive => ?_⟩
    obtain ⟨_, _, hgood, htlt, hptrEq, hal, _⟩ :=
      evalTargetPlace h1 hb hns hfrag ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩
        pointeeIt relOff htspec hk_addr
    obtain ⟨htpos, htderef⟩ :=
      evalTargetPlace_deref h1 hb hfrag ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩
        pointeeIt relOff htspec hk_addr
    rw [← hptrEq] at hderefPl hal htderef
    have hlo' := LocalsOk.rawPtr_extend h.locs hb
      (rawPtrEntry s.memory.nextTag mutbl ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩) rfl
    have hlo1' := LocalsOk.rawPtr_extend h1.locs hb
      (rawPtrEntry s.memory.nextTag mutbl ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩) rfl
    have h' := h.ctxWithBorrows_change hlo'
    have h1' := h1.ctxWithBorrows_change hlo1'
    have htgt : ∀ a pr,
        (ctxWithBorrows body ctx
          (rawPtrEntry s.memory.nextTag mutbl
            ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ :: s.memory.borrows)).ptrTargets
          s.memory.nextTag = some (a, pr) →
        (ctx.addrs.getD parentEntry.targetLocal 0 + (relOff : Int)).toNat = a ∧
          some (⟨((ctx.base.length + parentEntry.targetLocal : Nat) : Int)⟩, ()) = pr := by
      intro a pr h2
      simp only [ctxWithBorrows] at h2
      rw [borrowTargets_rawPtr_self body ctx s.memory.nextTag mutbl
        ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ s.memory.borrows pointeeIt relOff
        htspec] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      exact ⟨h2.1, h2.2⟩
    rcases he_form with rfl | rfl
    · have hck := checkValue_thinRawPtr (m? := some m1) _ htlt
        (some (⟨((ctx.base.length + parentEntry.targetLocal : Nat) : Int)⟩, ()))
      have hev := evalValue_addrOf_of h1.shape (.Raw .None) _ _ hderefPl hck
      exact evalStatement_assign_ptr_of h' i d hd hpt hlive _ _ htpos htlt _ hal _ m1 hev h1'
        htderef ⟨s.memory.nextTag, 0⟩ htgt
    · have hck := checkValue_refTy m1 mutbl pointeeIt hgood _ htpos htlt
        (some (⟨((ctx.base.length + parentEntry.targetLocal : Nat) : Int)⟩, ())) hal htderef
      have hev := evalValue_addrOf_of h1.shape (refPtrType mutbl pointeeIt) _ _ hderefPl hck
      exact evalStatement_assign_ptr_of h' i d hd hpt hlive _ _ htpos htlt _ hal _ m1 hev h1'
        htderef ⟨s.memory.nextTag, 0⟩ htgt
  · right
    refine ⟨hnot, fun hlive => ?_⟩
    have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
    have hspecF := h.hf.2 i d hd
    obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
    obtain ⟨pi, hpi⟩ := h.locs.some_of_live hs (fun hc => hlive (hc ▸ hs))
    have hplace := evalPlace_local_some h.shape i _ hspecF.2 pi hpi
    rcases he_form with rfl | rfl
    · exact ⟨msg, evalStatement_assign_ub_of hplace (evalValue_addrOf_place_ub hmsg)⟩
    · exact ⟨msg, evalStatement_assign_ub_of hplace (evalValue_addrOf_place_ub hmsg)⟩

/-! ## Pointer-copying rvalues -/

theorem rawPtrMetaOf_of_rawPtrPointeeOf {t : MirAst.Ty} {mutbl : MirAst.Mutability}
    {it : Gen.IntType} (h : rawPtrPointeeOf t = some (mutbl, it)) :
    rawPtrMetaOf t = some .None := by
  unfold rawPtrPointeeOf at h
  unfold rawPtrMetaOf
  cases hk : t.kind with
  | rawPtr m pointee =>
    rw [hk] at h
    obtain ⟨⟨sg, n⟩, hb, _⟩ := Option.map_eq_some_iff.mp h
    cases pointee <;> simp_all [intTyBytes, rawPtrMetaKind]
  | _ => rw [hk] at h; cases h

/-- `minimize`'s translation of a pointer- or reference-copying fragment rvalue:
a load of the pointer/reference local, for `Offset(_p, 0)` its in-bounds
offset by `0 * size_of::<T>()` bytes, or for `Transmute` a `CastOp::Transmute`
to `declPtrTy castTy`. -/
theorem translateRvalue_ptrRvalue {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType} {isRef : Bool} {rv : Rvalue}
    {targetTy : Option MirAst.Ty} {e : Gen.ValueExpr}
    (hok : ptrRvalueOk layouts decls mutbl pointeeIt isRef rv = true)
    (hnraw : ∀ m q, rv ≠ .rawPtr m q) (hnref : ∀ bk q, rv ≠ .ref bk q)
    (he : translateRvalue layouts decls targetTy rv = some e)
    (p : Nat) (hp : .copy ⟨p, []⟩ ∈ rvOperands rv) :
    e = .Load (.Local (localName p)) ∨
      (∃ (rIt : Gen.IntType) (z sz : Int), z = 0 ∧
        e = .BinOp (.PtrOffset true) (.Load (.Local (localName p)))
          (.BinOp (.Int .MulUnchecked) (.Constant (.Int z) (.Int rIt))
            (.Constant (.Int sz) (.Int rIt)))) ∨
      ∃ castTy, ptrPointeeOf castTy = some (mutbl, pointeeIt) ∧
        e = .UnOp (.Cast (.Transmute (declPtrTy castTy))) (.Load (.Local (localName p))) := by
  cases rv with
  | rawPtr m q => exact absurd rfl (hnraw m q)
  | ref bk q => exact absurd rfl (hnref bk q)
  | use op =>
    cases op with
    | copy pl =>
      obtain ⟨p', projs⟩ := pl
      cases projs with
      | nil =>
        simp only [rvOperands, List.mem_singleton, Operand.copy.injEq, Place.mk.injEq, and_true] at hp
        subst hp
        left
        simpa [translateRvalue, translateOperand, translatePlace] using he.symm
      | cons _ _ => simp [ptrRvalueOk] at hok
    | _ => simp [ptrRvalueOk] at hok
  | cast k op castTy =>
    cases k with
    | ptrToPtr =>
      cases op with
      | copy pl =>
        obtain ⟨p', projs⟩ := pl
        cases projs with
        | nil =>
          simp only [rvOperands, List.mem_singleton, Operand.copy.injEq, Place.mk.injEq, and_true] at hp
          subst hp
          left
          simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨⟨⟨_, _⟩, hcast_raw⟩, hsrc⟩ := hok
          cases hsp : (decls[p]? >>= (rawPtrPointeeOf ·.ty)) with
          | none => simp [hsp] at hsrc
          | some pr =>
            obtain ⟨srcMutbl, srcIt⟩ := pr
            cases hdp : decls[p]? with
            | none => simp [hdp] at hsp
            | some dp =>
              have hpt_raw : rawPtrPointeeOf dp.ty = some (srcMutbl, srcIt) := by
                simpa [hdp] using hsp
              have h1 := rawPtrMetaOf_of_rawPtrPointeeOf hpt_raw
              have h2 := rawPtrMetaOf_of_rawPtrPointeeOf hcast_raw
              simp [translateRvalue, translateOperand, translatePlace, operandRawPtrMeta, hdp, h1, h2] at he
              exact he.symm
        | cons _ _ => simp [ptrRvalueOk] at hok
      | _ => simp [ptrRvalueOk] at hok
    | transmute =>
      cases op with
      | copy pl =>
        obtain ⟨p', projs⟩ := pl
        cases projs with
        | nil =>
          simp only [rvOperands, List.mem_singleton, Operand.copy.injEq, Place.mk.injEq, and_true] at hp
          subst hp
          right; right
          simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨⟨_, hcast⟩, _⟩ := hok
          have hdst : ptrPointeeOf castTy = some (mutbl, pointeeIt) := by
            cases isRef with
            | false => exact (ptrPointeeOf_of_rawPtrPointeeOf (by simpa using hcast)).1
            | true => exact (ptrPointeeOf_of_refPointeeOf (by simpa using hcast)).1
          have htr := translateTy_of_ptrPointeeOf (layouts := layouts) hdst
          refine ⟨castTy, hdst, ?_⟩
          simp [translateRvalue, translateOperand, translatePlace, htr] at he
          exact he.symm
        | cons _ _ => simp [ptrRvalueOk] at hok
      | _ => simp [ptrRvalueOk] at hok
    | _ => simp [ptrRvalueOk] at hok
  | binaryOp bop l r =>
    cases bop with
    | offset =>
      cases l with
      | copy pl =>
        obtain ⟨p', projs⟩ := pl
        cases projs with
        | nil =>
          cases r with
          | constant c =>
            simp only [rvOperands, List.mem_cons, List.not_mem_nil, or_false, Operand.copy.injEq,
              Place.mk.injEq, and_true, reduceCtorEq] at hp
            subst hp
            right; left
            simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
            obtain ⟨⟨⟨_, _⟩, hpt_raw⟩, hz⟩ := hok
            have hpt := ptrPointeeOf_bind_of_rawPtrPointeeOf hpt_raw
            obtain ⟨rIt, hval, hit, _⟩ := zeroOffsetConstOk_iff.mp hz
            have hnb : isBoolTy c.ty = false := intTypeOf_isBoolTy hit
            refine ⟨rIt, intFromBits 0 rIt, pointeeIt.size.bytes, ?_, ?_⟩
            · cases hs : rIt.signed <;> simp [intFromBits, hs, Nat.two_pow_pos]
            · simp [translateRvalue, translateOperand, translatePlace, translateRelOp, translateBinOp,
                translateCheckedBinOp, operandPtrPointee, operandIntType, hpt, hval, hit, hnb,
                ptrOffsetExpr] at he
              exact he.symm
          | _ => simp [ptrRvalueOk] at hok
        | cons _ _ => simp [ptrRvalueOk] at hok
      | _ => simp [ptrRvalueOk] at hok
    | _ => simp [ptrRvalueOk] at hok
  | _ => simp [ptrRvalueOk] at hok

theorem bringInBounds_zero (signed : Signedness) (size : Size) : bringInBounds 0 signed size = 0 := by
  cases signed with
  | Unsigned => simp [bringInBounds]
  | Signed =>
    have : (0 : Int) < (2 : Int) ^ (Size.bits size - 1) := two_pow_pos _
    simp [bringInBounds, this]

/-- `Offset(p, 0)` as `minimize` translates it (`ptrOffsetExpr`): the in-bounds
offset of a thin pointer by `0 * size_of::<T>()` bytes is the pointer itself. -/
theorem evalValue_ptrOffset_zero {m m1 : Mach} {l : Gen.ValueExpr} {ptr : Ptr} {T : Gen.Type}
    (rIt : Gen.IntType) (z sz : Int) (hz : z = 0)
    (hl : evalValue m l = .ok ((.Ptr { thin_pointer := ptr, metadata := none }, T), m1))
    (h0 : 0 ≤ ptr.addr) (hmax : ptr.addr < 2 ^ 64) :
    evalValue m (.BinOp (.PtrOffset true) l
        (.BinOp (.Int .MulUnchecked) (.Constant (.Int z) (.Int rIt)) (.Constant (.Int sz) (.Int rIt)))) =
      .ok ((.Ptr { thin_pointer := ptr, metadata := none }, T), m1) := by
  subst hz
  have hoff := ptrOffsetInbounds_zero m1 ptr h0 hmax
  have hcan : IntType.can_represent rIt 0 = true := by
    have h1 : (0 : Int) < (2 : Int) ^ Size.bits rIt.size := two_pow_pos _
    have h2 : (0 : Int) < (2 : Int) ^ (Size.bits rIt.size - 1) := two_pow_pos _
    cases hs : rIt.signed <;> simp [IntType.can_represent, inBounds, hs, h1, h2] <;> omega
  rw [evalValue, hl]
  simp [evalValue, evalConstant, evalBinOp, evalIntBinOp, hcan, IntType.bring_in_bounds,
    bringInBounds_zero, evalPtrOffset, hoff, ThinPointer.widen]

/-- MiniRust's pointer- or reference-copying assignment (`_i = copy _p`,
`PtrToPtr`, `Transmute`, or `Offset(_p, 0)`) into the live pointer or reference
local `_i`: `_i` holds `_p`'s pointer; UB when `_p` holds none. -/
theorem evalStatement_assign_ptrRvalue_mr {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm) (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType} {isRef : Bool}
    (hpt : ptrPointeeOf d.ty = some (mutbl, pointeeIt))
    {rv : Rvalue} (hok : ptrRvalueOk body.layouts body.localDecls mutbl pointeeIt isRef rv = true)
    (hnraw : ∀ m q, rv ≠ .rawPtr m q) (hnref : ∀ bk q, rv ≠ .ref bk q)
    {targetTy : Option MirAst.Ty} (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    ∃ p, .copy ⟨p, []⟩ ∈ rvOperands rv ∧
      (isMutPtrLocal body.localDecls i = true → isMutPtrLocal body.localDecls p = true) ∧
      (∀ pv, view[p]? = some (.init (.ptr pv 8)) →
        (view[i]? ≠ some .dead →
          ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
          FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) (view.set i (.init (.ptr pv 8)))
            lm m' blk stmt) ∧
        ∃ (entry : BorrowEntry) (relOff : Nat), pv.offsetBytes = 0 ∧
          lookupBorrow s.memory.borrows pv.tag = some entry ∧
          ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
            some (pointeeIt, relOff)) ∧
      ((view[p]? = some .uninit ∨ view[p]? = some .dead) → view[i]? ≠ some .dead →
        ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hspecF := h.hf.2 i d hd
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  obtain ⟨p, _, hpmem, ⟨srcMutbl, hsrc, hmut⟩, _⟩ := evalRvalue_ptrRvalue hok hnraw hnref
  obtain ⟨dp, hdp, hp_pt⟩ : ∃ dp, body.localDecls[p]? = some dp ∧
      ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt) := by
    cases hdp : body.localDecls[p]? with
    | none => simp [hdp] at hsrc
    | some dp => exact ⟨dp, rfl, by simpa [hdp] using hsrc⟩
  have hmut_ip : isMutPtrLocal body.localDecls i = true → isMutPtrLocal body.localDecls p = true := by
    intro hmi
    unfold isMutPtrLocal at hmi ⊢
    rw [hd] at hmi
    rw [hdp]
    dsimp only [Option.bind_eq_bind, Option.bind_some] at hmi ⊢
    rw [hpt] at hmi
    rw [hp_pt]
    have hm : mutbl = .mut := by cases mutbl <;> simp at hmi <;> rfl
    rw [hmut hm]
  have he_form := translateRvalue_ptrRvalue hok hnraw hnref he p hpmem
  refine ⟨p, hpmem, hmut_ip, fun pv hpv => ?_, fun hu hlive => ?_⟩
  · rcases evalPtrLoad h hb hns hfrag p dp srcMutbl pointeeIt hdp hp_pt with
      ⟨ptrVal, entry, relOff, m1, hv, hoff0, hlookup, hk_addr, htspec, hload, h1⟩ |
        ⟨hnot, _⟩
    · rw [hv] at hpv
      simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hpv
      obtain ⟨rfl, -⟩ := hpv
      obtain ⟨_, _, _, htlt, hptrEq, hal, _⟩ :=
        evalTargetPlace h1 hb hns hfrag ⟨entry.targetLocal, entry.targetProjection⟩ pointeeIt relOff
          htspec hk_addr
      obtain ⟨htpos, htderef⟩ :=
        evalTargetPlace_deref h1 hb hfrag ⟨entry.targetLocal, entry.targetProjection⟩ pointeeIt
          relOff htspec hk_addr
      rw [← hptrEq] at hload hal htderef
      obtain ⟨T', hm1⟩ : ∃ T', evalValue m e =
          .ok ((.Ptr { thin_pointer := { addr := ((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat : Int),
                                         provenance := some (⟨((ctx.base.length + entry.targetLocal : Nat) : Int)⟩, ()) },
                       metadata := none }, T'), m1) := by
        rcases he_form with rfl | ⟨rIt, z, sz, hz, rfl⟩ | ⟨castTy, hcast_pt, rfl⟩
        · exact ⟨_, hload⟩
        · refine ⟨_, evalValue_ptrOffset_zero rIt z sz hz hload (Int.natCast_nonneg _) ?_⟩
          have h64 : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := by decide
          have hlt := Int.ofNat_lt.mpr htlt
          rw [h64] at hlt
          exact hlt
        · refine ⟨declPtrTy castTy, ?_⟩
          rw [evalValue, hload, ok_bind]
          dsimp only [evalUnOp]
          rw [evalCastOp_transmute_declPtrTy_ok m1 dp.ty castTy hcast_pt
            (ptrPointeeOf_good hcast_pt) _ htpos htlt _ hal htderef, ok_bind]
          rfl
      have htgt : ∀ a pr,
          (ctxWithBorrows body ctx s.memory.borrows).ptrTargets ptrVal.allocId = some (a, pr) →
          (ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat = a ∧
            some (⟨((ctx.base.length + entry.targetLocal : Nat) : Int)⟩, ()) = pr := by
        intro a pr h2
        have hbt : (ctxWithBorrows body ctx s.memory.borrows).ptrTargets ptrVal.allocId =
            some ((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat,
                  some (⟨((ctx.base.length + entry.targetLocal : Nat) : Int)⟩, ())) := by
          simp [ctxWithBorrows, borrowTargets, ProvenancePtr.tag] at hlookup ⊢
          simp [hlookup, htspec]
        rw [hbt] at h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        exact ⟨h2.1, h2.2⟩
      exact ⟨fun hlive => evalStatement_assign_ptr_of h i d hd hpt hlive e _ htpos htlt _ hal T'
        m1 hm1 h1 htderef ptrVal htgt, entry, relOff, hoff0, hlookup, htspec⟩
    · rcases hnot with h' | h' <;> rw [h'] at hpv <;> cases hpv
  · obtain ⟨pi, hpi⟩ := h.locs.some_of_live hs (fun hc => hlive (hc ▸ hs))
    have hplace := evalPlace_local_some h.shape i _ hspecF.2 pi hpi
    rcases evalPtrLoad h hb hns hfrag p dp srcMutbl pointeeIt hdp hp_pt with
      ⟨ptrVal, _, _, _, hv, _⟩ | ⟨_, msg, hmsg⟩
    · rcases hu with hu | hu <;> rw [hu] at hv <;> cases hv
    · refine ⟨msg, evalStatement_assign_ub_of hplace ?_⟩
      rcases he_form with rfl | ⟨rIt, z, sz, hz, rfl⟩ | ⟨_, _, rfl⟩
      · exact hmsg
      · rw [evalValue, hmsg]
        rfl
      · rw [evalValue, hmsg]
        rfl

/-! ## Fragment checks on raw pointer statements -/

theorem local_mem_stmtLocals_assign (dst : Place) (rv : Rvalue) (span : String) :
    dst.local_ ∈ stmtLocals ⟨.assign dst rv, span⟩ := by
  cases rv <;> simp [stmtLocals, local_mem_placeLocals]

theorem statementOk_ptrRvalueOk_of_rawPtr {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {i : Nat} {mutbl : MirAst.Mutability} {q : Place} {span : String} {d : LocalDecl}
    (hd : decls[i]? = some d)
    (h : statementOk decls ⟨.assign ⟨i, []⟩ (.rawPtr mutbl q), span⟩ layouts = true) :
    ∃ m' pointeeIt, ptrPointeeOf d.ty = some (m', pointeeIt) ∧
      ptrRvalueOk layouts decls m' pointeeIt (isRefTy d.ty) (.rawPtr mutbl q) = true := by
  simp only [statementOk, hd, copyRv] at h
  split at h
  · simp [rvalueOkB] at h
  · split at h
    · simp [rvalueOkO] at h
    · split at h
      · simp [rvalueOkTuple] at h
      · split at h
        · simp [rvalueOk, ptrDerefReadOk] at h
        · split at h
          · simp [arrayRvalueOk] at h
          · split at h
            · simp [tupleRvalueOk] at h
            · split at h
              · rename_i m' pointeeIt hpt
                exact ⟨m', pointeeIt, hpt, h⟩
              · simp at h

theorem statementOk_ptrRvalueOk_of_ref {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {i : Nat} {bkind : BorrowKind} {q : Place} {span : String} {d : LocalDecl}
    (hd : decls[i]? = some d)
    (h : statementOk decls ⟨.assign ⟨i, []⟩ (.ref bkind q), span⟩ layouts = true) :
    ∃ m' pointeeIt, ptrPointeeOf d.ty = some (m', pointeeIt) ∧
      ptrRvalueOk layouts decls m' pointeeIt (isRefTy d.ty) (.ref bkind q) = true := by
  simp only [statementOk, hd, copyRv] at h
  split at h
  · simp [rvalueOkB] at h
  · split at h
    · simp [rvalueOkO] at h
    · split at h
      · simp [rvalueOkTuple] at h
      · split at h
        · simp [rvalueOk, ptrDerefReadOk] at h
        · split at h
          · simp [arrayRvalueOk] at h
          · split at h
            · simp [tupleRvalueOk] at h
            · split at h
              · rename_i m' pointeeIt hpt
                exact ⟨m', pointeeIt, hpt, h⟩
              · simp at h

/-- `statementOk` on a direct `_i = &raw mutbl q`: `_i` is a thin raw pointer of
mutability `mutbl` to an integer type, and `q` is an admissible borrow target
of that type. -/
theorem statementOk_rawPtr_spec {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {i : Nat} {mutbl : MirAst.Mutability} {q : Place} {span : String} {d : LocalDecl}
    (hd : decls[i]? = some d) (hnd : ∀ rest, q.projection ≠ .deref :: rest)
    (h : statementOk decls ⟨.assign ⟨i, []⟩ (.rawPtr mutbl q), span⟩ layouts = true) :
    isRefTy d.ty = false ∧ ∃ pointeeIt relOff, ptrPointeeOf d.ty = some (mutbl, pointeeIt) ∧
      ptrTargetSpec layouts decls q = some (pointeeIt, relOff) := by
  obtain ⟨m', pointeeIt, hpt, hok⟩ := statementOk_ptrRvalueOk_of_rawPtr hd h
  have hok' : (!isRefTy d.ty && decide (mutbl = m') && ptrTargetOk layouts decls pointeeIt q) = true := by
    obtain ⟨k, projs⟩ := q
    cases projs with
    | nil => exact hok
    | cons ph pt =>
      cases ph with
      | deref => exact absurd rfl (hnd pt)
      | _ => exact hok
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hok'
  obtain ⟨⟨hnref, rfl⟩, htok⟩ := hok'
  unfold ptrTargetOk at htok
  split at htok
  · rename_i it' relOff hsp
    simp only [decide_eq_true_eq] at htok
    subst htok
    exact ⟨hnref, it', relOff, hpt, hsp⟩
  · simp at htok

/-- `statementOk` on a direct `_i = &q` / `_i = &mut q` / `_i = &two_phase mut q`:
`_i` is a reference of mutability `borrowKindMutbl bkind` to an integer type,
and `q` is an admissible borrow target of that type. -/
theorem statementOk_ref_spec {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {i : Nat} {bkind : BorrowKind} {q : Place} {span : String} {d : LocalDecl}
    (hd : decls[i]? = some d) (hnd : ∀ rest, q.projection ≠ .deref :: rest)
    (h : statementOk decls ⟨.assign ⟨i, []⟩ (.ref bkind q), span⟩ layouts = true) :
    isRefTy d.ty = true ∧
      ∃ pointeeIt relOff, ptrPointeeOf d.ty = some (borrowKindMutbl bkind, pointeeIt) ∧
        ptrTargetSpec layouts decls q = some (pointeeIt, relOff) := by
  obtain ⟨m', pointeeIt, hpt, hok⟩ := statementOk_ptrRvalueOk_of_ref hd h
  have hok' : (isRefTy d.ty &&
      decide (borrowKindMutbl bkind = m') && ptrTargetOk layouts decls pointeeIt q) = true := by
    obtain ⟨k, projs⟩ := q
    cases projs with
    | nil => exact hok
    | cons ph pt =>
      cases ph with
      | deref => exact absurd rfl (hnd pt)
      | _ => exact hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨href, rfl⟩, htok⟩ := hok'
  unfold ptrTargetOk at htok
  split at htok
  · rename_i it' relOff hsp
    simp only [decide_eq_true_eq] at htok
    subst htok
    exact ⟨href, it', relOff, hpt, hsp⟩
  · simp at htok

/-- `statementOk` on a raw-pointer reborrow `_i = &raw mutbl (*_p...)`: `rest = []`,
`_i` is a raw pointer of mutability `mutbl`, and `_p` is a raw pointer or
reference of compatible mutability to the same integer type. -/
theorem statementOk_rawPtr_reborrow_spec {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {i : Nat} {mutbl : MirAst.Mutability} {p : Nat} {rest : List ProjectionElem}
    {span : String} {d : LocalDecl}
    (hd : decls[i]? = some d)
    (h : statementOk decls ⟨.assign ⟨i, []⟩ (.rawPtr mutbl ⟨p, .deref :: rest⟩), span⟩ layouts = true) :
    rest = [] ∧ isRefTy d.ty = false ∧ p < decls.length ∧
      ∃ pointeeIt dp srcMutbl, ptrPointeeOf d.ty = some (mutbl, pointeeIt) ∧
        decls[p]? = some dp ∧ ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt) ∧
        (mutbl = .mut → srcMutbl = .mut) := by
  obtain ⟨m', pointeeIt, hpt, hok⟩ := statementOk_ptrRvalueOk_of_rawPtr hd h
  cases rest with
  | cons _ _ =>
    simp [ptrRvalueOk, ptrTargetOk, ptrTargetSpec] at hok
  | nil =>
    simp only [ptrRvalueOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hnref, rfl⟩, hp⟩, hsrc⟩ := hok
    cases hdp : decls[p]? with
    | none => simp [hdp] at hsrc
    | some dp =>
      simp only [hdp, Option.bind_eq_bind, Option.bind_some] at hsrc
      cases hsp : ptrPointeeOf dp.ty with
      | none => simp [hsp] at hsrc
      | some pr =>
        obtain ⟨srcMutbl, srcIt⟩ := pr
        simp only [hsp, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hsrc
        obtain ⟨rfl, hm⟩ := hsrc
        refine ⟨rfl, hnref, hp, srcIt, dp, srcMutbl, hpt, rfl, hsp, fun hmut => ?_⟩
        rcases hm with hm | hm
        · exact hm
        · subst hmut; cases hm

/-- `statementOk` on a reference reborrow `_i = &(*_p...)` / `_i = &mut (*_p...)`
/ `_i = &two_phase mut (*_p...)`: `rest = []`, `_i` is a reference of mutability
`borrowKindMutbl bkind`, and `_p` is a raw pointer or reference of compatible
mutability to the same integer type. -/
theorem statementOk_ref_reborrow_spec {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {i : Nat} {bkind : BorrowKind} {p : Nat} {rest : List ProjectionElem}
    {span : String} {d : LocalDecl}
    (hd : decls[i]? = some d)
    (h : statementOk decls ⟨.assign ⟨i, []⟩ (.ref bkind ⟨p, .deref :: rest⟩), span⟩ layouts = true) :
    rest = [] ∧ isRefTy d.ty = true ∧ p < decls.length ∧
      ∃ pointeeIt dp srcMutbl, ptrPointeeOf d.ty = some (borrowKindMutbl bkind, pointeeIt) ∧
        decls[p]? = some dp ∧ ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt) ∧
        (borrowKindMutbl bkind = .mut → srcMutbl = .mut) := by
  obtain ⟨m', pointeeIt, hpt, hok⟩ := statementOk_ptrRvalueOk_of_ref hd h
  cases rest with
  | cons _ _ =>
    simp [ptrRvalueOk, ptrTargetOk, ptrTargetSpec] at hok
  | nil =>
    simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨href, rfl⟩, hp⟩, hsrc⟩ := hok
    cases hdp : decls[p]? with
    | none => simp [hdp] at hsrc
    | some dp =>
      simp only [hdp, Option.bind_eq_bind, Option.bind_some] at hsrc
      cases hsp : ptrPointeeOf dp.ty with
      | none => simp [hsp] at hsrc
      | some pr =>
        obtain ⟨srcMutbl, srcIt⟩ := pr
        simp only [hsp, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hsrc
        obtain ⟨rfl, hm⟩ := hsrc
        refine ⟨rfl, href, hp, srcIt, dp, srcMutbl, hpt, rfl, hsp, fun hmut => ?_⟩
        rcases hm with hm | hm
        · exact hm
        · rw [hmut] at hm; cases hm

theorem copyRv_derefRead {rv : Rvalue} {p : Nat} {rest : List ProjectionElem}
    (hcrv : copyRv rv = .use (.copy ⟨p, .deref :: rest⟩)) :
    rv = .use (.copy ⟨p, .deref :: rest⟩) ∨
    rv = .use (.move ⟨p, .deref :: rest⟩) ∨
    rv = .copyForDeref ⟨p, .deref :: rest⟩ := by
  cases rv <;> simp [copyRv] at hcrv
  · rename_i op
    cases op <;> simp [copyOp] at hcrv <;> simp [hcrv]
  · simp [hcrv]

/-- `statementOk` on a root assignment whose rvalue reads through a pointer or
reference (`copy (*_p...)`, `move (*_p...)`, or `CopyForDeref(*_p...)`): an
unprojected dereference `*_p` of a thin raw pointer or reference local into an
integer local of the pointee type. -/
theorem statementOk_derefRead {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {i : Nat} {rv : Rvalue} {span : String} {d : LocalDecl} (hd : decls[i]? = some d)
    {p : Nat} {rest : List ProjectionElem}
    (hcrv : copyRv rv = .use (.copy ⟨p, .deref :: rest⟩))
    (h : statementOk decls ⟨.assign ⟨i, []⟩ rv, span⟩ layouts = true) :
    rest = [] ∧ ∃ it dp srcMutbl, intTypeOf d.ty = some it ∧ decls[p]? = some dp ∧
      ptrPointeeOf dp.ty = some (srcMutbl, it) := by
  have key : ∀ rv' : Rvalue, copyRv rv' = .use (.copy ⟨p, .deref :: rest⟩) →
      statementOk decls ⟨.assign ⟨i, []⟩ rv', span⟩ layouts = true →
      (rv' = .use (.copy ⟨p, .deref :: rest⟩) ∨
       rv' = .use (.move ⟨p, .deref :: rest⟩) ∨
       rv' = .copyForDeref ⟨p, .deref :: rest⟩) →
      rest = [] ∧ ∃ it dp srcMutbl, intTypeOf d.ty = some it ∧ decls[p]? = some dp ∧
        ptrPointeeOf dp.ty = some (srcMutbl, it) := by
    intro rv' hcrv' h' hrv'
    simp only [statementOk, hd, hcrv'] at h'
    split at h'
    · simp [rvalueOkB, operandOkB] at h'
    · split at h'
      · simp [rvalueOkO, operandOkO] at h'
      · split at h'
        · simp [rvalueOkTuple, operandOkTuple] at h'
        · split at h'
          · rename_i it hit
            simp only [Bool.or_eq_true] at h'
            rcases h' with h' | h'
            · exfalso
              cases rest with
              | nil =>
                simp only [rvalueOk, operandOk, placeOk, Bool.and_eq_true] at h'
                obtain ⟨⟨_, h'⟩, _⟩ := h'
                split at h' <;> simp [projOk] at h'
              | cons _ _ => simp [rvalueOk, operandOk, placeOk] at h'
            · cases rest with
              | cons _ _ => simp [ptrDerefReadOk] at h'
              | nil =>
                simp only [ptrDerefReadOk, Bool.and_eq_true, decide_eq_true_eq] at h'
                obtain ⟨_, hm⟩ := h'
                split at hm
                · rename_i srcMutbl pointeeIt hsp
                  simp only [decide_eq_true_eq] at hm
                  subst hm
                  cases hdp : decls[p]? with
                  | none => simp [hdp] at hsp
                  | some dp => exact ⟨rfl, pointeeIt, dp, srcMutbl, hit, rfl, by simpa [hdp] using hsp⟩
                · simp at hm
          · split at h'
            · rcases hrv' with rfl | rfl | rfl <;> simp [arrayRvalueOk] at h'
            · split at h'
              · rcases hrv' with rfl | rfl | rfl <;> simp [tupleRvalueOk, tuplePlaceSpec] at h'
              · split at h'
                · simp [ptrRvalueOk] at h'
                · simp at h'
  exact key rv hcrv h (copyRv_derefRead hcrv)

theorem stmtReadsOk_derefRead {mo : List Nat} {i : Nat} {rv : Rvalue} {span : String}
    {p : Nat} {rest : List ProjectionElem} (hcrv : copyRv rv = .use (.copy ⟨p, .deref :: rest⟩)) :
    stmtReadsOk mo ⟨.assign ⟨i, []⟩ rv, span⟩ = !mo.contains p := by
  rcases copyRv_derefRead hcrv with rfl | rfl | rfl <;> rfl

theorem ptrDerefReadSrc_eq_some {rv : Rvalue} {r : Nat} :
    ptrDerefReadSrc rv = some r ↔ ∃ rest, copyRv rv = .use (.copy ⟨r, .deref :: rest⟩) := by
  unfold ptrDerefReadSrc
  split
  · next p rest heq =>
    simp only [Option.some.injEq]
    exact ⟨fun h => ⟨rest, h ▸ heq⟩, fun ⟨rest', h⟩ => by rw [heq] at h; cases h; rfl⟩
  · next hne =>
    simp only [reduceCtorEq, false_iff, not_exists]
    intro rest heq
    exact hne r rest heq

theorem ptrDerefReadOk_false_of_src_none {decls : List LocalDecl} {it : Gen.IntType} {rv : Rvalue}
    (hsrc : ptrDerefReadSrc rv = none) :
    ptrDerefReadOk decls it (copyRv rv) = false := by
  unfold ptrDerefReadOk
  split
  · next p heq =>
    have hsome : ptrDerefReadSrc rv = some p := by simp [ptrDerefReadSrc, heq]
    rw [hsrc] at hsome
    cases hsome
  · rfl

/-- `statementOk` on a pointer-to-pointer dereference copy
`(*_i) = copy (*_r...)` / `move (*_r...)` / `CopyForDeref(*_r...)`: `_i` is a
mutable raw pointer or reference local, `_r` is a raw pointer or reference local
to the same integer type `pointeeIt`, and the source dereference is unprojected
(`copyRv rv = .use (.copy ⟨r, [.deref]⟩)`). -/
theorem statementOk_derefWrite_derefRead {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {i r : Nat} {rv : Rvalue} {span : String}
    (hsrc : ptrDerefReadSrc rv = some r)
    (h : statementOk decls ⟨.assign ⟨i, [.deref]⟩ rv, span⟩ layouts = true) :
    i < decls.length ∧ r < decls.length ∧
      copyRv rv = .use (.copy ⟨r, [.deref]⟩) ∧
      ∃ di dr pointeeIt srcMutbl,
        decls[i]? = some di ∧ ptrPointeeOf di.ty = some (.mut, pointeeIt) ∧
        decls[r]? = some dr ∧ ptrPointeeOf dr.ty = some (srcMutbl, pointeeIt) := by
  obtain ⟨rest, hcrv⟩ := ptrDerefReadSrc_eq_some.mp hsrc
  simp only [statementOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hi, h⟩ := h
  obtain ⟨di, hdi⟩ : ∃ di, decls[i]? = some di := ⟨_, List.getElem?_eq_getElem hi⟩
  simp only [hdi, Option.bind_eq_bind, Option.bind_some] at h
  cases hpt : ptrPointeeOf di.ty with
  | none => simp [hpt] at h
  | some pr =>
    obtain ⟨mutbl, pointeeIt⟩ := pr
    cases mutbl with
    | not => simp [hpt] at h
    | «mut» =>
      simp only [hpt, hcrv, Bool.or_eq_true] at h
      rcases h with h | h
      · exfalso
        cases rest with
        | nil =>
          simp only [rvalueOk, operandOk, placeOk, Bool.and_eq_true] at h
          obtain ⟨⟨_, h⟩, _⟩ := h
          split at h <;> simp [projOk] at h
        | cons _ _ => simp [rvalueOk, operandOk, placeOk] at h
      · cases rest with
        | cons _ _ => simp [ptrDerefReadOk] at h
        | nil =>
          simp only [ptrDerefReadOk, Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨hr, hm⟩ := h
          split at hm
          · rename_i srcMutbl srcIt hsp
            simp only [decide_eq_true_eq] at hm
            subst hm
            cases hdr : decls[r]? with
            | none => simp [hdr] at hsp
            | some dr =>
              exact ⟨hi, hr, hcrv, di, dr, srcIt, srcMutbl, hdi, hpt, rfl,
                by simpa [hdr] using hsp⟩
          · simp at hm

theorem stmtReadsOk_derefWrite_derefRead {mo : List Nat} {i r : Nat} {rv : Rvalue} {span : String}
    (hsrc : ptrDerefReadSrc rv = some r) :
    stmtReadsOk mo ⟨.assign ⟨i, [.deref]⟩ rv, span⟩ = (!mo.contains r && !mo.contains i) := by
  simp [stmtReadsOk, hsrc]

theorem stmtReadsOk_derefWrite_of_not_derefRead {mo : List Nat} {i : Nat}
    {proj : ProjectionElem} {rest : List ProjectionElem} {rv : Rvalue} {span : String}
    (hnd : ¬(proj = .deref ∧ rest = [] ∧ (ptrDerefReadSrc rv).isSome = true)) :
    stmtReadsOk mo ⟨.assign ⟨i, proj :: rest⟩ rv, span⟩ =
      (readsOk mo (rvOperands rv) &&
        (placeLocals ⟨i, proj :: rest⟩).all
          (fun j => !((rvOperands rv).foldl moveOut mo).contains j)) := by
  simp only [stmtReadsOk]
  cases proj with
  | deref =>
    cases rest with
    | nil =>
      cases hsrc : ptrDerefReadSrc rv with
      | none => rfl
      | some r => exact absurd ⟨rfl, rfl, by simp [hsrc]⟩ hnd
    | cons _ _ => rfl
  | _ => rfl

theorem stmtReadsOk_rawPtr_reborrow {mo : List Nat} {i : Nat} {mutbl : MirAst.Mutability}
    {p : Nat} {rest : List ProjectionElem} {span : String} :
    stmtReadsOk mo ⟨.assign ⟨i, []⟩ (.rawPtr mutbl ⟨p, .deref :: rest⟩), span⟩ = !mo.contains p := rfl

theorem stmtReadsOk_ref_reborrow {mo : List Nat} {i : Nat} {bkind : BorrowKind}
    {p : Nat} {rest : List ProjectionElem} {span : String} :
    stmtReadsOk mo ⟨.assign ⟨i, []⟩ (.ref bkind ⟨p, .deref :: rest⟩), span⟩ = !mo.contains p := rfl

theorem stmtReadsOk_root_of_not_deref {mo : List Nat} {i : Nat} {rv : Rvalue} {span : String}
    (hnraw : ∀ m q, rv ≠ .rawPtr m q) (hnref : ∀ bk q, rv ≠ .ref bk q)
    (hnd : ∀ p rest, copyRv rv ≠ .use (.copy ⟨p, .deref :: rest⟩)) :
    stmtReadsOk mo ⟨.assign ⟨i, []⟩ rv, span⟩ = readsOk mo (rvOperands rv) := by
  cases rv with
  | rawPtr m q => exact absurd rfl (hnraw m q)
  | ref bk q => exact absurd rfl (hnref bk q)
  | copyForDeref pl =>
    obtain ⟨p, projs⟩ := pl
    cases projs with
    | nil => rfl
    | cons ph pt =>
      cases ph with
      | deref => exact absurd rfl (hnd p pt)
      | _ => rfl
  | use op =>
    cases op with
    | copy pl =>
      obtain ⟨p, projs⟩ := pl
      cases projs with
      | nil => rfl
      | cons ph pt =>
        cases ph with
        | deref => exact absurd rfl (hnd p pt)
        | _ => rfl
    | move pl =>
      obtain ⟨p, projs⟩ := pl
      cases projs with
      | nil => rfl
      | cons ph pt =>
        cases ph with
        | deref => exact absurd rfl (hnd p pt)
        | _ => rfl
    | constant _ => rfl
  | _ => rfl

theorem ptrDerefReadOk_of_not_deref {decls : List LocalDecl} {it : Gen.IntType} {rv : Rvalue}
    (hnd : ∀ p rest, copyRv rv ≠ .use (.copy ⟨p, .deref :: rest⟩)) :
    ptrDerefReadOk decls it (copyRv rv) = false := by
  unfold ptrDerefReadOk
  split
  · rename_i p heq
    exact absurd heq (hnd p [])
  · rfl

theorem rvPost_derefRead {locals : List LocalSlot} {rv : Rvalue} {p : Nat}
    {rest : List ProjectionElem} (hcrv : copyRv rv = .use (.copy ⟨p, .deref :: rest⟩)) :
    rvPost locals rv = locals := by
  rcases copyRv_derefRead hcrv with rfl | rfl | rfl <;>
    simp [rvPost, opsPost, opPost, opMoved, rvOperands]

theorem translatePlace_deref {decls : List LocalDecl} {p : Nat} {dp : LocalDecl}
    {m : MirAst.Mutability} {it : Gen.IntType}
    (hdp : decls[p]? = some dp) (hpt : ptrPointeeOf dp.ty = some (m, it)) :
    translatePlace decls ⟨p, [.deref]⟩ = some (.Deref (.Load (.Local (localName p))) (.Int it)) := by
  have hder := derefPointeeTy_of_ptrPointeeOf hpt
  simp [translatePlace, hdp, hder, translateFieldPlace]

theorem translateRvalue_derefRead {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {targetTy : Option MirAst.Ty} {p : Nat} {dp : LocalDecl} {srcMutbl : MirAst.Mutability}
    {it : Gen.IntType} {e : Gen.ValueExpr}
    (hdp : decls[p]? = some dp) (hpt : ptrPointeeOf dp.ty = some (srcMutbl, it))
    (he : translateRvalue layouts decls targetTy (.use (.copy ⟨p, [.deref]⟩)) = some e) :
    e = .Load (.Deref (.Load (.Local (localName p))) (.Int it)) := by
  simp [translateRvalue, translateOperand, translatePlace_deref hdp hpt] at he
  exact he.symm

theorem moveKind_of_ptrRvalueOk {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {mutbl : MirAst.Mutability} {it : Gen.IntType} {isRef : Bool} {rv : Rvalue}
    (h : ptrRvalueOk layouts decls mutbl it isRef (copyRv rv) = true)
    (hnraw : ∀ m q, rv ≠ .rawPtr m q) (hnref : ∀ bk q, rv ≠ .ref bk q) :
    moveKind rv = true := by
  cases rv with
  | rawPtr m q => exact absurd rfl (hnraw m q)
  | ref bk q => exact absurd rfl (hnref bk q)
  | cast k op ty => cases k <;> first | rfl | simp_all [copyRv, ptrRvalueOk]
  | unaryOp uop op => cases uop <;> simp_all [copyRv, ptrRvalueOk]
  | aggregate k ops => cases k <;> simp_all [copyRv, ptrRvalueOk]
  | _ => simp_all [copyRv, ptrRvalueOk, moveKind]

theorem ptrRvalueOk_copy_unique {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {mutbl : MirAst.Mutability} {it : Gen.IntType} {isRef : Bool} {rv : Rvalue}
    (h : ptrRvalueOk layouts decls mutbl it isRef rv = true) {p p' : Nat}
    (hp : Operand.copy ⟨p, []⟩ ∈ rvOperands rv) (hp' : Operand.copy ⟨p', []⟩ ∈ rvOperands rv) :
    p = p' := by
  cases rv with
  | rawPtr _ _ | ref _ _ => simp [rvOperands] at hp
  | use op | cast _ op _ =>
    cases op <;> simp [rvOperands] at hp hp'
    cases hp; cases hp'; rfl
  | binaryOp bop l r =>
    cases bop with
    | offset =>
      cases l with
      | copy pl =>
        cases r with
        | constant c =>
          simp only [rvOperands, List.mem_cons, List.not_mem_nil, or_false,
            Operand.copy.injEq, reduceCtorEq] at hp hp'
          have heq := hp.trans hp'.symm
          exact congrArg Place.local_ heq
        | _ => simp [ptrRvalueOk] at h
      | _ => simp [ptrRvalueOk] at h
    | _ => simp [ptrRvalueOk] at h
  | _ => simp [ptrRvalueOk] at h

theorem placeLocals_of_noIndexProj {q : Place} (h : noIndexProj q.projection = true) :
    placeLocals q = [q.local_] := by
  obtain ⟨k, projs⟩ := q
  cases projs with
  | nil => rfl
  | cons ph pt => cases ph <;> simp_all [placeLocals, noIndexProj]

theorem readsAgree_copy_target {L V : List LocalSlot} {q : Place}
    (hni : noIndexProj q.projection = true) (h : L[q.local_]? = V[q.local_]?) :
    ReadsAgree L V [.copy q] := by
  intro op hop j hj
  simp only [List.mem_singleton] at hop
  subst hop
  simp only [opLocals, placeLocals_of_noIndexProj hni, List.mem_singleton] at hj
  subst hj
  exact h

/-! ## Reads through a pointer -/

theorem evalRvalue_derefRead_eq (locals : List LocalSlot) {rv : Rvalue} {p : Nat}
    (hcrv : copyRv rv = .use (.copy ⟨p, [.deref]⟩)) (mem : MirSemantics.Memory)
    (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    {dp : LocalDecl} {srcMutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    (hdp : decls[p]? = some dp) (hp_pt : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt))
    (ptrVal : ProvenancePtr) (sz : Nat) (hp : locals[p]? = some (.init (.ptr ptrVal sz)))
    (entry : BorrowEntry) (he : lookupBorrow mem.borrows ptrVal.tag = some entry)
    (hthin : needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes = false)
    (hperm : entry.perm ≠ .disabled) (hnd : ∀ rest, entry.targetProjection ≠ .deref :: rest)
    (slot : LocalSlot) (ht : locals[entry.targetLocal]? = some slot) :
    (∀ v, evalOperand locals (.copy ⟨entry.targetLocal, entry.targetProjection⟩)
        mem.borrows mem.globals layouts mem.callerLocals = .ok v locals →
      evalRvalue locals rv mem decls layouts =
        .ok v locals
          { mem with borrows := MirSemantics.freezeDerefReadBorrowsAt locals p [] mem.borrows }) ∧
    (evalOperand locals (.copy ⟨entry.targetLocal, entry.targetProjection⟩)
        mem.borrows mem.globals layouts mem.callerLocals = .ub →
      evalRvalue locals rv mem decls layouts = .ub) := by
  have hop := evalOperand_deref_eq_target locals p mem.borrows mem.globals layouts mem.callerLocals
    ptrVal sz hp entry he hthin hperm hnd slot ht
  refine ⟨fun v hv => ?_, fun hu => ?_⟩
  · exact evalRvalue_derefRead_freeze locals rv p hcrv mem decls layouts v locals
      (hop.trans hv) (validateLoadedValue_deref_of_ptrPointeeOf layouts decls p dp srcMutbl
        pointeeIt v hdp hp_pt)
  · exact evalRvalue_derefRead_ub_of_evalOperand locals rv p hcrv mem decls layouts
      (hop.trans hu)

theorem evalRvalue_derefRead_ub (locals : List LocalSlot) {rv : Rvalue} {p : Nat}
    (hcrv : copyRv rv = .use (.copy ⟨p, [.deref]⟩)) (mem : MirSemantics.Memory)
    (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (h : locals[p]? = some .uninit ∨ locals[p]? = some .dead) :
    evalRvalue locals rv mem decls layouts = .ub := by
  have hops := evalOperand_deref_ub_of_not_init locals p mem.borrows mem.globals layouts
    mem.callerLocals h
  rcases copyRv_derefRead hcrv with rfl | rfl | rfl
  · simp [evalRvalue, hops.1]
  · simp [evalRvalue, hops.2]
  · simp [evalRvalue, hops.1]

theorem writePlaceValue_deref_not_init (locals : List LocalSlot) (borrows : List BorrowEntry)
    (p : Nat) (val : Value) (h : locals[p]? = some .uninit ∨ locals[p]? = some .dead) :
    writePlaceValue locals borrows ⟨p, [.deref]⟩ val = .ub := by
  rcases h with h | h <;> simp [writePlaceValue, get?, h]

theorem evalStatement_assign_local_load_eq {m m1 : Mach} {i : Nat} {pe pe' : Gen.PlaceExpr}
    {place : Gen.Place BM} {ty : Gen.Type} {pl : Gen.Place BM} {T : Gen.Type}
    (hloc : evalPlace m (.Local (localName i)) = .ok ((pl, T), m))
    (hloc1 : evalPlace m1 (.Local (localName i)) = .ok ((pl, T), m1))
    (h1 : evalPlace m pe = .ok ((place, ty), m1)) (h2 : evalPlace m1 pe' = .ok ((place, ty), m1)) :
    evalStatement m (.Assign (.Local (localName i)) (.Load pe)) =
      evalStatement m1 (.Assign (.Local (localName i)) (.Load pe')) := by
  simp [evalStatement, hloc, hloc1, evalValue, h1, h2]

theorem evalStatement_assign_load_ub {m : Mach} {i : Nat} {pe : Gen.PlaceExpr}
    {pl : Gen.Place BM} {T : Gen.Type} {msg : String}
    (hloc : evalPlace m (.Local (localName i)) = .ok ((pl, T), m))
    (h : evalPlace m pe = .error (.ub msg)) :
    evalStatement m (.Assign (.Local (localName i)) (.Load pe)) = .error (.ub msg) :=
  evalStatement_assign_ub_of hloc (by rw [evalValue, h]; rfl)

theorem evalStatement_assign_place_ub {m : Mach} {pe : Gen.PlaceExpr} {e : Gen.ValueExpr}
    {msg : String} (h : evalPlace m pe = .error (.ub msg)) :
    evalStatement m (.Assign pe e) = .error (.ub msg) := by
  rw [evalStatement, h]
  rfl

theorem evalStatement_assign_deref_load_eq {m m1 m2 : Mach}
    {dstPe dstPe' srcPe srcPe' : Gen.PlaceExpr}
    {dstPlace srcPlace : Gen.Place BM} {dstTy srcTy : Gen.Type}
    (hdst1 : evalPlace m dstPe = .ok ((dstPlace, dstTy), m1))
    (hsrc1 : evalPlace m1 srcPe = .ok ((srcPlace, srcTy), m2))
    (hdst2 : evalPlace m2 dstPe' = .ok ((dstPlace, dstTy), m2))
    (hsrc2 : evalPlace m2 srcPe' = .ok ((srcPlace, srcTy), m2)) :
    evalStatement m (.Assign dstPe (.Load srcPe)) =
      evalStatement m2 (.Assign dstPe' (.Load srcPe')) := by
  simp [evalStatement, hdst1, hdst2, evalValue, hsrc1, hsrc2]

theorem evalStatement_assign_deref_load_ub {m m1 : Mach}
    {dstPe srcPe : Gen.PlaceExpr} {dstPlace : Gen.Place BM} {dstTy : Gen.Type} {msg : String}
    (hdst : evalPlace m dstPe = .ok ((dstPlace, dstTy), m1))
    (hsrc : evalPlace m1 srcPe = .error (.ub msg)) :
    evalStatement m (.Assign dstPe (.Load srcPe)) = .error (.ub msg) := by
  simp [evalStatement, hdst, evalValue, hsrc]

theorem projIdx_constantIndex (locals : List LocalSlot) {count offset minLen : Nat}
    {fromEnd : Bool} (hmin : minLen ≤ count)
    (hb : if fromEnd then 1 ≤ offset ∧ offset ≤ count else offset < count) :
    projIdx locals count (.constantIndex offset minLen fromEnd) =
      some (if fromEnd then count - offset else offset) := by
  have hnot : ¬ count < minLen := by omega
  cases fromEnd <;> simp only [Bool.false_eq_true, ↓reduceIte] at hb <;>
    simp only [projIdx, hnot, Bool.false_eq_true, ↓reduceIte] <;> split <;> first | rfl | omega

/-! ## Writes through a pointer -/

/-- A write `(*_p) = rv` lands on the borrow target `q` of `_p`'s pointer: in
MiniRust it is the assignment of `rv` to `q`'s place expression; in Anneal the
value of `rv` is stored in `q`'s local, either as a whole (an unprojected `q`;
`writePlaceValue_deref_root`) or through `q`'s projection
(`writePlaceValue_deref_proj`). Both fail exactly when `rv` reads an
uninitialized local. -/
theorem derefWrite_target {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m1 : Mach} {blk stmt : Nat}
    (h1 : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m1 blk stmt)
    (hbo : BorrowsOk body ctx view s lm) (hfrag : inFragment body = true)
    (hslotsA : SlotsOk body.layouts body.localDecls s.frame.locals)
    (hnA : s.frame.locals.length = body.localDecls.length)
    (q : Place) (pointeeIt : Gen.IntType) (relOff : Nat)
    (htspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    (hk_addr : q.local_ ∈ bodyAddrTakenLocals body)
    (hkAgree : s.frame.locals[q.local_]? = view[q.local_]?)
    (rv : Rvalue) (hrvok : rvalueOk body.layouts body.localDecls pointeeIt rv = true)
    (hagree : ReadsAgree s.frame.locals view (rvOperands rv))
    {targetTy : Option MirAst.Ty} (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e)
    (targetPe : Gen.PlaceExpr) (htpe : translatePlace body.localDecls q = some targetPe) :
    ∃ res : Option Value,
      (∀ w, res = some w →
        (∃ m3, evalStatement m1 (.Assign targetPe e) = .ok m3 ∧
          FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) (view.set q.local_ (.init w))
            lm m3 blk stmt) ∧
        ∃ v, evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
            .ok v s.frame.locals s.memory ∧
          ((q.projection = [] ∧ w = v) ∨
            ∃ ph pt rootVal, q.projection = ph :: pt ∧
              s.frame.locals[q.local_]? = some (.init rootVal) ∧
              ∀ L, writeProjectedValue L rootVal (ph :: pt) v = .ok w)) ∧
      (res = none →
        (∃ msg, evalStatement m1 (.Assign targetPe e) = .error (.ub msg)) ∧
        evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts = .ub) := by
  obtain ⟨hk_lt, hcases⟩ := ptrTargetSpec_cases h1.declsOk htspec
  obtain ⟨k, projs⟩ := q
  simp only at hk_lt hcases hk_addr hkAgree ⊢
  obtain ⟨hnd_k, _, _⟩ := hbo.target_ptrs hfrag k hk_addr
  have hnsOps : OpsNonScalarInit body.localDecls s.frame.locals (rvOperands rv) :=
    h1.nonScalar.opsInit_of_readsAgree hagree
  have hfr : rvBits body.localDecls s.frame.locals pointeeIt body.layouts rv =
      rvBits body.localDecls view pointeeIt body.layouts rv := rvBits_frame_raw hagree
  obtain ⟨sk, hsk⟩ : ∃ slot, view[k]? = some slot :=
    ⟨_, List.getElem?_eq_getElem (by rw [h1.locs.nlocals]; exact hk_lt)⟩
  rcases hcases with ⟨hproj, dk, hdk, hit⟩ |
      ⟨offset, minLen, fromEnd, dk, count, hproj, hdk, ha, hpok, hbound⟩ |
      ⟨idx, fieldTy, rest, hproj, hpok, htupSome, dk, fields, size, align, relOff', hdk, ht, hres⟩
  · -- an integer local
    subst hproj
    have hitd : itOf dk body.layouts = pointeeIt := (tyOf_int hit).2
    have hint : intTypeOf dk.ty = some (itOf dk body.layouts) := by rw [hitd]; exact hit
    have hgood : GoodSize pointeeIt.size.bytes := intTypeOf_good hit
    simp only [translatePlace, Option.some.injEq] at htpe
    subst htpe
    obtain ⟨hM1, hM2⟩ := evalStatement_assign h1 k dk hdk hnd_k hint rv
      (by rw [hitd]; exact hrvok) e he
    rw [hitd] at hM1 hM2
    obtain ⟨hA1, hA2⟩ := evalRvalue_frag body.localDecls s.frame.locals hslotsA hnA pointeeIt hgood
      rv hrvok hnsOps s.memory
    refine ⟨(rvBits body.localDecls view pointeeIt body.layouts rv).map
      (fun r => .scalar ⟨r, pointeeIt.size.bytes⟩), fun w hw => ?_, fun hw => ?_⟩
    · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hw
      exact ⟨hM1 r hr, _, hA1 r (hfr.trans hr), .inl ⟨rfl, rfl⟩⟩
    · have hr := Option.map_eq_none_iff.mp hw
      exact ⟨hM2 hr, hA2 (hfr.trans hr)⟩
  · -- an in-bounds constant element of an array local
    subst hproj
    have hgood := arrayTypeOf_good ha
    obtain ⟨⟨v0, rfl⟩, _⟩ := h1.nonScalar k dk sk hdk hsk (scalarTypeOf_none_of_arrayTypeOf ha)
      (isPtrTy_false_of_arrayTypeOf ha)
    have hsloti := (DeclSlotOk_of_arrayTypeOf ha (.init v0)).mp (h1.locs.slots k dk (.init v0) hdk hsk)
    match v0, hsloti, hsk with
    | .aggregate 0 elems, ⟨hlenE, _⟩, hsk =>
      have hskA : s.frame.locals[k]? = some (.init (.aggregate 0 elems)) := hkAgree.trans hsk
      obtain ⟨hM1, hM2⟩ := evalStatement_assign_index h1 k dk hdk pointeeIt count ha _ hpok targetPe
        htpe rv hrvok e he elems hsk
      obtain ⟨hA1, hA2⟩ := evalRvalue_frag body.localDecls s.frame.locals hslotsA hnA pointeeIt
        hgood rv hrvok hnsOps s.memory
      have hmin : minLen ≤ count := by
        simp only [projOk, Bool.and_eq_true, decide_eq_true_eq] at hpok
        exact hpok.1.1
      have hidx := projIdx_constantIndex view hmin hbound
      refine ⟨(rvBits body.localDecls view pointeeIt body.layouts rv).map
        (fun r => .aggregate 0 (elems.set (if fromEnd then count - offset else offset)
          (.scalar ⟨r, pointeeIt.size.bytes⟩))), fun w hw => ?_, fun hw => ?_⟩
      · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hw
        refine ⟨hM1 _ r hidx hr, _, hA1 r (hfr.trans hr),
          .inr ⟨_, [], _, rfl, hskA, fun L => ?_⟩⟩
        exact (writeProjectedValue_proj body.localDecls L count elems hlenE _ hpok
          _).1 _ (projIdx_constantIndex L hmin hbound)
      · have hr := Option.map_eq_none_iff.mp hw
        exact ⟨hM2 (.inr hr), hA2 (hfr.trans hr)⟩
  · -- a scalar field chain of a tuple/struct local
    subst hproj
    obtain ⟨⟨rootVal, rfl⟩, _⟩ := h1.nonScalar k dk sk hdk hsk (scalarTypeOf_none_of_tupleTypeOf ht)
      (isPtrTy_false_of_tupleTypeOf ht)
    have hskA : s.frame.locals[k]? = some (.init rootVal) := hkAgree.trans hsk
    have hsloti := (DeclSlotOk_of_tupleTypeOf ht (.init rootVal)).mp
      (h1.locs.slots k dk (.init rootVal) hdk hsk)
    obtain ⟨hleafWf, _⟩ := resolveFieldPath_wf hsloti.1 hres
    have hgood : GoodSize pointeeIt.size.bytes := (goodAlignBytes_iff pointeeIt.size.bytes).mp hleafWf
    obtain ⟨hM1, hM2⟩ := evalStatement_assign_field_scalar h1 k idx fieldTy rest htupSome pointeeIt
      hpok targetPe htpe rv hrvok e he rootVal hsk
    obtain ⟨hA1, hA2⟩ := evalRvalue_frag body.localDecls s.frame.locals hslotsA hnA pointeeIt hgood
      rv hrvok hnsOps s.memory
    refine ⟨(rvBits body.localDecls view pointeeIt body.layouts rv).bind (fun r =>
      writeFieldPath rootVal (.field idx fieldTy :: rest) (.scalar ⟨r, pointeeIt.size.bytes⟩)),
      fun w hw => ?_, fun hw => ?_⟩
    · cases hr : rvBits body.localDecls view pointeeIt body.layouts rv with
      | none => simp [hr] at hw
      | some r =>
        simp only [hr, Option.bind_some] at hw
        obtain ⟨newRootVal, m3, hwpath, hwsem, hm3, h3⟩ := hM1 r hr
        rw [hwpath] at hw
        cases hw
        exact ⟨⟨m3, hm3, h3⟩, _, hA1 r (hfr.trans hr),
          .inr ⟨_, _, rootVal, rfl, hskA, hwsem⟩⟩
    · cases hr : rvBits body.localDecls view pointeeIt body.layouts rv with
      | none => exact ⟨hM2 hr, hA2 (hfr.trans hr)⟩
      | some r =>
        obtain ⟨newRootVal, m3, hwpath, _⟩ := hM1 r hr
        simp [hr, hwpath] at hw

/-! ## `StatementKind.retag` / `Statement.Validate` correspondence -/

theorem statementOk_retag_spec {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {kind : RetagKind} {p : Place} {span : String}
    (hok : statementOk decls ⟨.retag kind p, span⟩ layouts = true) :
    ∃ (i : Nat) (di : LocalDecl) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType),
      p = ⟨i, []⟩ ∧ isRetagFnEntry kind = false ∧ decls[i]? = some di ∧
      ptrPointeeOf di.ty = some (mutbl, pointeeIt) := by
  rcases p with ⟨i, projs⟩
  cases projs with
  | cons _ _ => simp [statementOk] at hok
  | nil =>
    simp only [statementOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      isDeclPtrLocal] at hok
    obtain ⟨⟨hkind, hin⟩, hptr⟩ := hok
    obtain ⟨di, hdi⟩ : ∃ di, decls[i]? = some di := ⟨_, List.getElem?_eq_getElem hin⟩
    rw [hdi] at hptr
    simp only [isPtrTy, Option.isSome_iff_exists] at hptr
    obtain ⟨⟨mutbl, pointeeIt⟩, hpt⟩ := hptr
    exact ⟨i, di, mutbl, pointeeIt, rfl, hkind, hdi, hpt⟩

/-- Anneal's execution of `StatementKind.retag` (`isRetagFnEntry kind = false`) on
a thin pointer or reference local `_i`: advances the program counter unchanged when
`_i` holds an initialized pointer whose `BorrowEntry` is not `.disabled` (and not
`.frozen` when `_i` is a mutable reference), and raises UB when `_i` is
uninitialized or dead. -/
theorem evalStmt_retag_local (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (kind : RetagKind) (i : Nat) (span : String)
    (hkind : isRetagFnEntry kind = false) :
    (∀ (ptrVal : ProvenancePtr) (sz : Nat) (entry : BorrowEntry),
      s.frame.locals[i]? = some (.init (.ptr ptrVal sz)) →
      lookupBorrow s.memory.borrows ptrVal.tag = some entry →
      entry.perm ≠ .disabled →
      ((match placeTy decls layouts ⟨i, []⟩ with
        | some { kind := .ref .mut _, .. } => true
        | _ => false) = true → entry.perm ≠ .frozen) →
      evalStmt s ⟨.retag kind ⟨i, []⟩, span⟩ decls layouts =
        .tau (.running (advanceStmt s s.frame.locals s.memory))) ∧
    ((s.frame.locals[i]? = some .uninit ∨ s.frame.locals[i]? = some .dead) →
      evalStmt s ⟨.retag kind ⟨i, []⟩, span⟩ decls layouts = MirStepNode.fail .ub) := by
  refine ⟨fun ptrVal sz entry hi hlk hndis hnf => ?_, fun hu => ?_⟩
  · cases hperm : entry.perm with
    | disabled => exact absurd hperm hndis
    | active | reserved =>
      cases kind with
      | fnEntry => simp [isRetagFnEntry] at hkind
      | default | twoPhase | raw =>
        simp [evalStmt, evalOperand, get?, hi, readProjectedValue, hlk, hperm,
          MirStepNode.step, advanceStmt]
    | frozen =>
      have hnot_mut : (match placeTy decls layouts ⟨i, []⟩ with
          | some { kind := .ref .mut _, .. } => true
          | _ => false) = false := by
        cases hm : (match placeTy decls layouts ⟨i, []⟩ with
          | some { kind := .ref .mut _, .. } => true
          | _ => false) with
        | false => rfl
        | true => exact absurd hperm (hnf hm)
      cases kind with
      | fnEntry => simp [isRetagFnEntry] at hkind
      | default | twoPhase | raw =>
        simp [evalStmt, evalOperand, get?, hi, readProjectedValue, hlk, hperm,
          MirStepNode.step, advanceStmt]
        rw [hnot_mut]
        rfl
  · rcases hu with hu | hu <;> simp [evalStmt, evalOperand, get?, hu]

theorem retag_not_frozen_of_usable {decls : List LocalDecl} {layouts : Layout.LayoutTable}
    {i : Nat} {di : LocalDecl} {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    {entry : BorrowEntry}
    (hdi : decls[i]? = some di)
    (hi_ty : ptrPointeeOf di.ty = some (mutbl, pointeeIt))
    (hmut : mutbl = .mut → entry.perm = .active ∨ entry.perm = .reserved) :
    (match placeTy decls layouts ⟨i, []⟩ with
      | some { kind := .ref .mut _, .. } => true
      | _ => false) = true → entry.perm ≠ .frozen := by
  intro hm
  have hpl : placeTy decls layouts ⟨i, []⟩ = some di.ty := by
    simp [placeTy, resolveProjectedTy, get?, hdi]
  rw [hpl] at hm
  have hmut_eq : mutbl = .mut := by
    unfold ptrPointeeOf at hi_ty
    rcases di with ⟨_, ⟨kind, _⟩, _⟩
    dsimp only at hm hi_ty
    cases kind <;> try (simp at hm)
    rename_i m inner
    cases m
    · simp at hm
    · simp only [Option.map_eq_some_iff] at hi_ty
      obtain ⟨_, _, heq⟩ := hi_ty
      exact (Prod.mk.inj heq).1.symm
  rcases hmut hmut_eq with hp | hp <;> simp [hp]

/-- MiniRust's execution of `Statement::Validate` on a declared pointer or
reference local `_i`: when `view[i]?` holds an initialized pointer, validates
and retags `_i` in place while preserving `FrameOk` (and returning the live
`BorrowEntry` in `s.memory.borrows`); when `view[i]?` is `.uninit` or `.dead`,
raises UB. -/
theorem evalStatement_validate_local_mr {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm)
    (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (i : Nat) (di : LocalDecl) (srcMutbl : MirAst.Mutability) (srcIt : Gen.IntType)
    (fnEntry : Bool)
    (hdi : body.localDecls[i]? = some di)
    (hi_ty : ptrPointeeOf di.ty = some (srcMutbl, srcIt)) :
    (∃ (ptrVal : ProvenancePtr) (entry : BorrowEntry) (m1 : Mach),
      view[i]? = some (.init (.ptr ptrVal 8)) ∧
      lookupBorrow s.memory.borrows ptrVal.tag = some entry ∧
      evalStatement m (.Validate (.Local (localName i)) fnEntry) = .ok m1 ∧
      FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m1 blk stmt) ∨
    ((view[i]? = some .uninit ∨ view[i]? = some .dead) ∧
      ∃ msg, evalStatement m (.Validate (.Local (localName i)) fnEntry) = .error (.ub msg)) := by
  have hi_lt : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdi).1
  have hisPtr : isPtrTy di.ty = true := by simp [isPtrTy, hi_ty]
  obtain ⟨hTdi, hitdi⟩ := tyOf_isPtrTy (layouts := body.layouts) hisPtr
  have hloc := (h.hf.2 i di hdi).2
  rw [hTdi] at hloc
  obtain ⟨_, sloti, hdi', hsi⟩ := h.slot_exists i hi_lt
  rw [hdi] at hdi'; cases hdi'
  have hslotOk := h.slots i di sloti hdi hsi
  cases sloti with
  | dead =>
    right
    refine ⟨.inr hsi, ?_⟩
    cases hlm_i : mapGet lm (localName i) with
    | none =>
      exact ⟨"access to a dead local",
        by simp [evalStatement, evalPlace_local_none h.shape i (declPtrTy di.ty) hloc hlm_i]⟩
    | some ptr_i =>
      obtain ⟨id, hpid, _, _, _, _, hAi⟩ := h.locs.storage i di .dead ptr_i hdi hsi hlm_i
      simp only [hisPtr, ↓reduceIte, declSlotData_of_isPtrTy hisPtr, hitdi] at hAi
      obtain ⟨msg, hmsg⟩ := typedLoad_ptr_declPtrTy_uninit h.shape ptr_i id hpid di.ty hAi
      exact ⟨msg, by simp [evalStatement,
        evalPlace_local_some h.shape i (declPtrTy di.ty) hloc ptr_i hlm_i, placeLoad, hmsg]⟩
  | uninit =>
    right
    refine ⟨.inl hsi, ?_⟩
    obtain ⟨ptr_i, hlm_i⟩ := h.locs.some_of_live hsi (by simp)
    obtain ⟨id, hpid, _, _, _, _, hAi⟩ := h.locs.storage i di .uninit ptr_i hdi hsi hlm_i
    simp only [hisPtr, ↓reduceIte, declSlotData_of_isPtrTy hisPtr, hitdi] at hAi
    obtain ⟨msg, hmsg⟩ := typedLoad_ptr_declPtrTy_uninit h.shape ptr_i id hpid di.ty hAi
    exact ⟨msg, by simp [evalStatement,
      evalPlace_local_some h.shape i (declPtrTy di.ty) hloc ptr_i hlm_i, placeLoad, hmsg]⟩
  | init v =>
    left
    obtain ⟨ptrVal, rfl⟩ := (DeclSlotOk_of_isPtrTy hisPtr (.init v)).mp hslotOk
    obtain ⟨entry, relOff, _, hlookup, htspec⟩ :=
      hb.ptr_slots i di srcMutbl srcIt ptrVal hdi hi_ty hsi
    obtain ⟨hentry_mem, _⟩ := lookupBorrow_mem_and_tag hlookup
    obtain ⟨_, _, _, _, hk_addr, _⟩ := hb.entries_ok entry hentry_mem
    obtain ⟨_, _, hgood, _, hptrEq, hal, _⟩ :=
      evalTargetPlace h hb hns hfrag ⟨entry.targetLocal, entry.targetProjection⟩ srcIt relOff htspec hk_addr
    obtain ⟨htpos, htderef⟩ :=
      evalTargetPlace_deref h hb hfrag ⟨entry.targetLocal, entry.targetProjection⟩ srcIt relOff htspec hk_addr
    obtain ⟨ptr_i, hlm_i⟩ := h.locs.some_of_live hsi (by simp)
    obtain ⟨id, hpid, _, _, _, _, hAi⟩ :=
      h.locs.storage i di (.init (.ptr ptrVal 8)) ptr_i hdi hsi hlm_i
    simp only [hisPtr, ↓reduceIte, hitdi] at hAi
    obtain ⟨tAddr, tProv, htlt0, htgt, hAk⟩ := hAi
    have hbt : (ctxWithBorrows body ctx s.memory.borrows).ptrTargets ptrVal.allocId =
        some ((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat,
              some (⟨((ctx.base.length + entry.targetLocal : Nat) : Int)⟩, ())) := by
      simp [ctxWithBorrows, borrowTargets, ProvenancePtr.tag] at hlookup ⊢
      simp [hlookup, htspec]
    obtain ⟨rfl, rfl⟩ := htgt _ _ hbt
    have htal : Align.is_aligned ⟨srcIt.size.bytes⟩
        (((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat : Int)) = true := by
      rw [← hptrEq] at hal
      exact hal
    have htderef' : CM.dereferenceable m.mem
        { addr := ((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat : Int),
          provenance := some (⟨((ctx.base.length + entry.targetLocal : Nat) : Int)⟩, ()) }
        srcIt.size = .ok () := by
      rw [← hptrEq] at htderef
      exact htderef
    obtain ⟨m1, hm1, hs1⟩ := evalStatement_validate_declPtrTy h.shape (.Local (localName i))
      ptr_i id fnEntry hpid di.ty srcMutbl srcIt hi_ty hgood _ htpos htlt0 _ htal htderef'
      (evalPlace_local_some h.shape i (declPtrTy di.ty) hloc ptr_i hlm_i) hAk
    exact ⟨ptrVal, entry, m1, hsi, hlookup, hm1,
      FrameOk.mk' h.hf hs1 h.locs h.declsOk h.nonScalar⟩

/-! ## `PointerExposeProvenance` & `PointerWithExposedProvenance` (`IntPtrCast`) Correspondence (MR-3.3) -/

/-- When `m.intptrcast.exposed` is empty (`[]`), `int2ptrProvenance` deterministically
predicts `none` (unexposed integer-to-pointer cast). -/
theorem int2ptrProvenance_empty {m : Mach} (addr : Int)
    (hempty : m.intptrcast.exposed.elems = []) :
    int2ptrProvenance m addr = .ok none := by
  simp [int2ptrProvenance, hempty, pure, Except.pure]

theorem IntPtrCast.int2ptr_empty {m : Mach} (addr : Int)
    (hempty : m.intptrcast.exposed.elems = []) :
    IntPtrCast.int2ptr m addr = .ok { addr := addr, provenance := none } := by
  simp [IntPtrCast.int2ptr, int2ptrProvenance_empty addr hempty, bind, Except.bind, pure, Except.pure]

theorem int2ptrProvenanceM_empty {M : Type} [Gen.Memory M] [MemoryOps M] {m : Gen.Machine M}
    (addr : Int) (hempty : m.intptrcast.exposed.elems = []) :
    int2ptrProvenanceM m addr = .ok none := by
  simp [int2ptrProvenanceM, hempty, pure, Except.pure]

theorem IntPtrCast.int2ptrM_empty {M : Type} [Gen.Memory M] [MemoryOps M] {m : Gen.Machine M}
    (addr : Int) (hempty : m.intptrcast.exposed.elems = []) :
    IntPtrCast.int2ptrM m addr = .ok { addr := addr, provenance := none } := by
  simp [IntPtrCast.int2ptrM, int2ptrProvenanceM_empty addr hempty, bind, Except.bind, pure, Except.pure]

/-- When `m.intptrcast.exposed` holds a single provenance `[p]`, `int2ptrProvenance`
deterministically predicts `some p`. -/
theorem int2ptrProvenance_singleton {m : Mach} (addr : Int) (p : Prov)
    (hsingle : m.intptrcast.exposed.elems = [p]) :
    int2ptrProvenance m addr = .ok (some p) := by
  simp [int2ptrProvenance, hsingle, pure, Except.pure]

theorem IntPtrCast.int2ptr_singleton {m : Mach} (addr : Int) (p : Prov)
    (hsingle : m.intptrcast.exposed.elems = [p]) :
    IntPtrCast.int2ptr m addr = .ok { addr := addr, provenance := some p } := by
  simp [IntPtrCast.int2ptr, int2ptrProvenance_singleton addr p hsingle, bind, Except.bind, pure, Except.pure]

theorem int2ptrProvenanceM_singleton {M : Type} [Gen.Memory M] [MemoryOps M] {m : Gen.Machine M}
    (addr : Int) (p : Gen.Memory.Provenance M) (hsingle : m.intptrcast.exposed.elems = [p]) :
    int2ptrProvenanceM m addr = .ok (some p) := by
  simp [int2ptrProvenanceM, hsingle, pure, Except.pure]

theorem IntPtrCast.int2ptrM_singleton {M : Type} [Gen.Memory M] [MemoryOps M] {m : Gen.Machine M}
    (addr : Int) (p : Gen.Memory.Provenance M) (hsingle : m.intptrcast.exposed.elems = [p]) :
    IntPtrCast.int2ptrM m addr = .ok { addr := addr, provenance := some p } := by
  simp [IntPtrCast.int2ptrM, int2ptrProvenanceM_singleton addr p hsingle, bind, Except.bind, pure, Except.pure]

/-- When `m.intptrcast.exposed` holds `≥ 2` provenances and `int2ptrCandidates`
finds a unique live exposed allocation `[p]` containing `addr`, `int2ptrProvenance`
deterministically resolves to `some p`. -/
theorem int2ptrProvenance_multi_unique {m : Mach} (addr : Int)
    (p1 p2 : Prov) (rest : List Prov) (p : Prov)
    (hmulti : m.intptrcast.exposed.elems = p1 :: p2 :: rest)
    (hcand : int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr = [p]) :
    int2ptrProvenance m addr = .ok (some p) := by
  simp [int2ptrProvenance, hmulti, hcand, pure, Except.pure]

theorem IntPtrCast.int2ptr_multi_unique {m : Mach} (addr : Int)
    (p1 p2 : Prov) (rest : List Prov) (p : Prov)
    (hmulti : m.intptrcast.exposed.elems = p1 :: p2 :: rest)
    (hcand : int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr = [p]) :
    IntPtrCast.int2ptr m addr = .ok { addr := addr, provenance := some p } := by
  simp [IntPtrCast.int2ptr, int2ptrProvenance_multi_unique addr p1 p2 rest p hmulti hcand,
    bind, Except.bind, pure, Except.pure]

theorem int2ptrProvenanceM_multi_unique {M : Type} [Gen.Memory M] [MemoryOps M] {m : Gen.Machine M}
    (addr : Int) (p1 p2 : Gen.Memory.Provenance M) (rest : List (Gen.Memory.Provenance M))
    (p : Gen.Memory.Provenance M)
    (hmulti : m.intptrcast.exposed.elems = p1 :: p2 :: rest)
    (hcand : MemoryOps.exposedInBounds m.mem.memory m.intptrcast.exposed addr = [p]) :
    int2ptrProvenanceM m addr = .ok (some p) := by
  simp [int2ptrProvenanceM, hmulti, hcand, pure, Except.pure]

theorem IntPtrCast.int2ptrM_multi_unique {M : Type} [Gen.Memory M] [MemoryOps M] {m : Gen.Machine M}
    (addr : Int) (p1 p2 : Gen.Memory.Provenance M) (rest : List (Gen.Memory.Provenance M))
    (p : Gen.Memory.Provenance M)
    (hmulti : m.intptrcast.exposed.elems = p1 :: p2 :: rest)
    (hcand : MemoryOps.exposedInBounds m.mem.memory m.intptrcast.exposed addr = [p]) :
    IntPtrCast.int2ptrM m addr = .ok { addr := addr, provenance := some p } := by
  simp [IntPtrCast.int2ptrM, int2ptrProvenanceM_multi_unique addr p1 p2 rest p hmulti hcand,
    bind, Except.bind, pure, Except.pure]

/-- When `m.intptrcast.exposed` holds `≥ 2` provenances and no live exposed
allocation contains `addr` (`int2ptrCandidates = []`), `int2ptrProvenance`
halts with `Stop.unsupported` (angelic choice). -/
theorem int2ptrProvenance_multi_none_unsupported {m : Mach} (addr : Int)
    (p1 p2 : Prov) (rest : List Prov)
    (hmulti : m.intptrcast.exposed.elems = p1 :: p2 :: rest)
    (hcand : int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr = []) :
    int2ptrProvenance m addr =
      .error (.unsupported "int2ptr: multiple exposed allocations and none contains the address (angelic choice)") := by
  simp [int2ptrProvenance, hmulti, hcand, unsupported]

theorem IntPtrCast.int2ptr_multi_none_unsupported {m : Mach} (addr : Int)
    (p1 p2 : Prov) (rest : List Prov)
    (hmulti : m.intptrcast.exposed.elems = p1 :: p2 :: rest)
    (hcand : int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr = []) :
    IntPtrCast.int2ptr m addr =
      .error (.unsupported "int2ptr: multiple exposed allocations and none contains the address (angelic choice)") := by
  simp [IntPtrCast.int2ptr, int2ptrProvenance_multi_none_unsupported addr p1 p2 rest hmulti hcand,
    bind, Except.bind]

theorem int2ptrProvenanceM_multi_none_unsupported {M : Type} [Gen.Memory M] [MemoryOps M]
    {m : Gen.Machine M} (addr : Int)
    (p1 p2 : Gen.Memory.Provenance M) (rest : List (Gen.Memory.Provenance M))
    (hmulti : m.intptrcast.exposed.elems = p1 :: p2 :: rest)
    (hcand : MemoryOps.exposedInBounds m.mem.memory m.intptrcast.exposed addr = []) :
    int2ptrProvenanceM m addr =
      .error (.unsupported "int2ptr: multiple exposed allocations and none contains the address (angelic choice)") := by
  simp [int2ptrProvenanceM, hmulti, hcand, unsupported]

/-- When `m.intptrcast.exposed` holds `≥ 2` provenances and multiple live exposed
allocations meet at `addr` (`int2ptrCandidates = c1 :: c2 :: cs`),
`int2ptrProvenance` halts with `Stop.unsupported` (angelic choice). -/
theorem int2ptrProvenance_multi_ambiguous_unsupported {m : Mach} (addr : Int)
    (p1 p2 : Prov) (rest : List Prov) (c1 c2 : Prov) (cs : List Prov)
    (hmulti : m.intptrcast.exposed.elems = p1 :: p2 :: rest)
    (hcand : int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr = c1 :: c2 :: cs) :
    int2ptrProvenance m addr =
      .error (.unsupported "int2ptr: several exposed allocations meet at the address (angelic choice)") := by
  simp [int2ptrProvenance, hmulti, hcand, unsupported]

theorem IntPtrCast.int2ptr_multi_ambiguous_unsupported {m : Mach} (addr : Int)
    (p1 p2 : Prov) (rest : List Prov) (c1 c2 : Prov) (cs : List Prov)
    (hmulti : m.intptrcast.exposed.elems = p1 :: p2 :: rest)
    (hcand : int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr = c1 :: c2 :: cs) :
    IntPtrCast.int2ptr m addr =
      .error (.unsupported "int2ptr: several exposed allocations meet at the address (angelic choice)") := by
  simp [IntPtrCast.int2ptr,
    int2ptrProvenance_multi_ambiguous_unsupported addr p1 p2 rest c1 c2 cs hmulti hcand,
    bind, Except.bind]

theorem int2ptrProvenanceM_multi_ambiguous_unsupported {M : Type} [Gen.Memory M] [MemoryOps M]
    {m : Gen.Machine M} (addr : Int)
    (p1 p2 : Gen.Memory.Provenance M) (rest : List (Gen.Memory.Provenance M))
    (c1 c2 : Gen.Memory.Provenance M) (cs : List (Gen.Memory.Provenance M))
    (hmulti : m.intptrcast.exposed.elems = p1 :: p2 :: rest)
    (hcand : MemoryOps.exposedInBounds m.mem.memory m.intptrcast.exposed addr = c1 :: c2 :: cs) :
    int2ptrProvenanceM m addr =
      .error (.unsupported "int2ptr: several exposed allocations meet at the address (angelic choice)") := by
  simp [int2ptrProvenanceM, hmulti, hcand, unsupported]

/-- Exact characterization of membership in `int2ptrCandidates`. -/
theorem mem_int2ptrCandidates_iff (allocs : List Gen.Allocation)
    (exposed : LibSpecr.Set Prov) (addr : Int) (p : Prov) :
    p ∈ int2ptrCandidates allocs exposed addr ↔
      ∃ (a : Gen.Allocation) (i : Nat),
        (a, i) ∈ allocs.zipIdx ∧
        a.live = true ∧
        a.addr ≤ addr ∧
        addr ≤ a.addr + (Allocation.size a).bytes ∧
        setContains exposed (⟨(i : Int)⟩, ()) = true ∧
        p = (⟨(i : Int)⟩, ()) := by
  simp only [int2ptrCandidates, List.mem_map, List.mem_filter, Prod.exists,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, i, ⟨hzip, ⟨⟨hlive, hlo⟩, hhi⟩, hexp⟩, rfl⟩
    exact ⟨a, i, hzip, hlive, hlo, hhi, hexp, rfl⟩
  · rintro ⟨a, i, hzip, hlive, hlo, hhi, hexp, rfl⟩
    exact ⟨a, i, ⟨hzip, ⟨⟨hlive, hlo⟩, hhi⟩, hexp⟩, rfl⟩

/-- `evalIntrinsic` on `.PointerExposeProvenance` for a thin pointer argument
and `usize` return type exposes `ptr`'s provenance and returns `Value.Int ptr.addr`. -/
@[simp] theorem evalIntrinsic_expose_ok (m : Mach) (ptr : Ptr) (argTy : Gen.Type) :
    evalIntrinsic m .PointerExposeProvenance [(.Ptr ⟨ptr, none⟩, argTy)] (.Int usizeIt) =
      .ok (.Int ptr.addr, { m with intptrcast := IntPtrCast.expose m.intptrcast ptr }) :=
  rfl

@[simp] theorem evalIntrinsicM_expose_ok {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (ptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (argTy : Gen.Type) :
    evalIntrinsicM m .PointerExposeProvenance [(.Ptr ⟨ptr, none⟩, argTy)] (.Int usizeIt) =
      .ok (.Int ptr.addr, { m with intptrcast := IntPtrCast.exposeM m.intptrcast ptr }) :=
  rfl

/-- `evalIntrinsic` on `.PointerWithExposedProvenance` for an integer address
argument and thin pointer return type (`meta_kind = .None`). -/
theorem evalIntrinsic_withExposed_eq (m : Mach) (addr : Int) (argTy : Gen.Type)
    (retPtrTy : Gen.PtrType) (hmk : PtrType.meta_kind retPtrTy = .None) :
    evalIntrinsic m .PointerWithExposedProvenance [(.Int addr, argTy)] (.Ptr retPtrTy) =
      (do
        let ptr ← IntPtrCast.int2ptr m addr
        pure (.Ptr (ThinPointer.widen ptr none), m)) := by
  simp [evalIntrinsic, hmk]

theorem evalIntrinsic_withExposed_ok {m : Mach} {addr : Int} {argTy : Gen.Type}
    {retPtrTy : Gen.PtrType} {ptr : Ptr}
    (hmk : PtrType.meta_kind retPtrTy = .None)
    (hint : IntPtrCast.int2ptr m addr = .ok ptr) :
    evalIntrinsic m .PointerWithExposedProvenance [(.Int addr, argTy)] (.Ptr retPtrTy) =
      .ok (.Ptr ⟨ptr, none⟩, m) := by
  simp [evalIntrinsic, hmk, hint, ThinPointer.widen, bind, Except.bind, pure, Except.pure]

theorem evalIntrinsic_withExposed_err {m : Mach} {addr : Int} {argTy : Gen.Type}
    {retPtrTy : Gen.PtrType} {e : Stop}
    (hmk : PtrType.meta_kind retPtrTy = .None)
    (hint : IntPtrCast.int2ptr m addr = .error e) :
    evalIntrinsic m .PointerWithExposedProvenance [(.Int addr, argTy)] (.Ptr retPtrTy) =
      .error e := by
  simp [evalIntrinsic, hmk, hint, bind, Except.bind]

theorem evalIntrinsicM_withExposed_ok {M : Type} [Gen.Memory M] [MemoryOps M]
    {m : Gen.Machine M} {addr : Int} {argTy : Gen.Type}
    {retPtrTy : Gen.PtrType} {ptr : Gen.ThinPointer (Gen.Memory.Provenance M)}
    (hmk : PtrType.meta_kind retPtrTy = .None)
    (hint : IntPtrCast.int2ptrM m addr = .ok ptr) :
    evalIntrinsicM m .PointerWithExposedProvenance [(.Int addr, argTy)] (.Ptr retPtrTy) =
      .ok (.Ptr ⟨ptr, none⟩, m) := by
  simp [evalIntrinsicM, hmk, hint, ThinPointer.widen, bind, Except.bind, pure, Except.pure]

theorem evalIntrinsicM_withExposed_err {M : Type} [Gen.Memory M] [MemoryOps M]
    {m : Gen.Machine M} {addr : Int} {argTy : Gen.Type}
    {retPtrTy : Gen.PtrType} {e : Stop}
    (hmk : PtrType.meta_kind retPtrTy = .None)
    (hint : IntPtrCast.int2ptrM m addr = .error e) :
    evalIntrinsicM m .PointerWithExposedProvenance [(.Int addr, argTy)] (.Ptr retPtrTy) =
      .error e := by
  simp [evalIntrinsicM, hmk, hint, bind, Except.bind]

/-- Dereferencing a pointer with `provenance = none` (for example after an
unexposed `PointerWithExposedProvenance` cast) at any positive size (`size.bytes > 0`)
raises `Stop.ub "dereferencing pointer without provenance"`. -/
theorem checkPtr_none_ub (bm : BM) (addr : Int) (size : Size)
    (hpos : 0 < size.bytes) :
    BM.check_ptr bm { addr := addr, provenance := none } size =
      .error (.ub "dereferencing pointer without provenance") := by
  have hne : size.bytes ≠ 0 := by omega
  simp [BM.check_ptr, hne, ub]

/-- Dereferencing a pointer whose provenance `(AllocId(idx), ())` points to a
dead allocation (`a.live = false`) at any positive size (`size.bytes > 0`)
raises `Stop.ub "dereferencing pointer to dead allocation"`. -/
theorem checkPtr_dead_ub (bm : BM) (addr : Int) (idx : Nat) (a : Gen.Allocation)
    (size : Size)
    (hpos : 0 < size.bytes)
    (hget : bm.allocations[idx]? = some a) (hdead : a.live = false) :
    BM.check_ptr bm { addr := addr, provenance := some (⟨(idx : Int)⟩, ()) } size =
      .error (.ub "dereferencing pointer to dead allocation") := by
  have hne : size.bytes ≠ 0 := by omega
  obtain ⟨hlt, hidx⟩ := List.getElem?_eq_some_iff.mp hget
  simp [BM.check_ptr, hne, listIndex, hlt, hidx, hdead, ub, bind, Except.bind]

/-- Anneal's execution of `_i = Cast(PointerExposeProvenance, copy _p, usize)`
into a live local `_i`: when `_p` holds `.init (.ptr pv 8)`, stores
`.scalar ⟨pv.allocId * 65536 + pv.offsetBytes, 8⟩` into `_i`; when `_p` is
`.uninit` or `.dead`, raises UB. -/
theorem evalStmt_assign_expose (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i p : Nat) (targetTy : MirAst.Ty) (span : String)
    (hi : i < s.frame.locals.length)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hprot : s.memory.activeProtectors = []) :
    (∀ (pv : ProvenancePtr),
      s.frame.locals[p]? = some (.init (.ptr pv 8)) →
      s.frame.locals[i]? ≠ some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance (.copy ⟨p, []⟩) targetTy), span⟩
          decls layouts =
        .tau (.running (advanceStmt s
          (s.frame.locals.set i (.init (.scalar ⟨pv.allocId * 65536 + pv.offsetBytes, 8⟩)))
          s.memory))) ∧
    ((s.frame.locals[p]? = some .uninit ∨ s.frame.locals[p]? = some .dead) →
      evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance (.copy ⟨p, []⟩) targetTy), span⟩
          decls layouts = MirStepNode.fail .ub) := by
  have hav := evalStmt_assign_val s decls layouts i
    (.cast .pointerExposeProvenance (.copy ⟨p, []⟩) targetTy) span hi hbor_i hprot
  refine ⟨fun pv hp hnd => ?_, fun hu => ?_⟩
  · have hop : evalOperand s.frame.locals (.copy ⟨p, []⟩) s.memory.borrows s.memory.globals
        layouts s.memory.callerLocals = .ok (.ptr pv 8) s.frame.locals := by
      simp [evalOperand, get?, hp, readProjectedValue]
    have hrv := evalRvalue_expose s.frame.locals (.copy ⟨p, []⟩) targetTy s.memory decls layouts
      pv 8 s.frame.locals hop
    exact (hav.1 _ hrv).1 hnd
  · refine hav.2 ?_
    rcases hu with hu | hu <;>
      simp [evalRvalue, evalOperand, get?, hu]

/-- Anneal's execution of `_i = Cast(PointerWithExposedProvenance, copy _u, targetTy)`
into a live local `_i`: when `_u` holds `.init (.scalar sc)`, stores
`.ptr { allocId := sc.bits / 65536, offsetBytes := sc.bits % 65536 } 8` into `_i`;
when `_u` is `.uninit` or `.dead`, raises UB. -/
theorem evalStmt_assign_withExposed (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i u : Nat) (targetTy : MirAst.Ty) (span : String)
    (hi : i < s.frame.locals.length)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hprot : s.memory.activeProtectors = []) :
    (∀ (sc : ScalarInt),
      s.frame.locals[u]? = some (.init (.scalar sc)) →
      s.frame.locals[i]? ≠ some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerWithExposedProvenance (.copy ⟨u, []⟩) targetTy), span⟩
          decls layouts =
        .tau (.running (advanceStmt s
          (s.frame.locals.set i
            (.init (.ptr { allocId := sc.bits / 65536, offsetBytes := sc.bits % 65536 } 8)))
          s.memory))) ∧
    ((s.frame.locals[u]? = some .uninit ∨ s.frame.locals[u]? = some .dead) →
      evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerWithExposedProvenance (.copy ⟨u, []⟩) targetTy), span⟩
          decls layouts = MirStepNode.fail .ub) := by
  have hav := evalStmt_assign_val s decls layouts i
    (.cast .pointerWithExposedProvenance (.copy ⟨u, []⟩) targetTy) span hi hbor_i hprot
  refine ⟨fun sc hu hnd => ?_, fun hu => ?_⟩
  · have hop : evalOperand s.frame.locals (.copy ⟨u, []⟩) s.memory.borrows s.memory.globals
        layouts s.memory.callerLocals = .ok (.scalar sc) s.frame.locals := by
      simp [evalOperand, get?, hu, readProjectedValue]
    have hrv := evalRvalue_withExposed s.frame.locals (.copy ⟨u, []⟩) targetTy s.memory decls layouts
      sc s.frame.locals hop
    exact (hav.1 _ hrv).1 hnd
  · refine hav.2 ?_
    rcases hu with hu | hu <;>
      simp [evalRvalue, evalOperand, get?, hu]

/-- Anneal's `expose_provenance` -> `with_exposed_provenance` round-trip identity:
any `ProvenancePtr` with `pv.offsetBytes < 65536` (in particular `pv.offsetBytes = 0`)
recovers `pv` identically after `PointerExposeProvenance` followed by
`PointerWithExposedProvenance`. -/
theorem expose_withExposed_roundtrip (pv : ProvenancePtr) (hoff : pv.offsetBytes < 65536) :
    ({ allocId := (pv.allocId * 65536 + pv.offsetBytes) / 65536,
       offsetBytes := (pv.allocId * 65536 + pv.offsetBytes) % 65536 } : ProvenancePtr) = pv := by
  rcases pv with ⟨allocId, offsetBytes⟩
  change Nat at allocId
  dsimp only at hoff ⊢
  simp only [ProvenancePtr.mk.injEq]
  change (allocId * 65536 + offsetBytes) / 65536 = (allocId : Nat) ∧
    (allocId * 65536 + offsetBytes) % 65536 = offsetBytes
  exact ⟨by omega, by omega⟩

theorem copyOp_eq_copy_local_iff (op : MirAst.Operand) (p : Nat) :
    copyOp op = .copy ⟨p, []⟩ ↔ op = .copy ⟨p, []⟩ ∨ op = .move ⟨p, []⟩ := by
  cases op with
  | copy pl => simp [copyOp]
  | move pl => simp [copyOp]
  | constant c => simp [copyOp]

/-- Operand-generic Anneal execution of `_i = Cast(PointerExposeProvenance, op, targetTy)`
for any root-local operand `op` with `copyOp op = .copy ⟨p, []⟩` (covering both
`.copy ⟨p, []⟩` and `.move ⟨p, []⟩` permitted by `statementOkWithIntrinsics`):
when `_p` holds `.init (.ptr pv 8)`, updates the operand's moved-out local via
`opPost` and stores `.scalar ⟨pv.allocId * 65536 + pv.offsetBytes, 8⟩` into `_i`;
when `_p` is `.uninit` or `.dead`, raises UB. -/
theorem evalStmt_assign_expose_op (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i p : Nat) (op : MirAst.Operand)
    (targetTy : MirAst.Ty) (span : String)
    (hop_copy : copyOp op = .copy ⟨p, []⟩)
    (hi : i < s.frame.locals.length)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hprot : s.memory.activeProtectors = []) :
    (∀ (pv : ProvenancePtr),
      s.frame.locals[p]? = some (.init (.ptr pv 8)) →
      s.frame.locals[i]? ≠ some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op targetTy), span⟩
          decls layouts =
        .tau (.running (advanceStmt s
          ((opPost s.frame.locals op).set i
            (.init (.scalar ⟨pv.allocId * 65536 + pv.offsetBytes, 8⟩)))
          s.memory))) ∧
    ((s.frame.locals[p]? = some .uninit ∨ s.frame.locals[p]? = some .dead) →
      evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op targetTy), span⟩
          decls layouts = MirStepNode.fail .ub) := by
  rcases (copyOp_eq_copy_local_iff op p).mp hop_copy with rfl | rfl
  · have hpost : opPost s.frame.locals (.copy ⟨p, []⟩) = s.frame.locals := rfl
    rw [hpost]
    exact evalStmt_assign_expose s decls layouts i p targetTy span hi hbor_i hprot
  · have hil : i < (opPost s.frame.locals (.move ⟨p, []⟩)).length := by
      rw [opPost_length]; exact hi
    have hinv := invalidateConflictingBorrows_of_ne s.memory.borrows i .none hbor_i
    refine ⟨fun pv hp hnd => ?_, fun hu => ?_⟩
    · have hp_lt : p < s.frame.locals.length := (List.getElem?_eq_some_iff.mp hp).1
      have hop : evalOperand s.frame.locals (.move ⟨p, []⟩) s.memory.borrows s.memory.globals
          layouts s.memory.callerLocals =
          .ok (.ptr pv 8) (opPost s.frame.locals (.move ⟨p, []⟩)) := by
        simp only [evalOperand, get?, hp, opPost, opMoved]
        simp [set?, hp_lt]
      have hrv := evalRvalue_expose s.frame.locals (.move ⟨p, []⟩) targetTy s.memory decls layouts
        pv 8 (opPost s.frame.locals (.move ⟨p, []⟩)) hop
      simp only [evalStmt, hrv, get?]
      cases hsl : (opPost s.frame.locals (.move ⟨p, []⟩))[i]? with
      | none => simp [hil] at hsl
      | some slot =>
        cases slot with
        | dead => exact absurd ((opPost_dead _ _ _).mp hsl) hnd
        | uninit => simp [set?, hil, hprot, hinv, MirStepNode.step, memory_mk_nil_prot s.memory hprot]
        | init w => simp [set?, hil, hprot, hinv, MirStepNode.step, memory_mk_nil_prot s.memory hprot]
    · rcases hu with hu | hu <;>
        simp [evalStmt, evalRvalue, evalOperand, get?, hu]

/-- Operand-generic Anneal execution of `_i = Cast(PointerWithExposedProvenance, op, targetTy)`
for any root-local operand `op` with `copyOp op = .copy ⟨u, []⟩` (covering both
`.copy ⟨u, []⟩` and `.move ⟨u, []⟩` permitted by `statementOkWithIntrinsics`):
when `_u` holds `.init (.scalar sc)`, updates the operand's moved-out local via
`opPost` and stores
`.ptr { allocId := sc.bits / 65536, offsetBytes := sc.bits % 65536 } 8` into `_i`;
when `_u` is `.uninit` or `.dead`, raises UB. -/
theorem evalStmt_assign_withExposed_op (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i u : Nat) (op : MirAst.Operand)
    (targetTy : MirAst.Ty) (span : String)
    (hop_copy : copyOp op = .copy ⟨u, []⟩)
    (hi : i < s.frame.locals.length)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hprot : s.memory.activeProtectors = []) :
    (∀ (sc : ScalarInt),
      s.frame.locals[u]? = some (.init (.scalar sc)) →
      s.frame.locals[i]? ≠ some .dead →
      evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerWithExposedProvenance op targetTy), span⟩
          decls layouts =
        .tau (.running (advanceStmt s
          ((opPost s.frame.locals op).set i
            (.init (.ptr { allocId := sc.bits / 65536, offsetBytes := sc.bits % 65536 } 8)))
          s.memory))) ∧
    ((s.frame.locals[u]? = some .uninit ∨ s.frame.locals[u]? = some .dead) →
      evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerWithExposedProvenance op targetTy), span⟩
          decls layouts = MirStepNode.fail .ub) := by
  rcases (copyOp_eq_copy_local_iff op u).mp hop_copy with rfl | rfl
  · have hpost : opPost s.frame.locals (.copy ⟨u, []⟩) = s.frame.locals := rfl
    rw [hpost]
    exact evalStmt_assign_withExposed s decls layouts i u targetTy span hi hbor_i hprot
  · have hil : i < (opPost s.frame.locals (.move ⟨u, []⟩)).length := by
      rw [opPost_length]; exact hi
    have hinv := invalidateConflictingBorrows_of_ne s.memory.borrows i .none hbor_i
    refine ⟨fun sc hu hnd => ?_, fun hu => ?_⟩
    · have hu_lt : u < s.frame.locals.length := (List.getElem?_eq_some_iff.mp hu).1
      have hop : evalOperand s.frame.locals (.move ⟨u, []⟩) s.memory.borrows s.memory.globals
          layouts s.memory.callerLocals =
          .ok (.scalar sc) (opPost s.frame.locals (.move ⟨u, []⟩)) := by
        simp only [evalOperand, get?, hu, opPost, opMoved]
        simp [set?, hu_lt]
      have hrv := evalRvalue_withExposed s.frame.locals (.move ⟨u, []⟩) targetTy s.memory decls layouts
        sc (opPost s.frame.locals (.move ⟨u, []⟩)) hop
      simp only [evalStmt, hrv, get?]
      cases hsl : (opPost s.frame.locals (.move ⟨u, []⟩))[i]? with
      | none => simp [hil] at hsl
      | some slot =>
        cases slot with
        | dead => exact absurd ((opPost_dead _ _ _).mp hsl) hnd
        | uninit => simp [set?, hil, hprot, hinv, MirStepNode.step, memory_mk_nil_prot s.memory hprot]
        | init w => simp [set?, hil, hprot, hinv, MirStepNode.step, memory_mk_nil_prot s.memory hprot]
    · rcases hu with hu | hu <;>
        simp [evalStmt, evalRvalue, evalOperand, get?, hu]

/-! ## `evalTerminator` / `evalTerminatorM` step lemmas for `Terminator::Intrinsic` (MR-3.3 Pass A2) -/

@[simp] theorem evalArgs_singleton (m : Mach) (e : Gen.ValueExpr) :
    evalArgs m [e] =
      (do
        let (arg, m1) ← evalValue m e
        pure ([arg], m1)) := by
  simp [evalArgs, bind, Except.bind, pure, Except.pure]

@[simp] theorem evalArgsM_singleton {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (e : Gen.ValueExpr) :
    evalArgsM m [e] =
      (do
        let (arg, m1) ← evalValueM m e
        pure ([arg], m1)) := by
  simp [evalArgsM, bind, Except.bind, pure, Except.pure]

/-- Full `evalTerminator` step for `Terminator::Intrinsic .PointerExposeProvenance`:
evaluates `retExpr` to `(retPlace, .Int usizeIt)`, evaluates `argExpr` to a thin
pointer `(.Ptr ⟨ptr, none⟩, argTy)`, exposes `ptr` in `m2.intptrcast`, stores
`.Int ptr.addr` into `retPlace`, and jumps to `nb`. -/
theorem evalTerminator_intrinsic_expose_ok {m m1 m2 m3 m4 : Mach}
    {argExpr : Gen.ValueExpr} {retExpr : Gen.PlaceExpr} {nb : Gen.BbName}
    {retPlace : Gen.Place BM} {ptr : Ptr} {argTy : Gen.Type}
    (hplace : evalPlace m retExpr = .ok ((retPlace, .Int usizeIt), m1))
    (harg : evalValue m1 argExpr = .ok ((.Ptr ⟨ptr, none⟩, argTy), m2))
    (hstore : placeStore { m2 with intptrcast := IntPtrCast.expose m2.intptrcast ptr }
        retPlace (.Int ptr.addr) (.Int usizeIt) = .ok m3)
    (hjump : jumpToBlock m3 nb = .ok m4) :
    Interp.evalTerminator m (.Intrinsic .PointerExposeProvenance [argExpr] retExpr (some nb)) =
      .ok m4 := by
  simp [Interp.evalTerminator, hplace, harg, hstore, hjump, bind, Except.bind, pure, Except.pure]

/-- Polymorphic `evalTerminatorM` step for `Terminator::Intrinsic .PointerExposeProvenance`. -/
theorem evalTerminatorM_intrinsic_expose_ok {M : Type} [Gen.Memory M] [MemoryOps M]
    {m m1 m2 m3 m4 : Gen.Machine M}
    {argExpr : Gen.ValueExpr} {retExpr : Gen.PlaceExpr} {nb : Gen.BbName}
    {retPlace : Gen.Place M} {ptr : Gen.ThinPointer (Gen.Memory.Provenance M)} {argTy : Gen.Type}
    (hplace : evalPlaceM m retExpr = .ok ((retPlace, .Int usizeIt), m1))
    (harg : evalValueM m1 argExpr = .ok ((.Ptr ⟨ptr, none⟩, argTy), m2))
    (hstore : placeStoreM { m2 with intptrcast := IntPtrCast.exposeM m2.intptrcast ptr }
        retPlace (.Int ptr.addr) (.Int usizeIt) = .ok m3)
    (hjump : jumpToBlockM m3 nb = .ok m4) :
    Interp.evalTerminatorM m (.Intrinsic .PointerExposeProvenance [argExpr] retExpr (some nb)) =
      .ok m4 := by
  simp [Interp.evalTerminatorM, hplace, harg, hstore, hjump, bind, Except.bind, pure, Except.pure]

/-- Full `evalTerminator` step for `Terminator::Intrinsic .PointerWithExposedProvenance`
when `IntPtrCast.int2ptr` succeeds: evaluates `retExpr` to `(retPlace, .Ptr retPtrTy)`,
evaluates `argExpr` to `(.Int addr, argTy)`, predicts `ptr` via `IntPtrCast.int2ptr m2 addr`,
stores `.Ptr ⟨ptr, none⟩` into `retPlace`, and jumps to `nb`. -/
theorem evalTerminator_intrinsic_withExposed_ok {m m1 m2 m3 m4 : Mach}
    {argExpr : Gen.ValueExpr} {retExpr : Gen.PlaceExpr} {nb : Gen.BbName}
    {retPlace : Gen.Place BM} {retPtrTy : Gen.PtrType}
    {addr : Int} {argTy : Gen.Type} {ptr : Ptr}
    (hplace : evalPlace m retExpr = .ok ((retPlace, .Ptr retPtrTy), m1))
    (harg : evalValue m1 argExpr = .ok ((.Int addr, argTy), m2))
    (hmeta : PtrType.meta_kind retPtrTy = .None)
    (hint : IntPtrCast.int2ptr m2 addr = .ok ptr)
    (hstore : placeStore m2 retPlace (.Ptr ⟨ptr, none⟩) (.Ptr retPtrTy) = .ok m3)
    (hjump : jumpToBlock m3 nb = .ok m4) :
    Interp.evalTerminator m (.Intrinsic .PointerWithExposedProvenance [argExpr] retExpr (some nb)) =
      .ok m4 := by
  simp [Interp.evalTerminator, hplace, harg,
    evalIntrinsic_withExposed_ok hmeta hint, hstore, hjump, bind, Except.bind]

/-- Full `evalTerminator` error propagation for `Terminator::Intrinsic .PointerWithExposedProvenance`
when `IntPtrCast.int2ptr` stops with `.error err` (e.g., `Stop.unsupported`). -/
theorem evalTerminator_intrinsic_withExposed_err {m m1 m2 : Mach}
    {argExpr : Gen.ValueExpr} {retExpr : Gen.PlaceExpr} {nb : Option Gen.BbName}
    {retPlace : Gen.Place BM} {retPtrTy : Gen.PtrType}
    {addr : Int} {argTy : Gen.Type} {err : Stop}
    (hplace : evalPlace m retExpr = .ok ((retPlace, .Ptr retPtrTy), m1))
    (harg : evalValue m1 argExpr = .ok ((.Int addr, argTy), m2))
    (hmeta : PtrType.meta_kind retPtrTy = .None)
    (hint : IntPtrCast.int2ptr m2 addr = .error err) :
    Interp.evalTerminator m (.Intrinsic .PointerWithExposedProvenance [argExpr] retExpr nb) =
      .error err := by
  simp [Interp.evalTerminator, hplace, harg,
    evalIntrinsic_withExposed_err hmeta hint, bind, Except.bind]

/-- Polymorphic `evalTerminatorM` step for `Terminator::Intrinsic .PointerWithExposedProvenance`
when `IntPtrCast.int2ptrM` succeeds. -/
theorem evalTerminatorM_intrinsic_withExposed_ok {M : Type} [Gen.Memory M] [MemoryOps M]
    {m m1 m2 m3 m4 : Gen.Machine M}
    {argExpr : Gen.ValueExpr} {retExpr : Gen.PlaceExpr} {nb : Gen.BbName}
    {retPlace : Gen.Place M} {retPtrTy : Gen.PtrType}
    {addr : Int} {argTy : Gen.Type} {ptr : Gen.ThinPointer (Gen.Memory.Provenance M)}
    (hplace : evalPlaceM m retExpr = .ok ((retPlace, .Ptr retPtrTy), m1))
    (harg : evalValueM m1 argExpr = .ok ((.Int addr, argTy), m2))
    (hmeta : PtrType.meta_kind retPtrTy = .None)
    (hint : IntPtrCast.int2ptrM m2 addr = .ok ptr)
    (hstore : placeStoreM m2 retPlace (.Ptr ⟨ptr, none⟩) (.Ptr retPtrTy) = .ok m3)
    (hjump : jumpToBlockM m3 nb = .ok m4) :
    Interp.evalTerminatorM m (.Intrinsic .PointerWithExposedProvenance [argExpr] retExpr (some nb)) =
      .ok m4 := by
  simp [Interp.evalTerminatorM, hplace, harg,
    evalIntrinsicM_withExposed_ok hmeta hint, hstore, hjump, bind, Except.bind]

/-- Polymorphic `evalTerminatorM` error propagation for `Terminator::Intrinsic .PointerWithExposedProvenance`
when `IntPtrCast.int2ptrM` stops with `.error err`. -/
theorem evalTerminatorM_intrinsic_withExposed_err {M : Type} [Gen.Memory M] [MemoryOps M]
    {m m1 m2 : Gen.Machine M}
    {argExpr : Gen.ValueExpr} {retExpr : Gen.PlaceExpr} {nb : Option Gen.BbName}
    {retPlace : Gen.Place M} {retPtrTy : Gen.PtrType}
    {addr : Int} {argTy : Gen.Type} {err : Stop}
    (hplace : evalPlaceM m retExpr = .ok ((retPlace, .Ptr retPtrTy), m1))
    (harg : evalValueM m1 argExpr = .ok ((.Int addr, argTy), m2))
    (hmeta : PtrType.meta_kind retPtrTy = .None)
    (hint : IntPtrCast.int2ptrM m2 addr = .error err) :
    Interp.evalTerminatorM m (.Intrinsic .PointerWithExposedProvenance [argExpr] retExpr nb) =
      .error err := by
  simp [Interp.evalTerminatorM, hplace, harg,
    evalIntrinsicM_withExposed_err hmeta hint, bind, Except.bind]

end MiniRustSpec.Correspondence
