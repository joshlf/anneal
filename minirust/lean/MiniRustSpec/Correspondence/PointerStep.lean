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
# Raw pointer statements in both semantics (MR-3.1)

The statement-level facts on which `step_correspondence_N` rests for the raw
pointer statements that `inFragment` admits:

* `_i = &raw const q` / `_i = &raw mut q` (`evalStmt_assign_rawPtr`,
  `evalStatement_assign_rawPtr_mr`): Anneal pushes a fresh Tree Borrows entry
  for `q` and stores its tag; MiniRust stores the address of `q`'s bytes.
  `BorrowsOk.rawPtr` and `LocalsOk.rawPtr_extend` keep the borrow-table
  invariant and the pointer bytes of every other pointer local in sync.
* `_i = copy _p`, `_i = PtrToPtr(copy _p)`, and `_i = Offset(copy _p, 0)`
  (`evalRvalue_ptrRvalue`, `evalStatement_assign_ptrRvalue_mr`): both semantics
  copy the pointer (`BorrowsOk.advance_set_ptr`).
* `_i = copy (*_p)` (`evalRvalue_derefRead_eq`, `evalPlace_deref`): a read
  through `_p` is, in both semantics, a read of the place the pointer was taken
  of.
* `(*_p) = rv` (`evalStmt_assign_derefWrite`, `derefWrite_target`): a write
  through a `*mut` pointer is a write to that place; under `ptrAliasingOk` it
  never disables another borrow (`BorrowsOk.invalidateDeref_noop`).
* The inversions of the fragment checks on these statements
  (`statementOk_rawPtr_spec`, `statementOk_derefRead`, `ptrTargetSpec_cases`).
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
    ∃ mutbl, e.perm = rawPtrPerm mutbl ∧ e.rangeOffset = 0 ∧ e.rangeLen = 0 ∧
      (mutbl = .mut → e.targetLocal ∈ bodyMutAddrTakenLocals body) := by
  obtain ⟨mutbl, _, _, heq, _, hmut, _⟩ := hb.entries_ok e he
  exact ⟨mutbl, congrArg BorrowEntry.perm heq, congrArg BorrowEntry.rangeOffset heq,
    congrArg BorrowEntry.rangeLen heq, hmut⟩

theorem BorrowsOk.perm_ne_reserved {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    {e : BorrowEntry} (he : e ∈ s.memory.borrows) : e.perm ≠ .reserved := by
  obtain ⟨mutbl, hp, _⟩ := hb.perm_eq he
  rw [hp]; cases mutbl <;> simp [rawPtrPerm]

theorem BorrowsOk.perm_ne_disabled {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    {e : BorrowEntry} (he : e ∈ s.memory.borrows) : e.perm ≠ .disabled := by
  obtain ⟨mutbl, hp, _⟩ := hb.perm_eq he
  rw [hp]; cases mutbl <;> simp [rawPtrPerm]

theorem BorrowsOk.mut_of_active {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    {e : BorrowEntry} (he : e ∈ s.memory.borrows) (hact : e.perm = .active) :
    e.targetLocal ∈ bodyMutAddrTakenLocals body := by
  obtain ⟨mutbl, hp, _, _, hmut⟩ := hb.perm_eq he
  cases mutbl <;> first | exact hmut rfl | (rw [hp] at hact; simp [rawPtrPerm] at hact)

/-- A write through a pointer to a `&raw mut` borrow target never disables
another borrow: distinct borrows of a target with a mutable borrow are
disjoint (`BorrowsOk.mut_disjoint`). -/
theorem BorrowsOk.invalidateDeref_noop {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    (locals : List LocalSlot) (p : Nat) (ptrVal : ProvenancePtr) (entry : BorrowEntry)
    (hp : locals[p]? = some (.init (.ptr ptrVal 8)))
    (he : lookupBorrow s.memory.borrows ptrVal.tag = some entry)
    (hact : entry.perm = .active) :
    invalidateDerefWriteBorrows locals s.memory.borrows ⟨p, [.deref]⟩ [] = s.memory.borrows := by
  obtain ⟨hmem, htag⟩ := lookupBorrow_mem_and_tag he
  obtain ⟨_, _, hroff, hrlen, _⟩ := hb.perm_eq hmem
  have hmut := hb.mut_of_active hmem hact
  refine invalidateDerefWriteBorrows_noop locals s.memory.borrows p ptrVal entry hp he hrlen hroff ?_
  intro e he_mem hloc
  by_cases htg : e.tag = ptrVal.tag
  · exact .inl ⟨htg, hb.perm_ne_reserved he_mem⟩
  · refine .inr ⟨htg, ?_⟩
    exact hb.mut_disjoint e he_mem entry hmem (by rw [htag]; exact htg) hloc (hloc ▸ hmut)

/-- Storing a pointer into the pointer local `_i` (not a borrow target) whose
tag names a borrow of the declared pointee type keeps `BorrowsOk`. -/
theorem BorrowsOk.advance_set_ptr {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    {locals' : List LocalSlot} (i : Nat) (pv : ProvenancePtr)
    (hi_addr : i ∉ bodyAddrTakenLocals body)
    (hpv : ∀ (dp : LocalDecl) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType),
      body.localDecls[i]? = some dp → ptrPointeeOf dp.ty = some (mutbl, pointeeIt) →
      ∃ (entry : BorrowEntry) (relOff : Nat),
        pv.offsetBytes = 0 ∧
        lookupBorrow s.memory.borrows pv.tag = some entry ∧
        (mutbl = .mut → entry.perm = .active) ∧
        ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
          some (pointeeIt, relOff)) :
    BorrowsOk body ctx (view.set i (.init (.ptr pv 8))) (advanceStmt s locals' s.memory) lm := by
  have hb' := hb.advance_keep (locals' := locals')
  refine {
    tags_lt := hb'.tags_lt
    entries_ok := hb'.entries_ok
    target_ptrs := fun hfrag k hk => by
      obtain ⟨hnd, hlm, hd⟩ := hb'.target_ptrs hfrag k hk
      refine ⟨?_, hlm, hd⟩
      have hik : i ≠ k := fun h => hi_addr (h ▸ hk)
      rw [List.getElem?_set_ne hik]
      exact hnd
    mut_disjoint := hb'.mut_disjoint
    mut_pc_ok := hb'.mut_pc_ok
    ptr_slots := ?_ }
  intro p dp mutbl pointeeIt ptrVal hdp hpt hv
  by_cases hip : i = p
  · subst hip
    by_cases hlt : i < view.length
    · rw [List.getElem?_set_self hlt] at hv
      simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hv
      obtain ⟨rfl, -⟩ := hv
      exact hpv dp mutbl pointeeIt hdp hpt
    · rw [List.getElem?_eq_none (by simp; omega)] at hv
      cases hv
  · rw [List.getElem?_set_ne hip] at hv
    exact hb'.ptr_slots p dp mutbl pointeeIt ptrVal hdp hpt hv

/-- `BorrowsOk` after a statement that changes neither the borrow table nor
any pointer local nor any borrow target, under a locals map that agrees with
the old one on the borrow targets. -/
theorem BorrowsOk.advance_storage {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm lm' : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    {locals' : List LocalSlot} (i : Nat) (slot' : LocalSlot)
    (hi_addr : i ∉ bodyAddrTakenLocals body)
    (hnp : ∀ dp pv, body.localDecls[i]? = some dp → isPtrTy dp.ty = true →
      slot' ≠ .init (.ptr pv 8))
    (hlm : ∀ k ∈ bodyAddrTakenLocals body, mapGet lm' (localName k) = mapGet lm (localName k)) :
    BorrowsOk body ctx (view.set i slot') (advanceStmt s locals' s.memory) lm' :=
  (hb.with_lm hlm).advance_set_nonptr i slot' (fun hk => absurd hk hi_addr) hnp

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

/-- The pointer bytes of every initialized pointer local stay in sync after
`&raw` pushes an entry with a fresh tag. -/
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
  obtain ⟨entry, _, _, hlookup, _, _⟩ := hb.ptr_slots i d mutbl pointeeIt pv hd hpt hv
  obtain ⟨hmem, htag⟩ := lookupBorrow_mem_and_tag hlookup
  have hlt := hb.tags_lt entry hmem
  have hne : e.tag ≠ pv.allocId := by
    rw [he]
    have : entry.tag = pv.allocId := htag
    omega
  simp only [ctxWithBorrows] at h2 ⊢
  rw [borrowTargets_cons_ne body ctx e s.memory.borrows pv.allocId hne] at h2
  exact h2

/-- `BorrowsOk` after `_i = &raw mutbl q` pushed the entry
`rawPtrEntry nextTag mutbl q` and stored its tag in the pointer local `_i`. -/
theorem BorrowsOk.rawPtr {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    (hpa : ptrAliasingOk body = true)
    {bb : BasicBlockData} (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    {st : MirAst.Statement} (hst : bb.statements[s.frame.stmtIdx]? = some st)
    {i : Nat} {mutbl : MirAst.Mutability} {q : Place}
    (hkind : st.kind = .assign ⟨i, []⟩ (.rawPtr mutbl q))
    (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    (hdi : ∀ dp, body.localDecls[i]? = some dp → ptrPointeeOf dp.ty = some (mutbl, pointeeIt))
    (hi_addr : i ∉ bodyAddrTakenLocals body) (locals' : List LocalSlot) :
    BorrowsOk body ctx (view.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8)))
      (advanceStmt s locals' { s.memory with
        borrows := rawPtrEntry s.memory.nextTag mutbl q :: s.memory.borrows,
        nextTag := s.memory.nextTag + 1 }) lm := by
  have hbbmem : bb ∈ body.basicBlocks := List.mem_of_getElem? hbb
  have hstmem : st ∈ bb.statements := List.mem_of_getElem? hst
  have hq_addr : q.local_ ∈ bodyAddrTakenLocals body := mem_bodyAddrTakenLocals hbbmem hstmem hkind
  have hq_mut : mutbl = .mut → q.local_ ∈ bodyMutAddrTakenLocals body := fun hm => by
    subst hm; exact mem_bodyMutAddrTakenLocals hbbmem hstmem hkind
  obtain ⟨k, projs⟩ := q
  simp only at hq_addr hq_mut
  have hfresh : ∀ e' ∈ s.memory.borrows, e'.tag ≠ s.memory.nextTag :=
    fun e' he' h => by have := hb.tags_lt e' he'; omega
  -- A mutable-borrow target is only borrowed in `bb0`.
  have hmut_bb0 : k ∈ bodyMutAddrTakenLocals body →
      s.frame.blockIdx = 0 ∧ body.basicBlocks[0]? = some bb ∧
      rawPtrListDisjoint (bodyMutAddrTakenLocals body) bb.statements = true := by
    intro hkm
    obtain ⟨_, _, hmut⟩ := ptrAliasingOk_spec hpa
    rcases hmut with hemp | ⟨_, hbbs⟩
    · rw [List.isEmpty_iff] at hemp; rw [hemp] at hkm; simp at hkm
    · cases hbody : body.basicBlocks with
      | nil => rw [hbody] at hbb; simp at hbb
      | cons bb0 restBbs =>
        rw [hbody] at hbbs hbb
        obtain ⟨hdisj, hrest⟩ := hbbs
        cases hblk : s.frame.blockIdx with
        | zero =>
          rw [hblk] at hbb
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hbb
          subst hbb
          exact ⟨rfl, rfl, hdisj⟩
        | succ n =>
          rw [hblk] at hbb
          simp only [List.getElem?_cons_succ] at hbb
          have hno := hrest bb (List.mem_of_getElem? hbb)
          simp only [noMutAddrOfInStmts, List.all_eq_true] at hno
          have := hno st hstmem
          rw [hkind] at this
          simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem] at this
          exact absurd hkm this
  -- The new borrow and an older borrow of a mutable-borrow target are disjoint.
  have hnew_old : ∀ e2 ∈ s.memory.borrows, e2.targetLocal = k →
      k ∈ bodyMutAddrTakenLocals body →
      MirSemantics.projectionsOverlap projs e2.targetProjection = false ∧
      MirSemantics.projectionsOverlap e2.targetProjection projs = false := by
    intro e2 he2 hloc hkm
    obtain ⟨hb0, hbb0, hdisj⟩ := hmut_bb0 hkm
    rcases hb.mut_pc_ok k hkm with ⟨_, hpc⟩ | hne0
    · obtain ⟨idx, hidx, st', dst', mutbl', hst', hk'⟩ := hpc bb hbb0 e2 he2 hloc
      have hst'' : bb.statements[s.frame.stmtIdx]? = some st := hst
      have := rawPtrListDisjoint_lt hdisj hidx hst' hst'' hk' hkind hkm
      exact ⟨this.2, this.1⟩
    · exact absurd hb0 hne0
  refine {
    tags_lt := ?_
    entries_ok := ?_
    target_ptrs := ?_
    mut_disjoint := ?_
    mut_pc_ok := ?_
    ptr_slots := ?_ }
  · intro e' he'
    simp only [advanceStmt, List.mem_cons] at he' ⊢
    rcases he' with rfl | he'
    · simp [rawPtrEntry]
    · have := hb.tags_lt e' he'; omega
  · intro e' he'
    simp only [advanceStmt, List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact ⟨mutbl, pointeeIt, relOff, rfl, hq_addr, hq_mut, hspec⟩
    · exact hb.entries_ok e' he'
  · intro hfrag k' hk'
    obtain ⟨hnd, hlm, hd⟩ := hb.target_ptrs hfrag k' hk'
    refine ⟨?_, hlm, hd⟩
    have hik : i ≠ k' := fun h => hi_addr (h ▸ hk')
    rw [List.getElem?_set_ne hik]
    exact hnd
  · intro e1 he1 e2 he2 hne hloc hmut
    simp only [advanceStmt, List.mem_cons] at he1 he2
    rcases he1 with rfl | he1 <;> rcases he2 with rfl | he2
    · exact absurd rfl hne
    · exact (hnew_old e2 he2 hloc.symm hmut).1
    · have hloc' : e1.targetLocal = k := hloc
      exact (hnew_old e1 he1 hloc' (hloc' ▸ hmut)).2
    · exact hb.mut_disjoint e1 he1 e2 he2 hne hloc hmut
  · intro k' hk'
    rcases hb.mut_pc_ok k' hk' with ⟨hb0, hpc⟩ | hne0
    · refine .inl ⟨by simpa [advanceStmt] using hb0, fun bb0 hbb0 e' he' hke => ?_⟩
      simp only [advanceStmt, List.mem_cons] at he'
      rcases he' with rfl | he'
      · have hbb' : bb0 = bb := by
          rw [hb0] at hbb; rw [hbb] at hbb0; exact (Option.some.inj hbb0).symm
        subst hbb'
        refine ⟨s.frame.stmtIdx, by simp [advanceStmt], st, ⟨i, []⟩, mutbl, hst, ?_⟩
        simp only [rawPtrEntry] at hke ⊢
        rw [hkind, hke]
      · obtain ⟨idx, hidx, st', dst', mutbl', hst', hk'⟩ := hpc bb0 hbb0 e' he' hke
        exact ⟨idx, by simp [advanceStmt]; omega, st', dst', mutbl', hst', hk'⟩
    · exact .inr (by simpa [advanceStmt] using hne0)
  · intro p dp mutbl' pointeeIt' ptrVal hdp hpt hv
    by_cases hip : i = p
    · subst hip
      by_cases hlt : i < view.length
      · rw [List.getElem?_set_self hlt] at hv
        simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hv
        obtain ⟨rfl, -⟩ := hv
        rw [hdi dp hdp] at hpt
        simp only [Option.some.injEq, Prod.mk.injEq] at hpt
        obtain ⟨rfl, rfl⟩ := hpt
        refine ⟨rawPtrEntry s.memory.nextTag mutbl ⟨k, projs⟩, relOff, rfl, ?_,
          fun hm => by subst hm; rfl, hspec⟩
        simp only [advanceStmt]
        exact lookupBorrow_cons_self (rawPtrEntry s.memory.nextTag mutbl ⟨k, projs⟩) s.memory.borrows
      · rw [List.getElem?_eq_none (by simp; omega)] at hv
        cases hv
    · rw [List.getElem?_set_ne hip] at hv
      obtain ⟨entry, relOff', hoff, hlookup, hact, htspec⟩ :=
        hb.ptr_slots p dp mutbl' pointeeIt' ptrVal hdp hpt hv
      obtain ⟨hmem, htag⟩ := lookupBorrow_mem_and_tag hlookup
      refine ⟨entry, relOff', hoff, ?_, hact, htspec⟩
      simp only [advanceStmt]
      rw [lookupBorrow_cons_ne _ s.memory.borrows ptrVal.tag (by
        show s.memory.nextTag ≠ ptrVal.tag
        rw [← htag]; exact (hfresh entry hmem).symm)]
      exact hlookup

/-! ## Anneal -/

/-- Anneal's `_i = &raw mutbl q` on a live borrow target `q` (neither a
dereference nor indexed): a fresh entry is pushed and its tag stored in `_i`
(UB when `_i` is dead). -/
theorem evalStmt_assign_rawPtr (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i : Nat) (mutbl : MirAst.Mutability) (q : Place)
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
      evalStmt s ⟨.assign ⟨i, []⟩ (.rawPtr mutbl q), span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hrv := evalRvalue_rawPtr_local s.frame.locals mutbl q s.memory decls layouts hnd hni slotq
    hsq hliveq
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hi]
  have hinv : invalidateConflictingBorrows (rawPtrEntry s.memory.nextTag mutbl q :: s.memory.borrows)
      i .none = rawPtrEntry s.memory.nextTag mutbl q :: s.memory.borrows := by
    apply invalidateConflictingBorrows_of_ne
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · simpa [rawPtrEntry] using hqi
    · exact hbor e he'
  refine ⟨fun hlive => ?_, fun hdead => ?_⟩
  · have hlive' : s.frame.locals[i] ≠ .dead := fun h => hlive (by rw [hs, h])
    simp only [evalStmt, hrv, get?, hs, set?, hi, ↓reduceIte, hprot, hinv]
    cases hsl : s.frame.locals[i] with
    | dead => exact absurd hsl hlive'
    | uninit => rfl
    | init v => rfl
  · simp [evalStmt, hrv, get?, hdead]

/-- Anneal's read through a pointer to a live borrow target is a read of the
borrowed place. -/
theorem evalOperand_deref_eq_target (locals : List LocalSlot) (p : Nat)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation)
    (layouts : Layout.LayoutTable) (callerLocals : List LocalSlot)
    (ptrVal : ProvenancePtr) (sz : Nat) (hp : locals[p]? = some (.init (.ptr ptrVal sz)))
    (entry : BorrowEntry) (he : lookupBorrow borrows ptrVal.tag = some entry)
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
      cases ph with
      | deref => exact absurd rfl hph
      | _ => cases slot <;> simp [evalOperand, get?, hp, he, hpe, ht, htp, hpt]

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

/-- Anneal's evaluation of a pointer-copying fragment rvalue (`copy _p`,
`PtrToPtr(copy _p)`, or `Offset(copy _p, 0)`): the pointer held by `_p`. -/
theorem evalRvalue_ptrRvalue {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType} {rv : Rvalue}
    (hok : ptrRvalueOk layouts decls mutbl pointeeIt rv = true)
    (hnraw : ∀ m q, rv ≠ .rawPtr m q) :
    ∃ p, p < decls.length ∧ .copy ⟨p, []⟩ ∈ rvOperands rv ∧
      (∃ srcMutbl, (decls[p]? >>= (ptrPointeeOf ·.ty)) = some (srcMutbl, pointeeIt) ∧
        (mutbl = .mut → srcMutbl = .mut)) ∧
      ∀ (locals : List LocalSlot) (mem : MirSemantics.Memory),
        (∀ pv sz, locals[p]? = some (.init (.ptr pv sz)) →
          evalRvalue locals rv mem decls layouts = .ok (.ptr pv sz) locals mem) ∧
        ((locals[p]? = some .uninit ∨ locals[p]? = some .dead) →
          evalRvalue locals rv mem decls layouts = .ub) := by
  match rv, hok with
  | .use (.copy ⟨p, []⟩), hok =>
    simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    refine ⟨p, hok.1, by simp [rvOperands], ⟨mutbl, hok.2, fun h => h⟩,
      fun locals mem => ⟨fun pv sz hp => ?_, fun hu => ?_⟩⟩
    · simp [evalRvalue, evalOperand, get?, hp, readProjectedValue]
    · rcases hu with hu | hu <;> simp [evalRvalue, evalOperand, get?, hu]
  | .rawPtr m q, _ => exact absurd rfl (hnraw m q)
  | .cast .ptrToPtr (.copy ⟨p, []⟩) castTy, hok =>
    simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hp, _⟩, hsrc⟩ := hok
    cases hsp : (decls[p]? >>= (ptrPointeeOf ·.ty)) with
    | none => simp [hsp] at hsrc
    | some pr =>
      obtain ⟨srcMutbl, srcIt⟩ := pr
      simp only [hsp, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hsrc
      obtain ⟨hit, hm⟩ := hsrc
      subst hit
      refine ⟨p, hp, by simp [rvOperands], ⟨srcMutbl, hsp, fun h => ?_⟩,
        fun locals mem => ⟨fun pv sz hpv => ?_, fun hu => ?_⟩⟩
      · rcases hm with hm | hm
        · exact hm
        · subst h; cases hm
      · simp [evalRvalue, evalOperand, get?, hpv, readProjectedValue]
      · rcases hu with hu | hu <;> simp [evalRvalue, evalOperand, get?, hu]
  | .binaryOp .offset (.copy ⟨p, []⟩) (.constant c), hok =>
    simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hp, hpt⟩, hz⟩ := hok
    have hc : ∃ sz, c.val = .scalar (.int ⟨0, sz⟩) := by
      unfold zeroOffsetConstOk at hz
      split at hz
      · next sz _ hval _ => exact ⟨sz, hval⟩
      · simp at hz
    obtain ⟨sz, hval⟩ := hc
    refine ⟨p, hp, by simp [rvOperands], ⟨mutbl, hpt, fun h => h⟩,
      fun locals mem => ⟨fun pv psz hpv => ?_, fun hu => ?_⟩⟩
    · simp [evalRvalue, evalOperand, get?, hpv, readProjectedValue, hval, evalConstValue]
    · rcases hu with hu | hu <;> simp [evalRvalue, evalOperand, get?, hu]

/-- Anneal's write `(*_p) = rv` through a pointer whose write does not disable
any borrow. -/
theorem evalStmt_assign_derefWrite (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (p : Nat) (rv : Rvalue) (span : String)
    (hprot : s.memory.activeProtectors = []) (hcl : s.memory.callerLocals = []) :
    (∀ v locals', evalRvalue s.frame.locals rv s.memory decls layouts = .ok v s.frame.locals s.memory →
      writePlaceValue s.frame.locals s.memory.borrows ⟨p, [.deref]⟩ v = .ok locals' →
      invalidateDerefWriteBorrows s.frame.locals s.memory.borrows ⟨p, [.deref]⟩ [] =
        s.memory.borrows →
      evalStmt s ⟨.assign ⟨p, [.deref]⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s locals' s.memory))) ∧
    (∀ v, evalRvalue s.frame.locals rv s.memory decls layouts = .ok v s.frame.locals s.memory →
      writePlaceValue s.frame.locals s.memory.borrows ⟨p, [.deref]⟩ v = .ub →
      evalStmt s ⟨.assign ⟨p, [.deref]⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) ∧
    (evalRvalue s.frame.locals rv s.memory decls layouts = .ub →
      evalStmt s ⟨.assign ⟨p, [.deref]⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  refine ⟨fun v locals' hv hw hinv => ?_, fun v hv hw => ?_, fun hu => ?_⟩
  · simp only [evalStmt, hv, evalPlaceWrite, hprot, hw, hinv]
    simp [MirStepNode.step, memory_mk_nil_prot s.memory hprot]
  · simp only [evalStmt, hv, evalPlaceWrite, hprot, hw, hcl]
  · simp [evalStmt, hu]

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

/-- `ValueExpr::AddrOf` of a place expression that evaluates to a valid thin
raw pointer without changing the machine. -/
theorem evalValue_addrOf_of {m : Mach} {ctx : Ctx} {A : List Gen.Allocation}
    {f1 f2 : Frame} {rest : List Frame} (hsh : Shape m ctx (f1 :: f2 :: rest) A)
    {targetPe : Gen.PlaceExpr} {T : Gen.Type} (a : Int) (pr : Option Prov)
    (hev : evalPlace m targetPe =
      .ok (({ ptr := { thin_pointer := { addr := a, provenance := pr }, metadata := none },
               aligned := true }, T), m))
    (hck : checkValue (.Ptr { thin_pointer := { addr := a, provenance := pr }, metadata := none })
      (.Ptr (.Raw .None)) = .ok ()) :
    evalValue m (.AddrOf targetPe (.Raw .None)) =
      .ok ((.Ptr { thin_pointer := { addr := a, provenance := pr }, metadata := none },
            .Ptr (.Raw .None)), m) := by
  have hrt := retagPtrBM_shape hsh
    { thin_pointer := { addr := a, provenance := pr }, metadata := none }
  rw [evalValue, hev]
  simp only [ok_bind, hck, hrt]
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
thin raw pointer local `_p`: it loads `_p`, whose bytes encode the address of
`_p`'s borrow target (`evalPtrLoad`), and yields the target's place, aligned
for the pointee type; evaluating the target's own place expression on the
machine after the load yields the same place. -/
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
      lookupBorrow s.memory.borrows ptrVal.tag = some entry ∧
      (srcMutbl = .mut → entry.perm = .active) ∧
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
    ⟨ptrVal, entry, relOff, m1, hv, _, hlookup, hact, hk_addr, htspec, hload, h1⟩ |
      ⟨hnot, msg, hmsg⟩
  · left
    obtain ⟨_, _, hgood, _, _, hal, htgt⟩ :=
      evalTargetPlace h1 hb hns hfrag ⟨entry.targetLocal, entry.targetProjection⟩ it relOff htspec
        hk_addr
    refine ⟨ptrVal, entry, relOff, m1, hv, hlookup, hact, hk_addr, htspec, ?_, h1, htgt⟩
    rw [evalPlace]
    simp [hload, thinRawPtrTy, PtrType.safe_pointee, computeAlign, layout_eq _ hgood,
      LayoutStrategy.compute_size_and_align, hal]
  · right
    refine ⟨hnot, msg, ?_⟩
    rw [evalPlace]
    simp [hmsg]

/-- `ValueExpr::AddrOf` of the place of a borrow target: the pointer to the
target's bytes, which is a valid thin raw pointer. -/
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
    (ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat < 2 ^ 64 ∧
    evalValue m (.AddrOf targetPe (.Raw .None)) =
      .ok ((.Ptr { thin_pointer := { addr := ((ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat : Int),
                                     provenance := some (⟨((ctx.base.length + q.local_ : Nat) : Int)⟩, ()) },
                   metadata := none }, .Ptr (.Raw .None)), m) := by
  obtain ⟨_, _, _, htlt, hptrEq, _, hev⟩ :=
    evalTargetPlace h hb hns hfrag q pointeeIt relOff hspec hk_addr
  refine ⟨htlt, ?_⟩
  have hev' := hev targetPe hpe
  rw [← hptrEq] at hev'
  have hck := checkValue_thinRawPtr _ htlt (some (⟨((ctx.base.length + q.local_ : Nat) : Int)⟩, ()))
  exact evalValue_addrOf_of h.shape _ _ hev' hck

/-- `Machine::eval_statement` on an assignment to the live thin raw pointer
local `_i` whose source evaluates to a valid thin pointer: the pointer's bytes
are stored in `_i`'s allocation. -/
theorem evalStatement_assign_ptr_of {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (hp_ty : isPtrTy d.ty = true)
    (hlive : locals[i]? ≠ some .dead) (e : Gen.ValueExpr)
    (tAddr : Nat) (htlt : tAddr < 2 ^ 64) (tProv : Option Prov) (T' : Gen.Type) (m1 : Mach)
    (hm1 : evalValue m e =
      .ok ((.Ptr { thin_pointer := { addr := (tAddr : Int), provenance := tProv }, metadata := none },
            T'), m1))
    (h1 : FrameOk body f ctx locals lm m1 blk stmt)
    (pv : ProvenancePtr)
    (htgt : ∀ a pr, ctx.ptrTargets pv.allocId = some (a, pr) → tAddr = a ∧ tProv = pr) :
    ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
      FrameOk body f ctx (locals.set i (.init (.ptr pv 8))) lm m' blk stmt := by
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨hTd, hitd⟩ := tyOf_isPtrTy (layouts := body.layouts) hp_ty
  have hspec := (translateFn_spec body f h.hf).2.1 i d hd
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  have hslive : slot ≠ .dead := fun hc => hlive (hc ▸ hs)
  obtain ⟨p, hp⟩ := h.locs.some_of_live hs hslive
  obtain ⟨k, data, hpk, _, _, _, _, hlen, hA⟩ :=
    h1.locs.storage_any hd hs hp (h.declsOk d (List.mem_of_getElem? hd))
  rw [hTd] at hlen
  rw [hitd] at hA
  have hplace := evalPlace_local_some h.shape i _ hspec.2 p hp
  rw [hTd] at hplace
  have hst := typedStore_ptr_thinRawPtr h1.shape p k hpk data tAddr htlt tProv hA hlen
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

/-- MiniRust's `_i = &raw mutbl q` (`AddrOf`) into a live raw pointer local:
`_i` holds the address of `q`, which is the target of the fresh borrow that
Anneal pushes. -/
theorem evalStatement_assign_rawPtr_mr {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm) (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) (hp_ty : isPtrTy d.ty = true)
    (hlive : view[i]? ≠ some .dead)
    (mutbl : MirAst.Mutability) (q : Place) (pointeeIt : Gen.IntType) (relOff : Nat)
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
    obtain ⟨htlt, hev⟩ :=
      evalValue_addrOf h hb hns hfrag q pointeeIt relOff hspec hq_addr targetPe hpe
    have hlo' := LocalsOk.rawPtr_extend h.locs hb (rawPtrEntry s.memory.nextTag mutbl q) rfl
    have h' := h.ctxWithBorrows_change hlo'
    refine evalStatement_assign_ptr_of h' i d hd hp_ty hlive _ _ htlt _ _ m hev h'
      ⟨s.memory.nextTag, 0⟩ (fun a pr h2 => ?_)
    simp only [ctxWithBorrows] at h2
    rw [borrowTargets_rawPtr_self body ctx s.memory.nextTag mutbl q s.memory.borrows pointeeIt relOff
      hspec] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact ⟨h2.1, h2.2⟩

/-! ## Pointer-copying rvalues -/

theorem rawPtrMetaOf_of_ptrPointeeOf {t : MirAst.Ty} {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (h : ptrPointeeOf t = some (mutbl, it)) : rawPtrMetaOf t = some .None := by
  unfold ptrPointeeOf at h
  unfold rawPtrMetaOf
  cases hk : t.kind with
  | rawPtr m pointee =>
    rw [hk] at h
    obtain ⟨⟨sg, n⟩, hb, _⟩ := Option.map_eq_some_iff.mp h
    cases pointee <;> simp_all [intTyBytes, rawPtrMetaKind]
  | _ => rw [hk] at h; simp at h

/-- `minimize`'s translation of a pointer-copying fragment rvalue: a load of
the pointer local, or for `Offset(_p, 0)` its in-bounds offset by
`0 * size_of::<T>()` bytes. -/
theorem translateRvalue_ptrRvalue {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType} {rv : Rvalue}
    {targetTy : Option MirAst.Ty} {e : Gen.ValueExpr}
    (hok : ptrRvalueOk layouts decls mutbl pointeeIt rv = true) (hnraw : ∀ m q, rv ≠ .rawPtr m q)
    (he : translateRvalue layouts decls targetTy rv = some e)
    (p : Nat) (hp : .copy ⟨p, []⟩ ∈ rvOperands rv) :
    e = .Load (.Local (localName p)) ∨
      ∃ (rIt : Gen.IntType) (z sz : Int), z = 0 ∧
        e = .BinOp (.PtrOffset true) (.Load (.Local (localName p)))
          (.BinOp (.Int .MulUnchecked) (.Constant (.Int z) (.Int rIt)) (.Constant (.Int sz) (.Int rIt))) := by
  match rv, hok with
  | .use (.copy ⟨p', []⟩), _ =>
    simp only [rvOperands, List.mem_singleton, Operand.copy.injEq, Place.mk.injEq, and_true] at hp
    subst hp
    left
    simpa [translateRvalue, translateOperand, translatePlace] using he.symm
  | .rawPtr m q, _ => exact absurd rfl (hnraw m q)
  | .cast .ptrToPtr (.copy ⟨p', []⟩) castTy, hok =>
    simp only [rvOperands, List.mem_singleton, Operand.copy.injEq, Place.mk.injEq, and_true] at hp
    subst hp
    left
    simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨_, hcast⟩, hsrc⟩ := hok
    cases hsp : (decls[p]? >>= (ptrPointeeOf ·.ty)) with
    | none => simp [hsp] at hsrc
    | some pr =>
      obtain ⟨srcMutbl, srcIt⟩ := pr
      cases hdp : decls[p]? with
      | none => simp [hdp] at hsp
      | some dp =>
        have hpt : ptrPointeeOf dp.ty = some (srcMutbl, srcIt) := by simpa [hdp] using hsp
        have h1 := rawPtrMetaOf_of_ptrPointeeOf hpt
        have h2 := rawPtrMetaOf_of_ptrPointeeOf hcast
        simp [translateRvalue, translateOperand, translatePlace, operandRawPtrMeta, hdp, h1, h2] at he
        exact he.symm
  | .binaryOp .offset (.copy ⟨p', []⟩) (.constant c), hok =>
    simp only [rvOperands, List.mem_cons, List.not_mem_nil, or_false, Operand.copy.injEq,
      Place.mk.injEq, and_true, reduceCtorEq] at hp
    subst hp
    right
    simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨_, hpt⟩, hz⟩ := hok
    unfold zeroOffsetConstOk at hz
    split at hz
    · next sz' rIt hval hit =>
      have hsz : sz' = rIt.size.bytes := by simpa using hz
      have hnb : isBoolTy c.ty = false := intTypeOf_isBoolTy hit
      have hgood := intTypeOf_good hit
      have hpos : 0 < 2 ^ (8 * rIt.size.bytes) := Nat.two_pow_pos _
      refine ⟨rIt, intFromBits 0 rIt, pointeeIt.size.bytes, ?_, ?_⟩
      · cases hs : rIt.signed <;> simp [intFromBits, hs, Nat.two_pow_pos]
      · simp [translateRvalue, translateOperand, translatePlace, translateRelOp, translateBinOp,
          translateCheckedBinOp, operandPtrPointee, operandIntType, hpt, hval, hit, hnb, hsz, hpos,
          ptrOffsetExpr] at he
        exact he.symm
    · simp at hz

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

/-- An assignment to a local whose source raises UB raises that UB. -/
theorem evalStatement_assign_ub_of {m : Mach} {i : Nat} {e : Gen.ValueExpr} {pl : Gen.Place BM}
    {T : Gen.Type} {msg : String}
    (hpl : evalPlace m (.Local (localName i)) = .ok ((pl, T), m))
    (he : evalValue m e = .error (.ub msg)) :
    evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg) := by
  simp [evalStatement, hpl, he]

/-- MiniRust's pointer-copying assignment (`_i = copy _p`, `PtrToPtr`, or
`Offset(_p, 0)`) into the live raw pointer local `_i`: `_i` holds `_p`'s
pointer; UB when `_p` holds none. -/
theorem evalStatement_assign_ptrRvalue_mr {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm) (hns : NonScalarLive body view lm)
    (hfrag : inFragment body = true)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d)
    {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    (hpt : ptrPointeeOf d.ty = some (mutbl, pointeeIt))
    {rv : Rvalue} (hok : ptrRvalueOk body.layouts body.localDecls mutbl pointeeIt rv = true)
    (hnraw : ∀ m q, rv ≠ .rawPtr m q) {targetTy : Option MirAst.Ty} (e : Gen.ValueExpr)
    (he : translateRvalue body.layouts body.localDecls targetTy rv = some e) :
    ∃ p, .copy ⟨p, []⟩ ∈ rvOperands rv ∧
      (∀ pv, view[p]? = some (.init (.ptr pv 8)) →
        (view[i]? ≠ some .dead →
          ∃ m', evalStatement m (.Assign (.Local (localName i)) e) = .ok m' ∧
          FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) (view.set i (.init (.ptr pv 8)))
            lm m' blk stmt) ∧
        ∃ (entry : BorrowEntry) (relOff : Nat), pv.offsetBytes = 0 ∧
          lookupBorrow s.memory.borrows pv.tag = some entry ∧
          (mutbl = .mut → entry.perm = .active) ∧
          ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
            some (pointeeIt, relOff)) ∧
      ((view[p]? = some .uninit ∨ view[p]? = some .dead) → view[i]? ≠ some .dead →
        ∃ msg, evalStatement m (.Assign (.Local (localName i)) e) = .error (.ub msg)) := by
  have hp_ty : isPtrTy d.ty = true := by simp [isPtrTy, hpt]
  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hspecF := (translateFn_spec body f h.hf).2.1 i d hd
  obtain ⟨_, slot, _, hs⟩ := h.slot_exists i hi
  obtain ⟨p, _, hpmem, ⟨srcMutbl, hsrc, hmut⟩, _⟩ := evalRvalue_ptrRvalue hok hnraw
  obtain ⟨dp, hdp, hp_pt⟩ : ∃ dp, body.localDecls[p]? = some dp ∧
      ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt) := by
    cases hdp : body.localDecls[p]? with
    | none => simp [hdp] at hsrc
    | some dp => exact ⟨dp, rfl, by simpa [hdp] using hsrc⟩
  have he_form := translateRvalue_ptrRvalue hok hnraw he p hpmem
  refine ⟨p, hpmem, fun pv hpv => ?_, fun hu hlive => ?_⟩
  · rcases evalPtrLoad h hb hns hfrag p dp srcMutbl pointeeIt hdp hp_pt with
      ⟨ptrVal, entry, relOff, m1, hv, hoff0, hlookup, hact, hk_addr, htspec, hload, h1⟩ |
        ⟨hnot, _⟩
    · rw [hv] at hpv
      simp only [Option.some.injEq, LocalSlot.init.injEq, Value.ptr.injEq] at hpv
      obtain ⟨rfl, -⟩ := hpv
      obtain ⟨_, _, _, htlt, hptrEq, _, _⟩ :=
        evalTargetPlace h1 hb hns hfrag ⟨entry.targetLocal, entry.targetProjection⟩ pointeeIt relOff
          htspec hk_addr
      rw [← hptrEq] at hload
      have hm1 : evalValue m e =
          .ok ((.Ptr { thin_pointer := { addr := ((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat : Int),
                                         provenance := some (⟨((ctx.base.length + entry.targetLocal : Nat) : Int)⟩, ()) },
                       metadata := none }, thinRawPtrTy), m1) := by
        rcases he_form with rfl | ⟨rIt, z, sz, hz, rfl⟩
        · exact hload
        · refine evalValue_ptrOffset_zero rIt z sz hz hload (Int.natCast_nonneg _) ?_
          have h64 : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := by decide
          have hlt := Int.ofNat_lt.mpr htlt
          rw [h64] at hlt
          exact hlt
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
      exact ⟨fun hlive => evalStatement_assign_ptr_of h i d hd hp_ty hlive e _ htlt _ _ m1 hm1 h1
        ptrVal htgt, entry, relOff, hoff0, hlookup, fun hm => hact (hmut hm), htspec⟩
    · rcases hnot with h' | h' <;> rw [h'] at hpv <;> cases hpv
  · obtain ⟨pi, hpi⟩ := h.locs.some_of_live hs (fun hc => hlive (hc ▸ hs))
    have hplace := evalPlace_local_some h.shape i _ hspecF.2 pi hpi
    rcases evalPtrLoad h hb hns hfrag p dp srcMutbl pointeeIt hdp hp_pt with
      ⟨ptrVal, _, _, _, hv, _⟩ | ⟨_, msg, hmsg⟩
    · rcases hu with hu | hu <;> rw [hu] at hv <;> cases hv
    · refine ⟨msg, evalStatement_assign_ub_of hplace ?_⟩
      rcases he_form with rfl | ⟨rIt, z, sz, hz, rfl⟩
      · exact hmsg
      · rw [evalValue, hmsg]
        rfl

/-! ## Fragment checks on raw pointer statements -/

theorem local_mem_stmtLocals_assign (dst : Place) (rv : Rvalue) (span : String) :
    dst.local_ ∈ stmtLocals ⟨.assign dst rv, span⟩ := by
  cases rv <;> simp [stmtLocals, local_mem_placeLocals]

/-- `statementOk` on `_i = &raw mutbl q`: `_i` is a thin raw pointer of
mutability `mutbl` to an integer type, and `q` is an admissible borrow target
of that type. -/
theorem statementOk_rawPtr_spec {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {i : Nat} {mutbl : MirAst.Mutability} {q : Place} {span : String} {d : LocalDecl}
    (hd : decls[i]? = some d)
    (h : statementOk decls ⟨.assign ⟨i, []⟩ (.rawPtr mutbl q), span⟩ layouts = true) :
    ∃ pointeeIt relOff, ptrPointeeOf d.ty = some (mutbl, pointeeIt) ∧
      ptrTargetSpec layouts decls q = some (pointeeIt, relOff) := by
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
              · rename_i mutbl' pointeeIt hpt
                simp only [ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at h
                obtain ⟨rfl, htok⟩ := h
                unfold ptrTargetOk at htok
                split at htok
                · rename_i it' relOff hsp
                  simp only [decide_eq_true_eq] at htok
                  subst htok
                  exact ⟨it', relOff, hpt, hsp⟩
                · simp at htok
              · simp at h

theorem copyRv_derefRead {rv : Rvalue} {p : Nat} {rest : List ProjectionElem}
    (hcrv : copyRv rv = .use (.copy ⟨p, .deref :: rest⟩)) :
    rv = .use (.copy ⟨p, .deref :: rest⟩) ∨ rv = .use (.move ⟨p, .deref :: rest⟩) := by
  cases rv <;> simp [copyRv] at hcrv
  rename_i op
  cases op <;> simp [copyOp] at hcrv <;> simp [hcrv]

/-- `statementOk` on a root assignment whose rvalue reads through a pointer
(`copy (*_p...)` or `move (*_p...)`): an unprojected dereference `*_p` of a
thin raw pointer local into an integer local of the pointee type. -/
theorem statementOk_derefRead {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {i : Nat} {rv : Rvalue} {span : String} {d : LocalDecl} (hd : decls[i]? = some d)
    {p : Nat} {rest : List ProjectionElem}
    (hcrv : copyRv rv = .use (.copy ⟨p, .deref :: rest⟩))
    (h : statementOk decls ⟨.assign ⟨i, []⟩ rv, span⟩ layouts = true) :
    rest = [] ∧ ∃ it dp srcMutbl, intTypeOf d.ty = some it ∧ decls[p]? = some dp ∧
      ptrPointeeOf dp.ty = some (srcMutbl, it) := by
  have key : ∀ rv' : Rvalue, copyRv rv' = .use (.copy ⟨p, .deref :: rest⟩) →
      statementOk decls ⟨.assign ⟨i, []⟩ rv', span⟩ layouts = true →
      (rv' = .use (.copy ⟨p, .deref :: rest⟩) ∨ rv' = .use (.move ⟨p, .deref :: rest⟩)) →
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
            · rcases hrv' with rfl | rfl <;> simp [arrayRvalueOk] at h'
            · split at h'
              · rcases hrv' with rfl | rfl <;> simp [tupleRvalueOk, tuplePlaceSpec] at h'
              · split at h'
                · simp [ptrRvalueOk] at h'
                · simp at h'
  exact key rv hcrv h (copyRv_derefRead hcrv)

theorem stmtReadsOk_derefRead {mo : List Nat} {i : Nat} {rv : Rvalue} {span : String}
    {p : Nat} {rest : List ProjectionElem} (hcrv : copyRv rv = .use (.copy ⟨p, .deref :: rest⟩)) :
    stmtReadsOk mo ⟨.assign ⟨i, []⟩ rv, span⟩ = !mo.contains p := by
  rcases copyRv_derefRead hcrv with rfl | rfl <;> rfl

theorem stmtReadsOk_root_of_not_deref {mo : List Nat} {i : Nat} {rv : Rvalue} {span : String}
    (hnd : ∀ p rest, copyRv rv ≠ .use (.copy ⟨p, .deref :: rest⟩)) :
    stmtReadsOk mo ⟨.assign ⟨i, []⟩ rv, span⟩ = readsOk mo (rvOperands rv) := by
  cases rv with
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
  rcases copyRv_derefRead hcrv with rfl | rfl <;>
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
    {mutbl : MirAst.Mutability} {it : Gen.IntType} {rv : Rvalue}
    (h : ptrRvalueOk layouts decls mutbl it (copyRv rv) = true) (hnraw : ∀ m q, rv ≠ .rawPtr m q) :
    moveKind rv = true := by
  cases rv with
  | rawPtr m q => exact absurd rfl (hnraw m q)
  | cast k op ty => cases k <;> first | rfl | simp_all [copyRv, ptrRvalueOk]
  | unaryOp uop op => cases uop <;> simp_all [copyRv, ptrRvalueOk]
  | aggregate k ops => cases k <;> simp_all [copyRv, ptrRvalueOk]
  | _ => simp_all [copyRv, ptrRvalueOk, moveKind]

theorem ptrRvalueOk_copy_unique {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {mutbl : MirAst.Mutability} {it : Gen.IntType} {rv : Rvalue}
    (h : ptrRvalueOk layouts decls mutbl it rv = true) {p p' : Nat}
    (hp : Operand.copy ⟨p, []⟩ ∈ rvOperands rv) (hp' : Operand.copy ⟨p', []⟩ ∈ rvOperands rv) :
    p = p' := by
  match rv, h with
  | .use (.copy ⟨q, []⟩), _ =>
    simp only [rvOperands, List.mem_singleton] at hp hp'
    cases hp; cases hp'; rfl
  | .rawPtr _ _, _ => simp [rvOperands] at hp
  | .cast .ptrToPtr (.copy ⟨q, []⟩) _, _ =>
    simp only [rvOperands, List.mem_singleton] at hp hp'
    cases hp; cases hp'; rfl
  | .binaryOp .offset (.copy ⟨q, []⟩) (.constant c), _ =>
    simp only [rvOperands, List.mem_cons, reduceCtorEq, or_false, List.not_mem_nil] at hp hp'
    cases hp; cases hp'; rfl

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
    (ptrVal : ProvenancePtr) (sz : Nat) (hp : locals[p]? = some (.init (.ptr ptrVal sz)))
    (entry : BorrowEntry) (he : lookupBorrow mem.borrows ptrVal.tag = some entry)
    (hperm : entry.perm ≠ .disabled) (hnd : ∀ rest, entry.targetProjection ≠ .deref :: rest)
    (slot : LocalSlot) (ht : locals[entry.targetLocal]? = some slot) :
    evalRvalue locals rv mem decls layouts =
      evalRvalue locals (.use (.copy ⟨entry.targetLocal, entry.targetProjection⟩)) mem decls
        layouts := by
  have hop := evalOperand_deref_eq_target locals p mem.borrows mem.globals layouts mem.callerLocals
    ptrVal sz hp entry he hperm hnd slot ht
  rcases copyRv_derefRead hcrv with rfl | rfl
  · simp only [evalRvalue, hop]
  · simp only [evalRvalue, evalOperand_move_deref_eq, hop]

theorem evalRvalue_derefRead_ub (locals : List LocalSlot) {rv : Rvalue} {p : Nat}
    (hcrv : copyRv rv = .use (.copy ⟨p, [.deref]⟩)) (mem : MirSemantics.Memory)
    (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (h : locals[p]? = some .uninit ∨ locals[p]? = some .dead) :
    evalRvalue locals rv mem decls layouts = .ub := by
  have hops := evalOperand_deref_ub_of_not_init locals p mem.borrows mem.globals layouts
    mem.callerLocals h
  rcases copyRv_derefRead hcrv with rfl | rfl
  · simp [evalRvalue, hops.1]
  · simp [evalRvalue, hops.2]

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

theorem projIdx_constantIndex (locals : List LocalSlot) {count offset minLen : Nat}
    {fromEnd : Bool} (hmin : minLen ≤ count)
    (hb : if fromEnd then 1 ≤ offset ∧ offset ≤ count else offset < count) :
    projIdx locals count (.constantIndex offset minLen fromEnd) =
      some (if fromEnd then count - offset else offset) := by
  have hnot : ¬ count < minLen := by omega
  cases fromEnd <;> simp only [Bool.false_eq_true, ↓reduceIte] at hb <;>
    simp only [projIdx, hnot, Bool.false_eq_true, ↓reduceIte] <;> split <;> first | rfl | omega

theorem ptrPointeeOf_good {t : MirAst.Ty} {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (h : ptrPointeeOf t = some (mutbl, it)) : GoodSize it.size.bytes := by
  unfold ptrPointeeOf at h
  split at h
  · obtain ⟨⟨sg, n⟩, hb, heq⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, rfl⟩ := heq
    exact intTyBytes_good hb
  · simp at h

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
              writeProjectedValue s.frame.locals rootVal (ph :: pt) v = .ok w)) ∧
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
      have hidxA := projIdx_constantIndex s.frame.locals hmin hbound
      refine ⟨(rvBits body.localDecls view pointeeIt body.layouts rv).map
        (fun r => .aggregate 0 (elems.set (if fromEnd then count - offset else offset)
          (.scalar ⟨r, pointeeIt.size.bytes⟩))), fun w hw => ?_, fun hw => ?_⟩
      · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hw
        refine ⟨hM1 _ r hidx hr, _, hA1 r (hfr.trans hr),
          .inr ⟨_, [], _, rfl, hskA, ?_⟩⟩
        exact (writeProjectedValue_proj body.localDecls s.frame.locals count elems hlenE _ hpok
          _).1 _ hidxA
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
          .inr ⟨_, _, rootVal, rfl, hskA, hwsem s.frame.locals⟩⟩
    · cases hr : rvBits body.localDecls view pointeeIt body.layouts rv with
      | none => exact ⟨hM2 hr, hA2 (hfr.trans hr)⟩
      | some r =>
        obtain ⟨newRootVal, m3, hwpath, _⟩ := hM1 r hr
        simp [hr, hwpath] at hw

end MiniRustSpec.Correspondence
