/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Relation

/-!
# Lemmas about the translation and the MiniRust interpretation

Symbolic-evaluation facts used by the simulation proof: what `translateFn`
produces, and what the interpreted MiniRust functions compute on machines in
the shape described by `StateRel`.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-! ## Association lists -/

theorem mapGet_nil {K V : Type} [DecidableEq K] (k : K) : mapGet (⟨[]⟩ : Map K V) k = none := rfl

theorem mapGet_cons {K V : Type} [DecidableEq K] (k k' : K) (v : V) (es : List (K × V)) :
    mapGet ⟨(k', v) :: es⟩ k = if k' = k then some v else mapGet ⟨es⟩ k := by
  unfold mapGet
  by_cases h : k' = k <;> simp [h]

theorem mapGet_append_of_some {K V : Type} [DecidableEq K] (k : K) (v : V) (es es' : List (K × V))
    (h : mapGet ⟨es⟩ k = some v) : mapGet ⟨es ++ es'⟩ k = some v := by
  induction es with
  | nil => simp [mapGet_nil] at h
  | cons e es ih =>
    obtain ⟨k', v'⟩ := e
    rw [List.cons_append, mapGet_cons]
    rw [mapGet_cons] at h
    split
    · next hk => simp [hk] at h; simp [h]
    · next hk => simp [hk] at h; exact ih h

theorem localName_inj (a b : Nat) : localName a = localName b ↔ a = b := by
  simp [localName]

theorem bbName_inj (a b : Nat) : bbName a = bbName b ↔ a = b := by
  simp [bbName]

/-! ## Fragment types -/

theorem intTypeOf_isBoolTy {t : MirAst.Ty} {it : Gen.IntType} (h : intTypeOf t = some it) :
    isBoolTy t = false := by
  unfold intTypeOf intTyBytes at h
  unfold isBoolTy
  split at h <;> simp_all

theorem isBoolTy_intTypeOf {t : MirAst.Ty} (h : isBoolTy t = true) : intTypeOf t = none := by
  unfold isBoolTy at h
  unfold intTypeOf intTyBytes
  split at h <;> simp_all

theorem intTypeOf_isOrderingTy {t : MirAst.Ty} {it : Gen.IntType} (h : intTypeOf t = some it) :
    isOrderingTy t = false := by
  unfold intTypeOf intTyBytes at h
  unfold isOrderingTy
  split at h <;> simp_all

theorem isOrderingTy_intTypeOf {t : MirAst.Ty} (h : isOrderingTy t = true) : intTypeOf t = none := by
  unfold isOrderingTy at h
  unfold intTypeOf intTyBytes
  split at h <;> simp_all

theorem isOrderingTy_isBoolTy {t : MirAst.Ty} (h : isOrderingTy t = true) : isBoolTy t = false := by
  unfold isOrderingTy at h
  unfold isBoolTy
  split at h <;> simp_all

theorem intTypeOf_intBoolTupleOf {t : MirAst.Ty} {it : Gen.IntType} (h : intTypeOf t = some it) :
    intBoolTupleOf t = none := by
  unfold intTypeOf intTyBytes at h
  unfold intBoolTupleOf
  split at h <;> simp_all

theorem intBoolTupleOf_intTypeOf {t : MirAst.Ty} {it : Gen.IntType}
    (h : intBoolTupleOf t = some it) : intTypeOf t = none := by
  unfold intBoolTupleOf at h
  unfold intTypeOf intTyBytes
  split at h <;> simp_all

theorem intBoolTupleOf_isBoolTy {t : MirAst.Ty} {it : Gen.IntType}
    (h : intBoolTupleOf t = some it) : isBoolTy t = false := by
  unfold intBoolTupleOf at h
  unfold isBoolTy
  split at h <;> simp_all

theorem isBoolTy_intBoolTupleOf {t : MirAst.Ty} (h : isBoolTy t = true) :
    intBoolTupleOf t = none := by
  unfold isBoolTy at h
  unfold intBoolTupleOf
  split at h <;> simp_all

theorem intBoolTupleOf_isOrderingTy {t : MirAst.Ty} {it : Gen.IntType}
    (h : intBoolTupleOf t = some it) : isOrderingTy t = false := by
  unfold intBoolTupleOf at h
  unfold isOrderingTy
  split at h <;> simp_all

theorem isOrderingTy_intBoolTupleOf {t : MirAst.Ty} (h : isOrderingTy t = true) :
    intBoolTupleOf t = none := by
  unfold isOrderingTy at h
  unfold intBoolTupleOf
  split at h <;> simp_all

theorem scalarTypeOf_int {t : MirAst.Ty} {it : Gen.IntType} (h : intTypeOf t = some it) :
    scalarTypeOf t = some (.Int it) := by
  simp [scalarTypeOf, intTypeOf_isBoolTy h, intTypeOf_isOrderingTy h, intTypeOf_intBoolTupleOf h, h]

theorem scalarTypeOf_bool {t : MirAst.Ty} (h : isBoolTy t = true) : scalarTypeOf t = some .Bool := by
  simp [scalarTypeOf, h]

theorem scalarTypeOf_ordering {t : MirAst.Ty} (h : isOrderingTy t = true) :
    scalarTypeOf t = some orderingTy := by
  simp [scalarTypeOf, h, isOrderingTy_isBoolTy h]

theorem scalarTypeOf_tuple {t : MirAst.Ty} {it : Gen.IntType} (h : intBoolTupleOf t = some it) :
    scalarTypeOf t = some (intBoolTupleTy it) := by
  simp [scalarTypeOf, intBoolTupleOf_isBoolTy h, intBoolTupleOf_isOrderingTy h, h]

/-- A fragment type is `bool`, an integer type, `core::cmp::Ordering`, or a
2-tuple `(Int, bool)`. -/
theorem scalarTypeOf_cases {t : MirAst.Ty} {T : Gen.Type} (h : scalarTypeOf t = some T) :
    (isBoolTy t = true ∧ T = .Bool) ∨ (∃ it, intTypeOf t = some it ∧ T = .Int it) ∨
      (isOrderingTy t = true ∧ T = orderingTy) ∨
      (∃ it, intBoolTupleOf t = some it ∧ T = intBoolTupleTy it) := by
  unfold scalarTypeOf at h
  cases hb : isBoolTy t with
  | true => simp [hb] at h; exact .inl ⟨rfl, h.symm⟩
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    cases ho : isOrderingTy t with
    | true => simp [ho] at h; exact .inr (.inr (.inl ⟨rfl, h.symm⟩))
    | false =>
      simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
      cases htup : intBoolTupleOf t with
      | some it => simp [htup] at h; exact .inr (.inr (.inr ⟨it, rfl, h.symm⟩))
      | none =>
        simp only [htup] at h
        cases hit : intTypeOf t with
        | none => simp [hit] at h
        | some it => simp [hit] at h; exact .inr (.inl ⟨it, rfl, h.symm⟩)

theorem tyOf_int {d : LocalDecl} {it : Gen.IntType} (h : intTypeOf d.ty = some it) :
    tyOf d = .Int it ∧ itOf d = it := by
  simp [tyOf, itOf, scalarTypeOf_int h, h]

theorem tyOf_bool {d : LocalDecl} (h : isBoolTy d.ty = true) : tyOf d = .Bool ∧ itOf d = u8Ty := by
  simp [tyOf, itOf, scalarTypeOf_bool h, isBoolTy_intTypeOf h, isBoolTy_intBoolTupleOf h, u8Ty]

theorem tyOf_ordering {d : LocalDecl} (h : isOrderingTy d.ty = true) :
    tyOf d = orderingTy ∧ itOf d = u8Ty := by
  simp [tyOf, itOf, scalarTypeOf_ordering h, isOrderingTy_intTypeOf h, isOrderingTy_intBoolTupleOf h, u8Ty]

theorem tyOf_tuple {d : LocalDecl} {it : Gen.IntType} (h : intBoolTupleOf d.ty = some it) :
    tyOf d = intBoolTupleTy it ∧ itOf d = it := by
  simp [tyOf, itOf, scalarTypeOf_tuple h, intBoolTupleOf_intTypeOf h, h]

@[simp] theorem tupleIntOfTy_intBoolTupleTy (it : Gen.IntType) :
    tupleIntOfTy (intBoolTupleTy it) = some it := by
  simp [intBoolTupleTy, tupleIntOfTy]

@[simp] theorem tupleIntOfTy_int (it : Gen.IntType) : tupleIntOfTy (.Int it) = none := rfl
@[simp] theorem tupleIntOfTy_bool : tupleIntOfTy .Bool = none := rfl
@[simp] theorem tupleIntOfTy_orderingTy : tupleIntOfTy orderingTy = none := rfl

theorem declSlotData_of_none {d : LocalDecl} (h : intBoolTupleOf d.ty = none) (slot : LocalSlot) :
    declSlotData d slot = slotData (itOf d) slot := by
  simp [declSlotData, h]

theorem declSlotData_of_some {d : LocalDecl} {it : Gen.IntType} (h : intBoolTupleOf d.ty = some it)
    (slot : LocalSlot) : declSlotData d slot = tupleSlotData it slot := by
  simp [declSlotData, h]

/-- `2-tuple` constants are outside the fragment: `translateOperand` reads
only integer and `bool` scalars. -/
theorem translateOperand_tuple_const {c : ConstOperand} {it : Gen.IntType}
    (ht : intBoolTupleOf c.ty = some it) : translateOperand (.constant c) = none := by
  simp only [translateOperand, intBoolTupleOf_isBoolTy ht, Bool.false_eq_true, ↓reduceIte,
    intBoolTupleOf_intTypeOf ht]
  split <;> simp_all

/-- `Ordering` constants are outside the fragment: `translateOperand` reads
only integer and `bool` scalars. -/
theorem translateOperand_ordering_const {c : ConstOperand} (ho : isOrderingTy c.ty = true) :
    translateOperand (.constant c) = none := by
  simp only [translateOperand, isOrderingTy_isBoolTy ho, Bool.false_eq_true, ↓reduceIte,
    isOrderingTy_intTypeOf ho]
  split <;> simp_all

/-- `tyOf` is the translated type of a fragment local. -/
theorem tyOf_of_scalarTypeOf {d : LocalDecl} {T : Gen.Type} (h : scalarTypeOf d.ty = some T) :
    tyOf d = T := by
  simp [tyOf, h]


/-! ## `translateFn` -/

theorem translateLocals_get (k : Nat) (ds : List LocalDecl) (L : List (Gen.LocalName × Gen.Type))
    (h : translateLocals k ds = some L) (j : Nat) (d : LocalDecl) (hd : ds[j]? = some d) :
    ∃ T, scalarTypeOf d.ty = some T ∧ mapGet ⟨L⟩ (localName (k + j)) = some T := by
  induction ds generalizing k L j with
  | nil => simp at hd
  | cons d' ds ih =>
    simp only [translateLocals, Option.bind_eq_bind] at h
    cases hit : scalarTypeOf d'.ty with
    | none => simp [hit] at h
    | some it' =>
      cases hrest : translateLocals (k + 1) ds with
      | none => simp [hit, hrest] at h
      | some rest =>
        simp [hit, hrest] at h
        subst h
        cases j with
        | zero =>
          simp at hd; subst hd
          exact ⟨it', hit, by simp [mapGet_cons]⟩
        | succ j =>
          simp at hd
          obtain ⟨it, hit2, hget⟩ := ih (k + 1) rest hrest j hd
          refine ⟨it, hit2, ?_⟩
          rw [mapGet_cons]
          split
          · next heq => rw [localName_inj] at heq; omega
          · rw [show k + (j + 1) = k + 1 + j by omega]; exact hget

theorem translateBlocks_get (decls : List LocalDecl) (k : Nat) (bbs : List BasicBlockData)
    (B : List (Gen.BbName × Gen.BasicBlock)) (h : translateBlocks decls k bbs = some B) (j : Nat)
    (bb : BasicBlockData) (hb : bbs[j]? = some bb) :
    ∃ tb, translateBlock decls bb = some tb ∧ mapGet ⟨B⟩ (bbName (k + j)) = some tb := by
  induction bbs generalizing k B j with
  | nil => simp at hb
  | cons bb' bbs ih =>
    simp only [translateBlocks, Option.bind_eq_bind] at h
    cases htb : translateBlock decls bb' with
    | none => simp [htb] at h
    | some tb' =>
      cases hrest : translateBlocks decls (k + 1) bbs with
      | none => simp [htb, hrest] at h
      | some rest =>
        simp [htb, hrest] at h
        subst h
        cases j with
        | zero =>
          simp at hb; subst hb
          exact ⟨tb', htb, by simp [mapGet_cons]⟩
        | succ j =>
          simp at hb
          obtain ⟨tb, htb2, hget⟩ := ih (k + 1) rest hrest j hb
          refine ⟨tb, htb2, ?_⟩
          rw [mapGet_cons]
          split
          · next heq => rw [bbName_inj] at heq; omega
          · rw [show k + (j + 1) = k + 1 + j by omega]; exact hget

/-- What `translateFn` produces, in the form the simulation proof consumes. -/
theorem translateFn_spec (body : CapturedMir) (f : Gen.Function) (h : translateFn body = some f) :
    f.ret = localName 0 ∧
    (∀ (i : Nat) d, body.localDecls[i]? = some d →
      scalarTypeOf d.ty = some (tyOf d) ∧ mapGet f.locals (localName i) = some (tyOf d)) ∧
    (∀ (i : Nat) bb, body.basicBlocks[i]? = some bb →
      ∃ tb, translateBlock body.localDecls bb = some tb ∧ mapGet f.blocks (bbName i) = some tb) := by
  simp only [translateFn, Option.bind_eq_bind] at h
  cases hL : translateLocals 0 body.localDecls with
  | none => simp [hL] at h
  | some L =>
    cases hB : translateBlocks body.localDecls 0 body.basicBlocks with
    | none => simp [hL, hB] at h
    | some B =>
      simp [hL, hB] at h
      subst h
      refine ⟨rfl, ?_, ?_⟩
      · intro i d hd
        obtain ⟨T, hT, hget⟩ := translateLocals_get 0 body.localDecls L hL i d hd
        rw [tyOf_of_scalarTypeOf hT]; refine ⟨hT, ?_⟩
        simpa using hget
      · intro i bb hbb
        obtain ⟨tb, htb, hget⟩ := translateBlocks_get body.localDecls 0 body.basicBlocks B hB i bb hbb
        refine ⟨tb, htb, ?_⟩
        apply mapGet_append_of_some
        simpa using hget

theorem translateBlocks_append_get (decls : List LocalDecl) (k : Nat) (bbs : List BasicBlockData)
    (B : List (Gen.BbName × Gen.BasicBlock)) (h : translateBlocks decls k bbs = some B)
    (m : Nat) (hm : k + bbs.length ≤ m) (ib : Gen.BasicBlock) :
    mapGet ⟨B ++ [(bbName m, ib)]⟩ (bbName m) = some ib := by
  induction bbs generalizing k B with
  | nil => simp [translateBlocks] at h; subst h; simp [mapGet_cons]
  | cons bb bbs ih =>
    simp only [translateBlocks, Option.bind_eq_bind] at h
    cases htb : translateBlock decls bb with
    | none => simp [htb] at h
    | some tb =>
      cases hrest : translateBlocks decls (k + 1) bbs with
      | none => simp [htb, hrest] at h
      | some rest =>
        simp [htb, hrest] at h
        subst h
        rw [List.cons_append, mapGet_cons]
        split
        · next heq => rw [bbName_inj] at heq; simp at hm; omega
        · exact ih (k + 1) rest hrest (by simp at hm; omega)

/-- `translateFn` sets `f.start` to `bbName body.basicBlocks.length` and maps
that name to `initBlock` (`Goto(bb0)`). -/
theorem translateFn_start (body : CapturedMir) (f : Gen.Function) (h : translateFn body = some f) :
    f.start = bbName body.basicBlocks.length ∧
    mapGet f.blocks (bbName body.basicBlocks.length) = some (initBlock body) := by
  simp only [translateFn, Option.bind_eq_bind] at h
  cases hL : translateLocals 0 body.localDecls with
  | none => simp [hL] at h
  | some L =>
    cases hB : translateBlocks body.localDecls 0 body.basicBlocks with
    | none => simp [hL, hB] at h
    | some B =>
      simp [hL, hB] at h
      subst h
      exact ⟨rfl, translateBlocks_append_get body.localDecls 0 body.basicBlocks B hB
        body.basicBlocks.length (by omega) (initBlock body)⟩

/-! ## Multi-function translation lemmas (`translateFnInProg`, `translateProg`) -/

theorem FnLocalsSpec.of_translateFn {body : CapturedMir} {f : Gen.Function}
    (h : translateFn body = some f) : FnLocalsSpec body f := by
  obtain ⟨hret, hlocs, _⟩ := translateFn_spec body f h
  exact ⟨hret, hlocs⟩

theorem sameFragmentTy_spec {d1 d2 : LocalDecl} (h : sameFragmentTy d1.ty d2.ty = true) :
    tyOf d1 = tyOf d2 ∧ itOf d1 = itOf d2 ∧
      (∃ T, scalarTypeOf d1.ty = some T ∧ scalarTypeOf d2.ty = some T) ∧
      (∀ slot, declSlotData d1 slot = declSlotData d2 slot) := by
  unfold sameFragmentTy at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ((⟨hb1, hb2⟩ | ⟨ho1, ho2⟩) | htup) | hint
  · obtain ⟨hty1, hit1⟩ := tyOf_bool (d := d1) hb1
    obtain ⟨hty2, hit2⟩ := tyOf_bool (d := d2) hb2
    refine ⟨by rw [hty1, hty2], by rw [hit1, hit2],
      ⟨.Bool, scalarTypeOf_bool hb1, scalarTypeOf_bool hb2⟩, fun slot => ?_⟩
    rw [declSlotData_of_none (isBoolTy_intBoolTupleOf hb1),
      declSlotData_of_none (isBoolTy_intBoolTupleOf hb2), hit1, hit2]
  · obtain ⟨hty1, hit1⟩ := tyOf_ordering (d := d1) ho1
    obtain ⟨hty2, hit2⟩ := tyOf_ordering (d := d2) ho2
    refine ⟨by rw [hty1, hty2], by rw [hit1, hit2],
      ⟨orderingTy, scalarTypeOf_ordering ho1, scalarTypeOf_ordering ho2⟩, fun slot => ?_⟩
    rw [declSlotData_of_none (isOrderingTy_intBoolTupleOf ho1),
      declSlotData_of_none (isOrderingTy_intBoolTupleOf ho2), hit1, hit2]
  · cases ht1 : intBoolTupleOf d1.ty with
    | none => simp [ht1] at htup
    | some it1 =>
      cases ht2 : intBoolTupleOf d2.ty with
      | none => simp [ht1, ht2] at htup
      | some it2 =>
        simp [ht1, ht2, decide_eq_true_eq] at htup
        subst htup
        obtain ⟨hty1, hit1⟩ := tyOf_tuple (d := d1) ht1
        obtain ⟨hty2, hit2⟩ := tyOf_tuple (d := d2) ht2
        refine ⟨by rw [hty1, hty2], by rw [hit1, hit2],
          ⟨intBoolTupleTy it1, scalarTypeOf_tuple ht1, scalarTypeOf_tuple ht2⟩, fun slot => ?_⟩
        rw [declSlotData_of_some ht1, declSlotData_of_some ht2]
  · cases hi1 : intTypeOf d1.ty with
    | none => simp [hi1] at hint
    | some it1 =>
      cases hi2 : intTypeOf d2.ty with
      | none => simp [hi1, hi2] at hint
      | some it2 =>
        simp [hi1, hi2, decide_eq_true_eq] at hint
        subst hint
        obtain ⟨hty1, hit1⟩ := tyOf_int (d := d1) hi1
        obtain ⟨hty2, hit2⟩ := tyOf_int (d := d2) hi2
        have hnt1 : intBoolTupleOf d1.ty = none := by
          cases ht : intBoolTupleOf d1.ty with
          | none => rfl
          | some it => rw [intBoolTupleOf_intTypeOf ht] at hi1; cases hi1
        have hnt2 : intBoolTupleOf d2.ty = none := by
          cases ht : intBoolTupleOf d2.ty with
          | none => rfl
          | some it => rw [intBoolTupleOf_intTypeOf ht] at hi2; cases hi2
        refine ⟨by rw [hty1, hty2], by rw [hit1, hit2],
          ⟨.Int it1, scalarTypeOf_int hi1, scalarTypeOf_int hi2⟩, fun slot => ?_⟩
        rw [declSlotData_of_none hnt1, declSlotData_of_none hnt2, hit1, hit2]

theorem translateBlocksInProg_get (fnMap : List (String × Gen.FnName))
    (decls : List LocalDecl) (k nextC : Nat) (bbs : List BasicBlockData)
    (B extra : List (Gen.BbName × Gen.BasicBlock))
    (h : translateBlocksInProg fnMap decls k nextC bbs = some (B, extra))
    (j : Nat) (bb : BasicBlockData) (hb : bbs[j]? = some bb) :
    ∃ stmts term nc1 nc2 ex1,
      bb.statements.mapM (translateStatement decls) = some stmts ∧
      translateTerminatorInProg fnMap decls nc1 bb.terminator = some (term, nc2, ex1) ∧
      mapGet ⟨B⟩ (bbName (k + j)) = some ⟨stmts, term, .Regular⟩ := by
  induction bbs generalizing k nextC B extra j with
  | nil => simp at hb
  | cons bb' bbs ih =>
    simp only [translateBlocksInProg, Option.bind_eq_bind] at h
    cases hst : bb'.statements.mapM (translateStatement decls) with
    | none => simp [hst] at h
    | some stmts' =>
      cases htm : translateTerminatorInProg fnMap decls nextC bb'.terminator with
      | none => simp [hst, htm] at h
      | some trep =>
        obtain ⟨term', nextC', extra1⟩ := trep
        cases hrest : translateBlocksInProg fnMap decls (k + 1) nextC' bbs with
        | none => simp [hst, htm, hrest] at h
        | some rrep =>
          obtain ⟨rest, extraRest⟩ := rrep
          simp [hst, htm, hrest] at h
          obtain ⟨rfl, rfl⟩ := h
          cases j with
          | zero =>
            simp at hb; subst hb
            exact ⟨stmts', term', nextC, nextC', extra1, hst, htm, by simp [mapGet_cons]⟩
          | succ j =>
            simp at hb
            obtain ⟨stmts, term, nc1, nc2, ex1, hs, ht, hget⟩ :=
              ih (k + 1) nextC' rest extraRest hrest j hb
            refine ⟨stmts, term, nc1, nc2, ex1, hs, ht, ?_⟩
            rw [mapGet_cons]
            split
            · next heq => rw [bbName_inj] at heq; omega
            · rw [show k + (j + 1) = k + 1 + j by omega]; exact hget

theorem translateBlocksInProg_append_get (fnMap : List (String × Gen.FnName))
    (decls : List LocalDecl) (k nextC : Nat) (bbs : List BasicBlockData)
    (B extra : List (Gen.BbName × Gen.BasicBlock))
    (h : translateBlocksInProg fnMap decls k nextC bbs = some (B, extra))
    (m : Nat) (hm : k + bbs.length ≤ m) (ib : Gen.BasicBlock)
    (tail : List (Gen.BbName × Gen.BasicBlock)) :
    mapGet ⟨B ++ [(bbName m, ib)] ++ tail⟩ (bbName m) = some ib := by
  induction bbs generalizing k nextC B extra with
  | nil =>
    simp [translateBlocksInProg] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [mapGet_cons]
  | cons bb bbs ih =>
    simp only [translateBlocksInProg, Option.bind_eq_bind] at h
    cases hst : bb.statements.mapM (translateStatement decls) with
    | none => simp [hst] at h
    | some stmts =>
      cases htm : translateTerminatorInProg fnMap decls nextC bb.terminator with
      | none => simp [hst, htm] at h
      | some trep =>
        obtain ⟨term, nextC', extra1⟩ := trep
        cases hrest : translateBlocksInProg fnMap decls (k + 1) nextC' bbs with
        | none => simp [hst, htm, hrest] at h
        | some rrep =>
          obtain ⟨rest, extraRest⟩ := rrep
          simp [hst, htm, hrest] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [List.cons_append, mapGet_cons]
          split
          · next heq => rw [bbName_inj] at heq; simp at hm; omega
          · simpa [List.append_assoc] using ih (k + 1) nextC' rest extraRest hrest (by simp at hm; omega)

/-- What `translateFnInProg` produces: `FnLocalsSpec`, calling convention and
argument list, `initBlock` at `f.start`, and block lookup for every MIR basic
block. -/
theorem translateFnInProg_spec (fnMap : List (String × Gen.FnName))
    (body : CapturedMir) (f : Gen.Function) (h : translateFnInProg fnMap body = some f) :
    FnLocalsSpec body f ∧
    f.calling_convention = .Rust ∧
    f.args = (List.range body.argCount).map (fun k => localName (k + 1)) ∧
    f.start = bbName body.basicBlocks.length ∧
    mapGet f.blocks (bbName body.basicBlocks.length) = some (initBlock body) ∧
    (∀ (i : Nat) bb, body.basicBlocks[i]? = some bb →
      ∃ stmts term nc1 nc2 ex1,
        bb.statements.mapM (translateStatement body.localDecls) = some stmts ∧
        translateTerminatorInProg fnMap body.localDecls nc1 bb.terminator = some (term, nc2, ex1) ∧
        mapGet f.blocks (bbName i) = some ⟨stmts, term, .Regular⟩) := by
  simp only [translateFnInProg, Option.bind_eq_bind] at h
  cases hL : translateLocals 0 body.localDecls with
  | none => simp [hL] at h
  | some L =>
    cases hB : translateBlocksInProg fnMap body.localDecls 0 (body.basicBlocks.length + 1)
        body.basicBlocks with
    | none => simp [hL, hB] at h
    | some brep =>
      obtain ⟨B, extra⟩ := brep
      simp [hL, hB] at h
      subst h
      refine ⟨⟨rfl, ?_⟩, rfl, rfl, rfl, ?_, ?_⟩
      · intro i d hd
        obtain ⟨T, hT, hget⟩ := translateLocals_get 0 body.localDecls L hL i d hd
        rw [tyOf_of_scalarTypeOf hT]
        exact ⟨hT, by simpa using hget⟩
      · simpa using translateBlocksInProg_append_get fnMap body.localDecls 0
          (body.basicBlocks.length + 1) body.basicBlocks B extra hB
          body.basicBlocks.length (by omega) (initBlock body) extra
      · intro i bb hbb
        obtain ⟨stmts, term, nc1, nc2, ex1, hs, ht, hget⟩ :=
          translateBlocksInProg_get fnMap body.localDecls 0 (body.basicBlocks.length + 1)
            body.basicBlocks B extra hB i bb hbb
        refine ⟨stmts, term, nc1, nc2, ex1, hs, ht, ?_⟩
        apply mapGet_append_of_some
        simpa using hget

theorem translateProgFns_get (fnMap : List (String × Gen.FnName))
    (k : Nat) (bs : List CapturedMir) (F : List (Gen.FnName × Gen.Function))
    (h : translateProgFns fnMap k bs = some F) (j : Nat) (b : CapturedMir)
    (hb : bs[j]? = some b) :
    ∃ f, translateFnInProg fnMap b = some f ∧ mapGet ⟨F⟩ (fnName (k + j)) = some f := by
  induction bs generalizing k F j with
  | nil => simp at hb
  | cons b' bs ih =>
    simp only [translateProgFns, Option.bind_eq_bind] at h
    cases hf : translateFnInProg fnMap b' with
    | none => simp [hf] at h
    | some f' =>
      cases hrest : translateProgFns fnMap (k + 1) bs with
      | none => simp [hf, hrest] at h
      | some rest =>
        simp [hf, hrest] at h
        subst h
        cases j with
        | zero =>
          simp at hb; subst hb
          exact ⟨f', hf, by simp [mapGet_cons]⟩
        | succ j =>
          simp at hb
          obtain ⟨f, hf2, hget⟩ := ih (k + 1) rest hrest j hb
          refine ⟨f, hf2, ?_⟩
          rw [mapGet_cons]
          split
          · next heq => rw [fnName_inj] at heq; omega
          · rw [show k + (j + 1) = k + 1 + j by omega]; exact hget

theorem listByteEq_eq_true {xs ys : List UInt8} :
    MirSemantics.listByteEq xs ys = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [MirSemantics.listByteEq]
  | cons x xs ih =>
    cases ys with
    | nil => simp [MirSemantics.listByteEq]
    | cons y ys =>
      simp only [MirSemantics.listByteEq]
      cases hbeq : Nat.beq x.toBitVec.toNat y.toBitVec.toNat with
      | false =>
        constructor
        · intro hf; cases hf
        · rintro ⟨rfl, _⟩; simp at hbeq
      | true =>
        have hxy : x = y := by
          have hn : x.toBitVec.toNat = y.toBitVec.toNat := Nat.eq_of_beq_eq_true hbeq
          cases x; cases y
          simpa using BitVec.eq_of_toNat_eq hn
        subst hxy
        simpa using ih

theorem stringEq_eq_true {a b : String} :
    MirSemantics.stringEq a b = true ↔ a = b := by
  simp only [MirSemantics.stringEq, listByteEq_eq_true]
  constructor
  · intro h
    exact String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp h))
  · rintro rfl; rfl

theorem findCallee_idx {callees : List CapturedMir} {dp : String} {callee : CapturedMir}
    (h : MirSemantics.findCallee? callees dp = some callee) :
    ∃ (j : Nat), callees[j]? = some callee ∧ callee.defPath = dp := by
  induction callees with
  | nil => simp [MirSemantics.findCallee?] at h
  | cons c cs ih =>
    simp only [MirSemantics.findCallee?] at h
    cases hseq : MirSemantics.stringEq c.defPath dp with
    | true =>
      rw [hseq] at h; simp at h; subst h
      exact ⟨0, rfl, stringEq_eq_true.mp hseq⟩
    | false =>
      rw [hseq] at h; simp at h
      obtain ⟨j, hj, hdp⟩ := ih h
      exact ⟨j + 1, hj, hdp⟩

theorem lookupFnName_zipIdx_aux (bs : List CapturedMir) (k : Nat)
    (hnd : (bs.map (·.defPath)).Nodup) (j : Nat) (b : CapturedMir)
    (hb : bs[j]? = some b) :
    lookupFnName (bs.zipIdx k |>.map fun (x, idx) => (x.defPath, fnName idx)) b.defPath =
      some (fnName (k + j)) := by
  induction bs generalizing k j with
  | nil => simp at hb
  | cons b' bs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    cases j with
    | zero =>
      simp at hb; subst hb
      simp [List.zipIdx_cons, lookupFnName]
    | succ j =>
      simp at hb
      have hmem : b.defPath ∈ bs.map (·.defPath) :=
        List.mem_map.mpr ⟨b, List.mem_of_getElem? hb, rfl⟩
      have hne : (b'.defPath == b.defPath) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        exact hnd.1 (heq ▸ hmem)
      simp only [List.zipIdx_cons, List.map_cons, lookupFnName, hne, Bool.false_eq_true, ↓reduceIte]
      rw [show k + (j + 1) = k + 1 + j by omega]
      exact ih (k + 1) hnd.2 j hb

/-- Specification of `translateProg`: maps `entry` at `fnName 0`, and resolves
every callee found by Anneal's `findCallee? callees dp` to the corresponding
translated `Gen.Function` in `prog.functions` via `lookupFnName`. -/
theorem translateProg_spec {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} (hnd : ((entry :: callees).map (·.defPath)).Nodup)
    (h : translateProg entry callees = some prog) :
    (∃ fEntry, translateFnInProg (fnNameMap entry callees) entry = some fEntry ∧
      mapGet prog.functions (fnName 0) = some fEntry) ∧
    (∀ dp callee, MirSemantics.findCallee? callees dp = some callee →
      ∃ idx fCallee,
        callee ∈ entry :: callees ∧
        lookupFnName (fnNameMap entry callees) dp = some (fnName idx) ∧
        translateFnInProg (fnNameMap entry callees) callee = some fCallee ∧
        mapGet prog.functions (fnName idx) = some fCallee) := by
  simp only [translateProg, Option.bind_eq_bind] at h
  cases hF : translateProgFns (fnNameMap entry callees) 0 (entry :: callees) with
  | none => simp [hF] at h
  | some F =>
    simp [hF] at h
    subst h
    constructor
    · obtain ⟨fEntry, hfE, hgetE⟩ :=
        translateProgFns_get (fnNameMap entry callees) 0 (entry :: callees) F hF 0 entry rfl
      refine ⟨fEntry, hfE, ?_⟩
      apply mapGet_append_of_some
      simpa using hgetE
    · intro dp callee hfc
      obtain ⟨j, hj, rfl⟩ := findCallee_idx hfc
      have hbj : (entry :: callees)[j + 1]? = some callee := hj
      obtain ⟨fCallee, hfC, hgetC⟩ :=
        translateProgFns_get (fnNameMap entry callees) 0 (entry :: callees) F hF (j + 1) callee hbj
      have hlk : lookupFnName (fnNameMap entry callees) callee.defPath = some (fnName (j + 1)) := by
        simpa [fnNameMap] using lookupFnName_zipIdx_aux (entry :: callees) 0 hnd (j + 1) callee hbj
      refine ⟨j + 1, fCallee, .tail _ (List.mem_of_getElem? hj), hlk, hfC, ?_⟩
      apply mapGet_append_of_some
      simpa using hgetC

end MiniRustSpec.Correspondence
