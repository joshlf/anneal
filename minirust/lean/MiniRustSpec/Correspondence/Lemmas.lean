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
  cases hC : translateCallConv body.fnAbi.conv with
  | none => simp [hC] at h
  | some conv =>
    cases hL : translateLocals 0 body.localDecls with
    | none => simp [hC, hL] at h
    | some L =>
      cases hB : translateBlocks body.localDecls 0 body.basicBlocks with
      | none => simp [hC, hL, hB] at h
      | some B =>
        simp [hC, hL, hB] at h
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
  cases hC : translateCallConv body.fnAbi.conv with
  | none => simp [hC] at h
  | some conv =>
    cases hL : translateLocals 0 body.localDecls with
    | none => simp [hC, hL] at h
    | some L =>
      cases hB : translateBlocks body.localDecls 0 body.basicBlocks with
      | none => simp [hC, hL, hB] at h
      | some B =>
        simp [hC, hL, hB] at h
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

/-! ### Block layout of `translateFnInProg` (`splitStmts`, `SegChain`) -/

theorem mapGet_eq_of_mem_nodup {K V : Type} [DecidableEq K] {es : List (K × V)} {k : K} {v : V}
    (hnd : (es.map Prod.fst).Nodup) (hmem : (k, v) ∈ es) : mapGet ⟨es⟩ k = some v := by
  induction es with
  | nil => simp at hmem
  | cons e es ih =>
    obtain ⟨k', v'⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [mapGet_cons]
    rcases List.mem_cons.mp hmem with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · have hne : k' ≠ k := fun heq => hnd.1 (heq ▸ List.mem_map.mpr ⟨(k, v), h, rfl⟩)
      simp only [hne, ↓reduceIte]
      exact ih hnd.2 h

theorem isAssume_iff (s : MirAst.Statement) :
    isAssume s = true ↔ ∃ op, s.kind = .intrinsic (.assume op) := by
  unfold isAssume
  split
  · next op heq => exact ⟨fun _ => ⟨op, heq⟩, fun _ => rfl⟩
  · next hne => exact ⟨fun h => absurd h (by simp), fun ⟨op, hop⟩ => absurd hop (hne op)⟩

/-- The two shapes of `translateStmtResult`: an ordinary statement translated
by `translateStatement`, or an `Assume` that ends the current block. -/
theorem translateStmtResult_some {decls : List LocalDecl} {s : MirAst.Statement}
    {r : StatementResult} (h : translateStmtResult decls s = some r) :
    (isAssume s = false ∧ ∃ s', translateStatement decls s = some s' ∧ r = .statement s') ∨
    (∃ op op', s.kind = .intrinsic (.assume op) ∧ translateOperand op = some op' ∧
      r = .intrinsic .Assume unitPlace [op']) := by
  by_cases ha : ∃ op, s.kind = .intrinsic (.assume op)
  · obtain ⟨op, hk⟩ := ha
    simp only [translateStmtResult, hk] at h
    obtain ⟨op', hop, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inr ⟨op, op', hk, hop, rfl⟩
  · have hna : isAssume s = false := by
      cases hb : isAssume s with
      | false => rfl
      | true => exact absurd ((isAssume_iff s).mp hb) ha
    have heq : translateStmtResult decls s = (translateStatement decls s).map .statement := by
      unfold translateStmtResult
      split
      · next op heq => exact absurd ⟨op, heq⟩ ha
      · rfl
    rw [heq] at h
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inl ⟨hna, s', hs', rfl⟩

/-- `splitStmts` closes the open block `cur` and then takes the fresh names
`nc, nc + 1, ..` in order: the names of the finished blocks followed by the
name of the block left open are `cur` and those fresh names. -/
theorem splitStmts_names (cur : Gen.BbName) (acc : List Gen.Statement) (nc : Nat)
    (rs : List StatementResult) :
    nc ≤ (splitStmts cur acc nc rs).2.2.2 ∧
    (splitStmts cur acc nc rs).2.2.1.map Prod.fst ++ [(splitStmts cur acc nc rs).1] =
      cur :: (List.range' nc ((splitStmts cur acc nc rs).2.2.2 - nc)).map bbName := by
  induction rs generalizing cur acc nc with
  | nil => simp [splitStmts]
  | cons r rest ih =>
    cases r with
    | statement s => simpa [splitStmts] using ih cur (acc ++ [s]) nc
    | intrinsic op dest args =>
      obtain ⟨h1, h2⟩ := ih (bbName nc) [] (nc + 1)
      simp only [splitStmts]
      refine ⟨by omega, ?_⟩
      simp only [List.map_cons, List.cons_append]
      rw [h2]
      have hlen : (splitStmts (bbName nc) [] (nc + 1) rest).2.2.2 - nc =
          ((splitStmts (bbName nc) [] (nc + 1) rest).2.2.2 - (nc + 1)) + 1 := by omega
      rw [hlen, List.range'_succ]
      simp

/-- The cleanup blocks of `translateTerminatorInProg` take the fresh names
`nc, nc + 1, ..` (at most one, for a call's unwind action). -/
theorem translateTerminatorInProg_names {fnMap : FnMap} {decls : List LocalDecl} {nc : Nat}
    {t : MirAst.Terminator} {term : Gen.Terminator} {nc' : Nat}
    {ex : List (Gen.BbName × Gen.BasicBlock)}
    (h : translateTerminatorInProg fnMap decls nc t = some (term, nc', ex)) :
    nc ≤ nc' ∧ ex.map Prod.fst = (List.range' nc (nc' - nc)).map bbName := by
  unfold translateTerminatorInProg at h
  cases hk : t.kind
  case call func argOps destination target unwind =>
    simp only [hk, Option.bind_eq_bind] at h
    cases hdp : extractFnDefPath func <;> simp only [hdp, Option.bind_none, Option.bind_some] at h
    · cases h
    rename_i dp
    cases hlk : lookupFnTarget fnMap dp <;> simp only [hlk, Option.bind_none, Option.bind_some] at h
    · cases h
    rename_i fc
    cases ha : argOps.mapM translateCallArg <;> simp only [ha, Option.bind_none, Option.bind_some] at h
    · cases h
    cases hr : translatePlace destination <;> simp only [hr, Option.bind_none, Option.bind_some] at h
    · cases h
    cases unwind <;> simp [translateUnwindAction] at h <;> obtain ⟨_, rfl, rfl⟩ := h <;> simp
  all_goals
    simp only [hk, Option.bind_eq_bind] at h
    cases ht : translateTerminator decls t <;> simp only [ht, Option.bind_none, Option.bind_some] at h
    · cases h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, rfl⟩ := h
    simp

theorem nodup_map_bbName {l : List Nat} (h : l.Nodup) : (l.map bbName).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => h.1 ?_, ih h.2⟩
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
    rw [bbName_inj] at hxy
    exact hxy ▸ hy

theorem bbName_range'_nodup (a n : Nat) : ((List.range' a n).map bbName).Nodup :=
  nodup_map_bbName (by simpa using List.nodup_range' (s := a) (n := n))

theorem range'_append_of_le {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) :
    List.range' a (b - a) ++ List.range' b (c - b) = List.range' a (c - a) := by
  have := List.range'_append (s := a) (m := b - a) (n := c - b) (step := 1)
  simp only [Nat.one_mul] at this
  rw [show a + (b - a) = b by omega, show b - a + (c - b) = c - a by omega] at this
  exact this

theorem mem_bbName_range' {x : Gen.BbName} {a n : Nat} :
    x ∈ (List.range' a n).map bbName ↔ ∃ c, a ≤ c ∧ c < a + n ∧ x = bbName c := by
  simp only [List.mem_map, List.mem_range']
  constructor
  · rintro ⟨c, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨a + i, by omega, by omega, by simp⟩
  · rintro ⟨c, h1, h2, rfl⟩
    exact ⟨c, ⟨c - a, by omega, by omega⟩, rfl⟩

/-- `translateBlocksInProg` names each MIR block's first segment after the MIR
block and takes every other block name from the fresh range `nc, nc + 1, ..`,
so the names are pairwise distinct and each is either a MIR block name
`bbName (k + j)` or a fresh name `bbName c` with `nc ≤ c`. -/
theorem translateBlocksInProg_names {fnMap : FnMap} {decls : List LocalDecl} :
    ∀ (k nc : Nat) (bbs : List BasicBlockData) (B extra : List (Gen.BbName × Gen.BasicBlock)),
      translateBlocksInProg fnMap decls k nc bbs = some (B, extra) →
      k + bbs.length ≤ nc →
      ((B ++ extra).map Prod.fst).Nodup ∧
      ∀ e ∈ B ++ extra,
        (∃ j, j < bbs.length ∧ e.1 = bbName (k + j)) ∨ (∃ c, nc ≤ c ∧ e.1 = bbName c)
  | k, nc, [], B, extra, h, _ => by
    simp [translateBlocksInProg] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | k, nc, bb :: bbs, B, extra, h, hk => by
    simp only [translateBlocksInProg, Option.bind_eq_bind] at h
    cases hres : bb.statements.mapM (translateStmtResult decls) with
    | none => simp [hres] at h
    | some results =>
      simp only [hres, Option.bind_some] at h
      obtain ⟨hsp1, hsp2⟩ := splitStmts_names (bbName k) [] nc results
      generalize hsp : splitStmts (bbName k) [] nc results = sp at hsp1 hsp2 h
      cases htm : translateTerminatorInProg fnMap decls sp.2.2.2 bb.terminator with
      | none => simp [htm] at h
      | some trep =>
        obtain ⟨term, nc', ex1⟩ := trep
        obtain ⟨htm1, htm2⟩ := translateTerminatorInProg_names htm
        simp only [htm, Option.bind_some] at h
        cases hrest : translateBlocksInProg fnMap decls (k + 1) nc' bbs with
        | none => simp [hrest] at h
        | some rrep =>
          obtain ⟨rest, extraRest⟩ := rrep
          simp only [hrest, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [List.length_cons] at hk
          obtain ⟨ihNd, ihMem⟩ :=
            translateBlocksInProg_names (k + 1) nc' bbs rest extraRest hrest (by omega)
          let segs : List (Gen.BbName × Gen.BasicBlock) :=
            sp.2.2.1 ++ [(sp.1, ⟨sp.2.1, term, .Regular⟩)]
          have hsegNames : (segs ++ ex1).map Prod.fst =
              bbName k :: (List.range' nc (nc' - nc)).map bbName := by
            have h1 : segs.map Prod.fst = bbName k :: (List.range' nc (sp.2.2.2 - nc)).map bbName := by
              simpa [segs, List.map_append] using hsp2
            rw [List.map_append, h1, htm2, List.cons_append, ← List.map_append,
              range'_append_of_le hsp1 htm1]
          have hperm : List.Perm (((segs ++ rest) ++ (ex1 ++ extraRest)).map Prod.fst)
              ((bbName k :: (List.range' nc (nc' - nc)).map bbName) ++
                (rest ++ extraRest).map Prod.fst) := by
            rw [← hsegNames, ← List.map_append]
            apply List.Perm.map
            simp only [List.append_assoc]
            exact List.Perm.append_left segs (List.perm_append_comm_assoc rest ex1 extraRest)
          have hRestBound : ∀ x ∈ (rest ++ extraRest).map Prod.fst,
              (∃ j, j < bbs.length ∧ x = bbName (k + 1 + j)) ∨ (∃ c, nc' ≤ c ∧ x = bbName c) := by
            intro x hx
            obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
            exact ihMem e he
          refine ⟨hperm.nodup_iff.mpr ?_, ?_⟩
          · rw [List.nodup_append]
            refine ⟨?_, ihNd, ?_⟩
            · rw [List.nodup_cons]
              refine ⟨fun hmem => ?_, bbName_range'_nodup nc (nc' - nc)⟩
              obtain ⟨c, hc1, _, hc⟩ := mem_bbName_range'.mp hmem
              rw [bbName_inj] at hc
              omega
            · intro x hx y hy hxy
              subst hxy
              rcases hRestBound x hy with ⟨j, hj, hx'⟩ | ⟨c, hc, hx'⟩
              · rcases List.mem_cons.mp hx with hx0 | hx0
                · rw [hx0, bbName_inj] at hx'; omega
                · obtain ⟨c, hc1, hc2, hc⟩ := mem_bbName_range'.mp hx0
                  rw [hc, bbName_inj] at hx'; omega
              · rcases List.mem_cons.mp hx with hx0 | hx0
                · rw [hx0, bbName_inj] at hx'; omega
                · obtain ⟨c', hc1, hc2, hc'⟩ := mem_bbName_range'.mp hx0
                  rw [hc', bbName_inj] at hx'; omega
          · intro e he
            have he' : e.1 ∈ ((segs ++ rest) ++ (ex1 ++ extraRest)).map Prod.fst :=
              List.mem_map.mpr ⟨e, he, rfl⟩
            rcases List.mem_append.mp (hperm.mem_iff.mp he') with hx | hx
            · rcases List.mem_cons.mp hx with hx0 | hx0
              · exact .inl ⟨0, by simp, by simpa using hx0⟩
              · obtain ⟨c, hc1, _, hc⟩ := mem_bbName_range'.mp hx0
                exact .inr ⟨c, hc1, hc⟩
            · rcases hRestBound e.1 hx with ⟨j, hj, hx'⟩ | ⟨c, hc, hx'⟩
              · exact .inl ⟨j + 1, by simp; omega, by rw [hx']; congr 1; omega⟩
              · exact .inr ⟨c, by omega, hx'⟩

/-- `splitStmts` lays out the statements still to be processed as a
`SegChain` from the open block `cur` on, provided every block it finishes and
the block it leaves open (completed with `term`) can be looked up; `pre` are
the statements already pushed onto the open block (translated to `acc`). -/
theorem splitStmts_segChain {look : Gen.BbName → Option Gen.BasicBlock}
    {decls : List LocalDecl} {term : Gen.Terminator} :
    ∀ (ss : List MirAst.Statement) (rs : List StatementResult) (cur : Gen.BbName)
      (pre : List MirAst.Statement) (acc : List Gen.Statement) (nc : Nat),
      ss.mapM (translateStmtResult decls) = some rs →
      pre.mapM (translateStatement decls) = some acc →
      (∀ s ∈ pre, isAssume s = false) →
      (∀ e ∈ (splitStmts cur acc nc rs).2.2.1 ++
          [((splitStmts cur acc nc rs).1, ⟨(splitStmts cur acc nc rs).2.1, term, .Regular⟩)],
        look e.1 = some e.2) →
      SegChain look decls term cur (pre ++ ss)
  | [], rs, cur, pre, acc, nc, hrs, hpre, hna, hlook => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrs
    subst hrs
    have hl := hlook (cur, ⟨acc, term, .Regular⟩) (by simp [splitStmts])
    simpa using SegChain.last hl hpre hna
  | s :: ss, rs, cur, pre, acc, nc, hrs, hpre, hna, hlook => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at hrs
    cases hr : translateStmtResult decls s with
    | none => simp [hr] at hrs
    | some r =>
      cases hrest : ss.mapM (translateStmtResult decls) with
      | none => simp [hr, hrest] at hrs
      | some rs' =>
        simp only [hr, hrest, Option.bind_some, Option.pure_def, Option.some.injEq] at hrs
        subst hrs
        rcases translateStmtResult_some hr with ⟨hna1, s', hs', rfl⟩ | ⟨op, op', hk, hop, rfl⟩
        · have hpre' : (pre ++ [s]).mapM (translateStatement decls) = some (acc ++ [s']) := by
            rw [List.mapM_append, hpre]
            simp [hs']
          have hna' : ∀ x ∈ pre ++ [s], isAssume x = false := by
            intro x hx
            rcases List.mem_append.mp hx with h | h
            · exact hna x h
            · simp only [List.mem_singleton] at h
              subst h
              exact hna1
          have := splitStmts_segChain ss rs' cur (pre ++ [s]) (acc ++ [s']) nc hrest hpre' hna'
            (by simpa [splitStmts] using hlook)
          simpa using this
        · have hl0 := hlook (cur, ⟨acc, .Intrinsic .Assume [op'] unitPlace (some (bbName nc)),
            .Regular⟩) (by simp [splitStmts])
          have hrestChain := splitStmts_segChain ss rs' (bbName nc) [] [] (nc + 1) hrest rfl
            (by simp) (fun e he => hlook e (by
              simp only [splitStmts, List.cons_append, List.mem_cons]
              exact .inr he))
          exact SegChain.split hl0 hpre hna hk hop (by simpa using hrestChain)

/-- Every MIR block's statements are laid out as a `SegChain` from the block's
own name on, ending in the block's translated terminator. -/
theorem translateBlocksInProg_segChain {fnMap : FnMap} {decls : List LocalDecl}
    {look : Gen.BbName → Option Gen.BasicBlock} :
    ∀ (k nc : Nat) (bbs : List BasicBlockData) (B extra : List (Gen.BbName × Gen.BasicBlock)),
      translateBlocksInProg fnMap decls k nc bbs = some (B, extra) →
      (∀ e ∈ B, look e.1 = some e.2) →
      ∀ (j : Nat) (bb : BasicBlockData), bbs[j]? = some bb →
        ∃ term nc1 nc2 ex1,
          translateTerminatorInProg fnMap decls nc1 bb.terminator = some (term, nc2, ex1) ∧
          SegChain look decls term (bbName (k + j)) bb.statements
  | _, _, [], _, _, _, _, j, _, hb => by simp at hb
  | k, nc, bb' :: bbs, B, extra, h, hlook, j, bb, hb => by
    simp only [translateBlocksInProg, Option.bind_eq_bind] at h
    cases hres : bb'.statements.mapM (translateStmtResult decls) with
    | none => simp [hres] at h
    | some results =>
      simp only [hres, Option.bind_some] at h
      generalize hsp : splitStmts (bbName k) [] nc results = sp at h
      cases htm : translateTerminatorInProg fnMap decls sp.2.2.2 bb'.terminator with
      | none => simp [htm] at h
      | some trep =>
        obtain ⟨term, nc', ex1⟩ := trep
        simp only [htm, Option.bind_some] at h
        cases hrest : translateBlocksInProg fnMap decls (k + 1) nc' bbs with
        | none => simp [hrest] at h
        | some rrep =>
          obtain ⟨rest, extraRest⟩ := rrep
          simp only [hrest, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases j with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
            subst hb
            refine ⟨term, sp.2.2.2, nc', ex1, htm, ?_⟩
            have := splitStmts_segChain (look := look) (term := term) bb'.statements results
              (bbName k) [] [] nc hres rfl (by simp) (by
                rw [hsp]
                intro e he
                exact hlook e (List.mem_append.mpr (.inl he)))
            simpa using this
          | succ j =>
            simp only [List.getElem?_cons_succ] at hb
            obtain ⟨term2, nc1, nc2, ex2, htm2, hseg⟩ :=
              translateBlocksInProg_segChain (k + 1) nc' bbs rest extraRest hrest
                (fun e he => hlook e (List.mem_append.mpr (.inr he))) j bb hb
            refine ⟨term2, nc1, nc2, ex2, htm2, ?_⟩
            rw [show k + (j + 1) = k + 1 + j by omega]
            exact hseg

/-- What `translateFnInProg` produces: `FnLocalsSpec`, calling convention and
argument list, `initBlock` at `f.start`, and, for every MIR basic block, the
`SegChain` layout of its statements (split at every `Assume`) ending in its
translated terminator. -/
theorem translateFnInProg_spec (fnMap : FnMap)
    (body : CapturedMir) (f : Gen.Function) (h : translateFnInProg fnMap body = some f) :
    FnLocalsSpec body f ∧
    translateCallConv body.fnAbi.conv = some f.calling_convention ∧
    f.args = (List.range body.argCount).map (fun k => localName (k + 1)) ∧
    f.start = bbName body.basicBlocks.length ∧
    mapGet f.blocks (bbName body.basicBlocks.length) = some (initBlock body) ∧
    (∀ (i : Nat) bb, body.basicBlocks[i]? = some bb →
      ∃ term nc1 nc2 ex1,
        translateTerminatorInProg fnMap body.localDecls nc1 bb.terminator =
          some (term, nc2, ex1) ∧
        SegChain (mapGet f.blocks) body.localDecls term (bbName i) bb.statements) := by
  simp only [translateFnInProg, Option.bind_eq_bind] at h
  cases hC : translateCallConv body.fnAbi.conv with
  | none => simp [hC] at h
  | some conv =>
    cases hL : translateLocals 0 body.localDecls with
    | none => simp [hC, hL] at h
    | some L =>
      cases hB : translateBlocksInProg fnMap body.localDecls 0 (body.basicBlocks.length + 1)
          body.basicBlocks with
      | none => simp [hC, hL, hB] at h
      | some brep =>
        obtain ⟨B, extra⟩ := brep
        simp [hC, hL, hB] at h
        subst h
        obtain ⟨hnd, hmem⟩ := translateBlocksInProg_names 0 (body.basicBlocks.length + 1)
          body.basicBlocks B extra hB (by omega)
        have hinit : bbName body.basicBlocks.length ∉ (B ++ extra).map Prod.fst := by
          intro hm
          obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
          rcases hmem e he with ⟨j, hj, hj'⟩ | ⟨c, hc, hc'⟩
          · rw [heq, bbName_inj] at hj'; omega
          · rw [heq, bbName_inj] at hc'; omega
        have hall : ((B ++ (bbName body.basicBlocks.length, initBlock body) :: extra).map
            Prod.fst).Nodup := by
          have hperm : List.Perm
              ((B ++ (bbName body.basicBlocks.length, initBlock body) :: extra).map Prod.fst)
              (bbName body.basicBlocks.length :: (B ++ extra).map Prod.fst) := by
            simp only [List.map_append, List.map_cons]
            exact List.perm_middle
          rw [hperm.nodup_iff, List.nodup_cons]
          exact ⟨hinit, hnd⟩
        refine ⟨⟨rfl, ?_⟩, rfl, rfl, rfl, ?_, ?_⟩
        · intro i d hd
          obtain ⟨T, hT, hget⟩ := translateLocals_get 0 body.localDecls L hL i d hd
          rw [tyOf_of_scalarTypeOf hT]
          exact ⟨hT, by simpa using hget⟩
        · exact mapGet_eq_of_mem_nodup hall (by simp)
        · intro i bb hbb
          have := translateBlocksInProg_segChain (look := mapGet
              ⟨B ++ (bbName body.basicBlocks.length, initBlock body) :: extra⟩)
            0 (body.basicBlocks.length + 1) body.basicBlocks B extra hB
            (fun e he => mapGet_eq_of_mem_nodup hall (List.mem_append.mpr (.inl he))) i bb hbb
          simpa using this

/-- A `SegChain` over statements none of which is an `Assume` is a single
segment: block `name` holds their translations followed by `term`. -/
theorem SegChain.eq_last {look : Gen.BbName → Option Gen.BasicBlock}
    {decls : List LocalDecl} {term : Gen.Terminator} {name : Gen.BbName}
    {ss : List MirAst.Statement} (h : SegChain look decls term name ss)
    (hna : ∀ s ∈ ss, isAssume s = false) :
    ∃ stmts, look name = some ⟨stmts, term, .Regular⟩ ∧
      ss.mapM (translateStatement decls) = some stmts := by
  cases h with
  | last hlook htr _ => exact ⟨_, hlook, htr⟩
  | split _ _ _ hs _ _ =>
    have h1 := hna _ (List.mem_append_right _ List.mem_cons_self)
    simp [isAssume, hs] at h1

/-- Single-body fragment statements (`statementOk`) are never `Assume`. -/
theorem statementOk_isAssume {decls : List LocalDecl} {s : MirAst.Statement}
    (h : statementOk decls s = true) : isAssume s = false := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | intrinsic i => simp [statementOk] at h
  | _ => rfl

theorem translateProgFns_get (fnMap : FnMap)
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

theorem lookupFnName_of_lookupFnTarget {fnMap : FnMap} {dp : String}
    {fn : Gen.FnName} {conv : Gen.CallingConvention}
    (h : lookupFnTarget fnMap dp = some (fn, conv)) :
    lookupFnName fnMap dp = some fn := by
  induction fnMap with
  | nil => simp [lookupFnTarget] at h
  | cons entry rest ih =>
    obtain ⟨k, fn', conv'⟩ := entry
    simp only [lookupFnTarget, lookupFnName] at h ⊢
    by_cases hif : (k == dp) = true
    · simp [hif] at h ⊢; exact h.1
    · simp [hif] at h ⊢; exact ih h

theorem lookupFnTarget_zipIdx_aux (bs : List CapturedMir) (k : Nat)
    (hnd : (bs.map (·.defPath)).Nodup) (j : Nat) (b : CapturedMir)
    (hb : bs[j]? = some b) :
    lookupFnTarget
      (bs.zipIdx k |>.map fun (x, idx) =>
        (x.defPath, (fnName idx, (translateCallConv x.fnAbi.conv).getD .Rust)))
      b.defPath =
      some (fnName (k + j), (translateCallConv b.fnAbi.conv).getD .Rust) := by
  induction bs generalizing k j with
  | nil => simp at hb
  | cons b' bs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    cases j with
    | zero =>
      simp at hb; subst hb
      simp [List.zipIdx_cons, lookupFnTarget]
    | succ j =>
      simp at hb
      have hmem : b.defPath ∈ bs.map (·.defPath) :=
        List.mem_map.mpr ⟨b, List.mem_of_getElem? hb, rfl⟩
      have hne : (b'.defPath == b.defPath) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        exact hnd.1 (heq ▸ hmem)
      simp only [List.zipIdx_cons, List.map_cons, lookupFnTarget, hne, Bool.false_eq_true, ↓reduceIte]
      rw [show k + (j + 1) = k + 1 + j by omega]
      exact ih (k + 1) hnd.2 j hb

theorem lookupFnName_zipIdx_aux (bs : List CapturedMir) (k : Nat)
    (hnd : (bs.map (·.defPath)).Nodup) (j : Nat) (b : CapturedMir)
    (hb : bs[j]? = some b) :
    lookupFnName
      (bs.zipIdx k |>.map fun (x, idx) =>
        (x.defPath, (fnName idx, (translateCallConv x.fnAbi.conv).getD .Rust)))
      b.defPath =
      some (fnName (k + j)) :=
  lookupFnName_of_lookupFnTarget (lookupFnTarget_zipIdx_aux bs k hnd j b hb)

/-- Specification of `translateProg`: maps `entry` at `fnName 0`, and resolves
every callee found by Anneal's `findCallee? callees dp` to the corresponding
translated `Gen.Function` in `prog.functions` via `lookupFnName` and
`lookupFnTarget`. -/
theorem translateProg_spec {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} (hnd : ((entry :: callees).map (·.defPath)).Nodup)
    (h : translateProg entry callees = some prog) :
    (∃ fEntry, translateFnInProg (fnNameMap entry callees) entry = some fEntry ∧
      mapGet prog.functions (fnName 0) = some fEntry) ∧
    (∀ dp callee, MirSemantics.findCallee? callees dp = some callee →
      ∃ idx fCallee,
        callee ∈ entry :: callees ∧
        lookupFnName (fnNameMap entry callees) dp = some (fnName idx) ∧
        lookupFnTarget (fnNameMap entry callees) dp =
          some (fnName idx, fCallee.calling_convention) ∧
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
      obtain ⟨_, hconvC, _, _, _, _⟩ := translateFnInProg_spec (fnNameMap entry callees) callee fCallee hfC
      have hlkTgt : lookupFnTarget (fnNameMap entry callees) callee.defPath =
          some (fnName (j + 1), fCallee.calling_convention) := by
        have hraw := lookupFnTarget_zipIdx_aux (entry :: callees) 0 hnd (j + 1) callee hbj
        simpa [fnNameMap, hconvC] using hraw
      have hlk : lookupFnName (fnNameMap entry callees) callee.defPath = some (fnName (j + 1)) :=
        lookupFnName_of_lookupFnTarget hlkTgt
      refine ⟨j + 1, fCallee, .tail _ (List.mem_of_getElem? hj), hlk, hlkTgt, hfC, ?_⟩
      apply mapGet_append_of_some
      simpa using hgetC

/-- Exact characterization of `translateCallConv`: succeeds iff the MIR calling
convention is `.c` (`CallingConvention.C`) or `.rust` (`CallingConvention.Rust`). -/
theorem translateCallConv_eq_some_iff {cc : Layout.CallConv} {conv : Gen.CallingConvention} :
    translateCallConv cc = some conv ↔
      (cc = .c ∧ conv = .C) ∨ (cc = .rust ∧ conv = .Rust) := by
  cases cc <;> cases conv <;> simp [translateCallConv]

/-- Structural characterization of `translateUnwindAction` on any fragment
call `UnwindAction` (`callUnwindOk unwind = true`): allocates fresh cleanup
block `bbName nextCleanup`, increments `nextCleanup`, and emits a single
`BbKind.Cleanup` block with empty statement list and the corresponding unwind
terminator (`.ResumeUnwind`, `.Unreachable`, or `buildAbort`). -/
theorem translateUnwindAction_spec (nextCleanup : Nat) (unwind : MirAst.UnwindAction)
    (hok : callUnwindOk unwind = true) :
    ∃ term : Gen.Terminator,
      translateUnwindAction nextCleanup unwind =
        (bbName nextCleanup, nextCleanup + 1,
          [(bbName nextCleanup, ⟨[], term, .Cleanup⟩)]) ∧
      ((unwind = .continue_ ∧ term = .ResumeUnwind) ∨
       (unwind = .unreachable ∧ term = .Unreachable) ∨
       (unwind = .terminate ∧ term = buildAbort)) := by
  cases unwind with
  | continue_ => exact ⟨.ResumeUnwind, rfl, .inl ⟨rfl, rfl⟩⟩
  | unreachable => exact ⟨.Unreachable, rfl, .inr (.inl ⟨rfl, rfl⟩)⟩
  | terminate => exact ⟨buildAbort, rfl, .inr (.inr ⟨rfl, rfl⟩)⟩
  | cleanup _ => simp [callUnwindOk] at hok

/-- Structural and CFG specification of `mkStartFn entryIdx`: C calling
convention, 0 arguments, return local `_0 : unitTy`, start block `bb0` calling
`fnName entryIdx` with next block `bb1` (`IntrinsicOp.Exit`) and unwind block
`bb2` (`buildAbort`, `BbKind.Catch`). -/
theorem mkStartFn_spec (entryIdx : Nat) :
    (mkStartFn entryIdx).calling_convention = .C ∧
    (mkStartFn entryIdx).args = [] ∧
    (mkStartFn entryIdx).ret = localName 0 ∧
    (mkStartFn entryIdx).start = bbName 0 ∧
    (mkStartFn entryIdx).implicit_writes = true ∧
    mapGet (mkStartFn entryIdx).locals (localName 0) = some unitTy ∧
    mapGet (mkStartFn entryIdx).blocks (bbName 0) =
      some ⟨[], .Call (fnPtrExpr (fnName entryIdx)) .Rust [] buildUnitPlace
        (some (bbName 1)) (some (bbName 2)), .Regular⟩ ∧
    mapGet (mkStartFn entryIdx).blocks (bbName 1) =
      some ⟨[], .Intrinsic .Exit [] buildUnitPlace none, .Regular⟩ ∧
    mapGet (mkStartFn entryIdx).blocks (bbName 2) =
      some ⟨[], buildAbort, .Catch⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- On any non-`.call` terminator, `translateTerminatorInProg` delegates
directly to `translateTerminator`, leaves `nextCleanup` unchanged, and
synthesizes no extra cleanup blocks. -/
theorem translateTerminatorInProg_eq_of_not_call (fnMap : FnMap)
    (decls : List LocalDecl) (nextCleanup : Nat) (t : MirAst.Terminator)
    (hnc : ∀ func args dst tgt unw, t.kind ≠ .call func args dst tgt unw) :
    translateTerminatorInProg fnMap decls nextCleanup t =
      (translateTerminator decls t).map (fun term => (term, nextCleanup, [])) := by
  unfold translateTerminatorInProg
  cases hk : t.kind <;> try (cases translateTerminator decls t <;> rfl)
  case call func args dst tgt unw =>
    exact absurd hk (hnc func args dst tgt unw)

theorem splitStmts_statements (cur : Gen.BbName) (acc : List Gen.Statement) (nc : Nat) :
    ∀ ss : List Gen.Statement,
      splitStmts cur acc nc (ss.map .statement) = (cur, acc ++ ss, [], nc)
  | [] => by simp [splitStmts]
  | s :: ss => by
    simp only [List.map_cons, splitStmts]
    rw [splitStmts_statements cur (acc ++ [s]) nc ss]
    simp

theorem mapM_translateStmtResult_of_noAssume {decls : List LocalDecl} :
    ∀ ss : List MirAst.Statement, (∀ s ∈ ss, isAssume s = false) →
      ss.mapM (translateStmtResult decls) =
        (ss.mapM (translateStatement decls)).map (List.map .statement)
  | [], _ => rfl
  | s :: ss, hna => by
    have hs : translateStmtResult decls s = (translateStatement decls s).map .statement := by
      unfold translateStmtResult
      split
      · next op heq =>
        have := hna s List.mem_cons_self
        simp [isAssume, heq] at this
      · rfl
    simp only [List.mapM_cons, Option.bind_eq_bind, hs,
      mapM_translateStmtResult_of_noAssume ss (fun x hx => hna x (List.mem_cons_of_mem _ hx))]
    cases translateStatement decls s <;> cases ss.mapM (translateStatement decls) <;> simp

/-- When `bbs` contains no `.call` terminators and no `Assume` statements,
`translateBlocksInProg` agrees with `translateBlocks` and synthesizes no extra
blocks (`extra = []`). -/
theorem translateBlocksInProg_eq_of_no_calls (fnMap : FnMap)
    (decls : List LocalDecl) (k nextCleanup : Nat) (bbs : List BasicBlockData)
    (hnc : ∀ bb ∈ bbs, ∀ func args dst tgt unw,
      bb.terminator.kind ≠ .call func args dst tgt unw)
    (hna : ∀ bb ∈ bbs, ∀ s ∈ bb.statements, isAssume s = false) :
    translateBlocksInProg fnMap decls k nextCleanup bbs =
      (translateBlocks decls k bbs).map (fun B => (B, [])) := by
  induction bbs generalizing k nextCleanup with
  | nil => rfl
  | cons bb bbs ih =>
    have hbb := hnc bb List.mem_cons_self
    have hrest := ih (k + 1) nextCleanup (fun b hb => hnc b (List.mem_cons_of_mem _ hb))
      (fun b hb => hna b (List.mem_cons_of_mem _ hb))
    unfold translateBlocksInProg translateBlocks translateBlock
    rw [mapM_translateStmtResult_of_noAssume bb.statements (hna bb List.mem_cons_self)]
    cases bb.statements.mapM (translateStatement decls) with
    | none => rfl
    | some stmts =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, splitStmts_statements,
        List.nil_append]
      rw [translateTerminatorInProg_eq_of_not_call fnMap decls nextCleanup bb.terminator hbb]
      cases translateTerminator decls bb.terminator with
      | none => rfl
      | some term =>
        simp only [Option.map_some, Option.bind_some]
        rw [hrest]
        cases translateBlocks decls (k + 1) bbs <;> rfl

/-- When `body` contains no `.call` terminators and no `Assume` statements,
`translateFnInProg fnMap body` produces the exact same `Option Gen.Function` as
single-function `translateFn body` regardless of `fnMap`. -/
theorem translateFnInProg_eq_translateFn_of_no_calls (fnMap : FnMap)
    (body : CapturedMir)
    (hnc : ∀ bb ∈ body.basicBlocks, ∀ func args dst tgt unw,
      bb.terminator.kind ≠ .call func args dst tgt unw)
    (hna : ∀ bb ∈ body.basicBlocks, ∀ s ∈ bb.statements, isAssume s = false) :
    translateFnInProg fnMap body = translateFn body := by
  simp only [translateFnInProg, translateFn,
    translateBlocksInProg_eq_of_no_calls fnMap body.localDecls 0
      (body.basicBlocks.length + 1) body.basicBlocks hnc hna,
    Option.bind_eq_bind]
  cases translateCallConv body.fnAbi.conv with
  | none => rfl
  | some conv =>
    cases translateLocals 0 body.localDecls with
    | none => rfl
    | some locals =>
      cases translateBlocks body.localDecls 0 body.basicBlocks with
      | none => rfl
      | some B => simp

end MiniRustSpec.Correspondence
