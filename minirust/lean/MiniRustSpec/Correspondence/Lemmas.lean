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

theorem arrayTypeOf_none_of_intTypeOf {t : MirAst.Ty} {it : Gen.IntType}
    (h : intTypeOf t = some it) : arrayTypeOf t = none := by
  unfold intTypeOf intTyBytes at h
  unfold arrayTypeOf
  split at h <;> simp_all

theorem tupleTypeOf_none_of_intTypeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty}
    {it : Gen.IntType} (h : intTypeOf t = some it) : tupleTypeOf layouts t = none := by
  unfold intTypeOf intTyBytes at h
  unfold tupleTypeOf
  split
  · rfl
  · split at h <;> simp_all

theorem intTypeOf_none_of_arrayTypeOf {t : MirAst.Ty} {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf t = some (elemIt, count)) : intTypeOf t = none := by
  unfold arrayTypeOf at h
  unfold intTypeOf intTyBytes
  split at h <;> simp_all

theorem isBoolTy_false_of_arrayTypeOf {t : MirAst.Ty} {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf t = some (elemIt, count)) : isBoolTy t = false := by
  unfold arrayTypeOf at h
  unfold isBoolTy
  split at h <;> simp_all

theorem isOrderingTy_false_of_arrayTypeOf {t : MirAst.Ty} {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf t = some (elemIt, count)) : isOrderingTy t = false := by
  unfold arrayTypeOf at h
  unfold isOrderingTy
  split at h <;> simp_all

theorem intBoolTupleOf_none_of_arrayTypeOf {t : MirAst.Ty} {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf t = some (elemIt, count)) : intBoolTupleOf t = none := by
  unfold arrayTypeOf at h
  unfold intBoolTupleOf
  split at h <;> simp_all

theorem scalarTypeOf_none_of_arrayTypeOf {t : MirAst.Ty} {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf t = some (elemIt, count)) : scalarTypeOf t = none := by
  simp [scalarTypeOf, isBoolTy_false_of_arrayTypeOf h, isOrderingTy_false_of_arrayTypeOf h,
    intBoolTupleOf_none_of_arrayTypeOf h, intTypeOf_none_of_arrayTypeOf h]

theorem tupleTypeOf_none_of_arrayTypeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty}
    {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf t = some (elemIt, count)) : tupleTypeOf layouts t = none := by
  unfold arrayTypeOf at h
  unfold tupleTypeOf
  split
  · rfl
  · split at h <;> simp_all

theorem not_scalar_of_tupleTypeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty}
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tupleTypeOf layouts t = some (fields, size, align)) :
    isBoolTy t = false ∧ isOrderingTy t = false ∧
      intBoolTupleOf t = none ∧ intTypeOf t = none ∧ arrayTypeOf t = none := by
  unfold tupleTypeOf at h
  cases hguard : isOrderingTy t || (intBoolTupleOf t).isSome with
  | true => simp [hguard] at h
  | false =>
    simp only [hguard, Bool.false_eq_true, ↓reduceIte] at h
    simp only [Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hguard
    refine ⟨?_, hguard.1, hguard.2, ?_, ?_⟩
    · unfold isBoolTy; split at h <;> simp_all
    · unfold intTypeOf intTyBytes; split at h <;> simp_all
    · unfold arrayTypeOf; split at h <;> simp_all

theorem intTypeOf_none_of_tupleTypeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty}
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tupleTypeOf layouts t = some (fields, size, align)) : intTypeOf t = none :=
  (not_scalar_of_tupleTypeOf h).2.2.2.1

theorem arrayTypeOf_none_of_tupleTypeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty}
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tupleTypeOf layouts t = some (fields, size, align)) : arrayTypeOf t = none :=
  (not_scalar_of_tupleTypeOf h).2.2.2.2

theorem scalarTypeOf_none_of_tupleTypeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty}
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tupleTypeOf layouts t = some (fields, size, align)) : scalarTypeOf t = none := by
  obtain ⟨hb, ho, htup, hit, _⟩ := not_scalar_of_tupleTypeOf h
  simp [scalarTypeOf, hb, ho, htup, hit]

theorem arrayTypeOf_none_of_scalarTypeOf {t : MirAst.Ty} {T : Gen.Type}
    (h : scalarTypeOf t = some T) : arrayTypeOf t = none := by
  cases ha : arrayTypeOf t with
  | none => rfl
  | some p =>
    obtain ⟨elemIt, count⟩ := p
    rw [scalarTypeOf_none_of_arrayTypeOf ha] at h
    cases h

theorem tupleTypeOf_none_of_scalarTypeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty} {T : Gen.Type}
    (h : scalarTypeOf t = some T) : tupleTypeOf layouts t = none := by
  cases ht : tupleTypeOf layouts t with
  | none => rfl
  | some p =>
    obtain ⟨fields, size, align⟩ := p
    rw [scalarTypeOf_none_of_tupleTypeOf ht] at h
    cases h

theorem not_other_of_ptrPointeeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty}
    {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (h : ptrPointeeOf t = some (mutbl, it)) :
    isBoolTy t = false ∧ isOrderingTy t = false ∧
      intBoolTupleOf t = none ∧ intTypeOf t = none ∧
      arrayTypeOf t = none ∧ tupleTypeOf layouts t = none ∧
      scalarTypeOf t = none := by
  unfold ptrPointeeOf at h
  cases hk : t.kind with
  | rawPtr m pointee | ref m pointee =>
    have hb : isBoolTy t = false := by simp [isBoolTy, hk]
    have ho : isOrderingTy t = false := by simp [isOrderingTy, hk]
    have htup : intBoolTupleOf t = none := by simp [intBoolTupleOf, hk]
    have hit : intTypeOf t = none := by simp [intTypeOf, intTyBytes, hk]
    have harr : arrayTypeOf t = none := by simp [arrayTypeOf, hk]
    have htspec : tupleTypeOf layouts t = none := by
      unfold tupleTypeOf
      split
      · rfl
      · simp [hk]
    have hsc : scalarTypeOf t = none := by
      simp [scalarTypeOf, hb, ho, htup, hit]
    exact ⟨hb, ho, htup, hit, harr, htspec, hsc⟩
  | _ => simp [hk] at h

theorem not_other_of_isPtrTy {layouts : Layout.LayoutTable} {t : MirAst.Ty}
    (h : isPtrTy t = true) :
    isBoolTy t = false ∧ isOrderingTy t = false ∧
      intBoolTupleOf t = none ∧ intTypeOf t = none ∧
      arrayTypeOf t = none ∧ tupleTypeOf layouts t = none ∧
      scalarTypeOf t = none := by
  unfold isPtrTy at h
  obtain ⟨⟨mutbl, it⟩, hp⟩ := Option.isSome_iff_exists.mp h
  exact not_other_of_ptrPointeeOf hp

theorem layoutPointerBytes_of_localDeclOk_isPtrTy {layouts : Layout.LayoutTable}
    {d : MirAst.LocalDecl} (hdok : localDeclOk layouts d = true) (hp : isPtrTy d.ty = true) :
    MirSemantics.layoutPointerBytes layouts = 8 := by
  obtain ⟨_, _, _, _, harr, htup, hsc⟩ := not_other_of_isPtrTy (layouts := layouts) hp
  simpa [localDeclOk, hsc, hp, harr, htup] using hdok

theorem isPtrTy_false_of_scalarTypeOf {t : MirAst.Ty} {T : Gen.Type}
    (h : scalarTypeOf t = some T) : isPtrTy t = false := by
  cases hp : isPtrTy t with
  | false => rfl
  | true =>
    have hnone := (not_other_of_isPtrTy (layouts := ⟨64, true, []⟩) hp).2.2.2.2.2.2
    rw [hnone] at h
    cases h

theorem isPtrTy_false_of_arrayTypeOf {t : MirAst.Ty} {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf t = some (elemIt, count)) : isPtrTy t = false := by
  cases hp : isPtrTy t with
  | false => rfl
  | true =>
    have hnone := (not_other_of_isPtrTy (layouts := ⟨64, true, []⟩) hp).2.2.2.2.1
    rw [hnone] at h
    cases h

theorem isPtrTy_false_of_tupleTypeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty}
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tupleTypeOf layouts t = some (fields, size, align)) : isPtrTy t = false := by
  cases hp : isPtrTy t with
  | false => rfl
  | true =>
    have hnone := (not_other_of_isPtrTy (layouts := layouts) hp).2.2.2.2.2.1
    rw [hnone] at h
    cases h

theorem ptrPointeeOf_of_rawPtrPointeeOf {t : MirAst.Ty} {mutbl : MirAst.Mutability}
    {it : Gen.IntType} (h : rawPtrPointeeOf t = some (mutbl, it)) :
    ptrPointeeOf t = some (mutbl, it) ∧ isRefTy t = false := by
  unfold rawPtrPointeeOf at h
  cases hk : t.kind <;> simp_all [ptrPointeeOf, isRefTy, refPointeeOf]

theorem ptrPointeeOf_of_refPointeeOf {t : MirAst.Ty} {mutbl : MirAst.Mutability}
    {it : Gen.IntType} (h : refPointeeOf t = some (mutbl, it)) :
    ptrPointeeOf t = some (mutbl, it) ∧ isRefTy t = true := by
  refine ⟨?_, by simp [isRefTy, h]⟩
  unfold refPointeeOf at h
  cases hk : t.kind <;> simp_all [ptrPointeeOf]

theorem declPtrTy_of_rawPtrPointeeOf {t : MirAst.Ty} {mutbl : MirAst.Mutability}
    {it : Gen.IntType} (h : rawPtrPointeeOf t = some (mutbl, it)) :
    declPtrTy t = thinRawPtrTy := by
  unfold rawPtrPointeeOf at h
  cases hk : t.kind <;> simp_all [declPtrTy]

theorem declPtrTy_of_refPointeeOf {t : MirAst.Ty} {mutbl : MirAst.Mutability}
    {it : Gen.IntType} (h : refPointeeOf t = some (mutbl, it)) :
    declPtrTy t = refTy mutbl it := by
  unfold refPointeeOf at h
  cases hk : t.kind with
  | ref m pointee =>
    simp only [hk, Option.map_eq_some_iff] at h
    obtain ⟨⟨s, n⟩, hb, heq⟩ := h
    injection heq with hm hit
    subst hm; subst hit
    simp [declPtrTy, hk, hb]
  | _ => simp [hk] at h

theorem declPtrTy_of_isRefTy_false {t : MirAst.Ty} {mutbl : MirAst.Mutability}
    {it : Gen.IntType} (h : ptrPointeeOf t = some (mutbl, it)) (href : isRefTy t = false) :
    rawPtrPointeeOf t = some (mutbl, it) ∧ declPtrTy t = thinRawPtrTy := by
  unfold ptrPointeeOf at h
  unfold isRefTy refPointeeOf at href
  cases hk : t.kind with
  | rawPtr m pointee =>
    simp [hk] at h
    exact ⟨by simp [rawPtrPointeeOf, hk, h], by simp [declPtrTy, hk]⟩
  | ref m pointee =>
    rw [hk] at h href
    cases hb : intTyBytes pointee <;> simp [hb] at h href
  | _ => simp [hk] at h

theorem declPtrTy_of_isRefTy_true {t : MirAst.Ty} {mutbl : MirAst.Mutability}
    {it : Gen.IntType} (h : ptrPointeeOf t = some (mutbl, it)) (href : isRefTy t = true) :
    refPointeeOf t = some (mutbl, it) ∧ declPtrTy t = refTy mutbl it := by
  unfold ptrPointeeOf at h
  unfold isRefTy refPointeeOf at href
  cases hk : t.kind with
  | rawPtr m pointee => simp [hk] at href
  | ref m pointee =>
    simp [hk] at h
    have hr : refPointeeOf t = some (mutbl, it) := by simp [refPointeeOf, hk, h]
    exact ⟨hr, declPtrTy_of_refPointeeOf hr⟩
  | _ => simp [hk] at h

theorem declPtrTy_cases (t : MirAst.Ty) :
    declPtrTy t = thinRawPtrTy ∨
      ∃ mutbl it, refPointeeOf t = some (mutbl, it) ∧ declPtrTy t = refTy mutbl it := by
  unfold declPtrTy
  cases hk : t.kind with
  | ref mutbl pointee =>
    simp only []
    cases hb : intTyBytes pointee with
    | none => exact .inl rfl
    | some p =>
      obtain ⟨s, n⟩ := p
      exact .inr ⟨mutbl, ⟨s, ⟨n⟩⟩, by simp [refPointeeOf, hk, hb], rfl⟩
  | _ => exact .inl rfl

@[simp] theorem tyBytes_declPtrTy (t : MirAst.Ty) : tyBytes (declPtrTy t) = 8 := by
  rcases declPtrTy_cases t with h | ⟨mutbl, it, _, h⟩
  · rw [h]; rfl
  · rw [h]; rfl

theorem translateTy_of_ptrPointeeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty}
    {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (h : ptrPointeeOf t = some (mutbl, it)) :
    translateTy layouts t = some (declPtrTy t) := by
  obtain ⟨_, _, _, _, harr, htspec, hsc⟩ := not_other_of_ptrPointeeOf (layouts := layouts) h
  unfold ptrPointeeOf at h
  cases hk : t.kind with
  | rawPtr m pointee =>
    simp only [hk, Option.map_eq_some_iff] at h
    obtain ⟨⟨s, n⟩, hb, _⟩ := h
    have hraw : rawPtrTypeOf t = some thinRawPtrTy := by
      unfold intTyBytes at hb
      unfold rawPtrTypeOf rawPtrMetaOf rawPtrMetaKind thinRawPtrTy
      rw [hk]
      cases pointee <;> simp_all
    simp [translateTy, hsc, harr, htspec, hraw, declPtrTy, hk]
  | ref m pointee =>
    simp only [hk, Option.map_eq_some_iff] at h
    obtain ⟨⟨s, n⟩, hb, _⟩ := h
    have hraw : rawPtrTypeOf t = none := by simp [rawPtrTypeOf, rawPtrMetaOf, hk]
    have href : refTypeOf t = some (refTy m ⟨s, ⟨n⟩⟩) := by simp [refTypeOf, hk, hb]
    simp [translateTy, hsc, harr, htspec, hraw, href, declPtrTy, hk, hb]
  | _ => simp [hk] at h

theorem translateTy_of_scalarTypeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty} {T : Gen.Type}
    (h : scalarTypeOf t = some T) : translateTy layouts t = some T := by
  simp [translateTy, h]

theorem translateTy_of_intTypeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty} {it : Gen.IntType}
    (h : intTypeOf t = some it) : translateTy layouts t = some (.Int it) :=
  translateTy_of_scalarTypeOf (scalarTypeOf_int h)

theorem translateTy_of_arrayTypeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty}
    {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf t = some (elemIt, count)) :
    translateTy layouts t = some (.Array (.Int elemIt) (Int.ofNat count)) := by
  simp [translateTy, scalarTypeOf_none_of_arrayTypeOf h, h]

theorem translateTy_of_tupleTypeOf {layouts : Layout.LayoutTable} {t : MirAst.Ty}
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tupleTypeOf layouts t = some (fields, size, align)) :
    translateTy layouts t = some ((TupleSpec.tuple fields size align).toMiniRustTy) := by
  simp [translateTy, scalarTypeOf_none_of_tupleTypeOf h, arrayTypeOf_none_of_tupleTypeOf h, h]

theorem tyOf_of_translateTy {d : LocalDecl} {layouts : Layout.LayoutTable} {T : Gen.Type}
    (h : translateTy layouts d.ty = some T) : tyOf d layouts = T := by
  simp [tyOf, h]

/-- `tyOf` is the translated type of a scalar-family fragment local. -/
theorem tyOf_of_scalarTypeOf {d : LocalDecl} {layouts : Layout.LayoutTable} {T : Gen.Type}
    (h : scalarTypeOf d.ty = some T) : tyOf d layouts = T :=
  tyOf_of_translateTy (translateTy_of_scalarTypeOf h)

theorem tyOf_int {d : LocalDecl} {layouts : Layout.LayoutTable} {it : Gen.IntType}
    (h : intTypeOf d.ty = some it) :
    tyOf d layouts = .Int it ∧ itOf d layouts = it := by
  simp [tyOf_of_scalarTypeOf (scalarTypeOf_int h), itOf, intTypeOf_isBoolTy h,
    intTypeOf_isOrderingTy h, h]

theorem tyOf_bool {d : LocalDecl} {layouts : Layout.LayoutTable} (h : isBoolTy d.ty = true) :
    tyOf d layouts = .Bool ∧ itOf d layouts = u8Ty := by
  simp [tyOf_of_scalarTypeOf (scalarTypeOf_bool h), itOf, h, u8Ty]

theorem tyOf_ordering {d : LocalDecl} {layouts : Layout.LayoutTable} (h : isOrderingTy d.ty = true) :
    tyOf d layouts = orderingTy ∧ itOf d layouts = u8Ty := by
  simp [tyOf_of_scalarTypeOf (scalarTypeOf_ordering h), itOf, h, u8Ty]

theorem tyOf_tuple {d : LocalDecl} {layouts : Layout.LayoutTable} {it : Gen.IntType}
    (h : intBoolTupleOf d.ty = some it) :
    tyOf d layouts = intBoolTupleTy it ∧ itOf d layouts = it := by
  simp [tyOf_of_scalarTypeOf (scalarTypeOf_tuple h), itOf, intBoolTupleOf_isBoolTy h,
    intBoolTupleOf_isOrderingTy h, intBoolTupleOf_intTypeOf h, h]

theorem tyOf_array {d : LocalDecl} {layouts : Layout.LayoutTable}
    {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf d.ty = some (elemIt, count)) :
    tyOf d layouts = .Array (.Int elemIt) (Int.ofNat count) ∧ itOf d layouts = elemIt := by
  refine ⟨tyOf_of_translateTy (translateTy_of_arrayTypeOf h), ?_⟩
  simp [itOf, isBoolTy_false_of_arrayTypeOf h, isOrderingTy_false_of_arrayTypeOf h,
    intTypeOf_none_of_arrayTypeOf h, intBoolTupleOf_none_of_arrayTypeOf h, h]

theorem tyOf_tupleSpec {d : LocalDecl} {layouts : Layout.LayoutTable}
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tupleTypeOf layouts d.ty = some (fields, size, align)) :
    tyOf d layouts = (TupleSpec.tuple fields size align).toMiniRustTy ∧
      itOf d layouts = ⟨.Unsigned, ⟨align⟩⟩ := by
  obtain ⟨hb, ho, htup, hit, harr⟩ := not_scalar_of_tupleTypeOf h
  refine ⟨tyOf_of_translateTy (translateTy_of_tupleTypeOf h), ?_⟩
  simp [itOf, hb, ho, hit, htup, harr, h]

theorem tyOf_ptr {d : LocalDecl} {layouts : Layout.LayoutTable}
    {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (h : ptrPointeeOf d.ty = some (mutbl, it)) :
    tyOf d layouts = declPtrTy d.ty ∧ itOf d layouts = usizeIt := by
  obtain ⟨hb, ho, htup, hit, harr, htspec, _⟩ := not_other_of_ptrPointeeOf (layouts := layouts) h
  have hp : isPtrTy d.ty = true := by simp [isPtrTy, h]
  refine ⟨tyOf_of_translateTy (translateTy_of_ptrPointeeOf h), ?_⟩
  simp [itOf, hb, ho, hit, htup, harr, htspec, hp]

theorem tyOf_isPtrTy {d : LocalDecl} {layouts : Layout.LayoutTable}
    (h : isPtrTy d.ty = true) :
    tyOf d layouts = declPtrTy d.ty ∧ itOf d layouts = usizeIt := by
  unfold isPtrTy at h
  obtain ⟨⟨mutbl, it⟩, hp⟩ := Option.isSome_iff_exists.mp h
  exact tyOf_ptr hp

theorem itOf_eq_of_intTypeOf {layouts : Layout.LayoutTable} {d : LocalDecl} {it : Gen.IntType}
    (h : intTypeOf d.ty = some it) : itOf d layouts = it :=
  (tyOf_int h).2

theorem itOf_eq_of_arrayTypeOf {layouts : Layout.LayoutTable} {d : LocalDecl}
    {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf d.ty = some (elemIt, count)) : itOf d layouts = elemIt :=
  (tyOf_array h).2

theorem itOf_eq_of_tupleTypeOf {layouts : Layout.LayoutTable} {d : LocalDecl}
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tupleTypeOf layouts d.ty = some (fields, size, align)) :
    itOf d layouts = ⟨.Unsigned, ⟨align⟩⟩ :=
  (tyOf_tupleSpec h).2

@[simp] theorem tupleIntOfTy_intBoolTupleTy (it : Gen.IntType) :
    tupleIntOfTy (intBoolTupleTy it) = some it := by
  simp [intBoolTupleTy, tupleIntOfTy]

@[simp] theorem tupleIntOfTy_int (it : Gen.IntType) : tupleIntOfTy (.Int it) = none := rfl
@[simp] theorem tupleIntOfTy_bool : tupleIntOfTy .Bool = none := rfl
@[simp] theorem tupleIntOfTy_orderingTy : tupleIntOfTy orderingTy = none := rfl
@[simp] theorem tupleIntOfTy_array (T : Gen.Type) (n : Int) : tupleIntOfTy (.Array T n) = none := rfl
@[simp] theorem tupleIntOfTy_ptr (pt : Gen.PtrType) : tupleIntOfTy (.Ptr pt) = none := rfl

theorem declSlotData_of_none {d : LocalDecl} {layouts : Layout.LayoutTable}
    (h : intBoolTupleOf d.ty = none) (ha : arrayTypeOf d.ty = none)
    (ht : tupleTypeOf layouts d.ty = none) (slot : LocalSlot) :
    declSlotData d slot layouts = slotData (itOf d layouts) slot := by
  unfold declSlotData
  rw [h]
  dsimp only
  split <;> simp [ha, ht]

theorem declSlotData_of_some {d : LocalDecl} {layouts : Layout.LayoutTable} {it : Gen.IntType}
    (h : intBoolTupleOf d.ty = some it) (slot : LocalSlot) :
    declSlotData d slot layouts = tupleSlotData it slot := by
  simp [declSlotData, h]

theorem declSlotData_of_array {d : LocalDecl} {layouts : Layout.LayoutTable}
    {elemIt : Gen.IntType} {count : Nat} (h : arrayTypeOf d.ty = some (elemIt, count))
    (slot : LocalSlot) :
    declSlotData d slot layouts =
      match slot with
      | .init (.aggregate 0 elems) => (elems.map (valBytes elemIt)).flatten
      | _ => List.replicate (count * elemIt.size.bytes) .Uninit := by
  simp only [declSlotData, intBoolTupleOf_none_of_arrayTypeOf h, isBoolTy_false_of_arrayTypeOf h,
    isOrderingTy_false_of_arrayTypeOf h, intTypeOf_none_of_arrayTypeOf h, h,
    Option.isSome_none, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem declSlotData_of_tupleSpec {d : LocalDecl} {layouts : Layout.LayoutTable}
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tupleTypeOf layouts d.ty = some (fields, size, align)) (slot : LocalSlot) :
    declSlotData d slot layouts =
      match slot with
      | .init v => (TupleSpec.tuple fields size align).encodeVal v
      | _ => List.replicate size .Uninit := by
  obtain ⟨hb, ho, htup, hit, harr⟩ := not_scalar_of_tupleTypeOf h
  simp only [declSlotData, htup, hb, ho, hit, harr, h,
    Option.isSome_none, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem DeclSlotOk_of_scalarTypeOf {d : LocalDecl} {layouts : Layout.LayoutTable} {T : Gen.Type}
    (h : scalarTypeOf d.ty = some T) (slot : LocalSlot) :
    DeclSlotOk d slot layouts ↔ SlotOk (tyOf d layouts) slot := by
  simp [DeclSlotOk, h]

theorem DeclSlotOk_of_arrayTypeOf {d : LocalDecl} {layouts : Layout.LayoutTable}
    {elemIt : Gen.IntType} {count : Nat} (h : arrayTypeOf d.ty = some (elemIt, count))
    (slot : LocalSlot) :
    DeclSlotOk d slot layouts ↔
      match slot with
      | .dead => True
      | .uninit => True
      | .init v =>
        match v with
        | .aggregate 0 elems => elems.length = count ∧ ∀ v ∈ elems, ElemOk elemIt v
        | _ => False := by
  simp only [DeclSlotOk, scalarTypeOf_none_of_arrayTypeOf h, h,
    Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  exact Iff.rfl

theorem DeclSlotOk_of_tupleTypeOf {d : LocalDecl} {layouts : Layout.LayoutTable}
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tupleTypeOf layouts d.ty = some (fields, size, align)) (slot : LocalSlot) :
    DeclSlotOk d slot layouts ↔
      match slot with
      | .dead => True
      | .uninit => True
      | .init v =>
        (TupleSpec.tuple fields size align).wf = true ∧
        (TupleSpec.tuple fields size align).valOk v = true := by
  simp only [DeclSlotOk, scalarTypeOf_none_of_tupleTypeOf h, arrayTypeOf_none_of_tupleTypeOf h, h,
    Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  exact Iff.rfl

theorem DeclSlotOk_of_isPtrTy {d : LocalDecl} {layouts : Layout.LayoutTable}
    (h : isPtrTy d.ty = true) (slot : LocalSlot) :
    DeclSlotOk d slot layouts ↔
      match slot with
      | .dead => True
      | .uninit => True
      | .init v => ∃ ptrVal, v = .ptr ptrVal 8 := by
  obtain ⟨_, _, _, _, harr, htspec, hsc⟩ := not_other_of_isPtrTy (layouts := layouts) h
  simp only [DeclSlotOk, hsc, harr, htspec, h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  cases slot <;> exact Iff.rfl

theorem DeclSlotOk_of_ptrPointeeOf {d : LocalDecl} {layouts : Layout.LayoutTable}
    {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (h : ptrPointeeOf d.ty = some (mutbl, it)) (slot : LocalSlot) :
    DeclSlotOk d slot layouts ↔
      match slot with
      | .dead => True
      | .uninit => True
      | .init v => ∃ ptrVal, v = .ptr ptrVal 8 :=
  DeclSlotOk_of_isPtrTy (by simp [isPtrTy, h]) slot

/-- `2-tuple` constants are outside the fragment: `translateOperand` reads
only integer and `bool` scalars. -/
theorem translateOperand_tuple_const {decls : List LocalDecl} {c : ConstOperand} {it : Gen.IntType}
    (ht : intBoolTupleOf c.ty = some it) : translateOperand decls (.constant c) = none := by
  simp only [translateOperand, intBoolTupleOf_isBoolTy ht, Bool.false_eq_true, ↓reduceIte,
    intBoolTupleOf_intTypeOf ht]
  split <;> simp_all

/-- `Ordering` constants are outside the fragment: `translateOperand` reads
only integer and `bool` scalars. -/
theorem translateOperand_ordering_const {decls : List LocalDecl} {c : ConstOperand}
    (ho : isOrderingTy c.ty = true) : translateOperand decls (.constant c) = none := by
  simp only [translateOperand, isOrderingTy_isBoolTy ho, Bool.false_eq_true, ↓reduceIte,
    isOrderingTy_intTypeOf ho]
  split <;> simp_all


/-! ## `translateFn` -/

theorem translateLocals_get (layouts : Layout.LayoutTable) (k : Nat) (ds : List LocalDecl)
    (L : List (Gen.LocalName × Gen.Type))
    (h : translateLocals layouts k ds = some L) (j : Nat) (d : LocalDecl) (hd : ds[j]? = some d) :
    ∃ T, translateTy layouts d.ty = some T ∧ mapGet ⟨L⟩ (localName (k + j)) = some T := by
  induction ds generalizing k L j with
  | nil => simp at hd
  | cons d' ds ih =>
    simp only [translateLocals, Option.bind_eq_bind] at h
    cases hit : translateTy layouts d'.ty with
    | none => simp [hit] at h
    | some it' =>
      cases hrest : translateLocals layouts (k + 1) ds with
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

theorem translateBlocks_get (layouts : Layout.LayoutTable) (decls : List LocalDecl) (k : Nat)
    (bbs : List BasicBlockData) (B : List (Gen.BbName × Gen.BasicBlock))
    (h : translateBlocks layouts decls k bbs = some B) (j : Nat)
    (bb : BasicBlockData) (hb : bbs[j]? = some bb) :
    ∃ tb, translateBlock layouts decls bb = some tb ∧ mapGet ⟨B⟩ (bbName (k + j)) = some tb := by
  induction bbs generalizing k B j with
  | nil => simp at hb
  | cons bb' bbs ih =>
    simp only [translateBlocks, Option.bind_eq_bind] at h
    cases htb : translateBlock layouts decls bb' with
    | none => simp [htb] at h
    | some tb' =>
      cases hrest : translateBlocks layouts decls (k + 1) bbs with
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
      translateTy body.layouts d.ty = some (tyOf d body.layouts) ∧
        mapGet f.locals (localName i) = some (tyOf d body.layouts)) ∧
    (∀ (i : Nat) bb, body.basicBlocks[i]? = some bb →
      ∃ tb, translateBlock body.layouts body.localDecls bb = some tb ∧
        mapGet f.blocks (bbName i) = some tb) := by
  simp only [translateFn, Option.bind_eq_bind] at h
  cases hC : translateCallConv body.fnAbi.conv with
  | none => simp [hC] at h
  | some conv =>
    cases hL : translateLocals body.layouts 0 body.localDecls with
    | none => simp [hC, hL] at h
    | some L =>
      cases hB : translateBlocks body.layouts body.localDecls 0 body.basicBlocks with
      | none => simp [hC, hL, hB] at h
      | some B =>
        simp [hC, hL, hB] at h
        subst h
        refine ⟨rfl, ?_, ?_⟩
        · intro i d hd
          obtain ⟨T, hT, hget⟩ := translateLocals_get body.layouts 0 body.localDecls L hL i d hd
          rw [tyOf_of_translateTy hT]; refine ⟨hT, ?_⟩
          simpa using hget
        · intro i bb hbb
          obtain ⟨tb, htb, hget⟩ :=
            translateBlocks_get body.layouts body.localDecls 0 body.basicBlocks B hB i bb hbb
          refine ⟨tb, htb, ?_⟩
          apply mapGet_append_of_some
          simpa using hget

theorem translateBlocks_append_get (layouts : Layout.LayoutTable) (decls : List LocalDecl)
    (k : Nat) (bbs : List BasicBlockData) (B : List (Gen.BbName × Gen.BasicBlock))
    (h : translateBlocks layouts decls k bbs = some B)
    (m : Nat) (hm : k + bbs.length ≤ m) (ib : Gen.BasicBlock) :
    mapGet ⟨B ++ [(bbName m, ib)]⟩ (bbName m) = some ib := by
  induction bbs generalizing k B with
  | nil => simp [translateBlocks] at h; subst h; simp [mapGet_cons]
  | cons bb bbs ih =>
    simp only [translateBlocks, Option.bind_eq_bind] at h
    cases htb : translateBlock layouts decls bb with
    | none => simp [htb] at h
    | some tb =>
      cases hrest : translateBlocks layouts decls (k + 1) bbs with
      | none => simp [htb, hrest] at h
      | some rest =>
        simp [htb, hrest] at h
        subst h
        rw [List.cons_append, mapGet_cons]
        split
        · next heq => rw [bbName_inj] at heq; simp at hm; omega
        · exact ih (k + 1) rest hrest (by simp at hm; omega)

/-- `translateFn` sets `f.start` to `bbName body.basicBlocks.length` and maps
that name to `initBlock body`. -/
theorem translateFn_start (body : CapturedMir) (f : Gen.Function) (h : translateFn body = some f) :
    f.start = bbName body.basicBlocks.length ∧
    mapGet f.blocks (bbName body.basicBlocks.length) = some (initBlock body) := by
  simp only [translateFn, Option.bind_eq_bind] at h
  cases hC : translateCallConv body.fnAbi.conv with
  | none => simp [hC] at h
  | some conv =>
    cases hL : translateLocals body.layouts 0 body.localDecls with
    | none => simp [hC, hL] at h
    | some L =>
      cases hB : translateBlocks body.layouts body.localDecls 0 body.basicBlocks with
      | none => simp [hC, hL, hB] at h
      | some B =>
        simp [hC, hL, hB] at h
        subst h
        exact ⟨rfl, translateBlocks_append_get body.layouts body.localDecls 0 body.basicBlocks B hB
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
  · obtain ⟨hty1, hit1⟩ := tyOf_bool (d := d1) (layouts := ⟨64, true, []⟩) hb1
    obtain ⟨hty2, hit2⟩ := tyOf_bool (d := d2) (layouts := ⟨64, true, []⟩) hb2
    refine ⟨by rw [hty1, hty2], by rw [hit1, hit2],
      ⟨.Bool, scalarTypeOf_bool hb1, scalarTypeOf_bool hb2⟩, fun slot => ?_⟩
    rw [declSlotData_of_none (isBoolTy_intBoolTupleOf hb1)
        (arrayTypeOf_none_of_scalarTypeOf (scalarTypeOf_bool hb1))
        (tupleTypeOf_none_of_scalarTypeOf (scalarTypeOf_bool hb1)),
      declSlotData_of_none (isBoolTy_intBoolTupleOf hb2)
        (arrayTypeOf_none_of_scalarTypeOf (scalarTypeOf_bool hb2))
        (tupleTypeOf_none_of_scalarTypeOf (scalarTypeOf_bool hb2)), hit1, hit2]
  · obtain ⟨hty1, hit1⟩ := tyOf_ordering (d := d1) (layouts := ⟨64, true, []⟩) ho1
    obtain ⟨hty2, hit2⟩ := tyOf_ordering (d := d2) (layouts := ⟨64, true, []⟩) ho2
    refine ⟨by rw [hty1, hty2], by rw [hit1, hit2],
      ⟨orderingTy, scalarTypeOf_ordering ho1, scalarTypeOf_ordering ho2⟩, fun slot => ?_⟩
    rw [declSlotData_of_none (isOrderingTy_intBoolTupleOf ho1)
        (arrayTypeOf_none_of_scalarTypeOf (scalarTypeOf_ordering ho1))
        (tupleTypeOf_none_of_scalarTypeOf (scalarTypeOf_ordering ho1)),
      declSlotData_of_none (isOrderingTy_intBoolTupleOf ho2)
        (arrayTypeOf_none_of_scalarTypeOf (scalarTypeOf_ordering ho2))
        (tupleTypeOf_none_of_scalarTypeOf (scalarTypeOf_ordering ho2)), hit1, hit2]
  · cases ht1 : intBoolTupleOf d1.ty with
    | none => simp [ht1] at htup
    | some it1 =>
      cases ht2 : intBoolTupleOf d2.ty with
      | none => simp [ht1, ht2] at htup
      | some it2 =>
        simp [ht1, ht2, decide_eq_true_eq] at htup
        subst htup
        obtain ⟨hty1, hit1⟩ := tyOf_tuple (d := d1) (layouts := ⟨64, true, []⟩) ht1
        obtain ⟨hty2, hit2⟩ := tyOf_tuple (d := d2) (layouts := ⟨64, true, []⟩) ht2
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
        obtain ⟨hty1, hit1⟩ := tyOf_int (d := d1) (layouts := ⟨64, true, []⟩) hi1
        obtain ⟨hty2, hit2⟩ := tyOf_int (d := d2) (layouts := ⟨64, true, []⟩) hi2
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
        rw [declSlotData_of_none hnt1
            (arrayTypeOf_none_of_scalarTypeOf (scalarTypeOf_int hi1))
            (tupleTypeOf_none_of_scalarTypeOf (scalarTypeOf_int hi1)),
          declSlotData_of_none hnt2
            (arrayTypeOf_none_of_scalarTypeOf (scalarTypeOf_int hi2))
            (tupleTypeOf_none_of_scalarTypeOf (scalarTypeOf_int hi2)), hit1, hit2]

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
    {r : StatementResult} (h : translateStmtResult decls s layouts = some r) :
    (isAssume s = false ∧ ∃ s', translateStatement decls s layouts = some s' ∧ r = .statement s') ∨
    (∃ op op', s.kind = .intrinsic (.assume op) ∧ translateOperand decls op = some op' ∧
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
    have heq : translateStmtResult decls s layouts = (translateStatement decls s layouts).map .statement := by
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

theorem translateRsIntrinsic_cfgWf (f : Gen.Function) (name : RsIntrinsic) (argOps : List MirAst.Operand) (destination : MirAst.Place) (target : Option Nat) (res : TerminatorResult)
    (htgt : ∀ t, target = some t → checkNextBlock f Gen.BbKind.Regular (bbName t) = true)
    (h : translateRsIntrinsic decls name argOps destination target = some res) :
    res.stmts.all (stmtCfgWf f) = true ∧ termCfgWf f Gen.BbKind.Regular res.terminator = true := by
  unfold translateRsIntrinsic at h
  split at h
  · simp only [Option.bind_eq_bind] at h
    cases hargs : argOps.mapM (translateOperand decls) <;> simp [hargs] at h
    cases hret : translatePlace decls destination <;> simp [hret] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by rfl, ?_⟩
    simp [termCfgWf]
    cases target with
    | none => rfl
    | some t => exact htgt t rfl
  · rename_i hs
    split at h
    · rename_i v t
      simp only [Option.bind_eq_bind] at h
      cases hv : translateOperand decls v <;> simp [hv] at h
      cases hret : translatePlace decls destination <;> simp [hret] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by rfl, ?_⟩
      simp [termCfgWf]
      exact htgt t rfl
    · cases h
  · rename_i hs
    split at h
    · rename_i l r t
      simp only [Option.bind_eq_bind] at h
      cases hl : translateOperand decls l <;> simp [hl] at h
      cases hr : translateOperand decls r <;> simp [hr] at h
      cases hret : translatePlace decls destination <;> simp [hret] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by rfl, ?_⟩
      simp [termCfgWf]
      exact htgt t rfl
    · cases h
  · rename_i hs
    cases target with
    | none => cases h
    | some t =>
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by rfl, ?_⟩
      simp [termCfgWf]
      exact htgt t rfl
  · obtain ⟨rfl, rfl⟩ := h
    refine ⟨by rfl, ?_⟩
    simp [termCfgWf, abortTerminator]
  · cases h

theorem translateTerminatorInProg_names {fnMap : FnMap} {decls : List LocalDecl} {nc : Nat}
    {t : MirAst.Terminator} {term : Gen.Terminator} {nc' : Nat}
    {ex : List (Gen.BbName × Gen.BasicBlock)}
    (h : translateTerminatorInProg fnMap layouts decls nc t = some (term, nc', ex)) :
    nc ≤ nc' ∧ ex.map Prod.fst = (List.range' nc (nc' - nc)).map bbName := by
  unfold translateTerminatorInProg at h
  cases hk : t.kind
  case call func argOps destination target unwind =>
    simp only [hk, Option.bind_eq_bind] at h
    cases hdp : extractFnDefPath func <;> simp only [hdp, Option.bind_none, Option.bind_some] at h
    · cases h
    rename_i dp
    cases hintr : translateIntrinsicOrNone decls dp argOps destination target
    · simp only [hintr] at h
      cases hlk : lookupFnTarget fnMap dp <;> simp only [hlk, Option.bind_none, Option.bind_some] at h
      · cases h
      rename_i fc
      cases ha : argOps.mapM (translateCallArg decls) <;> simp only [ha, Option.bind_none, Option.bind_some] at h
      · cases h
      cases hr : translatePlace decls destination <;> simp only [hr, Option.bind_none, Option.bind_some] at h
      · cases h
      cases unwind <;> simp [translateUnwindAction] at h <;> obtain ⟨_, rfl, rfl⟩ := h <;> simp
    · rename_i res
      simp only [hintr] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp
  all_goals
    simp only [hk, Option.bind_eq_bind] at h
    cases ht : translateTerminator layouts decls t <;> simp only [ht, Option.bind_none, Option.bind_some] at h
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
      translateBlocksInProg fnMap layouts decls k nc bbs = some (B, extra) →
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
    cases hres : bb.statements.mapM (translateStmtResult decls · layouts) with
    | none => simp [hres] at h
    | some results =>
      simp only [hres, Option.bind_some] at h
      obtain ⟨hsp1, hsp2⟩ := splitStmts_names (bbName k) [] nc results
      generalize hsp : splitStmts (bbName k) [] nc results = sp at hsp1 hsp2 h
      cases htm : translateTerminatorInProg fnMap layouts decls sp.2.2.2 bb.terminator with
      | none => simp [htm] at h
      | some trep =>
        obtain ⟨term, nc', ex1⟩ := trep
        obtain ⟨htm1, htm2⟩ := translateTerminatorInProg_names htm
        simp only [htm, Option.bind_some] at h
        cases hrest : translateBlocksInProg fnMap layouts decls (k + 1) nc' bbs with
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
      ss.mapM (translateStmtResult decls · layouts) = some rs →
      pre.mapM (translateStatement decls · layouts) = some acc →
      (∀ s ∈ pre, isAssume s = false) →
      (∀ e ∈ (splitStmts cur acc nc rs).2.2.1 ++
          [((splitStmts cur acc nc rs).1, ⟨(splitStmts cur acc nc rs).2.1, term, .Regular⟩)],
        look e.1 = some e.2) →
      SegChain look decls layouts term cur (pre ++ ss)
  | [], rs, cur, pre, acc, nc, hrs, hpre, hna, hlook => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrs
    subst hrs
    have hl := hlook (cur, ⟨acc, term, .Regular⟩) (by simp [splitStmts])
    simpa using SegChain.last hl hpre hna
  | s :: ss, rs, cur, pre, acc, nc, hrs, hpre, hna, hlook => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at hrs
    cases hr : translateStmtResult decls s layouts with
    | none => simp [hr] at hrs
    | some r =>
      cases hrest : ss.mapM (translateStmtResult decls · layouts) with
      | none => simp [hr, hrest] at hrs
      | some rs' =>
        simp only [hr, hrest, Option.bind_some, Option.pure_def, Option.some.injEq] at hrs
        subst hrs
        rcases translateStmtResult_some hr with ⟨hna1, s', hs', rfl⟩ | ⟨op, op', hk, hop, rfl⟩
        · have hpre' : (pre ++ [s]).mapM (translateStatement decls · layouts) = some (acc ++ [s']) := by
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
      translateBlocksInProg fnMap layouts decls k nc bbs = some (B, extra) →
      (∀ e ∈ B, look e.1 = some e.2) →
      ∀ (j : Nat) (bb : BasicBlockData), bbs[j]? = some bb →
        ∃ term nc1 nc2 ex1,
          translateTerminatorInProg fnMap layouts decls nc1 bb.terminator = some (term, nc2, ex1) ∧
          SegChain look decls layouts term (bbName (k + j)) bb.statements
  | _, _, [], _, _, _, _, j, _, hb => by simp at hb
  | k, nc, bb' :: bbs, B, extra, h, hlook, j, bb, hb => by
    simp only [translateBlocksInProg, Option.bind_eq_bind] at h
    cases hres : bb'.statements.mapM (translateStmtResult decls · layouts) with
    | none => simp [hres] at h
    | some results =>
      simp only [hres, Option.bind_some] at h
      generalize hsp : splitStmts (bbName k) [] nc results = sp at h
      cases htm : translateTerminatorInProg fnMap layouts decls sp.2.2.2 bb'.terminator with
      | none => simp [htm] at h
      | some trep =>
        obtain ⟨term, nc', ex1⟩ := trep
        simp only [htm, Option.bind_some] at h
        cases hrest : translateBlocksInProg fnMap layouts decls (k + 1) nc' bbs with
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
        translateTerminatorInProg fnMap body.layouts body.localDecls nc1 bb.terminator =
          some (term, nc2, ex1) ∧
        SegChain (mapGet f.blocks) body.localDecls body.layouts term (bbName i) bb.statements) := by
  simp only [translateFnInProg, Option.bind_eq_bind] at h
  cases hC : translateCallConv body.fnAbi.conv with
  | none => simp [hC] at h
  | some conv =>
    cases hL : translateLocals body.layouts 0 body.localDecls with
    | none => simp [hC, hL] at h
    | some L =>
      cases hB : translateBlocksInProg fnMap body.layouts body.localDecls 0 (body.basicBlocks.length + 1)
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
          obtain ⟨T, hT, hget⟩ := translateLocals_get body.layouts 0 body.localDecls L hL i d hd
          rw [tyOf_of_translateTy hT]
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
    {ss : List MirAst.Statement} (h : SegChain look decls layouts term name ss)
    (hna : ∀ s ∈ ss, isAssume s = false) :
    ∃ stmts, look name = some ⟨stmts, term, .Regular⟩ ∧
      ss.mapM (translateStatement decls · layouts) = some stmts := by
  cases h with
  | last hlook htr _ => exact ⟨_, hlook, htr⟩
  | split _ _ _ hs _ _ =>
    have h1 := hna _ (List.mem_append_right _ List.mem_cons_self)
    simp [isAssume, hs] at h1

/-- Single-body fragment statements (`statementOk`) are never `Assume`. -/
theorem statementOk_isAssume {decls : List LocalDecl} {s : MirAst.Statement}
    (h : statementOk decls s layouts = true) : isAssume s = false := by
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
theorem translateTerminatorInProg_eq_of_not_call (fnMap : FnMap) (layouts : Layout.LayoutTable)
    (decls : List LocalDecl) (nextCleanup : Nat) (t : MirAst.Terminator)
    (hnc : ∀ func args dst tgt unw, t.kind ≠ .call func args dst tgt unw) :
    translateTerminatorInProg fnMap layouts decls nextCleanup t =
      (translateTerminator layouts decls t).map (fun term => (term, nextCleanup, [])) := by
  unfold translateTerminatorInProg
  cases hk : t.kind <;> try (cases translateTerminator layouts decls t <;> rfl)
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
      ss.mapM (translateStmtResult decls · layouts) =
        (ss.mapM (translateStatement decls · layouts)).map (List.map .statement)
  | [], _ => rfl
  | s :: ss, hna => by
    have hs : translateStmtResult decls s layouts = (translateStatement decls s layouts).map .statement := by
      unfold translateStmtResult
      split
      · next op heq =>
        have := hna s List.mem_cons_self
        simp [isAssume, heq] at this
      · rfl
    simp only [List.mapM_cons, Option.bind_eq_bind, hs,
      mapM_translateStmtResult_of_noAssume ss (fun x hx => hna x (List.mem_cons_of_mem _ hx))]
    cases translateStatement decls s layouts <;> cases ss.mapM (translateStatement decls · layouts) <;> simp

/-- When `bbs` contains no `.call` terminators and no `Assume` statements,
`translateBlocksInProg` agrees with `translateBlocks` and synthesizes no extra
blocks (`extra = []`). -/
theorem translateBlocksInProg_eq_of_no_calls (fnMap : FnMap)
    (decls : List LocalDecl) (k nextCleanup : Nat) (bbs : List BasicBlockData)
    (hnc : ∀ bb ∈ bbs, ∀ func args dst tgt unw,
      bb.terminator.kind ≠ .call func args dst tgt unw)
    (hna : ∀ bb ∈ bbs, ∀ s ∈ bb.statements, isAssume s = false) :
    translateBlocksInProg fnMap layouts decls k nextCleanup bbs =
      (translateBlocks layouts decls k bbs).map (fun B => (B, [])) := by
  induction bbs generalizing k nextCleanup with
  | nil => rfl
  | cons bb bbs ih =>
    have hbb := hnc bb List.mem_cons_self
    have hrest := ih (k + 1) nextCleanup (fun b hb => hnc b (List.mem_cons_of_mem _ hb))
      (fun b hb => hna b (List.mem_cons_of_mem _ hb))
    unfold translateBlocksInProg translateBlocks translateBlock
    rw [mapM_translateStmtResult_of_noAssume bb.statements (hna bb List.mem_cons_self)]
    cases bb.statements.mapM (translateStatement decls · layouts) with
    | none => rfl
    | some stmts =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, splitStmts_statements,
        List.nil_append]
      rw [translateTerminatorInProg_eq_of_not_call fnMap layouts decls nextCleanup bb.terminator hbb]
      cases translateTerminator layouts decls bb.terminator with
      | none => rfl
      | some term =>
        simp only [Option.map_some, Option.bind_some]
        rw [hrest]
        cases translateBlocks layouts decls (k + 1) bbs <;> rfl

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
    cases translateLocals body.layouts 0 body.localDecls with
    | none => rfl
    | some locals =>
      cases translateBlocks body.layouts body.localDecls 0 body.basicBlocks with
      | none => rfl
      | some B => simp

theorem progStatementOk_notAssume {decls : List LocalDecl} {s : MirAst.Statement}
    (h : progStatementOk decls s layouts = true) (hna : isAssume s = false) :
    statementOk decls s layouts = true := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | intrinsic intr =>
    cases intr with
    | assume _ => simp [isAssume] at hna
    | copyNonOverlapping _ _ _ => simpa [progStatementOk] using h
  | _ => simpa [progStatementOk] using h

theorem progStatementOk_assume {decls : List LocalDecl} {s : MirAst.Statement}
    {op : Operand} (h : progStatementOk decls s layouts = true)
    (hs : s.kind = .intrinsic (.assume op)) :
    operandOkB layouts decls (copyOp op) = true := by
  obtain ⟨kind, span⟩ := s
  simp only at hs
  subst hs
  simpa [progStatementOk] using h

private theorem mapM_get_spec {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys →
      ys.length = xs.length ∧
      ∀ (j : Nat) x, xs[j]? = some x → ∃ y, ys[j]? = some y ∧ f x = some y
  | [], ys, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun j _ hx => by simp at hx⟩
  | x0 :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hy0 : f x0 with
    | none => simp [hy0] at h
    | some y0 =>
      cases hys : xs.mapM f with
      | none => simp [hy0, hys] at h
      | some ys' =>
        simp [hy0, hys] at h
        subst h
        obtain ⟨hl, hg⟩ := mapM_get_spec f xs ys' hys
        refine ⟨by simp [hl], fun j x hx => ?_⟩
        cases j with
        | zero => simp at hx; subst hx; exact ⟨y0, rfl, hy0⟩
        | succ j => simp at hx ⊢; exact hg j x hx

theorem SegChain.pcZero {look : Gen.BbName → Option Gen.BasicBlock}
    {decls : List LocalDecl} {term : Gen.Terminator} {blk : Nat}
    {ss : List MirAst.Statement} (h : SegChain look decls layouts term (bbName blk) ss) :
    SegPc look decls layouts term blk ss 0 blk 0 := by
  generalize hn : bbName blk = nm at h
  cases h with
  | last hlook htr hna =>
    subst hn
    exact .hereLast hlook htr hna (Nat.zero_le _)
  | split hlook htr hna hs hop hrest =>
    subst hn
    exact .hereSplit hlook htr hna hs hop hrest (Nat.zero_le _)

theorem SegPc.atStmt_notAssume {look : Gen.BbName → Option Gen.BasicBlock}
    {decls : List LocalDecl} {term : Gen.Terminator}
    {entrySeg : Nat} {ss : List MirAst.Statement} {idx curSeg segStmt : Nat}
    {st : MirAst.Statement}
    (h : SegPc look decls layouts term entrySeg ss idx curSeg segStmt)
    (hst : ss[idx]? = some st) (hnaSt : isAssume st = false) :
    ∃ tb st', look (bbName curSeg) = some tb ∧
      segStmt < tb.statements.length ∧
      tb.statements[segStmt]? = some st' ∧
      translateStatement decls st layouts = some st' ∧
      SegPc look decls layouts term entrySeg ss (idx + 1) curSeg (segStmt + 1) := by
  induction h with
  | hereLast hlook htr hna _ =>
    obtain ⟨_, hspec⟩ := mapM_get_spec _ _ _ htr
    obtain ⟨st', hst'get, hst'tr⟩ := hspec _ st hst
    have hlt := (List.getElem?_eq_some_iff.mp hst'get).1
    have hltSs := (List.getElem?_eq_some_iff.mp hst).1
    exact ⟨⟨_, term, .Regular⟩, st', hlook, hlt, hst'get, hst'tr,
      .hereLast hlook htr hna (by omega)⟩
  | @hereSplit curSeg nextSeg segStmt pre post s op op' stmts
      hlook htr hna hs hop hrest hle =>
    rcases Nat.lt_or_eq_of_le hle with hltPre | rfl
    · rw [List.getElem?_append_left hltPre] at hst
      obtain ⟨_, hspec⟩ := mapM_get_spec _ _ _ htr
      obtain ⟨st', hst'get, hst'tr⟩ := hspec _ st hst
      exact ⟨⟨stmts, .Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg)), .Regular⟩,
        st', hlook, (List.getElem?_eq_some_iff.mp hst'get).1, hst'get, hst'tr,
        .hereSplit hlook htr hna hs hop hrest (by omega)⟩
    · rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hst
      subst hst
      obtain ⟨k, sp⟩ := s
      simp only at hs
      subst hs
      simp [isAssume] at hnaSt
  | @stepSplit entrySeg nextSeg curSeg segStmt restIdx pre post s op op' stmts
      hlook htr hna hs hop _ ih =>
    rw [List.getElem?_append_right (by omega),
      show pre.length + 1 + restIdx - pre.length = restIdx + 1 by omega,
      List.getElem?_cons_succ] at hst
    obtain ⟨tb, st', htb, hlt, hget, htrSt, hpc'⟩ := ih hst
    refine ⟨tb, st', htb, hlt, hget, htrSt, ?_⟩
    rw [show pre.length + 1 + restIdx + 1 = pre.length + 1 + (restIdx + 1) by omega]
    exact .stepSplit hlook htr hna hs hop hpc'

theorem SegPc.atStmt_assume {look : Gen.BbName → Option Gen.BasicBlock}
    {decls : List LocalDecl} {term : Gen.Terminator}
    {entrySeg : Nat} {ss : List MirAst.Statement} {idx curSeg segStmt : Nat}
    {st : MirAst.Statement} {op : Operand}
    (h : SegPc look decls layouts term entrySeg ss idx curSeg segStmt)
    (hst : ss[idx]? = some st) (hk : st.kind = .intrinsic (.assume op)) :
    ∃ stmts op' nextSeg,
      look (bbName curSeg) =
        some ⟨stmts, .Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg)), .Regular⟩ ∧
      segStmt = stmts.length ∧
      translateOperand decls op = some op' ∧
      SegPc look decls layouts term entrySeg ss (idx + 1) nextSeg 0 := by
  have hAss : isAssume st = true := by
    obtain ⟨k, sp⟩ := st
    simp only at hk
    subst hk
    rfl
  induction h with
  | hereLast _ _ hna _ =>
    have hfalse := hna st (List.mem_of_getElem? hst)
    rw [hAss] at hfalse
    simp at hfalse
  | @hereSplit curSeg nextSeg segStmt pre post s opS op' stmts
      hlook htr hna hs hop hrest hle =>
    rcases Nat.lt_or_eq_of_le hle with hltPre | rfl
    · rw [List.getElem?_append_left hltPre] at hst
      have hfalse := hna st (List.mem_of_getElem? hst)
      rw [hAss] at hfalse
      simp at hfalse
    · rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hst
      subst hst
      have hopEq : opS = op := by
        cases hs.symm.trans hk
        rfl
      subst hopEq
      obtain ⟨hlen, _⟩ := mapM_get_spec _ _ _ htr
      refine ⟨stmts, op', nextSeg, hlook, hlen.symm, hop, ?_⟩
      rw [show pre.length + 1 = pre.length + 1 + 0 by omega]
      exact .stepSplit hlook htr hna hs hop hrest.pcZero
  | @stepSplit entrySeg nextSeg curSeg segStmt restIdx pre post s opS op' stmts
      hlook htr hna hs hop _ ih =>
    rw [List.getElem?_append_right (by omega),
      show pre.length + 1 + restIdx - pre.length = restIdx + 1 by omega,
      List.getElem?_cons_succ] at hst
    obtain ⟨stmts', op'', nextSeg', hlk', hlen', hop'', hpc'⟩ := ih hst
    refine ⟨stmts', op'', nextSeg', hlk', hlen', hop'', ?_⟩
    rw [show pre.length + 1 + restIdx + 1 = pre.length + 1 + (restIdx + 1) by omega]
    exact .stepSplit hlook htr hna hs hop hpc'

theorem SegPc.atEnd {look : Gen.BbName → Option Gen.BasicBlock}
    {decls : List LocalDecl} {term : Gen.Terminator}
    {entrySeg : Nat} {ss : List MirAst.Statement} {idx curSeg segStmt : Nat}
    (h : SegPc look decls layouts term entrySeg ss idx curSeg segStmt)
    (hend : idx = ss.length) :
    ∃ stmts, look (bbName curSeg) = some ⟨stmts, term, .Regular⟩ ∧
      segStmt = stmts.length := by
  induction h with
  | hereLast hlook htr _ _ =>
    obtain ⟨hlen, _⟩ := mapM_get_spec _ _ _ htr
    exact ⟨_, hlook, hend.trans hlen.symm⟩
  | hereSplit _ _ _ _ _ _ hle =>
    simp only [List.length_append, List.length_cons] at hend
    omega
  | stepSplit _ _ _ _ _ _ ih =>
    simp only [List.length_append, List.length_cons] at hend
    exact ih (by omega)

/-! ### Universal CFG and program well-formedness (`funcCfgWf`, `progWf`) -/

theorem nodup_map_localName {l : List Nat} (h : l.Nodup) : (l.map localName).Nodup := by
  induction l with
  | nil => exact .nil
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih h.2⟩
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hm
    rw [localName_inj] at heq
    subst heq
    exact h.1 hy

theorem nodup_map_fnName {l : List Nat} (h : l.Nodup) : (l.map fnName).Nodup := by
  induction l with
  | nil => exact .nil
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih h.2⟩
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hm
    rw [fnName_inj] at heq
    subst heq
    exact h.1 hy

theorem translateLocals_names :
    ∀ (k : Nat) (ds : List LocalDecl) (L : List (Gen.LocalName × Gen.Type)),
      translateLocals layouts k ds = some L →
      L.map Prod.fst = (List.range' k ds.length).map localName
  | _, [], L, h => by
    simp [translateLocals] at h
    subst h
    rfl
  | k, d :: ds, L, h => by
    simp only [translateLocals, Option.bind_eq_bind] at h
    cases hT : translateTy layouts d.ty with
    | none => simp [hT] at h
    | some ty =>
      cases hR : translateLocals layouts (k + 1) ds with
      | none => simp [hT, hR] at h
      | some rest =>
        simp [hT, hR] at h
        subst h
        simp [translateLocals_names (k + 1) ds rest hR, List.range']

theorem SegChain.head_regular {f : Gen.Function}
    {decls : List LocalDecl} {term : Gen.Terminator} {name : Gen.BbName}
    {ss : List MirAst.Statement}
    (h : SegChain (mapGet f.blocks) decls layouts term name ss) :
    checkNextBlock f .Regular name = true := by
  cases h with
  | last hlook _ _ => simp [checkNextBlock, hlook]
  | split hlook _ _ _ _ _ => simp [checkNextBlock, hlook]

theorem stmtCfgWf_of_translateStatement {body : CapturedMir} {f : Gen.Function}
    {s : MirAst.Statement} {st : Gen.Statement}
    (hL : FnLocalsSpec body f)
    (hargs : f.args = (List.range body.argCount).map (fun k => localName (k + 1)))
    (hok : statementOk body.localDecls s body.layouts = true)
    (hsd : ∀ i, s.kind = .storageDead i → body.argCount < i)
    (htr : translateStatement body.localDecls s body.layouts = some st) :
    stmtCfgWf f st = true := by
  have hstor : (∀ l, st = .StorageLive l → ∃ i, s.kind = .storageLive i ∧ l = localName i) ∧
      (∀ l, st = .StorageDead l → ∃ i, s.kind = .storageDead i ∧ l = localName i) := by
    clear hL hargs hok hsd
    unfold translateStatement at htr
    split at htr <;>
      refine ⟨fun l hl => ?_, fun l hl => ?_⟩ <;> subst hl <;>
      simp_all [Option.map_eq_some_iff, Option.bind_eq_some_iff]
  obtain ⟨hret, hloc⟩ := hL
  cases st with
  | StorageLive l =>
    obtain ⟨i, hk, rfl⟩ := hstor.1 l rfl
    obtain ⟨kind, span⟩ := s
    simp only at hk
    subst hk
    simp only [statementOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hlt, _⟩ := hok
    have hd : body.localDecls[i]? = some body.localDecls[i] := List.getElem?_eq_getElem hlt
    obtain ⟨_, hget⟩ := hloc i body.localDecls[i] hd
    simp [stmtCfgWf, hget]
  | StorageDead l =>
    obtain ⟨i, hk, rfl⟩ := hstor.2 l rfl
    obtain ⟨kind, span⟩ := s
    simp only at hk
    subst hk
    simp only [statementOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hlt, _⟩ := hok
    have hgt : body.argCount < i := hsd i rfl
    have hd : body.localDecls[i]? = some body.localDecls[i] := List.getElem?_eq_getElem hlt
    obtain ⟨_, hget⟩ := hloc i body.localDecls[i] hd
    have hneRet : (localName i != f.ret) = true := by
      rw [hret, bne_iff_ne, ne_eq, localName_inj]
      omega
    have hnotArg : localName i ∉ f.args := by
      rw [hargs]
      intro hm
      obtain ⟨k, hk, heq⟩ := List.mem_map.mp hm
      rw [List.mem_range] at hk
      rw [localName_inj] at heq
      omega
    simp [stmtCfgWf, hget, hneRet, hnotArg]
  | _ => rfl

theorem splitStmts_cfgWf {f : Gen.Function} {term : Gen.Terminator}
    (hterm : termCfgWf f .Regular term = true) :
    ∀ (cur : Gen.BbName) (acc : List Gen.Statement) (nc : Nat) (rs : List StatementResult),
      (∀ st ∈ acc, stmtCfgWf f st = true) →
      (∀ r ∈ rs, (∀ st, r = .statement st → stmtCfgWf f st = true) ∧
        (∀ op d a, r = .intrinsic op d a → op = .Assume)) →
      (∀ e ∈ (splitStmts cur acc nc rs).2.2.1 ++
          [((splitStmts cur acc nc rs).1, ⟨(splitStmts cur acc nc rs).2.1, term, .Regular⟩)],
        mapGet f.blocks e.1 = some e.2) →
      checkNextBlock f .Regular cur = true ∧
      ∀ e ∈ (splitStmts cur acc nc rs).2.2.1 ++
          [((splitStmts cur acc nc rs).1, ⟨(splitStmts cur acc nc rs).2.1, term, .Regular⟩)],
        e.2.statements.all (stmtCfgWf f) = true ∧ termCfgWf f e.2.kind e.2.terminator = true
  | cur, acc, nc, [], hacc, _, hlook => by
    have hl := hlook (cur, ⟨acc, term, .Regular⟩) (by simp [splitStmts])
    refine ⟨by simp [checkNextBlock, hl], ?_⟩
    intro e he
    simp only [splitStmts, List.nil_append, List.mem_singleton] at he
    subst he
    exact ⟨List.all_eq_true.mpr hacc, hterm⟩
  | cur, acc, nc, .statement st :: rest, hacc, hrs, hlook => by
    have hst : stmtCfgWf f st = true := (hrs (.statement st) List.mem_cons_self).1 st rfl
    have hacc' : ∀ x ∈ acc ++ [st], stmtCfgWf f x = true := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hacc x h
      · simp only [List.mem_singleton] at h; subst h; exact hst
    exact splitStmts_cfgWf hterm cur (acc ++ [st]) nc rest hacc'
      (fun r hr => hrs r (List.mem_cons_of_mem _ hr)) (by simpa [splitStmts] using hlook)
  | cur, acc, nc, .intrinsic op dest args :: rest, hacc, hrs, hlook => by
    have hop : op = .Assume :=
      (hrs (.intrinsic op dest args) List.mem_cons_self).2 op dest args rfl
    subst hop
    have hl0 := hlook (cur, ⟨acc, .Intrinsic .Assume args dest (some (bbName nc)), .Regular⟩)
      (by simp [splitStmts])
    obtain ⟨hnext, hrestWf⟩ := splitStmts_cfgWf hterm (bbName nc) [] (nc + 1) rest (by simp)
      (fun r hr => hrs r (List.mem_cons_of_mem _ hr))
      (fun e he => hlook e (by
        simp only [splitStmts, List.cons_append, List.mem_cons]
        exact .inr he))
    refine ⟨by simp [checkNextBlock, hl0], ?_⟩
    intro e he
    simp only [splitStmts, List.cons_append, List.mem_cons] at he
    rcases he with rfl | he'
    · exact ⟨List.all_eq_true.mpr hacc, by simp [termCfgWf, hnext]⟩
    · exact hrestWf e he'

theorem termCfgWf_of_translateTerminator {f : Gen.Function} {decls : List LocalDecl}
    {nblocks : Nat} {t : MirAst.Terminator} {term : Gen.Terminator}
    (hEntry : ∀ j, j < nblocks → checkNextBlock f .Regular (bbName j) = true)
    (hok : terminatorOk layouts decls nblocks t = true)
    (htr : translateTerminator layouts decls t = some term) :
    termCfgWf f .Regular term = true := by
  obtain ⟨kind, span⟩ := t
  cases kind with
  | goto target =>
    simp only [terminatorOk, decide_eq_true_eq] at hok
    simp only [translateTerminator, Option.some.injEq] at htr
    subst htr
    exact hEntry target hok
  | switchInt discr targets =>
    simp only [terminatorOk] at hok
    cases hsit : switchIntType layouts decls (copyOp discr) with
    | none => simp [hsit] at hok
    | some it =>
      simp only [hsit, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨_, hbr⟩, _⟩, hoth⟩ := hok
      simp only [translateTerminator, Option.bind_eq_bind] at htr
      cases hd : translateOperand decls (copyOp discr) with
      | none => simp [hd] at htr
      | some dop =>
        simp only [hd, Option.bind_some] at htr
        cases hot : operandType layouts decls (copyOp discr) with
        | none => simp [hot] at htr
        | some oty =>
          cases oty <;> simp [hot] at htr
          all_goals
            subst htr
            simp only [termCfgWf, switchCases, Bool.and_eq_true, List.all_eq_true, List.mem_map,
              forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
            exact ⟨fun p hp => hEntry p.2 (hbr p hp).2, hEntry targets.otherwise hoth⟩
  | unreachable =>
    simp only [translateTerminator, Option.some.injEq] at htr
    subst htr
    rfl
  | return_ =>
    simp only [translateTerminator, Option.some.injEq] at htr
    subst htr
    rfl
  | _ =>
    simp [terminatorOk] at hok

theorem translateBlocksInProg_cfgWf {fnMap : FnMap} {callees : List CapturedMir}
    {body : CapturedMir} {f : Gen.Function}
    (hL : FnLocalsSpec body f)
    (hargs : f.args = (List.range body.argCount).map (fun k => localName (k + 1)))
    (hEntry : ∀ j, j < body.basicBlocks.length → checkNextBlock f .Regular (bbName j) = true)
    (hsdBody : storageDeadOk body = true) :
    ∀ (k nc : Nat) (bbs : List BasicBlockData)
      (B extra : List (Gen.BbName × Gen.BasicBlock)),
      k + bbs.length = body.basicBlocks.length →
      (∀ j bb, bbs[j]? = some bb →
        body.basicBlocks[k + j]? = some bb ∧
        bb.statements.all (progStatementOk body.localDecls · body.layouts) = true ∧
        terminatorInProgOk callees body (k + j) bb.terminator = true) →
      translateBlocksInProg fnMap body.layouts body.localDecls k nc bbs = some (B, extra) →
      (∀ e ∈ B ++ extra, mapGet f.blocks e.1 = some e.2) →
      ∀ e ∈ B ++ extra,
        e.2.statements.all (stmtCfgWf f) = true ∧ termCfgWf f e.2.kind e.2.terminator = true
  | _, _, [], B, extra, _, _, htr, _ => by
    simp only [translateBlocksInProg, Option.some.injEq, Prod.mk.injEq] at htr
    obtain ⟨rfl, rfl⟩ := htr
    simp
  | k, nc, bb :: bbs, B, extra, hlen, hbbs, htr, hlook => by
    obtain ⟨hbb0Eq, hstmtsOk, htermOk⟩ := hbbs 0 bb (by simp)
    have hbbk : body.basicBlocks[k]? = some bb := by simpa using hbb0Eq
    have hbbMem : bb ∈ body.basicBlocks := List.mem_of_getElem? hbbk
    have hsdBb : ∀ s ∈ bb.statements, ∀ i, s.kind = .storageDead i → body.argCount < i := by
      simp only [storageDeadOk, List.all_eq_true] at hsdBody
      intro s hs i hk
      have h1 := hsdBody bb hbbMem s hs
      simp [hk] at h1
      exact h1
    simp only [translateBlocksInProg, Option.bind_eq_bind] at htr
    cases hres : bb.statements.mapM (translateStmtResult body.localDecls · body.layouts) with
    | none => simp [hres] at htr
    | some results =>
      simp only [hres, Option.bind_some] at htr
      generalize hsp : splitStmts (bbName k) [] nc results = sp at htr
      cases htm : translateTerminatorInProg fnMap body.layouts body.localDecls sp.2.2.2 bb.terminator with
      | none => simp [htm] at htr
      | some trep =>
        obtain ⟨term, nc', ex1⟩ := trep
        simp only [htm, Option.bind_some] at htr
        cases hrest : translateBlocksInProg fnMap body.layouts body.localDecls (k + 1) nc' bbs with
        | none => simp [hrest] at htr
        | some rrep =>
          obtain ⟨rest, extraRest⟩ := rrep
          simp only [hrest, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at htr
          obtain ⟨rfl, rfl⟩ := htr
          have hrsWf : ∀ r ∈ results,
              (∀ st, r = .statement st → stmtCfgWf f st = true) ∧
              (∀ op d a, r = .intrinsic op d a → op = .Assume) := by
            obtain ⟨hlenR, hgetR⟩ := mapM_get_spec _ _ _ hres
            intro r hr
            obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hr
            have hidxS : idx < bb.statements.length := hlenR ▸ hidx
            let s := bb.statements[idx]
            have hsEq : bb.statements[idx]? = some s := List.getElem?_eq_getElem hidxS
            obtain ⟨r', hr'Eq, hsTr⟩ := hgetR idx s hsEq
            have hrEq : results[idx] = r' :=
              Option.some.inj ((List.getElem?_eq_getElem hidx).symm.trans hr'Eq)
            have hsMem : s ∈ bb.statements := List.mem_of_getElem? hsEq
            have hpOk : progStatementOk body.localDecls s body.layouts = true :=
              (List.all_eq_true.mp hstmtsOk) s hsMem
            rcases translateStmtResult_some hsTr with ⟨hna, st, hstTr, hEq⟩ | ⟨op, op', _, _, hEq⟩
            · refine ⟨fun st' h' => ?_, fun op d a h' => ?_⟩
              · rw [hrEq, hEq, StatementResult.statement.injEq] at h'
                subst h'
                exact stmtCfgWf_of_translateStatement hL hargs
                  (progStatementOk_notAssume hpOk hna) (hsdBb s hsMem) hstTr
              · rw [hrEq, hEq] at h'
                cases h'
            · refine ⟨fun st h' => ?_, fun op2 d a h' => ?_⟩
              · rw [hrEq, hEq] at h'
                cases h'
              · rw [hrEq, hEq, StatementResult.intrinsic.injEq] at h'
                exact h'.1.symm
          have htermExWf : termCfgWf f .Regular term = true ∧
              ∀ e ∈ ex1, e.2.statements.all (stmtCfgWf f) = true ∧
                termCfgWf f e.2.kind e.2.terminator = true := by
            simp only [terminatorInProgOk, Bool.or_eq_true] at htermOk
            rcases htermOk with htOk | hcOk
            · have hnc : ∀ func args dst tgt unw,
                  bb.terminator.kind ≠ .call func args dst tgt unw := by
                intro func args dst tgt unw hk
                simp [terminatorOk, hk] at htOk
              rw [translateTerminatorInProg_eq_of_not_call fnMap body.layouts body.localDecls sp.2.2.2
                bb.terminator hnc, Option.map_eq_some_iff] at htm
              obtain ⟨t', ht', heq⟩ := htm
              obtain ⟨rfl, _, rfl⟩ := Prod.mk.injEq .. ▸ heq
              exact ⟨termCfgWf_of_translateTerminator hEntry htOk ht', by simp⟩
            · simp only [callTerminatorOk, Nat.add_zero] at hcOk
              rw [hbbk] at hcOk
              cases htk : bb.terminator.kind with
              | call func argOps destination target unwind =>
                rw [htk] at hcOk
                cases target with
                | none => simp at hcOk
                | some targetBb =>
                  cases hdp : extractFnDefPath func with
                  | none => simp [hdp] at hcOk
                  | some dp =>
                    simp only [hdp] at hcOk
                    revert hcOk
                    cases hintr : translateIntrinsicOrNone body.localDecls dp argOps destination (some targetBb) with
                    | some res =>
                      intro hcOk
                      cases hcOk
                    | none =>
                      intro hcOk
                      cases hfc : monoCallee? callees func dp with
                      | none => simp [hfc] at hcOk
                      | some callee =>
                        cases hcd : callee.localDecls with
                        | nil => simp [hfc, hcd] at hcOk
                        | cons retDecl restDecls =>
                          simp only [hfc, hcd, Bool.and_eq_true, decide_eq_true_eq] at hcOk
                          have htgtLt : targetBb < body.basicBlocks.length := hcOk.1.1.1.1.1.1.1
                          have hunwOk : callUnwindOk unwind = true := hcOk.1.1.1.1.1.1.2
                          simp only [translateTerminatorInProg, htk, hdp, Option.bind_eq_bind,
                            Option.bind_some] at htm
                          simp only [hintr] at htm
                          cases hlk : lookupFnTarget fnMap dp with
                          | none => simp [hlk] at htm
                          | some fnConv =>
                            cases hargsTr : argOps.mapM (translateCallArg body.localDecls) with
                            | none => simp [hlk, hargsTr] at htm
                            | some args' =>
                              cases hretTr : translatePlace body.localDecls destination with
                              | none => simp [hlk, hargsTr, hretTr] at htm
                              | some retPlace =>
                                obtain ⟨uwTerm, huwEq, huwCases⟩ :=
                                  translateUnwindAction_spec sp.2.2.2 unwind hunwOk
                                simp only [hlk, hargsTr, hretTr, huwEq, Option.bind_some, pure,
                                  Option.some.injEq, Prod.mk.injEq] at htm
                                obtain ⟨rfl, rfl, rfl⟩ := htm
                                have hexMem : mapGet f.blocks (bbName sp.2.2.2) =
                                    some ⟨[], uwTerm, .Cleanup⟩ :=
                                  hlook (bbName sp.2.2.2, ⟨[], uwTerm, .Cleanup⟩) (by simp)
                                have huwTermWf : termCfgWf f .Cleanup uwTerm = true := by
                                  rcases huwCases with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
                                    rfl
                                refine ⟨?_, ?_⟩
                                · simp [termCfgWf, hEntry targetBb htgtLt, checkUnwindBlock, hexMem]
                                · intro e he
                                  simp only [List.mem_singleton] at he
                                  subst he
                                  exact ⟨rfl, huwTermWf⟩

              | _ => simp [htk] at hcOk
          obtain ⟨_, hsegWf⟩ := splitStmts_cfgWf htermExWf.1 (bbName k) [] nc results (by simp)
            hrsWf (by
              rw [hsp]
              intro e he
              apply hlook
              simp only [List.mem_append] at he ⊢
              rcases he with h | h
              · exact .inl (.inl (.inl h))
              · exact .inl (.inl (.inr h)))
          rw [hsp] at hsegWf
          have hrestWf := translateBlocksInProg_cfgWf hL hargs hEntry hsdBody (k + 1) nc' bbs
            rest extraRest (by simp at hlen; omega)
            (fun j b hj => by
              have h1 := hbbs (j + 1) b (by simpa using hj)
              simpa [show k + (j + 1) = k + 1 + j by omega] using h1)
            hrest
            (fun e he => by
              apply hlook
              simp only [List.mem_append] at he ⊢
              rcases he with h | h
              · exact .inl (.inr h)
              · exact .inr (.inr h))
          intro e he
          simp only [List.append_assoc, List.mem_append] at he
          rcases he with h1 | h2 | h3 | h4 | h5
          · exact hsegWf e (List.mem_append.mpr (.inl h1))
          · exact hsegWf e (List.mem_append.mpr (.inr h2))
          · exact hrestWf e (List.mem_append.mpr (.inl h3))
          · exact htermExWf.2 e h4
          · exact hrestWf e (List.mem_append.mpr (.inr h5))

theorem translateFnInProg_funcCfgWf_core {fnMap : FnMap} {callees : List CapturedMir}
    {body : CapturedMir} {f : Gen.Function}
    (hargLe : body.argCount + 1 ≤ body.localDecls.length)
    (hneNil : body.basicBlocks ≠ [])
    (hbbsAll : (List.range body.basicBlocks.length).all (fun blk =>
      match body.basicBlocks[blk]? with
      | some bb =>
        !bb.isCleanup &&
        bb.statements.all (progStatementOk body.localDecls · body.layouts) &&
        terminatorInProgOk callees body blk bb.terminator
      | none => true) = true)
    (hsd : storageDeadOk body = true)
    (htr : translateFnInProg fnMap body = some f) :
    funcCfgWf f = true := by
  obtain ⟨hL, _, hargs, hstart, hinit, hsegs⟩ := translateFnInProg_spec fnMap body f htr
  have hnPos : 0 < body.basicBlocks.length := List.length_pos_iff.mpr hneNil
  have hEntry : ∀ j, j < body.basicBlocks.length → checkNextBlock f .Regular (bbName j) = true := by
    intro j hj
    have hbb : body.basicBlocks[j]? = some body.basicBlocks[j] := List.getElem?_eq_getElem hj
    obtain ⟨_, _, _, _, _, hseg⟩ := hsegs j body.basicBlocks[j] hbb
    exact hseg.head_regular
  simp only [translateFnInProg, Option.bind_eq_bind] at htr
  cases hC : translateCallConv body.fnAbi.conv with
  | none => simp [hC] at htr
  | some conv =>
    cases hLoc : translateLocals body.layouts 0 body.localDecls with
    | none => simp [hC, hLoc] at htr
    | some L =>
      cases hB : translateBlocksInProg fnMap body.layouts body.localDecls 0 (body.basicBlocks.length + 1)
          body.basicBlocks with
      | none => simp [hC, hLoc, hB] at htr
      | some brep =>
        obtain ⟨B, extra⟩ := brep
        simp only [hC, hLoc, hB, Option.bind_some, pure, Option.some.injEq] at htr
        have hfBlocks : f.blocks = ⟨B ++ [(bbName body.basicBlocks.length, initBlock body)] ++ extra⟩ := by
          rw [← htr]
        have hfLocals : f.locals = ⟨L⟩ := by rw [← htr]
        have hlocNd : (f.locals.entries.map Prod.fst).Nodup := by
          rw [hfLocals, translateLocals_names 0 body.localDecls L hLoc]
          exact nodup_map_localName (List.nodup_range')
        obtain ⟨hndBE, hmemBE⟩ := translateBlocksInProg_names 0 (body.basicBlocks.length + 1)
          body.basicBlocks B extra hB (by omega)
        have hinitNot : bbName body.basicBlocks.length ∉ (B ++ extra).map Prod.fst := by
          intro hm
          obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
          rcases hmemBE e he with ⟨j, hj, hj'⟩ | ⟨c, hc, hc'⟩
          · rw [heq, bbName_inj] at hj'; omega
          · rw [heq, bbName_inj] at hc'; omega
        have hblkNd : (f.blocks.entries.map Prod.fst).Nodup := by
          rw [hfBlocks]
          have hperm : List.Perm
              ((B ++ [(bbName body.basicBlocks.length, initBlock body)] ++ extra).map Prod.fst)
              (bbName body.basicBlocks.length :: (B ++ extra).map Prod.fst) := by
            simp only [List.append_assoc, List.singleton_append, List.map_append, List.map_cons]
            exact List.perm_middle
          exact hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hinitNot, hndBE⟩)
        obtain ⟨hret, hlocSpec⟩ := hL
        have hretSome : (mapGet f.locals f.ret).isSome = true := by
          have hd0 : body.localDecls[0]? = some (body.localDecls[0]'(by omega)) :=
            List.getElem?_eq_getElem (by omega)
          obtain ⟨_, hg0⟩ := hlocSpec 0 _ hd0
          rw [hret, hg0]
          rfl
        have hargsSome : f.args.all (fun a => (mapGet f.locals a).isSome) = true := by
          rw [hargs, List.all_eq_true]
          intro a ha
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
          rw [List.mem_range] at hk
          have hdk : body.localDecls[k + 1]? = some (body.localDecls[k + 1]'(by omega)) :=
            List.getElem?_eq_getElem (by omega)
          obtain ⟨_, hgk⟩ := hlocSpec (k + 1) _ hdk
          rw [hgk]
          rfl
        have hretArgsNd : (f.ret :: f.args).Nodup := by
          have heq : f.ret :: f.args = (List.range (body.argCount + 1)).map localName := by
            rw [hret, hargs, List.range_succ_eq_map, List.map_cons, List.map_map]
            rfl
          rw [heq]
          exact nodup_map_localName List.nodup_range
        have hstartOk : checkNextBlock f .Regular f.start = true := by
          rw [hstart, checkNextBlock, hinit]
          rfl
        have hinitStmtsOk : (initBlock body).statements.all (stmtCfgWf f) = true := by
          simp only [initBlock, alwaysStorageLiveLocals, List.all_eq_true, List.mem_map,
            List.mem_filter, List.mem_range]
          rintro st ⟨loc, ⟨hlocLt, _⟩, rfl⟩
          have hdl : body.localDecls[loc]? = some body.localDecls[loc] :=
            List.getElem?_eq_getElem hlocLt
          obtain ⟨_, hgl⟩ := hlocSpec loc _ hdl
          simp [stmtCfgWf, hgl]
        have hinitTermOk : termCfgWf f (initBlock body).kind (initBlock body).terminator = true :=
          hEntry 0 hnPos
        have hBEWf := translateBlocksInProg_cfgWf (callees := callees) ⟨hret, hlocSpec⟩ hargs hEntry
          hsd 0 (body.basicBlocks.length + 1) body.basicBlocks B extra (by simp)
          (fun j bb hj => by
            obtain ⟨hjLt, _⟩ := List.getElem?_eq_some_iff.mp hj
            have h1 := (List.all_eq_true.mp hbbsAll) j (List.mem_range.mpr hjLt)
            simp only [hj, Bool.and_eq_true] at h1
            exact ⟨by simpa using hj, h1.1.2, by simpa using h1.2⟩)
          hB
          (fun e he => by
            rw [hfBlocks]
            have hmem' : e ∈ B ++ [(bbName body.basicBlocks.length, initBlock body)] ++ extra := by
              simp only [List.append_assoc, List.mem_append] at he ⊢
              rcases he with h | h
              · exact .inl h
              · exact .inr (.inr h)
            exact mapGet_eq_of_mem_nodup (by simpa [hfBlocks] using hblkNd) hmem')
        have hallBlocks : f.blocks.entries.all
            (fun p => p.2.statements.all (stmtCfgWf f) && termCfgWf f p.2.kind p.2.terminator) = true := by
          rw [hfBlocks, List.all_eq_true]
          intro e he
          simp only [List.append_assoc, List.singleton_append, List.mem_append, List.mem_cons] at he
          rcases he with hB' | rfl | hex'
          · obtain ⟨h1, h2⟩ := hBEWf e (List.mem_append.mpr (.inl hB'))
            simp [h1, h2]
          · simp [hinitStmtsOk, hinitTermOk]
          · obtain ⟨h1, h2⟩ := hBEWf e (List.mem_append.mpr (.inr hex'))
            simp [h1, h2]
        simp [funcCfgWf, hlocNd, hblkNd, hretSome, hargsSome, hretArgsNd, hstartOk, hallBlocks]

/-- Every function translated by `translateFnInProg` on a `bodyInProgFragment`
MIR body satisfies `funcCfgWf` (including multi-`Assume` split basic blocks,
`initBlock`, and synthesized call unwind blocks). -/
theorem translateFnInProg_funcCfgWf {fnMap : FnMap} {callees : List CapturedMir}
    {body : CapturedMir} {f : Gen.Function}
    (hfrag : bodyInProgFragment fnMap callees body = true)
    (htr : translateFnInProg fnMap body = some f) :
    funcCfgWf f = true := by
  simp only [bodyInProgFragment, Bool.and_eq_true, decide_eq_true_eq] at hfrag
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hargLe⟩, _⟩, _⟩, hneNil⟩, hbbsAll⟩, hsd⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hfrag
  exact translateFnInProg_funcCfgWf_core hargLe hneNil hbbsAll hsd htr

/-- Single-body fragment translations (`inFragment` + `translateFn`) also
universally satisfy `funcCfgWf`. -/
theorem translateFn_funcCfgWf {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (htr : translateFn body = some f) :
    funcCfgWf f = true := by
  simp only [inFragment, Bool.and_eq_true, decide_eq_true_eq] at hfrag
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hargLe⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hneNil⟩, hbbs⟩, hsd⟩, _⟩, _⟩, _⟩, _⟩ := hfrag
  have hnc : ∀ bb ∈ body.basicBlocks, ∀ func args dst tgt unw,
      bb.terminator.kind ≠ .call func args dst tgt unw := by
    intro bb hbb func args dst tgt unw hk
    have hbbOk := (List.all_eq_true.mp hbbs) bb hbb
    simp [terminatorOk, hk] at hbbOk
  have hna : ∀ bb ∈ body.basicBlocks, ∀ s ∈ bb.statements, isAssume s = false := by
    intro bb hbb s hs
    have hbbOk := (List.all_eq_true.mp hbbs) bb hbb
    simp only [Bool.and_eq_true, List.all_eq_true] at hbbOk
    exact statementOk_isAssume (hbbOk.1.2 s hs)
  have htrProg : translateFnInProg [] body = some f := by
    rw [translateFnInProg_eq_translateFn_of_no_calls [] body hnc hna]
    exact htr
  have hbbsAll : (List.range body.basicBlocks.length).all (fun blk =>
      match body.basicBlocks[blk]? with
      | some bb =>
        !bb.isCleanup &&
        bb.statements.all (progStatementOk body.localDecls · body.layouts) &&
        terminatorInProgOk [] body blk bb.terminator
      | none => true) = true := by
    rw [List.all_eq_true]
    intro blk _
    cases hbb : body.basicBlocks[blk]? with
    | none => rfl
    | some bb =>
      have hbbOk := (List.all_eq_true.mp hbbs) bb (List.mem_of_getElem? hbb)
      simp only [Bool.and_eq_true, List.all_eq_true] at hbbOk ⊢
      refine ⟨⟨hbbOk.1.1, fun s hs => ?_⟩, ?_⟩
      · have hsOk := hbbOk.1.2 s hs
        have hsNa := statementOk_isAssume hsOk
        unfold progStatementOk
        split
        · next op hk => simp [isAssume, hk] at hsNa
        · exact hsOk
      · simp [terminatorInProgOk, hbbOk.2]
  exact translateFnInProg_funcCfgWf_core hargLe hneNil hbbsAll hsd htrProg

/-- `minimize`'s synthesized `mkStartFn` wrapper satisfies `funcCfgWf` for every
entry function index `entryIdx`. -/
theorem mkStartFn_funcCfgWf (entryIdx : Nat) :
    funcCfgWf (mkStartFn entryIdx) = true := by
  obtain ⟨_, hargs, hret, hstart, _, hloc0, hb0, hb1, hb2⟩ := mkStartFn_spec entryIdx
  have hlocNd : ((mkStartFn entryIdx).locals.entries.map Prod.fst).Nodup := by
    change [localName 0].Nodup
    simp
  have hblkNd : ((mkStartFn entryIdx).blocks.entries.map Prod.fst).Nodup := by
    change [bbName 0, bbName 1, bbName 2].Nodup
    simp [bbName_inj]
  have hstartOk : checkNextBlock (mkStartFn entryIdx) .Regular (mkStartFn entryIdx).start = true := by
    rw [hstart, checkNextBlock, hb0]
    rfl
  have hb0Term : termCfgWf (mkStartFn entryIdx) .Regular
      (.Call (fnPtrExpr (fnName entryIdx)) .Rust [] buildUnitPlace (some (bbName 1)) (some (bbName 2))) = true := by
    simp [termCfgWf, checkNextBlock, checkUnwindBlock, hb1, hb2]
  have hb1Term : termCfgWf (mkStartFn entryIdx) .Regular
      (.Intrinsic .Exit [] buildUnitPlace none) = true := rfl
  have hb2Term : termCfgWf (mkStartFn entryIdx) .Catch buildAbort = true := rfl
  have hallB : (mkStartFn entryIdx).blocks.entries.all
      (fun p => p.2.statements.all (stmtCfgWf (mkStartFn entryIdx)) &&
        termCfgWf (mkStartFn entryIdx) p.2.kind p.2.terminator) = true := by
    change ([(_, _), (_, _), (_, _)] : List (Gen.BbName × Gen.BasicBlock)).all _ = true
    simp [hb0Term, hb1Term, hb2Term]
  simp [funcCfgWf, hlocNd, hblkNd, hret, hargs, hloc0, hstartOk, hallB]

theorem translateProgFns_names_and_mem {fnMap : FnMap} :
    ∀ (k : Nat) (bs : List CapturedMir) (F : List (Gen.FnName × Gen.Function)),
      translateProgFns fnMap k bs = some F →
      F.map Prod.fst = (List.range' k bs.length).map fnName ∧
      ∀ p ∈ F, ∃ b ∈ bs, translateFnInProg fnMap b = some p.2
  | _, [], F, h => by
    simp only [translateProgFns, Option.some.injEq] at h
    subst h
    simp
  | k, b :: bs, F, h => by
    simp only [translateProgFns, Option.bind_eq_bind] at h
    cases hf : translateFnInProg fnMap b with
    | none => simp [hf] at h
    | some f =>
      cases hrest : translateProgFns fnMap (k + 1) bs with
      | none => simp [hf, hrest] at h
      | some rest =>
        simp only [hf, hrest, Option.bind_some, pure, Option.some.injEq] at h
        subst h
        obtain ⟨hnames, hmem⟩ := translateProgFns_names_and_mem (k + 1) bs rest hrest
        refine ⟨by simp [hnames, List.range'], ?_⟩
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨b, List.mem_cons_self, hf⟩
        · obtain ⟨b', hb', htr'⟩ := hmem p hp'
          exact ⟨b', List.mem_cons_of_mem _ hb', htr'⟩

/-- Universal program well-formedness theorem: every multi-function MIR program
`(entry, callees)` in `progInFragment` translates to a MiniRust `Gen.Program`
satisfying `progWf` (`funcCfgWf` on `entry`, every callee, and `mkStartFn`,
distinct function names, and a C-ABI 0-arg 1-ZST `start` function). -/
theorem translateProg_progWf {entry : CapturedMir} {callees : List CapturedMir}
    {p : Gen.Program}
    (hfrag : progInFragment entry callees = true)
    (htr : translateProg entry callees = some p) :
    progWf p = true := by
  simp only [progInFragment, Bool.and_eq_true, List.all_eq_true] at hfrag
  obtain ⟨⟨⟨_, hbodies⟩, _⟩, _⟩ := hfrag
  simp only [translateProg, Option.bind_eq_bind] at htr
  cases hF : translateProgFns (fnNameMap entry callees) 0 (entry :: callees) with
  | none => simp [hF] at htr
  | some F =>
    simp only [hF, Option.bind_some, pure, Option.some.injEq] at htr
    subst htr
    obtain ⟨hFnames, hFmem⟩ := translateProgFns_names_and_mem 0 (entry :: callees) F hF
    have hfnNd : ((F ++ [(fnName (1 + callees.length), mkStartFn 0)]).map Prod.fst).Nodup := by
      have heq : (F ++ [(fnName (1 + callees.length), mkStartFn 0)]).map Prod.fst =
          (List.range' 0 (1 + callees.length + 1)).map fnName := by
        rw [List.map_append, hFnames]
        have hr : List.range' 0 (1 + callees.length + 1) =
            List.range' 0 (entry :: callees).length ++ [1 + callees.length] := by
          have := range'_append_of_le (a := 0) (b := 1 + callees.length) (c := 1 + callees.length + 1)
            (by omega) (by omega)
          simpa [Nat.add_comm 1 callees.length] using this.symm
        rw [hr, List.map_append]
        rfl
      rw [heq]
      exact nodup_map_fnName List.nodup_range'
    have hallWf : (F ++ [(fnName (1 + callees.length), mkStartFn 0)]).all
        (fun q => funcCfgWf q.2) = true := by
      rw [List.all_eq_true]
      intro q hq
      rcases List.mem_append.mp hq with hqF | hqS
      · obtain ⟨b, hb, hbf⟩ := hFmem q hqF
        exact translateFnInProg_funcCfgWf (hbodies b hb) hbf
      · simp only [List.mem_singleton] at hqS
        subst hqS
        exact mkStartFn_funcCfgWf 0
    have hstartGet : mapGet ⟨F ++ [(fnName (1 + callees.length), mkStartFn 0)]⟩
        (fnName (1 + callees.length)) = some (mkStartFn 0) :=
      mapGet_eq_of_mem_nodup hfnNd (by simp)
    have hfnNdDec : decide ((F ++ [(fnName (1 + callees.length), mkStartFn 0)]).map Prod.fst).Nodup = true :=
      decide_eq_true hfnNd
    have hstartBody : ((mkStartFn 0).calling_convention == .C &&
        (mkStartFn 0).args.isEmpty &&
        match mapGet (mkStartFn 0).locals (mkStartFn 0).ret with
        | some retTy =>
          match Interp.Type.layout retTy with
          | .ok (.Sized sz align) => sz == ⟨0⟩ && align == ⟨1⟩
          | _ => false
        | none => false) = true := by
      decide
    unfold progWf
    dsimp only
    rw [hfnNdDec, hallWf, hstartGet]
    dsimp only [Bool.true_and]
    exact hstartBody

/-! ## Uniform byte-chunk lists for homogeneous arrays -/

theorem drop_length_add_append {β : Type} (a b : List β) (n : Nat) :
    (a ++ b).drop (a.length + n) = b.drop n := by
  induction a with
  | nil => simp
  | cons _ a ih => simp [Nat.succ_add, ih]

theorem take_length_add_append {β : Type} (a b : List β) (n : Nat) :
    (a ++ b).take (a.length + n) = a ++ b.take n := by
  induction a with
  | nil => simp
  | cons _ a ih => simp [Nat.succ_add, ih]

theorem flatten_map_length {α β : Type} (f : α → List β) (k : Nat) (xs : List α)
    (hf : ∀ x ∈ xs, (f x).length = k) :
    (xs.map f).flatten.length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : (f x).length = k := hf x (by simp)
    have hxs : ∀ y ∈ xs, (f y).length = k := fun y hy => hf y (by simp [hy])
    simp [hx, ih hxs, Nat.succ_mul, Nat.add_comm]

theorem drop_mul_take_flatten_map {α β : Type} (f : α → List β) (k : Nat)
    (xs : List α) (hf : ∀ x ∈ xs, (f x).length = k) (i : Nat) (x : α)
    (hi : xs[i]? = some x) :
    ((xs.map f).flatten.drop (i * k)).take k = f x := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    have hhd : (f hd).length = k := hf hd (by simp)
    have htl : ∀ y ∈ tl, (f y).length = k := fun y hy => hf y (by simp [hy])
    cases i with
    | zero =>
      simp at hi; subst hi
      have htake := take_length_add_append (f hd) (tl.map f).flatten 0
      rw [hhd, Nat.add_zero] at htake
      simpa using htake
    | succ j =>
      simp at hi
      rw [List.map_cons, List.flatten_cons,
        show (j + 1) * k = (f hd).length + j * k by rw [hhd, Nat.succ_mul, Nat.add_comm],
        drop_length_add_append]
      exact ih htl j hi

theorem subsliceWithLength_flatten_map {α β : Type} (f : α → List β) (k : Nat)
    (xs : List α) (hf : ∀ x ∈ xs, (f x).length = k) (i : Nat) (x : α)
    (hi : xs[i]? = some x) :
    subsliceWithLength (xs.map f).flatten ((i * k : Nat) : Int) (k : Int) = .ok (f x) := by
  have hlt : i < xs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hlen : (xs.map f).flatten.length = xs.length * k := flatten_map_length f k xs hf
  have hle : i * k + k ≤ (xs.map f).flatten.length := by
    rw [hlen, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right k (by omega)
  have hle' : ((i * k : Nat) : Int) + (k : Int) ≤ ((xs.map f).flatten.length : Int) := by
    exact_mod_cast hle
  unfold subsliceWithLength
  split
  · have htonat1 : (((i * k : Nat) : Int)).toNat = i * k := rfl
    have htonat2 : ((k : Int)).toNat = k := rfl
    rw [htonat1, htonat2, drop_mul_take_flatten_map f k xs hf i x hi]
    rfl
  · next hbad =>
    exfalso
    apply hbad
    exact ⟨by omega, by omega, hle'⟩

theorem splice_flatten_map {α β : Type} (f : α → List β) (k : Nat)
    (xs : List α) (hf : ∀ x ∈ xs, (f x).length = k) (i : Nat) (v : α)
    (hi : i < xs.length) :
    (xs.map f).flatten.take (i * k) ++ f v ++ (xs.map f).flatten.drop (i * k + k) =
      ((xs.set i v).map f).flatten := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    have hhd : (f hd).length = k := hf hd (by simp)
    have htl : ∀ y ∈ tl, (f y).length = k := fun y hy => hf y (by simp [hy])
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.map_cons, List.flatten_cons, List.set_cons_zero]
      have hdrop := drop_length_add_append (f hd) (tl.map f).flatten 0
      rw [hhd, Nat.add_zero] at hdrop
      simp [hdrop]
    | succ j =>
      simp only [List.length_cons] at hi
      have hj : j < tl.length := by omega
      simp only [List.map_cons, List.flatten_cons, List.set_cons_succ]
      rw [show (j + 1) * k = (f hd).length + j * k by rw [hhd, Nat.succ_mul, Nat.add_comm],
        take_length_add_append,
        show (f hd).length + j * k + k = (f hd).length + (j * k + k) by omega,
        drop_length_add_append]
      simp only [List.append_assoc]
      congr 1
      simpa [List.append_assoc] using ih htl j hj

/-! ## Offset byte splicing (`spliceAt`) and `TupleSpec` layout algebra -/

theorem spliceAt_length {α : Type} (xs : List α) (off : Nat) (bs : List α)
    (h : off + bs.length ≤ xs.length) :
    (spliceAt xs off bs).length = xs.length := by
  simp [spliceAt, List.length_take, List.length_drop]
  omega

theorem getElem?_spliceAt {α : Type} (xs : List α) (off : Nat) (bs : List α)
    (h : off + bs.length ≤ xs.length) (k : Nat) :
    (spliceAt xs off bs)[k]? =
      if k < off then xs[k]?
      else if k < off + bs.length then bs[k - off]?
      else xs[k]? := by
  unfold spliceAt
  have hmin : min off xs.length = off := Nat.min_eq_left (by omega)
  rw [List.append_assoc, List.getElem?_append]
  simp only [List.length_take, hmin]
  by_cases hk1 : k < off
  · simp [hk1]
  · simp only [hk1, ↓reduceIte, List.getElem?_append]
    by_cases hk2 : k < off + bs.length
    · have hk2' : k - off < bs.length := by omega
      simp [hk2, hk2']
    · have hk2' : ¬ k - off < bs.length := by omega
      simp only [hk2, hk2', ↓reduceIte, List.getElem?_drop]
      congr 1
      omega

theorem getElem?_drop_take {α : Type} (xs : List α) (off len k : Nat) :
    ((xs.drop off).take len)[k]? = if k < len then xs[off + k]? else none := by
  rw [List.getElem?_take]
  split
  · simp [List.getElem?_drop]
  · rfl

theorem drop_take_length {α : Type} (xs : List α) (off len : Nat)
    (h : off + len ≤ xs.length) :
    ((xs.drop off).take len).length = len := by
  simp [List.length_take, List.length_drop]
  omega

theorem drop_take_spliceAt_self {α : Type} (xs : List α) (off : Nat) (bs : List α)
    (h : off + bs.length ≤ xs.length) :
    ((spliceAt xs off bs).drop off).take bs.length = bs := by
  apply List.ext_getElem?
  intro k
  rw [getElem?_drop_take]
  by_cases hk : k < bs.length
  · simp only [hk, ↓reduceIte, getElem?_spliceAt xs off bs h]
    have h1 : ¬ off + k < off := by omega
    have h2 : off + k < off + bs.length := by omega
    simp [h1, h2]
  · simp [hk]

theorem drop_take_spliceAt_disjoint {α : Type} (xs : List α) (off : Nat) (bs : List α)
    (targetOff targetLen : Nat)
    (h : off + bs.length ≤ xs.length)
    (hdisj : off + bs.length ≤ targetOff ∨ targetOff + targetLen ≤ off) :
    ((spliceAt xs off bs).drop targetOff).take targetLen = (xs.drop targetOff).take targetLen := by
  apply List.ext_getElem?
  intro k
  rw [getElem?_drop_take, getElem?_drop_take]
  by_cases hk : k < targetLen
  · simp only [hk, ↓reduceIte, getElem?_spliceAt xs off bs h]
    rcases hdisj with hleft | hright
    · have h1 : ¬ targetOff + k < off := by omega
      have h2 : ¬ targetOff + k < off + bs.length := by omega
      simp [h1, h2]
    · have h1 : targetOff + k < off := by omega
      simp [h1]
  · simp [hk]

theorem spliceAt_same {α : Type} (xs : List α) (off : Nat) (bs1 bs2 : List α)
    (h1 : off + bs1.length ≤ xs.length) (hlen : bs1.length = bs2.length) :
    spliceAt (spliceAt xs off bs1) off bs2 = spliceAt xs off bs2 := by
  have h1' : (spliceAt xs off bs1).length = xs.length := spliceAt_length xs off bs1 h1
  have h2 : off + bs2.length ≤ xs.length := by omega
  have h2' : off + bs2.length ≤ (spliceAt xs off bs1).length := by omega
  apply List.ext_getElem?
  intro k
  rw [getElem?_spliceAt _ off bs2 h2', getElem?_spliceAt xs off bs2 h2,
    getElem?_spliceAt xs off bs1 h1]
  by_cases hk1 : k < off
  · simp [hk1]
  · by_cases hk2 : k < off + bs2.length
    · simp [hk1, hk2]
    · have hk2' : ¬ k < off + bs1.length := by omega
      simp [hk1, hk2, hk2']

theorem spliceAt_comm {α : Type} (xs : List α) (off1 : Nat) (bs1 : List α)
    (off2 : Nat) (bs2 : List α)
    (h1 : off1 + bs1.length ≤ xs.length)
    (h2 : off2 + bs2.length ≤ xs.length)
    (hdisj : off1 + bs1.length ≤ off2 ∨ off2 + bs2.length ≤ off1) :
    spliceAt (spliceAt xs off1 bs1) off2 bs2 = spliceAt (spliceAt xs off2 bs2) off1 bs1 := by
  have hlen1 : (spliceAt xs off1 bs1).length = xs.length := spliceAt_length xs off1 bs1 h1
  have hlen2 : (spliceAt xs off2 bs2).length = xs.length := spliceAt_length xs off2 bs2 h2
  have h2' : off2 + bs2.length ≤ (spliceAt xs off1 bs1).length := by omega
  have h1' : off1 + bs1.length ≤ (spliceAt xs off2 bs2).length := by omega
  apply List.ext_getElem?
  intro k
  rw [getElem?_spliceAt _ off2 bs2 h2', getElem?_spliceAt _ off1 bs1 h1',
    getElem?_spliceAt xs off1 bs1 h1, getElem?_spliceAt xs off2 bs2 h2]
  by_cases ha1 : k < off1 <;> by_cases ha2 : k < off1 + bs1.length <;>
    by_cases hb1 : k < off2 <;> by_cases hb2 : k < off2 + bs2.length <;>
    simp only [ha1, ha2, hb1, hb2, ↓reduceIte] <;> omega

theorem spliceAt_nested {α : Type} (xs : List α) (off1 len1 off2 : Nat) (sub : List α)
    (h1 : off1 + len1 ≤ xs.length) (h2 : off2 + sub.length ≤ len1) :
    spliceAt xs off1 (spliceAt ((xs.drop off1).take len1) off2 sub) =
      spliceAt xs (off1 + off2) sub := by
  have hslice_len : ((xs.drop off1).take len1).length = len1 := drop_take_length xs off1 len1 h1
  have h2' : off2 + sub.length ≤ ((xs.drop off1).take len1).length := by omega
  have hinner_len : (spliceAt ((xs.drop off1).take len1) off2 sub).length = len1 := by
    rw [spliceAt_length _ off2 sub h2', hslice_len]
  have houter1 : off1 + (spliceAt ((xs.drop off1).take len1) off2 sub).length ≤ xs.length := by
    omega
  have houter2 : (off1 + off2) + sub.length ≤ xs.length := by omega
  apply List.ext_getElem?
  intro k
  rw [getElem?_spliceAt xs off1 _ houter1, getElem?_spliceAt xs (off1 + off2) sub houter2,
    hinner_len]
  by_cases hk1 : k < off1
  · have hk2 : k < off1 + off2 := by omega
    simp [hk1, hk2]
  · by_cases hk2 : k < off1 + len1
    · simp only [hk1, hk2, ↓reduceIte]
      rw [getElem?_spliceAt ((xs.drop off1).take len1) off2 sub h2', getElem?_drop_take]
      have hk_sub_len : k - off1 < len1 := by omega
      simp only [hk_sub_len, ↓reduceIte, show off1 + (k - off1) = k by omega]
      by_cases hk3 : k - off1 < off2
      · have hk3' : k < off1 + off2 := by omega
        simp [hk3, hk3']
      · have hk3' : ¬ k < off1 + off2 := by omega
        by_cases hk4 : k - off1 < off2 + sub.length
        · have hk4' : k < (off1 + off2) + sub.length := by omega
          simp [hk3, hk3', hk4, hk4', show k - off1 - off2 = k - (off1 + off2) by omega]
        · have hk4' : ¬ k < (off1 + off2) + sub.length := by omega
          simp [hk3, hk3', hk4, hk4']
    · have hk3 : ¬ k < off1 + off2 := by omega
      have hk4 : ¬ k < (off1 + off2) + sub.length := by omega
      simp [hk1, hk2, hk3, hk4]

theorem writeSubsliceAtIndex_eq_spliceAt {α : Type} (xs : List α) (off : Nat) (bs : List α)
    (h : off + bs.length ≤ xs.length) :
    writeSubsliceAtIndex xs (off : Int) bs = .ok (spliceAt xs off bs) := by
  unfold writeSubsliceAtIndex spliceAt
  have h1 : (0 : Int) ≤ (off : Int) := by omega
  have h2 : (off : Int) + (bs.length : Int) ≤ (xs.length : Int) := by exact_mod_cast h
  simp [h1, h2]
  rfl

theorem subsliceWithLength_eq_drop_take {α : Type} (xs : List α) (off len : Nat)
    (h : off + len ≤ xs.length) :
    subsliceWithLength xs (off : Int) (len : Int) = .ok ((xs.drop off).take len) := by
  unfold subsliceWithLength
  have h1 : (0 : Int) ≤ (off : Int) := by omega
  have h2 : (0 : Int) ≤ (len : Int) := by omega
  have h3 : (off : Int) + (len : Int) ≤ (xs.length : Int) := by exact_mod_cast h
  simp [h1, h2, h3]
  rfl

theorem valBytes_length (it : Gen.IntType) (v : Value) :
    (valBytes it v).length = it.size.bytes := by
  cases v <;> simp [valBytes, scalarBytes, uninitBytes, leBytes_length]

mutual

theorem TupleSpec.encodeVal_length :
    ∀ (s : TupleSpec) (v : Value), s.wf = true → (s.encodeVal v).length = s.size
  | .scalar it, v, _ => valBytes_length it v
  | .tuple fields size align, v, hwf => by
    simp only [TupleSpec.wf, Bool.and_eq_true] at hwf
    rcases hwf with ⟨⟨⟨_, _⟩, _⟩, hfields⟩
    cases v with
    | aggregate vIdx vals =>
      cases vIdx with
      | zero =>
        simp only [TupleSpec.encodeVal, TupleSpec.size]
        exact TupleSpec.encodeFields_length size align fields vals
          (List.replicate size .Uninit) hfields (by simp)
      | succ _ => simp [TupleSpec.encodeVal, TupleSpec.size]
    | _ => simp [TupleSpec.encodeVal, TupleSpec.size]

theorem TupleSpec.encodeFields_length (size align : Nat) :
    ∀ (fields : List (Nat × TupleSpec)) (vals : List Value) (bytes : List Byte),
      TupleSpec.fieldsWf size align fields = true →
      bytes.length = size →
      (TupleSpec.encodeFields fields vals bytes).length = size
  | [], _, bytes, _, hlen => hlen
  | _ :: _, [], bytes, _, hlen => hlen
  | (off, s) :: restF, v :: restV, bytes, hwf, hlen => by
    simp only [TupleSpec.fieldsWf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    rcases hwf with ⟨⟨⟨⟨⟨hswf, hoff⟩, _⟩, _⟩, _⟩, hrest⟩
    have hvlen : (s.encodeVal v).length = s.size := TupleSpec.encodeVal_length s v hswf
    have hsplice : (spliceAt bytes off (s.encodeVal v)).length = size := by
      rw [spliceAt_length bytes off (s.encodeVal v) (by omega), hlen]
    exact TupleSpec.encodeFields_length size align restF restV
      (spliceAt bytes off (s.encodeVal v)) hrest hsplice

end

theorem TupleSpec.encodeFields_preserve_disjoint_slice (size align : Nat)
    (fields : List (Nat × TupleSpec)) (vals : List Value) (bytes : List Byte)
    (targetOff targetLen : Nat)
    (hwf : TupleSpec.fieldsWf size align fields = true)
    (hlen : bytes.length = size)
    (hdisj : ∀ p ∈ fields, p.1 + p.2.size ≤ targetOff ∨ targetOff + targetLen ≤ p.1) :
    ((TupleSpec.encodeFields fields vals bytes).drop targetOff).take targetLen =
      (bytes.drop targetOff).take targetLen := by
  induction fields generalizing vals bytes with
  | nil => rfl
  | cons hd restF ih =>
    obtain ⟨off, s⟩ := hd
    cases vals with
    | nil => rfl
    | cons v restV =>
      simp only [TupleSpec.fieldsWf, Bool.and_eq_true, decide_eq_true_eq] at hwf
      rcases hwf with ⟨⟨⟨⟨⟨hswf, hoff⟩, _⟩, _⟩, _⟩, hrest⟩
      have hvlen : (s.encodeVal v).length = s.size := TupleSpec.encodeVal_length s v hswf
      have hsplice_len : (spliceAt bytes off (s.encodeVal v)).length = size := by
        rw [spliceAt_length bytes off (s.encodeVal v) (by omega), hlen]
      have hdisj_hd : off + (s.encodeVal v).length ≤ targetOff ∨ targetOff + targetLen ≤ off := by
        rw [hvlen]
        exact hdisj (off, s) (by simp)
      have hdisj_tl : ∀ p ∈ restF, p.1 + p.2.size ≤ targetOff ∨ targetOff + targetLen ≤ p.1 :=
        fun p hp => hdisj p (by simp [hp])
      simp only [TupleSpec.encodeFields]
      rw [ih restV (spliceAt bytes off (s.encodeVal v)) hrest hsplice_len hdisj_tl,
        drop_take_spliceAt_disjoint bytes off (s.encodeVal v) targetOff targetLen
          (by omega) hdisj_hd]

theorem TupleSpec.encodeFields_field_slice (size align : Nat)
    (fields : List (Nat × TupleSpec)) (vals : List Value) (bytes : List Byte)
    (idx off : Nat) (fSpec : TupleSpec) (fv : Value)
    (hwf : TupleSpec.fieldsWf size align fields = true)
    (hlen : bytes.length = size)
    (hf : fields[idx]? = some (off, fSpec))
    (hv : vals[idx]? = some fv) :
    fSpec.wf = true ∧
    off + fSpec.size ≤ size ∧
    off % fSpec.align = 0 ∧
    fSpec.align ≤ align ∧
    ((TupleSpec.encodeFields fields vals bytes).drop off).take fSpec.size =
      fSpec.encodeVal fv := by
  induction fields generalizing vals bytes idx with
  | nil => simp at hf
  | cons hd restF ih =>
    obtain ⟨off0, s0⟩ := hd
    cases vals with
    | nil => simp at hv
    | cons v0 restV =>
      simp only [TupleSpec.fieldsWf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf
      rcases hwf with ⟨⟨⟨⟨⟨hswf0, hoff0⟩, hmod0⟩, hal0⟩, hdisj0⟩, hrest⟩
      have hvlen0 : (s0.encodeVal v0).length = s0.size := TupleSpec.encodeVal_length s0 v0 hswf0
      have hsplice_len : (spliceAt bytes off0 (s0.encodeVal v0)).length = size := by
        rw [spliceAt_length bytes off0 (s0.encodeVal v0) (by omega), hlen]
      cases idx with
      | zero =>
        simp at hf hv
        rcases hf with ⟨rfl, rfl⟩
        subst hv
        refine ⟨hswf0, hoff0, hmod0, hal0, ?_⟩
        simp only [TupleSpec.encodeFields]
        have hdisj' : ∀ p ∈ restF, p.1 + p.2.size ≤ off0 ∨ off0 + s0.size ≤ p.1 := by
          intro p hp
          rcases hdisj0 p hp with h1 | h2
          · exact Or.inr h1
          · exact Or.inl h2
        rw [TupleSpec.encodeFields_preserve_disjoint_slice size align restF restV
          (spliceAt bytes off0 (s0.encodeVal v0)) off0 s0.size hrest hsplice_len hdisj',
          ← hvlen0, drop_take_spliceAt_self bytes off0 (s0.encodeVal v0) (by omega)]
      | succ j =>
        simp at hf hv
        simp only [TupleSpec.encodeFields]
        exact ih restV (spliceAt bytes off0 (s0.encodeVal v0)) j hrest hsplice_len hf hv

theorem TupleSpec.encodeFields_comm_disjoint_splice (size align : Nat)
    (fields : List (Nat × TupleSpec)) (vals : List Value) (bytes : List Byte)
    (targetOff : Nat) (bs : List Byte)
    (hwf : TupleSpec.fieldsWf size align fields = true)
    (hlen : bytes.length = size)
    (hbs : targetOff + bs.length ≤ size)
    (hdisj : ∀ p ∈ fields, p.1 + p.2.size ≤ targetOff ∨ targetOff + bs.length ≤ p.1) :
    TupleSpec.encodeFields fields vals (spliceAt bytes targetOff bs) =
      spliceAt (TupleSpec.encodeFields fields vals bytes) targetOff bs := by
  induction fields generalizing vals bytes with
  | nil => rfl
  | cons hd restF ih =>
    obtain ⟨off, s⟩ := hd
    cases vals with
    | nil => rfl
    | cons v restV =>
      simp only [TupleSpec.fieldsWf, Bool.and_eq_true, decide_eq_true_eq] at hwf
      rcases hwf with ⟨⟨⟨⟨⟨hswf, hoff⟩, _⟩, _⟩, _⟩, hrest⟩
      have hvlen : (s.encodeVal v).length = s.size := TupleSpec.encodeVal_length s v hswf
      have hsplice_len : (spliceAt bytes off (s.encodeVal v)).length = size := by
        rw [spliceAt_length bytes off (s.encodeVal v) (by omega), hlen]
      have hdisj_hd : off + (s.encodeVal v).length ≤ targetOff ∨ targetOff + bs.length ≤ off := by
        rw [hvlen]
        exact hdisj (off, s) (by simp)
      have hdisj_tl : ∀ p ∈ restF, p.1 + p.2.size ≤ targetOff ∨ targetOff + bs.length ≤ p.1 :=
        fun p hp => hdisj p (by simp [hp])
      simp only [TupleSpec.encodeFields]
      rw [← spliceAt_comm bytes off (s.encodeVal v) targetOff bs (by omega) (by omega) hdisj_hd,
        ih restV (spliceAt bytes off (s.encodeVal v)) hrest hsplice_len hdisj_tl]

theorem TupleSpec.encodeFields_set (size align : Nat)
    (fields : List (Nat × TupleSpec)) (vals : List Value) (bytes : List Byte)
    (idx off : Nat) (fSpec : TupleSpec) (fv' : Value)
    (hwf : TupleSpec.fieldsWf size align fields = true)
    (hlen : bytes.length = size)
    (hvals_len : vals.length = fields.length)
    (hf : fields[idx]? = some (off, fSpec)) :
    TupleSpec.encodeFields fields (vals.set idx fv') bytes =
      spliceAt (TupleSpec.encodeFields fields vals bytes) off (fSpec.encodeVal fv') := by
  induction fields generalizing vals bytes idx with
  | nil => simp at hf
  | cons hd restF ih =>
    obtain ⟨off0, s0⟩ := hd
    cases vals with
    | nil => simp at hvals_len
    | cons v0 restV =>
      simp only [TupleSpec.fieldsWf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf
      rcases hwf with ⟨⟨⟨⟨⟨hswf0, hoff0⟩, _⟩, _⟩, hdisj0⟩, hrest⟩
      have hvlen0 : (s0.encodeVal v0).length = s0.size := TupleSpec.encodeVal_length s0 v0 hswf0
      have hsplice_len : (spliceAt bytes off0 (s0.encodeVal v0)).length = size := by
        rw [spliceAt_length bytes off0 (s0.encodeVal v0) (by omega), hlen]
      cases idx with
      | zero =>
        simp at hf
        rcases hf with ⟨rfl, rfl⟩
        have hvlen' : (s0.encodeVal fv').length = s0.size :=
          TupleSpec.encodeVal_length s0 fv' hswf0
        have hdisj' :
            ∀ p ∈ restF, p.1 + p.2.size ≤ off0 ∨ off0 + (s0.encodeVal fv').length ≤ p.1 := by
          intro p hp
          rw [hvlen']
          rcases hdisj0 p hp with h1 | h2
          · exact Or.inr h1
          · exact Or.inl h2
        simp only [List.set_cons_zero, TupleSpec.encodeFields]
        rw [← TupleSpec.encodeFields_comm_disjoint_splice size align restF restV
          (spliceAt bytes off0 (s0.encodeVal v0)) off0 (s0.encodeVal fv')
          hrest hsplice_len (by omega) hdisj',
          spliceAt_same bytes off0 (s0.encodeVal v0) (s0.encodeVal fv')
            (by omega) (by omega)]
      | succ j =>
        simp at hf hvals_len
        simp only [List.set_cons_succ, TupleSpec.encodeFields]
        exact ih restV (spliceAt bytes off0 (s0.encodeVal v0)) j hrest hsplice_len hvals_len hf

theorem drop_take_nested {α : Type} (xs : List α) (off1 len1 off2 len2 : Nat)
    (h : off2 + len2 ≤ len1) :
    (((xs.drop off1).take len1).drop off2).take len2 = (xs.drop (off1 + off2)).take len2 := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_drop_take, getElem?_drop_take, getElem?_drop_take]
  by_cases hi : i < len2
  · have hi1 : off2 + i < len1 := by omega
    simp [hi, hi1, Nat.add_assoc]
  · simp [hi]

theorem spliceAt_zero_full {α : Type} (xs ys : List α) (h : xs.length = ys.length) :
    spliceAt xs 0 ys = ys := by
  unfold spliceAt
  simp [h]

theorem TupleSpec.fieldsToMiniRust_length (fields : List (Nat × TupleSpec)) :
    (TupleSpec.fieldsToMiniRust fields).length = fields.length := by
  induction fields with
  | nil => rfl
  | cons p rest ih => obtain ⟨_, _⟩ := p; simp [TupleSpec.fieldsToMiniRust, ih]

theorem TupleSpec.fieldsToMiniRust_getElem? (fields : List (Nat × TupleSpec))
    (idx off : Nat) (s : TupleSpec) (h : fields[idx]? = some (off, s)) :
    (TupleSpec.fieldsToMiniRust fields)[idx]? = some (⟨off⟩, s.toMiniRustTy) := by
  induction fields generalizing idx with
  | nil => simp at h
  | cons p rest ih =>
    obtain ⟨off0, s0⟩ := p
    cases idx with
    | zero =>
      simp at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | succ j =>
      simp at h
      simpa [TupleSpec.fieldsToMiniRust] using ih j h

theorem TupleSpec.fieldsToMiniRustVal_length (fields : List (Nat × TupleSpec)) (vals : List Value) :
    (TupleSpec.fieldsToMiniRustVal fields vals).length = min fields.length vals.length := by
  induction fields generalizing vals with
  | nil => simp [TupleSpec.fieldsToMiniRustVal]
  | cons p rest ih =>
    obtain ⟨_, _⟩ := p
    cases vals with
    | nil => simp [TupleSpec.fieldsToMiniRustVal]
    | cons v vs => simp [TupleSpec.fieldsToMiniRustVal, ih, Nat.min_def]; split <;> omega

theorem TupleSpec.fieldsValOk_length {fields : List (Nat × TupleSpec)} {vals : List Value}
    (h : TupleSpec.fieldsValOk fields vals = true) :
    vals.length = fields.length := by
  induction fields generalizing vals with
  | nil =>
    cases vals <;> simp [TupleSpec.fieldsValOk] at h ⊢
  | cons p rest ih =>
    obtain ⟨_, _⟩ := p
    cases vals with
    | nil => simp [TupleSpec.fieldsValOk] at h
    | cons v vs =>
      simp only [TupleSpec.fieldsValOk, Bool.and_eq_true] at h
      simp [ih h.2]

theorem TupleSpec.fieldsValOk_getElem? {fields : List (Nat × TupleSpec)} {vals : List Value}
    (hok : TupleSpec.fieldsValOk fields vals = true) {idx off : Nat} {fSpec : TupleSpec}
    (hf : fields[idx]? = some (off, fSpec)) :
    ∃ fv, vals[idx]? = some fv ∧ fSpec.valOk fv = true := by
  induction fields generalizing vals idx with
  | nil => simp at hf
  | cons p rest ih =>
    obtain ⟨off0, s0⟩ := p
    cases vals with
    | nil => simp [TupleSpec.fieldsValOk] at hok
    | cons v0 restV =>
      simp only [TupleSpec.fieldsValOk, Bool.and_eq_true] at hok
      cases idx with
      | zero =>
        simp at hf
        rcases hf with ⟨rfl, rfl⟩
        exact ⟨v0, rfl, hok.1⟩
      | succ j =>
        simp at hf
        exact ih hok.2 hf

theorem TupleSpec.fieldsValOk_set {fields : List (Nat × TupleSpec)} {vals : List Value}
    (hok : TupleSpec.fieldsValOk fields vals = true) {idx off : Nat} {fSpec : TupleSpec}
    {fv' : Value} (hf : fields[idx]? = some (off, fSpec)) (hv' : fSpec.valOk fv' = true) :
    TupleSpec.fieldsValOk fields (vals.set idx fv') = true := by
  induction fields generalizing vals idx with
  | nil => simp at hf
  | cons p rest ih =>
    obtain ⟨off0, s0⟩ := p
    cases vals with
    | nil => simp [TupleSpec.fieldsValOk] at hok
    | cons v0 restV =>
      simp only [TupleSpec.fieldsValOk, Bool.and_eq_true] at hok
      cases idx with
      | zero =>
        simp at hf
        rcases hf with ⟨rfl, rfl⟩
        simp [TupleSpec.fieldsValOk, hv', hok.2]
      | succ j =>
        simp at hf
        simp [TupleSpec.fieldsValOk, hok.1, ih hok.2 hf]

theorem TupleSpec.fieldsWf_getElem? {size align : Nat} {fields : List (Nat × TupleSpec)}
    (hwf : TupleSpec.fieldsWf size align fields = true) {idx off : Nat} {fSpec : TupleSpec}
    (hf : fields[idx]? = some (off, fSpec)) :
    fSpec.wf = true ∧ off + fSpec.size ≤ size ∧ off % fSpec.align = 0 ∧ fSpec.align ≤ align := by
  induction fields generalizing idx with
  | nil => simp at hf
  | cons p rest ih =>
    obtain ⟨off0, s0⟩ := p
    simp only [TupleSpec.fieldsWf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    rcases hwf with ⟨⟨⟨⟨⟨hswf, hoff⟩, hmod⟩, hal⟩, _⟩, hrest⟩
    cases idx with
    | zero =>
      simp at hf
      rcases hf with ⟨rfl, rfl⟩
      exact ⟨hswf, hoff, hmod, hal⟩
    | succ j =>
      simp at hf
      exact ih hrest hf

/-- Traverse a chain of `.field` projections on an Anneal `Value`. -/
def readFieldPath : Value → List ProjectionElem → Option Value
  | val, [] => some val
  | .aggregate 0 vals, .field idx _ :: rest =>
    match vals[idx]? with
    | some fv => readFieldPath fv rest
    | none => none
  | _, _ => none

/-- Update a `Value` at a chain of `.field` projections. -/
def writeFieldPath : Value → List ProjectionElem → Value → Option Value
  | _, [], newVal => some newVal
  | .aggregate 0 vals, .field idx _ :: rest, newVal =>
    match vals[idx]? with
    | some oldFv =>
      match writeFieldPath oldFv rest newVal with
      | some newFv => some (.aggregate 0 (vals.set idx newFv))
      | none => none
    | none => none
  | _, _, _ => none

theorem resolveFieldPath_wf {layouts : Layout.LayoutTable} {rootSpec leafSpec : TupleSpec}
    {projs : List ProjectionElem} {totalOff : Nat}
    (hwf : rootSpec.wf = true)
    (hres : resolveFieldPath layouts rootSpec projs = some (totalOff, leafSpec)) :
    leafSpec.wf = true ∧ totalOff + leafSpec.size ≤ rootSpec.size := by
  induction projs generalizing rootSpec totalOff with
  | nil =>
    simp [resolveFieldPath] at hres
    rcases hres with ⟨rfl, rfl⟩
    exact ⟨hwf, by omega⟩
  | cons p rest ih =>
    cases rootSpec with
    | scalar _ =>
      cases p <;> simp [resolveFieldPath] at hres
    | tuple fields size align =>
      cases p with
      | field idx fieldTy =>
        simp only [resolveFieldPath, Option.bind_eq_bind] at hres
        cases hf : fields[idx]? with
        | none => simp [hf] at hres
        | some pair =>
          obtain ⟨off, subSpec⟩ := pair
          simp only [hf, Option.bind_some] at hres
          cases hexp : specOfRigidTy layouts fieldTy.kind fieldTy.layoutIdx with
          | none => simp [hexp] at hres
          | some expectedSpec =>
            simp only [hexp, Option.bind_some] at hres
            by_cases heq : subSpec = expectedSpec
            · simp only [heq, ↓reduceIte] at hres
              cases hrest : resolveFieldPath layouts expectedSpec rest with
              | none => simp [hrest] at hres
              | some rpair =>
                obtain ⟨restOff, leafSpec'⟩ := rpair
                simp [hrest] at hres
                rcases hres with ⟨rfl, rfl⟩
                subst heq
                simp only [TupleSpec.wf, Bool.and_eq_true] at hwf
                have hfwf := TupleSpec.fieldsWf_getElem? hwf.2 hf
                obtain ⟨hleafWf, hrestBound⟩ := ih hfwf.1 hrest
                exact ⟨hleafWf, by change off + restOff + leafSpec'.size ≤ size; omega⟩
            · simp [heq] at hres
      | _ => simp [resolveFieldPath] at hres

theorem resolveFieldPath_read {layouts : Layout.LayoutTable} {rootSpec leafSpec : TupleSpec}
    {projs : List ProjectionElem} {totalOff : Nat} {rootVal : Value}
    (hwf : rootSpec.wf = true) (hval : rootSpec.valOk rootVal = true)
    (hres : resolveFieldPath layouts rootSpec projs = some (totalOff, leafSpec)) :
    ∃ leafVal,
      readFieldPath rootVal projs = some leafVal ∧
      leafSpec.valOk leafVal = true ∧
      ((rootSpec.encodeVal rootVal).drop totalOff).take leafSpec.size =
        leafSpec.encodeVal leafVal ∧
      ∀ locals, MirSemantics.readProjectedValue locals rootVal projs = .ok leafVal := by
  induction projs generalizing rootSpec totalOff rootVal with
  | nil =>
    simp [resolveFieldPath] at hres
    rcases hres with ⟨rfl, rfl⟩
    have hlen := TupleSpec.encodeVal_length rootSpec rootVal hwf
    refine ⟨rootVal, rfl, hval, ?_, fun _ => rfl⟩
    rw [List.drop_zero, ← hlen, List.take_length]
  | cons p rest ih =>
    cases rootSpec with
    | scalar _ =>
      cases p <;> simp [resolveFieldPath] at hres
    | tuple fields size align =>
      cases p with
      | field idx fieldTy =>
        simp only [resolveFieldPath, Option.bind_eq_bind] at hres
        cases hf : fields[idx]? with
        | none => simp [hf] at hres
        | some pair =>
          obtain ⟨off, subSpec⟩ := pair
          simp only [hf, Option.bind_some] at hres
          cases hexp : specOfRigidTy layouts fieldTy.kind fieldTy.layoutIdx with
          | none => simp [hexp] at hres
          | some expectedSpec =>
            simp only [hexp, Option.bind_some] at hres
            by_cases heq : subSpec = expectedSpec
            · simp only [heq, ↓reduceIte] at hres
              cases hrest : resolveFieldPath layouts expectedSpec rest with
              | none => simp [hrest] at hres
              | some rpair =>
                obtain ⟨restOff, leafSpec'⟩ := rpair
                simp [hrest] at hres
                rcases hres with ⟨rfl, rfl⟩
                subst heq
                cases rootVal with
                | aggregate vIdx vals =>
                  cases vIdx with
                  | zero =>
                    simp only [TupleSpec.wf, Bool.and_eq_true] at hwf
                    simp only [TupleSpec.valOk, Bool.and_eq_true] at hval
                    obtain ⟨fv, hfv, hfvOk⟩ := TupleSpec.fieldsValOk_getElem? hval.2 hf
                    have hslice := TupleSpec.encodeFields_field_slice size align fields vals
                      (List.replicate size .Uninit) idx off subSpec fv hwf.2 (by simp) hf hfv
                    obtain ⟨_, hrestBound⟩ := resolveFieldPath_wf hslice.1 hrest
                    obtain ⟨leafVal, hread, hleafOk, hsubSlice, hprojRead⟩ :=
                      ih hslice.1 hfvOk hrest
                    refine ⟨leafVal, ?_, hleafOk, ?_, ?_⟩
                    · simp [readFieldPath, hfv, hread]
                    · simp only [TupleSpec.encodeVal]
                      rw [← drop_take_nested _ off subSpec.size restOff leafSpec'.size hrestBound,
                        hslice.2.2.2.2, hsubSlice]
                    · intro locals
                      simp [MirSemantics.readProjectedValue, Trusted.Sequence.get?, hfv, hprojRead locals]
                  | succ _ => simp [TupleSpec.valOk] at hval
                | _ => simp [TupleSpec.valOk] at hval
            · simp [heq] at hres
      | _ => simp [resolveFieldPath] at hres

theorem resolveFieldPath_write {layouts : Layout.LayoutTable} {rootSpec leafSpec : TupleSpec}
    {projs : List ProjectionElem} {totalOff : Nat} {rootVal newLeafVal : Value}
    (hwf : rootSpec.wf = true) (hval : rootSpec.valOk rootVal = true)
    (hres : resolveFieldPath layouts rootSpec projs = some (totalOff, leafSpec))
    (hnew : leafSpec.valOk newLeafVal = true) :
    ∃ newRootVal,
      writeFieldPath rootVal projs newLeafVal = some newRootVal ∧
      rootSpec.valOk newRootVal = true ∧
      rootSpec.encodeVal newRootVal =
        spliceAt (rootSpec.encodeVal rootVal) totalOff (leafSpec.encodeVal newLeafVal) ∧
      ∀ locals, MirSemantics.writeProjectedValue locals rootVal projs newLeafVal = .ok newRootVal := by
  induction projs generalizing rootSpec totalOff rootVal with
  | nil =>
    simp [resolveFieldPath] at hres
    rcases hres with ⟨rfl, rfl⟩
    have hlen1 := TupleSpec.encodeVal_length rootSpec rootVal hwf
    have hlen2 := TupleSpec.encodeVal_length rootSpec newLeafVal hwf
    refine ⟨newLeafVal, rfl, hnew, ?_, fun _ => rfl⟩
    rw [spliceAt_zero_full _ _ (by omega)]
  | cons p rest ih =>
    cases rootSpec with
    | scalar _ =>
      cases p <;> simp [resolveFieldPath] at hres
    | tuple fields size align =>
      cases p with
      | field idx fieldTy =>
        simp only [resolveFieldPath, Option.bind_eq_bind] at hres
        cases hf : fields[idx]? with
        | none => simp [hf] at hres
        | some pair =>
          obtain ⟨off, subSpec⟩ := pair
          simp only [hf, Option.bind_some] at hres
          cases hexp : specOfRigidTy layouts fieldTy.kind fieldTy.layoutIdx with
          | none => simp [hexp] at hres
          | some expectedSpec =>
            simp only [hexp, Option.bind_some] at hres
            by_cases heq : subSpec = expectedSpec
            · simp only [heq, ↓reduceIte] at hres
              cases hrest : resolveFieldPath layouts expectedSpec rest with
              | none => simp [hrest] at hres
              | some rpair =>
                obtain ⟨restOff, leafSpec'⟩ := rpair
                simp [hrest] at hres
                rcases hres with ⟨rfl, rfl⟩
                subst heq
                cases rootVal with
                | aggregate vIdx vals =>
                  cases vIdx with
                  | zero =>
                    simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
                    simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hval
                    obtain ⟨fv, hfv, hfvOk⟩ := TupleSpec.fieldsValOk_getElem? hval.2 hf
                    have hslice := TupleSpec.encodeFields_field_slice size align fields vals
                      (List.replicate size .Uninit) idx off subSpec fv hwf.2 (by simp) hf hfv
                    obtain ⟨hleafWf, hrestBound⟩ := resolveFieldPath_wf hslice.1 hrest
                    obtain ⟨newFv, hwrite, hnewFvOk, hnewFvEnc, hprojWrite⟩ :=
                      ih hslice.1 hfvOk hrest
                    have hidx_lt : idx < vals.length := (List.getElem?_eq_some_iff.mp hfv).1
                    refine ⟨.aggregate 0 (vals.set idx newFv), ?_, ?_, ?_, ?_⟩
                    · simp [writeFieldPath, hfv, hwrite]
                    · simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq,
                        List.length_set]
                      exact ⟨hval.1, TupleSpec.fieldsValOk_set hval.2 hf hnewFvOk⟩
                    · simp only [TupleSpec.encodeVal]
                      rw [TupleSpec.encodeFields_set size align fields vals
                        (List.replicate size .Uninit) idx off subSpec newFv hwf.2 (by simp) hval.1 hf,
                        hnewFvEnc, ← hslice.2.2.2.2]
                      have htotLen :
                          (TupleSpec.encodeFields fields vals (List.replicate size .Uninit)).length = size :=
                        TupleSpec.encodeFields_length size align fields vals
                          (List.replicate size .Uninit) hwf.2 (by simp)
                      have hleafLen : (leafSpec'.encodeVal newLeafVal).length = leafSpec'.size :=
                        TupleSpec.encodeVal_length leafSpec' newLeafVal hleafWf
                      have hoffBound : off + subSpec.size ≤ size := hslice.2.1
                      exact spliceAt_nested
                        (TupleSpec.encodeFields fields vals (List.replicate size .Uninit))
                        off subSpec.size restOff (leafSpec'.encodeVal newLeafVal)
                        (by omega) (by omega)
                    · intro locals
                      have hfv' : vals[idx] = fv :=
                        Option.some.inj (by rw [← hfv, List.getElem?_eq_getElem hidx_lt])
                      simp [MirSemantics.writeProjectedValue, Trusted.Sequence.get?,
                        Trusted.Sequence.set?, hidx_lt, hfv', hprojWrite locals]
                  | succ _ => simp [TupleSpec.valOk] at hval
                | _ => simp [TupleSpec.valOk] at hval
            · simp [heq] at hres
      | _ => simp [resolveFieldPath] at hres

theorem resolveFieldPath_ty {layouts : Layout.LayoutTable} {baseTy : MirAst.Ty}
    {rootSpec leafSpec : TupleSpec} {projs : List ProjectionElem} {totalOff : Nat}
    (hbase : specOfRigidTy layouts baseTy.kind baseTy.layoutIdx = some rootSpec)
    (hres : resolveFieldPath layouts rootSpec projs = some (totalOff, leafSpec)) :
    ∃ leafTy,
      resolveProjTy baseTy projs = some leafTy ∧
      MirSemantics.resolveProjectedTy layouts baseTy projs = some leafTy ∧
      specOfRigidTy layouts leafTy.kind leafTy.layoutIdx = some leafSpec := by
  induction projs generalizing baseTy rootSpec totalOff with
  | nil =>
    simp [resolveFieldPath] at hres
    rcases hres with ⟨rfl, rfl⟩
    exact ⟨baseTy, rfl, rfl, hbase⟩
  | cons p rest ih =>
    cases rootSpec with
    | scalar _ =>
      cases p <;> simp [resolveFieldPath] at hres
    | tuple fields size align =>
      cases p with
      | field idx fieldTy =>
        simp only [resolveFieldPath, Option.bind_eq_bind] at hres
        cases hf : fields[idx]? with
        | none => simp [hf] at hres
        | some pair =>
          obtain ⟨off, subSpec⟩ := pair
          simp only [hf, Option.bind_some] at hres
          cases hexp : specOfRigidTy layouts fieldTy.kind fieldTy.layoutIdx with
          | none => simp [hexp] at hres
          | some expectedSpec =>
            simp only [hexp, Option.bind_some] at hres
            by_cases heq : subSpec = expectedSpec
            · simp only [heq, ↓reduceIte] at hres
              cases hrest : resolveFieldPath layouts expectedSpec rest with
              | none => simp [hrest] at hres
              | some rpair =>
                obtain ⟨restOff, leafSpec'⟩ := rpair
                simp [hrest] at hres
                rcases hres with ⟨rfl, rfl⟩
                exact ih hexp hrest
            · simp [heq] at hres
      | _ => simp [resolveFieldPath] at hres

theorem intTypeOf_of_specOfRigidTy_scalar {layouts : Layout.LayoutTable} {ty : MirAst.Ty}
    {it : Gen.IntType} (h : specOfRigidTy layouts ty.kind ty.layoutIdx = some (.scalar it)) :
    intTypeOf ty = some it := by
  unfold specOfRigidTy at h
  split at h
  · next _ w hk =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s, n⟩, hb, heq⟩ := h
    cases heq
    unfold intTypeOf
    rw [hk]
    simp [hb]
  · next _ w hk =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s, n⟩, hb, heq⟩ := h
    cases heq
    unfold intTypeOf
    rw [hk]
    simp [hb]
  · next _ fieldKinds _ =>
    cases hl : layouts.lookup ty.layoutIdx with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · split at h <;> simp [Option.bind_eq_some_iff] at h
      · simp at h
  · next _ _ fieldKinds _ =>
    cases hl : layouts.lookup ty.layoutIdx with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · split at h <;> simp [Option.bind_eq_some_iff] at h
      · simp at h
  · simp at h

theorem specOfRigidTy_of_tupleTypeOf {layouts : Layout.LayoutTable} {ty : MirAst.Ty}
    {fields : List (Nat × TupleSpec)} {size align : Nat}
    (h : tupleTypeOf layouts ty = some (fields, size, align)) :
    specOfRigidTy layouts ty.kind ty.layoutIdx = some (.tuple fields size align) := by
  unfold tupleTypeOf at h
  cases hguard : isOrderingTy ty || (intBoolTupleOf ty).isSome with
  | true => simp [hguard] at h
  | false =>
    simp only [hguard, Bool.false_eq_true, ↓reduceIte] at h
    cases hk : ty.kind with
    | tuple _ | adt _ _ =>
      simp only [hk] at h
      cases hs : specOfRigidTy layouts ty.kind ty.layoutIdx with
      | none => rw [hk] at hs; simp [hs] at h
      | some s =>
        rw [hk] at hs
        cases s with
        | scalar _ => simp [hs] at h
        | tuple fs sz al =>
          simp [hs] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          exact hs
    | _ => simp [hk] at h

theorem goodAlignBytes_dvd {a b : Nat} (ha : goodAlignBytes a = true)
    (hb : goodAlignBytes b = true) (hle : a ≤ b) : a ∣ b := by
  simp only [goodAlignBytes, decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> omega

theorem TupleSpec.wf_align_good : ∀ (s : TupleSpec), s.wf = true → goodAlignBytes s.align = true
  | .scalar it, hwf => hwf
  | .tuple _ _ _, hwf => by
    simp only [TupleSpec.wf, Bool.and_eq_true] at hwf
    exact hwf.1.1.1

theorem resolveFieldPath_align {layouts : Layout.LayoutTable} {rootSpec leafSpec : TupleSpec}
    {projs : List ProjectionElem} {totalOff : Nat}
    (hwf : rootSpec.wf = true)
    (hres : resolveFieldPath layouts rootSpec projs = some (totalOff, leafSpec)) :
    leafSpec.align ∣ rootSpec.align ∧ leafSpec.align ∣ totalOff := by
  induction projs generalizing rootSpec totalOff with
  | nil =>
    simp [resolveFieldPath] at hres
    rcases hres with ⟨rfl, rfl⟩
    exact ⟨Nat.dvd_refl _, Nat.dvd_zero _⟩
  | cons p rest ih =>
    cases rootSpec with
    | scalar _ =>
      cases p <;> simp [resolveFieldPath] at hres
    | tuple fields size align =>
      cases p with
      | field idx fieldTy =>
        simp only [resolveFieldPath, Option.bind_eq_bind] at hres
        cases hf : fields[idx]? with
        | none => simp [hf] at hres
        | some pair =>
          obtain ⟨off, subSpec⟩ := pair
          simp only [hf, Option.bind_some] at hres
          cases hexp : specOfRigidTy layouts fieldTy.kind fieldTy.layoutIdx with
          | none => simp [hexp] at hres
          | some expectedSpec =>
            simp only [hexp, Option.bind_some] at hres
            by_cases heq : subSpec = expectedSpec
            · simp only [heq, ↓reduceIte] at hres
              cases hrest : resolveFieldPath layouts expectedSpec rest with
              | none => simp [hrest] at hres
              | some rpair =>
                obtain ⟨restOff, leafSpec'⟩ := rpair
                simp [hrest] at hres
                rcases hres with ⟨rfl, rfl⟩
                subst heq
                have hrootGood : goodAlignBytes align = true :=
                  TupleSpec.wf_align_good (.tuple fields size align) hwf
                simp only [TupleSpec.wf, Bool.and_eq_true] at hwf
                obtain ⟨hsubWf, _, hmod, hle⟩ := TupleSpec.fieldsWf_getElem? hwf.2 hf
                have hsubGood : goodAlignBytes subSpec.align = true :=
                  TupleSpec.wf_align_good subSpec hsubWf
                have hsubDvdRoot : subSpec.align ∣ align :=
                  goodAlignBytes_dvd hsubGood hrootGood hle
                have hsubDvdOff : subSpec.align ∣ off := Nat.dvd_of_mod_eq_zero hmod
                obtain ⟨hleafDvdSub, hleafDvdRest⟩ := ih hsubWf hrest
                exact ⟨Nat.dvd_trans hleafDvdSub hsubDvdRoot,
                  Nat.dvd_add (Nat.dvd_trans hleafDvdSub hsubDvdOff) hleafDvdRest⟩
            · simp [heq] at hres
      | _ => simp [resolveFieldPath] at hres

end MiniRustSpec.Correspondence



