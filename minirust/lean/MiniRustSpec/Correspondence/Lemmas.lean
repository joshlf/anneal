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
  cases hL : translateLocals body.layouts 0 body.localDecls with
  | none => simp [hL] at h
  | some L =>
    cases hB : translateBlocks body.layouts body.localDecls 0 body.basicBlocks with
    | none => simp [hL, hB] at h
    | some B =>
      simp [hL, hB] at h
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
  cases hL : translateLocals body.layouts 0 body.localDecls with
  | none => simp [hL] at h
  | some L =>
    cases hB : translateBlocks body.layouts body.localDecls 0 body.basicBlocks with
    | none => simp [hL, hB] at h
    | some B =>
      simp [hL, hB] at h
      subst h
      exact ⟨rfl, translateBlocks_append_get body.layouts body.localDecls 0 body.basicBlocks B hB
        body.basicBlocks.length (by omega) (initBlock body)⟩

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
