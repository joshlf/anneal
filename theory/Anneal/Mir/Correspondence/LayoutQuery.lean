/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/
import Trusted.Correspondence
import Anneal.Mir.Correspondence.Codec

/-!
# Demand-time `LayoutQuery` proofs for `Trusted.Correspondence`

Untrusted proofs about `Trusted.Correspondence.evalLayoutQuery`
(`proofs-rs/lean-miri#64`): single-source scalar consistency, fail-closed
out-of-bounds and dangling identifiers, prefix monotonicity, agreement with
eager materialization, totality of pointee queries on encoded programs, the
codec-driven resolution agreement (`refResolveTy_encode`), and
`refProgWellFormed_encodeProg`, together with a non-vacuity witness for
`ProgWellFormed`.
-/

namespace Anneal.Mir.Correspondence

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Correspondence

set_option linter.constructorNameAsVariable false

/-! ## Part 4 — Demand-time `LayoutQuery` hook -/

theorem nth?_eq_getElem? {α : Type} : ∀ (xs : List α) (i : Nat), nth? xs i = xs[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => by simp [nth?, nth?_eq_getElem? xs i]

/-- `nth? L.entries` *is* Trusted's `LayoutTable.lookup`. -/
theorem nth?_entries_eq_lookup (L : LayoutTable) (i : Nat) : nth? L.entries i = L.lookup i := by
  simp [LayoutTable.lookup, Trusted.Sequence.get?, nth?_eq_getElem?]

theorem nth?_map {α β : Type} (f : α → β) : ∀ (xs : List α) (i : Nat),
    nth? (xs.map f) i = (nth? xs i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => nth?_map f xs i

/-- Single-source consistency: a scalar answer is exactly the scalar
classification of the `localLayout` answer for the same `TyId`. -/
theorem layoutQuery_scalar_iff (tt : TypeTable) (L : LayoutTable) (t : TyId) (c : ScalarClass)
    (n : Nat) :
    evalLayoutQuery tt L (.scalarTypeClass t) = .ok (.scalar c n) ↔
      ∃ k l, evalLayoutQuery tt L (.localLayout t) = .ok (.layout k l) ∧
        scalarClassOfKind k = some c ∧ l.size.bytes = n := by
  simp only [evalLayoutQuery]
  cases h : tyLayout tt L t with
  | none => simp
  | some p =>
    obtain ⟨ty, l⟩ := p
    simp only
    cases hc : scalarClassOfKind ty.kind with
    | none =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨k, l', h1, h2, _⟩
      cases h1; rw [hc] at h2; cases h2
    | some c' =>
      constructor
      · intro e; cases e; exact ⟨ty.kind, l, rfl, hc, rfl⟩
      · rintro ⟨k, l', h1, h2, h3⟩
        cases h1; rw [hc] at h2; cases h2; subst h3; rfl

/-- Out-of-bounds `TyId`s fail closed. -/
theorem layoutQuery_oob_fails_closed (tt : TypeTable) (L : LayoutTable) (t : TyId)
    (h : tt.types.length ≤ t) :
    evalLayoutQuery tt L (.localLayout t) = .missingHook ∧
    evalLayoutQuery tt L (.scalarTypeClass t) = .missingHook ∧
    evalLayoutQuery tt L (.pointeeTypes t) = .missingHook ∧
    evalLayoutQuery tt L (.retagTypeShape t) = .missingHook := by
  have hn : nth? tt.types t = none := by
    rw [nth?_eq_getElem?]; exact List.getElem?_eq_none h
  simp [evalLayoutQuery, tyLayout, hn]

/-- Dangling `LayoutIdx`s fail closed. -/
theorem layoutQuery_dangling_layout_fails_closed (tt : TypeTable) (L : LayoutTable) (t : TyId)
    (ty : Ty) (h₁ : nth? tt.types t = some ty) (h₂ : L.entries.length ≤ ty.layoutIdx) :
    evalLayoutQuery tt L (.localLayout t) = .missingHook := by
  have hn : nth? L.entries ty.layoutIdx = none := by
    rw [nth?_eq_getElem?]; exact List.getElem?_eq_none h₂
  simp [evalLayoutQuery, tyLayout, h₁, hn]

/-- The zero-sized `()` built-in (pre-interned at `KindId 0`) has a 0-byte
layout in every encoded program, for every layout table. -/
theorem layoutQuery_zst_unit (p : V2026Prog) (L : LayoutTable) :
    ∃ l, evalLayoutQuery (encodeProg p).types L (.builtinLayout 0) = .ok (.layout (.tuple []) l) ∧
      l.size.bytes = 0 := by
  have h0 := (encodeProg_types_canonical p).2.2.2.2.1
  simp only [evalLayoutQuery, h0]
  exact ⟨_, rfl, rfl⟩

theorem tyLayout_extends {tt tt' : TypeTable} {L L' : LayoutTable}
    (ht : ∃ l, tt'.types = tt.types ++ l) (he : ∃ l, L'.entries = L.entries ++ l)
    (t : TyId) (r : Ty × TypeLayout) (hr : tyLayout tt L t = some r) :
    tyLayout tt' L' t = some r := by
  obtain ⟨lt, ht⟩ := ht
  obtain ⟨le, he⟩ := he
  unfold tyLayout at hr ⊢
  cases h1 : nth? tt.types t with
  | none => simp [h1] at hr
  | some ty =>
    simp only [h1] at hr
    have h1' : nth? tt'.types t = some ty := by rw [ht]; exact nth?_append_left lt h1
    simp only [h1']
    cases h2 : nth? L.entries ty.layoutIdx with
    | none => simp [h2] at hr
    | some l =>
      simp only [h2] at hr
      have h2' : nth? L'.entries ty.layoutIdx = some l := by rw [he]; exact nth?_append_left le h2
      simp only [h2']; exact hr

/-- Monotone table-extension / call-cone narrowing invariance: appending
types, kinds or layout entries (e.g. for additional callees) preserves every
successful answer on existing `TyId`s. -/
theorem layoutQuery_mono_prefix {tt tt' : TypeTable} {L L' : LayoutTable}
    (htt : tt.Extends tt') (hptr : L'.pointerBits = L.pointerBits)
    (hL : ∃ l, L'.entries = L.entries ++ l) (q : LayoutQuery) (a : LayoutAnswer)
    (h : evalLayoutQuery tt L q = .ok a) : evalLayoutQuery tt' L' q = .ok a := by
  have hty := tyLayout_extends htt.2 hL
  obtain ⟨⟨lk, hk⟩, ⟨lt, ht⟩⟩ := htt
  cases q with
  | localLayout t =>
    simp only [evalLayoutQuery] at h ⊢
    cases h1 : tyLayout tt L t with
    | none => simp [h1] at h
    | some r => simp only [h1] at h; simp only [hty t r h1]; exact h
  | scalarTypeClass t =>
    simp only [evalLayoutQuery] at h ⊢
    cases h1 : tyLayout tt L t with
    | none => simp [h1] at h
    | some r => simp only [h1] at h; simp only [hty t r h1]; exact h
  | castTypeInfo s d =>
    simp only [evalLayoutQuery] at h ⊢
    cases h1 : tyLayout tt L s with
    | none => simp [h1] at h
    | some r₁ =>
      cases h2 : tyLayout tt L d with
      | none => simp [h1, h2] at h
      | some r₂ => simp only [h1, h2] at h; simp only [hty s r₁ h1, hty d r₂ h2]; exact h
  | pointeeTypes t =>
    simp only [evalLayoutQuery] at h ⊢
    cases h1 : nth? tt.types t with
    | none => simp [h1] at h
    | some ty =>
      have h1' : nth? tt'.types t = some ty := by rw [ht]; exact nth?_append_left lt h1
      simp only [h1] at h; simp only [h1']
      have key : ∀ pk i, indexOf? rigidTyBEq tt.kinds pk = some i →
          indexOf? rigidTyBEq tt'.kinds pk = some i := by
        intro pk i hi
        rw [hk, indexOf?_append_of_mem rigidTyBEq_lawful lk
          (mem_of_nth? (nth?_of_indexOf? rigidTyBEq_lawful hi)), hi]
      generalize ty.kind = kd at h ⊢
      cases kd with
      | ref m pk =>
        simp only at h ⊢
        cases hi : indexOf? rigidTyBEq tt.kinds pk with
        | none => simp [hi] at h
        | some i => simp only [hi] at h; simp only [key pk i hi, hptr]; exact h
      | rawPtr m pk =>
        simp only at h ⊢
        cases hi : indexOf? rigidTyBEq tt.kinds pk with
        | none => simp [hi] at h
        | some i => simp only [hi] at h; simp only [key pk i hi, hptr]; exact h
      | _ => exact h
  | retagTypeShape t =>
    simp only [evalLayoutQuery] at h ⊢
    cases h1 : nth? tt.types t with
    | none => simp [h1] at h
    | some ty =>
      have h1' : nth? tt'.types t = some ty := by rw [ht]; exact nth?_append_left lt h1
      simp only [h1] at h; simp only [h1']; exact h
  | builtinLayout k =>
    simp only [evalLayoutQuery] at h ⊢
    cases h1 : nth? tt.kinds k with
    | none => simp [h1] at h
    | some kind =>
      have h1' : nth? tt'.kinds k = some kind := by rw [hk]; exact nth?_append_left lk h1
      simp only [h1] at h; simp only [h1', hptr]; exact h

/-- The demand-time `localLayout` hook refines the eager table pointwise. -/
theorem layoutQuery_agrees_with_eager (tt : TypeTable) (L : LayoutTable) (t : TyId) (k : RigidTy)
    (l : TypeLayout) :
    evalLayoutQuery tt L (.localLayout t) = .ok (.layout k l) ↔
      nth? (eagerLayoutTable tt L) t = some (some (k, l)) := by
  simp only [evalLayoutQuery, eagerLayoutTable, nth?_map, tyLayout]
  cases h1 : nth? tt.types t with
  | none => simp
  | some ty =>
    cases h2 : nth? L.entries ty.layoutIdx with
    | none => simp [h2]
    | some l' => simp [h2]

/-- `pointeeTypes` is total on every interned pointer `TyId` of an encoded
program (its pointee kind was interned bottom-up). -/
theorem layoutQuery_pointee_total (p : V2026Prog) (L : LayoutTable) (t : TyId) (ty : Ty)
    (m : Mutability) (pk : RigidTy) (h : nth? (encodeProg p).types.types t = some ty)
    (hk : ty.kind = .ref m pk ∨ ty.kind = .rawPtr m pk) :
    ∃ k, evalLayoutQuery (encodeProg p).types L (.pointeeTypes t) =
      .ok (.pointee k (pointeeLayoutOf L.pointerBits pk)) := by
  have hsub := (encodeProg_types_canonical p).2.2.2.1 ty (mem_of_nth? h)
  have hpk : pk ∈ (encodeProg p).types.kinds := by
    apply hsub
    rcases hk with hk | hk <;> rw [hk] <;> simp only [rigidTyPostorder] <;>
      exact List.mem_append_left _ (mem_rigidTyPostorder_self pk)
  obtain ⟨i, hi⟩ := indexOf?_isSome_of_mem rigidTyBEq_lawful hpk
  refine ⟨i, ?_⟩
  simp only [evalLayoutQuery, h]
  rcases hk with hk | hk <;> rw [hk] <;> simp only [hi]

/-! ## Codec-driven resolution of types -/

theorem refResolveTy_encode {tt : TypeTable} {ty : Ty} (L : LayoutTable) (h : ty ∈ tt.types) :
    refResolveTy tt L (encodeType tt ty) = annealResolveTy L ty := by
  have hd : nth? tt.types (encodeType tt ty) = some ty := decodeType_encodeType_of_mem h
  simp only [refResolveTy, evalLayoutQuery, tyLayout, hd, annealResolveTy]
  cases nth? L.entries ty.layoutIdx <;> rfl

/-- Every declared local type of `b` is interned. -/
abbrev DeclsCovered (tt : TypeTable) (b : CapturedMir) : Prop := ∀ d ∈ b.localDecls, d.ty ∈ tt.types

theorem encodeBody_layouts (tt : TypeTable) (b : CapturedMir) :
    (encodeBody tt b).layouts = b.layouts :=
  rfl

theorem nth?_encodeDecls (tt : TypeTable) (b : CapturedMir) (l : Nat) :
    nth? (encodeBody tt b).localDecls l = (nth? b.localDecls l).map (encodeLocalDecl tt) :=
  nth?_map _ _ _

/-- Every body of `p` is covered by the program table. -/
theorem encodeProg_body_covered (p : V2026Prog) (b : CapturedMir) (hb : b ∈ p.bodies) :
    Covers (collectProgTypes p) (bodyTys b) :=
  (collectProgTypes_covers p).flatMap b hb

theorem bodyCovered_decls {tt : TypeTable} {b : CapturedMir} (h : Covers tt (bodyTys b)) :
    DeclsCovered tt b :=
  fun d hdm => h.append.1 d.ty (List.mem_map.mpr ⟨d, hdm, rfl⟩)

theorem bodyCovered_block {tt : TypeTable} {b : CapturedMir} (h : Covers tt (bodyTys b))
    {bb : BasicBlockData} (hbb : bb ∈ b.basicBlocks) : Covers tt (blockTys bb) :=
  h.append.2.flatMap bb hbb

theorem encodeProg_bodies (p : V2026Prog) :
    (encodeProg p).bodies = p.bodies.map (encodeBody (collectProgTypes p)) := rfl

theorem encodeProg_types (p : V2026Prog) : (encodeProg p).types = collectProgTypes p := rfl

theorem encodeProg_entry (p : V2026Prog) : (encodeProg p).entry = p.entry := rfl

/-- On every type occurrence of every body, `M_ref`'s demand-time resolution of
the encoded `TyId` equals `M_anneal`'s deep resolution. -/
theorem encodeProg_refResolveTy_agrees (p : V2026Prog) (b : CapturedMir) (hb : b ∈ p.bodies) :
    ∀ ty ∈ bodyTys b,
      refResolveTy (encodeProg p).types b.layouts (encodeType (encodeProg p).types ty) =
        annealResolveTy b.layouts ty := by
  intro ty hty
  exact refResolveTy_encode b.layouts (encodeProg_body_covered p b hb ty hty)

/-- Encoding a well-formed `V2026Prog` produces a well-formed `RefProg`
(`WellFormed p → RefWellFormed (encodeProg p)`). -/
theorem refProgWellFormed_encodeProg (p : V2026Prog) (h : ProgWellFormed p) :
    RefProgWellFormed (encodeProg p) := by
  obtain ⟨hent, hb⟩ := h
  refine ⟨encodeProg_types_good p, ?_, ?_⟩
  · simp only [encodeProg_bodies, encodeProg_entry, List.length_map]; exact hent
  · intro rb hrb
    simp only [encodeProg_bodies, List.mem_map] at hrb
    obtain ⟨b, hbm, rfl⟩ := hrb
    obtain ⟨hph, _, hd⟩ := hb b hbm
    have hcov := bodyCovered_decls (encodeProg_body_covered p b hbm)
    refine ⟨hph, ?_⟩
    intro rd hrd
    simp only [encodeBody, List.mem_map] at hrd
    obtain ⟨d, hdm, rfl⟩ := hrd
    obtain ⟨⟨k, l⟩, hty⟩ := hd d hdm
    have href : refResolveTy (encodeProg p).types b.layouts (encodeType (collectProgTypes p) d.ty) =
        some (k, l) := by
      rw [encodeProg_types, refResolveTy_encode b.layouts (hcov d hdm), hty]
    simp only [refResolveTy] at href
    cases hq : evalLayoutQuery (encodeProg p).types b.layouts
        (.localLayout (encodeType (collectProgTypes p) d.ty)) with
    | missingHook => rw [hq] at href; cases href
    | blocked => rw [hq] at href; cases href
    | ok a =>
      rw [hq] at href
      cases a with
      | layout k' l' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at href
        obtain ⟨rfl, rfl⟩ := href
        exact ⟨_, _, hq⟩
      | _ => cases href

/-! ## Non-vacuity of `ProgWellFormed` -/

/-- A synthesized `u8` layout on `x86_64`. -/
def lqU8Layout : TypeLayout :=
  (pointeeLayoutOf 64 (.uint .u8)).getD
    { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory, fields := .primitive,
      variants := .single 0, isUninhabited := false }

/-- `fn lq() -> u8 { _0 = 7; return }` with one `u8` local. -/
def lqWitnessBody : CapturedMir :=
  { defPath := "lq", phase := .runtimePostCleanup, role := .subject, argCount := 0
    localDecls := [⟨.mut, ⟨.uint .u8, 0⟩, none⟩]
    basicBlocks := [⟨[⟨.assign ⟨0, []⟩ (.use (.constant ⟨⟨.uint .u8, 0⟩, .scalar (.int ⟨7, 1⟩)⟩)), ""⟩],
      ⟨.return_, ""⟩, false⟩]
    fnAbi := ⟨[], ⟨lqU8Layout, .ignore⟩, .rust, true⟩
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [lqU8Layout] }
    allocations := [] }

/-- The single-body witness program. -/
def lqWitnessProg : V2026Prog := ⟨[lqWitnessBody], 0⟩

/-- Non-vacuity witness for `ProgWellFormed` (and hence `RefProgWellFormed`). -/
theorem progWellFormed_nonvacuous :
    ∃ p : V2026Prog, ProgWellFormed p ∧ ∃ b ∈ p.bodies, b.localDecls ≠ [] ∧ b.basicBlocks ≠ [] := by
  refine ⟨lqWitnessProg, ⟨by decide, ?_⟩, lqWitnessBody, List.Mem.head _, by simp [lqWitnessBody],
    by simp [lqWitnessBody]⟩
  intro b hb
  simp only [lqWitnessProg, List.mem_singleton] at hb
  subst hb
  refine ⟨rfl, rfl, ?_⟩
  intro d hd
  simp only [lqWitnessBody, List.mem_singleton] at hd
  subst hd
  exact ⟨(.uint .u8, lqU8Layout), rfl⟩

theorem refProgWellFormed_nonvacuous :
    ProgWellFormed lqWitnessProg ∧ RefProgWellFormed (encodeProg lqWitnessProg) := by
  have hwf : ProgWellFormed lqWitnessProg := by
    refine ⟨by decide, ?_⟩
    intro b hb
    simp only [lqWitnessProg, List.mem_singleton] at hb
    subst hb
    refine ⟨rfl, rfl, ?_⟩
    intro d hd
    simp only [lqWitnessBody, List.mem_singleton] at hd
    subst hd
    exact ⟨(.uint .u8, lqU8Layout), rfl⟩
  exact ⟨hwf, refProgWellFormed_encodeProg lqWitnessProg hwf⟩

/-- **`LayoutQueryCorrespondenceClaim`** (proved here; restated in
`Anneal.Mir.Correspondence.Claims`). -/
theorem layoutQueryCorrespondenceClaim_proof : LayoutQueryCorrespondenceClaim :=
  ⟨refProgWellFormed_encodeProg,
   fun p b hb => encodeProg_refResolveTy_agrees p b hb,
   layoutQuery_oob_fails_closed,
   layoutQuery_dangling_layout_fails_closed,
   fun _ _ _ _ q a htt hptr hL h => layoutQuery_mono_prefix htt hptr hL q a h,
   layoutQuery_agrees_with_eager,
   layoutQuery_scalar_iff,
   layoutQuery_pointee_total,
   layoutQuery_zst_unit,
   progWellFormed_nonvacuous⟩

end Anneal.Mir.Correspondence
