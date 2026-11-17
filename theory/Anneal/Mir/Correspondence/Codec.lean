/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/
import Trusted.Correspondence

/-!
# Codec proofs for `Trusted.Correspondence`

Untrusted proofs about the type-interning codec defined in
`Trusted.Correspondence`:

* lawfulness of the structural Boolean equalities (`rigidTyBEq`, `tyBEq`,
  `defPathBEq`), proved without `Classical.choice`;
* the generic canonical interning library (`indexOf?`, `insertIfAbsent`,
  `insertAll`, `typesAreCanonical`) over any lawful Boolean equality;
* type-table invariants (`TypeTable.Good`, `TypeTable.Extends`);
* round trips for every syntax node, the headline zero-precondition codec
  theorems (`decodeProg_encodeProg`, `encodeProg_injective`,
  `encodeProg_types_canonical`, `encodeProg_traitImpl_kinds_interned`), and
  constructor-tag preservation (anti-laundering).
-/

namespace Anneal.Mir.Correspondence

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Correspondence

set_option linter.constructorNameAsVariable false

/-! ## Part 0 — Lawful structural Boolean equality -/

/-- A Boolean equality is lawful when it decides propositional equality. -/
def LawfulEq {α : Type} (eq : α → α → Bool) : Prop := ∀ a b, eq a b = true ↔ a = b

theorem uintTyEq_lawful : LawfulEq uintTyEq := by
  intro a b
  constructor
  · cases a <;> cases b <;> intro h <;> first | rfl | exact absurd h (by decide)
  · rintro rfl; cases a <;> rfl

theorem intTyEq_lawful : LawfulEq intTyEq := by
  intro a b
  constructor
  · cases a <;> cases b <;> intro h <;> first | rfl | exact absurd h (by decide)
  · rintro rfl; cases a <;> rfl

theorem floatTyEq_lawful : LawfulEq floatTyEq := by
  intro a b
  constructor
  · cases a <;> cases b <;> intro h <;> first | rfl | exact absurd h (by decide)
  · rintro rfl; cases a <;> rfl

theorem mutabilityEq_lawful : LawfulEq mutabilityEq := by
  intro a b
  constructor
  · cases a <;> cases b <;> intro h <;> first | rfl | exact absurd h (by decide)
  · rintro rfl; cases a <;> rfl

theorem safetyEq_lawful : LawfulEq safetyEq := by
  intro a b
  constructor
  · cases a <;> cases b <;> intro h <;> first | rfl | exact absurd h (by decide)
  · rintro rfl; cases a <;> rfl

theorem callConvBEq_lawful : LawfulEq callConvBEq := by
  intro a b
  constructor
  · cases a <;> cases b <;> intro h <;> simp_all [callConvBEq]
  · rintro rfl; cases a <;> simp [callConvBEq]

theorem defPathBEq_lawful : LawfulEq defPathBEq := by
  intro a b; simp [defPathBEq]

mutual
theorem rigidTyBEq_refl : (a : RigidTy) → rigidTyBEq a a = true
  | .param _ _ => by simp [rigidTyBEq]
  | .alias _ a => by simp [rigidTyBEq, rigidTyListBEq_refl a]
  | .bool => rfl
  | .char => rfl
  | .int w => by simp [rigidTyBEq, (intTyEq_lawful w w).2 rfl]
  | .uint w => by simp [rigidTyBEq, (uintTyEq_lawful w w).2 rfl]
  | .float w => by simp [rigidTyBEq, (floatTyEq_lawful w w).2 rfl]
  | .never => rfl
  | .str => rfl
  | .tuple a => by simp [rigidTyBEq, rigidTyListBEq_refl a]
  | .array e _ => by simp [rigidTyBEq, rigidTyBEq_refl e]
  | .slice e => by simp [rigidTyBEq, rigidTyBEq_refl e]
  | .ref m p => by simp [rigidTyBEq, rigidTyBEq_refl p, (mutabilityEq_lawful m m).2 rfl]
  | .rawPtr m p => by simp [rigidTyBEq, rigidTyBEq_refl p, (mutabilityEq_lawful m m).2 rfl]
  | .adt _ a => by simp [rigidTyBEq, rigidTyListBEq_refl a]
  | .fnDef _ a => by simp [rigidTyBEq, rigidTyListBEq_refl a]
  | .fnPtr i o s cc => by
    simp [rigidTyBEq, rigidTyListBEq_refl i, rigidTyBEq_refl o, (safetyEq_lawful s s).2 rfl,
      (callConvBEq_lawful cc cc).2 rfl]
  | .closure _ a => by simp [rigidTyBEq, rigidTyListBEq_refl a]
  | .dynamic _ => by simp [rigidTyBEq]
  | .foreign _ => by simp [rigidTyBEq]
  | .other _ => by simp [rigidTyBEq]
theorem rigidTyListBEq_refl : (as : List RigidTy) → rigidTyListBEq as as = true
  | [] => rfl
  | a :: as => by simp [rigidTyListBEq, rigidTyBEq_refl a, rigidTyListBEq_refl as]
end

mutual
theorem eq_of_rigidTyBEq : (a b : RigidTy) → rigidTyBEq a b = true → a = b
  | .param i n, b, h => by
    cases b <;> simp [rigidTyBEq] at h
    obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl
  | .alias p a, b, h => by
    cases b <;> simp [rigidTyBEq] at h
    case alias q b' => obtain ⟨h1, h2⟩ := h; subst h1; rw [eq_of_rigidTyListBEq a b' h2]
  | .bool, b, h => by cases b <;> simp [rigidTyBEq] at h ⊢
  | .char, b, h => by cases b <;> simp [rigidTyBEq] at h ⊢
  | .int w, b, h => by
    cases b <;> simp [rigidTyBEq] at h ⊢
    exact (intTyEq_lawful _ _).1 h
  | .uint w, b, h => by
    cases b <;> simp [rigidTyBEq] at h ⊢
    exact (uintTyEq_lawful _ _).1 h
  | .float w, b, h => by
    cases b <;> simp [rigidTyBEq] at h ⊢
    exact (floatTyEq_lawful _ _).1 h
  | .never, b, h => by cases b <;> simp [rigidTyBEq] at h ⊢
  | .str, b, h => by cases b <;> simp [rigidTyBEq] at h ⊢
  | .tuple a, b, h => by
    cases b <;> simp [rigidTyBEq] at h
    case tuple b' => rw [eq_of_rigidTyListBEq a b' h]
  | .array e n, b, h => by
    cases b <;> simp [rigidTyBEq] at h
    case array f m => obtain ⟨h1, h2⟩ := h; subst h2; rw [eq_of_rigidTyBEq e f h1]
  | .slice e, b, h => by
    cases b <;> simp [rigidTyBEq] at h
    case slice f => rw [eq_of_rigidTyBEq e f h]
  | .ref m p, b, h => by
    cases b <;> simp [rigidTyBEq] at h
    case ref n q =>
      obtain ⟨h1, h2⟩ := h
      rw [(mutabilityEq_lawful m n).1 h1, eq_of_rigidTyBEq p q h2]
  | .rawPtr m p, b, h => by
    cases b <;> simp [rigidTyBEq] at h
    case rawPtr n q =>
      obtain ⟨h1, h2⟩ := h
      rw [(mutabilityEq_lawful m n).1 h1, eq_of_rigidTyBEq p q h2]
  | .adt p a, b, h => by
    cases b <;> simp [rigidTyBEq] at h
    case adt q b' => obtain ⟨h1, h2⟩ := h; subst h1; rw [eq_of_rigidTyListBEq a b' h2]
  | .fnDef p a, b, h => by
    cases b <;> simp [rigidTyBEq] at h
    case fnDef q b' => obtain ⟨h1, h2⟩ := h; subst h1; rw [eq_of_rigidTyListBEq a b' h2]
  | .fnPtr i o s cc, b, h => by
    cases b <;> simp [rigidTyBEq] at h
    case fnPtr j p t dd =>
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      rw [eq_of_rigidTyListBEq i j h1, eq_of_rigidTyBEq o p h2, (safetyEq_lawful s t).1 h3,
        (callConvBEq_lawful cc dd).1 h4]
  | .closure p a, b, h => by
    cases b <;> simp [rigidTyBEq] at h
    case closure q b' => obtain ⟨h1, h2⟩ := h; subst h1; rw [eq_of_rigidTyListBEq a b' h2]
  | .dynamic p, b, h => by cases b <;> simp [rigidTyBEq] at h ⊢; exact h
  | .foreign p, b, h => by cases b <;> simp [rigidTyBEq] at h ⊢; exact h
  | .other r, b, h => by cases b <;> simp [rigidTyBEq] at h ⊢; exact h
theorem eq_of_rigidTyListBEq : (as bs : List RigidTy) → rigidTyListBEq as bs = true → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [rigidTyListBEq] at h
  | _ :: _, [], h => by simp [rigidTyListBEq] at h
  | a :: as, b :: bs, h => by
    simp [rigidTyListBEq] at h
    rw [eq_of_rigidTyBEq a b h.1, eq_of_rigidTyListBEq as bs h.2]
end

theorem rigidTyBEq_lawful : LawfulEq rigidTyBEq := fun a b =>
  ⟨eq_of_rigidTyBEq a b, fun h => h ▸ rigidTyBEq_refl a⟩

theorem tyBEq_lawful : LawfulEq tyBEq := by
  intro a b
  obtain ⟨k₁, l₁⟩ := a
  obtain ⟨k₂, l₂⟩ := b
  simp only [tyBEq, Bool.and_eq_true, decide_eq_true_eq, Ty.mk.injEq]
  rw [rigidTyBEq_lawful]

/-! ## Part 1 — Generic canonical interning library -/

theorem nth?_append_left {α : Type} : ∀ {xs : List α} {i : Nat} {a : α} (l : List α),
    nth? xs i = some a → nth? (xs ++ l) i = some a
  | [], _, _, _, h => by simp [nth?] at h
  | x :: xs, 0, a, l, h => by simpa [nth?] using h
  | x :: xs, i + 1, a, l, h => by simp [nth?] at h ⊢; exact nth?_append_left l h

theorem mem_of_nth? {α : Type} : ∀ {ys : List α} {k : Nat} {b : α}, nth? ys k = some b → b ∈ ys
  | [], _, _, h => by simp [nth?] at h
  | y :: ys, 0, b, h => by simp [nth?] at h; subst h; exact List.Mem.head _
  | y :: ys, k + 1, b, h => by simp [nth?] at h; exact List.Mem.tail _ (mem_of_nth? h)

theorem decodeList_map {α β : Type} (f : β → Option α) (g : α → β) :
    ∀ (xs : List α), (∀ x ∈ xs, f (g x) = some x) → decodeList f (xs.map g) = some xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map, decodeList]
    rw [h x (List.Mem.head _), decodeList_map f g xs (fun y hy => h y (List.Mem.tail _ hy))]

section Intern

variable {α : Type} {eq : α → α → Bool}

theorem nth?_of_indexOf? (heq : LawfulEq eq) : ∀ {xs : List α} {a : α} {i : Nat},
    indexOf? eq xs a = some i → nth? xs i = some a
  | [], _, _, h => by simp [indexOf?] at h
  | x :: xs, a, i, h => by
    cases hx : eq x a with
    | true =>
      simp only [indexOf?, hx, Option.some.injEq] at h
      subst h
      simp [nth?, (heq x a).1 hx]
    | false =>
      simp only [indexOf?, hx] at h
      cases hj : indexOf? eq xs a with
      | none => rw [hj] at h; cases h
      | some j =>
        rw [hj] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp [nth?, nth?_of_indexOf? heq hj]

theorem indexOf?_isSome_of_mem (heq : LawfulEq eq) : ∀ {xs : List α} {a : α}, a ∈ xs →
    ∃ i, indexOf? eq xs a = some i
  | [], _, h => by cases h
  | x :: xs, a, h => by
    cases hx : eq x a with
    | true => exact ⟨0, by simp [indexOf?, hx]⟩
    | false =>
      have hne : x ≠ a := fun e => by rw [(heq x a).2 e] at hx; cases hx
      have hm : a ∈ xs := by
        cases h with
        | head => exact absurd rfl hne
        | tail _ h' => exact h'
      obtain ⟨i, hi⟩ := indexOf?_isSome_of_mem heq hm
      exact ⟨i + 1, by simp [indexOf?, hx, hi]⟩

theorem indexOf?_eq_none_of_not_mem (heq : LawfulEq eq) : ∀ {xs : List α} {a : α}, a ∉ xs →
    indexOf? eq xs a = none
  | [], _, _ => rfl
  | x :: xs, a, h => by
    have hx : eq x a = false := by
      cases hc : eq x a with
      | false => rfl
      | true => exact absurd ((heq x a).1 hc ▸ List.Mem.head _) h
    have hm : a ∉ xs := fun m => h (List.Mem.tail _ m)
    simp [indexOf?, hx, indexOf?_eq_none_of_not_mem heq hm]

theorem not_mem_of_indexOf?_eq_none (heq : LawfulEq eq) {xs : List α} {a : α}
    (h : indexOf? eq xs a = none) : a ∉ xs := by
  intro hm
  obtain ⟨i, hi⟩ := indexOf?_isSome_of_mem heq hm
  rw [h] at hi; cases hi

theorem nth?_lookupId_of_mem (heq : LawfulEq eq) {xs : List α} {a : α} (h : a ∈ xs) :
    nth? xs (lookupId eq xs a) = some a := by
  obtain ⟨i, hi⟩ := indexOf?_isSome_of_mem heq h
  simp [lookupId, hi, nth?_of_indexOf? heq hi]

theorem mem_insertIfAbsent (heq : LawfulEq eq) : ∀ {a b : α} {xs : List α},
    b ∈ insertIfAbsent eq a xs ↔ b = a ∨ b ∈ xs
  | a, b, [] => by simp [insertIfAbsent]
  | a, b, x :: xs => by
    cases hx : eq x a with
    | true =>
      have e : x = a := (heq x a).1 hx
      subst e
      simp only [insertIfAbsent, hx]
      constructor
      · intro h; exact Or.inr h
      · intro h
        cases h with
        | inl h => subst h; exact List.Mem.head _
        | inr h => exact h
    | false =>
      simp only [insertIfAbsent, hx, List.mem_cons]
      rw [mem_insertIfAbsent heq]
      constructor
      · intro h; rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · intro h; rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem mem_insertIfAbsent_self (heq : LawfulEq eq) (a : α) (xs : List α) :
    a ∈ insertIfAbsent eq a xs :=
  (mem_insertIfAbsent heq).mpr (Or.inl rfl)

theorem mem_insertIfAbsent_of_mem (heq : LawfulEq eq) {a b : α} {xs : List α} (h : b ∈ xs) :
    b ∈ insertIfAbsent eq a xs :=
  (mem_insertIfAbsent heq).mpr (Or.inr h)

theorem insertIfAbsent_prefix : ∀ (a : α) (xs : List α), ∃ l, insertIfAbsent eq a xs = xs ++ l
  | a, [] => ⟨[a], rfl⟩
  | a, x :: xs => by
    cases hx : eq x a with
    | true => exact ⟨[], by simp [insertIfAbsent, hx]⟩
    | false =>
      obtain ⟨l, hl⟩ := insertIfAbsent_prefix a xs
      exact ⟨l, by simp [insertIfAbsent, hx, hl]⟩

theorem canonical_insertIfAbsent (heq : LawfulEq eq) : ∀ (a : α) (xs : List α),
    typesAreCanonical eq xs = true → typesAreCanonical eq (insertIfAbsent eq a xs) = true
  | a, [], _ => by simp [insertIfAbsent, typesAreCanonical, indexOf?]
  | a, x :: xs, h => by
    cases hx : eq x a with
    | true => simpa [insertIfAbsent, hx] using h
    | false =>
      simp only [insertIfAbsent, hx]
      simp only [typesAreCanonical, Bool.and_eq_true, Option.isNone_iff_eq_none] at h ⊢
      refine ⟨?_, canonical_insertIfAbsent heq a xs h.2⟩
      apply indexOf?_eq_none_of_not_mem heq
      intro hm
      rcases (mem_insertIfAbsent heq).mp hm with h' | h'
      · subst h'; rw [(heq x x).2 rfl] at hx; cases hx
      · exact not_mem_of_indexOf?_eq_none heq h.1 h'

theorem mem_insertAll (heq : LawfulEq eq) : ∀ {acc ys : List α} {b : α},
    b ∈ insertAll eq acc ys ↔ b ∈ acc ∨ b ∈ ys
  | acc, [], b => by simp [insertAll]
  | acc, y :: ys, b => by
    simp only [insertAll]
    rw [mem_insertAll heq, mem_insertIfAbsent heq]
    simp only [List.mem_cons]
    constructor
    · intro h; rcases h with (h | h) | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · intro h; rcases h with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

theorem insertAll_prefix : ∀ (acc ys : List α), ∃ l, insertAll eq acc ys = acc ++ l
  | acc, [] => ⟨[], by simp [insertAll]⟩
  | acc, y :: ys => by
    obtain ⟨l₁, h₁⟩ := insertIfAbsent_prefix (eq := eq) y acc
    obtain ⟨l₂, h₂⟩ := insertAll_prefix (insertIfAbsent eq y acc) ys
    exact ⟨l₁ ++ l₂, by simp only [insertAll]; rw [h₂, h₁, List.append_assoc]⟩

theorem canonical_insertAll (heq : LawfulEq eq) : ∀ (acc ys : List α),
    typesAreCanonical eq acc = true → typesAreCanonical eq (insertAll eq acc ys) = true
  | _, [], h => h
  | acc, y :: ys, h => canonical_insertAll heq _ ys (canonical_insertIfAbsent heq y acc h)

theorem indexOf?_append_of_mem (heq : LawfulEq eq) : ∀ {xs : List α} {a : α} (l : List α),
    a ∈ xs → indexOf? eq (xs ++ l) a = indexOf? eq xs a
  | [], _, _, h => by cases h
  | x :: xs, a, l, h => by
    cases hx : eq x a with
    | true => simp [indexOf?, hx]
    | false =>
      have hne : x ≠ a := fun e => by rw [(heq x a).2 e] at hx; cases hx
      have hm : a ∈ xs := by
        cases h with
        | head => exact absurd rfl hne
        | tail _ h' => exact h'
      simp [indexOf?, hx, indexOf?_append_of_mem heq l hm]

/-- In a canonical list, equal entries sit at equal indices. -/
theorem nth?_injective_of_canonical (heq : LawfulEq eq) : ∀ {xs : List α} {i j : Nat} {a : α},
    typesAreCanonical eq xs = true → nth? xs i = some a → nth? xs j = some a → i = j
  | [], _, _, _, _, h, _ => by simp [nth?] at h
  | x :: xs, 0, 0, _, _, _, _ => rfl
  | x :: xs, 0, j + 1, a, hc, hi, hj => by
    simp only [typesAreCanonical, Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
    simp [nth?] at hi hj; subst hi
    exact absurd (mem_of_nth? hj) (not_mem_of_indexOf?_eq_none heq hc.1)
  | x :: xs, i + 1, 0, a, hc, hi, hj => by
    simp only [typesAreCanonical, Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
    simp [nth?] at hi hj; subst hj
    exact absurd (mem_of_nth? hi) (not_mem_of_indexOf?_eq_none heq hc.1)
  | x :: xs, i + 1, j + 1, a, hc, hi, hj => by
    simp only [typesAreCanonical, Bool.and_eq_true] at hc
    simp [nth?] at hi hj
    rw [nth?_injective_of_canonical heq hc.2 hi hj]

end Intern

/-! ## Part 2 — Type tables and bottom-up (post-order) kind interning -/

/-- Immediate structural children of a kind (every `RigidTy` constructor). -/
def rigidTyChildren : RigidTy → List RigidTy
  | .alias _ a => a
  | .tuple a => a
  | .array e _ => [e]
  | .slice e => [e]
  | .ref _ p => [p]
  | .rawPtr _ p => [p]
  | .adt _ a => a
  | .fnDef _ a => a
  | .fnPtr i o _ _ => i ++ [o]
  | .closure _ a => a
  | _ => []

theorem mem_rigidTyPostorder_self (k : RigidTy) : k ∈ rigidTyPostorder k := by
  cases k <;> simp [rigidTyPostorder]

theorem mem_rigidTyPostorderList_of_mem : ∀ {c : RigidTy} {cs : List RigidTy},
    c ∈ cs → c ∈ rigidTyPostorderList cs
  | _, [], h => by cases h
  | c, k :: ks, h => by
    simp only [rigidTyPostorderList, List.mem_append]
    cases h with
    | head => exact Or.inl (mem_rigidTyPostorder_self _)
    | tail _ h' => exact Or.inr (mem_rigidTyPostorderList_of_mem h')

/-- Every immediate child of `k` occurs (strictly before `k`) in its post-order. -/
theorem rigidTyChildren_mem_postorder (k : RigidTy) :
    ∀ c ∈ rigidTyChildren k, c ∈ rigidTyPostorder k := by
  intro c hc
  cases k with
  | alias p a =>
    simp only [rigidTyPostorder]; exact List.mem_append_left _ (mem_rigidTyPostorderList_of_mem hc)
  | tuple a =>
    simp only [rigidTyPostorder]; exact List.mem_append_left _ (mem_rigidTyPostorderList_of_mem hc)
  | adt p a =>
    simp only [rigidTyPostorder]; exact List.mem_append_left _ (mem_rigidTyPostorderList_of_mem hc)
  | fnDef p a =>
    simp only [rigidTyPostorder]; exact List.mem_append_left _ (mem_rigidTyPostorderList_of_mem hc)
  | closure p a =>
    simp only [rigidTyPostorder]; exact List.mem_append_left _ (mem_rigidTyPostorderList_of_mem hc)
  | array e n =>
    simp only [rigidTyChildren, List.mem_singleton] at hc; subst hc
    simp only [rigidTyPostorder]; exact List.mem_append_left _ (mem_rigidTyPostorder_self _)
  | slice e =>
    simp only [rigidTyChildren, List.mem_singleton] at hc; subst hc
    simp only [rigidTyPostorder]; exact List.mem_append_left _ (mem_rigidTyPostorder_self _)
  | ref m e =>
    simp only [rigidTyChildren, List.mem_singleton] at hc; subst hc
    simp only [rigidTyPostorder]; exact List.mem_append_left _ (mem_rigidTyPostorder_self _)
  | rawPtr m e =>
    simp only [rigidTyChildren, List.mem_singleton] at hc; subst hc
    simp only [rigidTyPostorder]; exact List.mem_append_left _ (mem_rigidTyPostorder_self _)
  | fnPtr i o s cc =>
    simp only [rigidTyChildren, List.mem_append, List.mem_singleton] at hc
    simp only [rigidTyPostorder]
    rcases hc with hc | hc
    · exact List.mem_append_left _ (List.mem_append_left _ (mem_rigidTyPostorderList_of_mem hc))
    · subst hc; exact List.mem_append_left _ (List.mem_append_right _ (mem_rigidTyPostorder_self _))
  | param _ _ => simp [rigidTyChildren] at hc
  | bool => simp [rigidTyChildren] at hc
  | char => simp [rigidTyChildren] at hc
  | int _ => simp [rigidTyChildren] at hc
  | uint _ => simp [rigidTyChildren] at hc
  | float _ => simp [rigidTyChildren] at hc
  | never => simp [rigidTyChildren] at hc
  | str => simp [rigidTyChildren] at hc
  | dynamic _ => simp [rigidTyChildren] at hc
  | foreign _ => simp [rigidTyChildren] at hc
  | other _ => simp [rigidTyChildren] at hc

theorem extends_refl (tt : TypeTable) : tt.Extends tt :=
  ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩

theorem extends_trans {a b c : TypeTable} (h₁ : a.Extends b) (h₂ : b.Extends c) :
    a.Extends c := by
  obtain ⟨⟨l₁, k₁⟩, ⟨m₁, t₁⟩⟩ := h₁
  obtain ⟨⟨l₂, k₂⟩, ⟨m₂, t₂⟩⟩ := h₂
  exact ⟨⟨l₁ ++ l₂, by rw [k₂, k₁, List.append_assoc]⟩, ⟨m₁ ++ m₂, by rw [t₂, t₁, List.append_assoc]⟩⟩

theorem extends_types_mem {a b : TypeTable} (h : a.Extends b) {ty : Ty}
    (hm : ty ∈ a.types) : ty ∈ b.types := by
  obtain ⟨_, ⟨l, hl⟩⟩ := h; rw [hl]; exact List.mem_append_left _ hm

theorem extends_kinds_mem {a b : TypeTable} (h : a.Extends b) {k : RigidTy}
    (hm : k ∈ a.kinds) : k ∈ b.kinds := by
  obtain ⟨⟨l, hl⟩, _⟩ := h; rw [hl]; exact List.mem_append_left _ hm

theorem internTy_extends (tt : TypeTable) (ty : Ty) : tt.Extends (internTy tt ty) :=
  ⟨insertAll_prefix _ _, insertIfAbsent_prefix _ _⟩

theorem internTys_extends : ∀ (tt : TypeTable) (tys : List Ty), tt.Extends (internTys tt tys)
  | tt, [] => extends_refl tt
  | tt, ty :: tys => extends_trans (internTy_extends tt ty) (internTys_extends _ tys)

theorem mem_internTys : ∀ {tt : TypeTable} {tys : List Ty} {ty : Ty},
    ty ∈ tys → ty ∈ (internTys tt tys).types
  | _, [], _, h => by cases h
  | tt, t :: tys, ty, h => by
    simp only [internTys]
    cases h with
    | head => exact extends_types_mem (internTys_extends _ tys) (mem_insertIfAbsent_self tyBEq_lawful _ _)
    | tail _ h' => exact mem_internTys h'

theorem initTypeTable_good : initTypeTable.Good := by
  refine ⟨by decide, rfl, ?_⟩
  intro ty h; cases h

theorem internTy_good {tt : TypeTable} (h : tt.Good) (ty : Ty) : (internTy tt ty).Good := by
  obtain ⟨hk, ht, hc⟩ := h
  refine ⟨canonical_insertAll rigidTyBEq_lawful _ _ hk,
    canonical_insertIfAbsent tyBEq_lawful _ _ ht, ?_⟩
  intro t htm x hx
  simp only [internTy] at htm ⊢
  rcases (mem_insertIfAbsent tyBEq_lawful).mp htm with e | e
  · subst e; exact (mem_insertAll rigidTyBEq_lawful).mpr (Or.inr hx)
  · exact (mem_insertAll rigidTyBEq_lawful).mpr (Or.inl (hc t e hx))

theorem internTys_good : ∀ {tt : TypeTable} (_ : tt.Good) (tys : List Ty), (internTys tt tys).Good
  | _, h, [] => h
  | _, h, ty :: tys => internTys_good (internTy_good h ty) tys

theorem internKinds_extends (tt : TypeTable) (ks : List RigidTy) :
    tt.Extends (internKinds tt ks) :=
  ⟨insertAll_prefix _ _, ⟨[], by simp [internKinds]⟩⟩

theorem internKinds_good {tt : TypeTable} (h : tt.Good) (ks : List RigidTy) :
    (internKinds tt ks).Good := by
  obtain ⟨hk, ht, hc⟩ := h
  refine ⟨canonical_insertAll rigidTyBEq_lawful _ _ hk, ht, ?_⟩
  intro t htm x hx
  exact (mem_insertAll rigidTyBEq_lawful).mpr (Or.inl (hc t htm hx))

theorem rigidTyPostorder_sub_postorderList : ∀ {k : RigidTy} {ks : List RigidTy},
    k ∈ ks → rigidTyPostorder k ⊆ rigidTyPostorderList ks
  | _, [], h => by cases h
  | _, _ :: ks, h => by
    intro x hx
    simp only [rigidTyPostorderList, List.mem_append]
    cases h with
    | head => exact Or.inl hx
    | tail _ h' => exact Or.inr (rigidTyPostorder_sub_postorderList h' hx)

theorem mem_internKinds_postorder {tt : TypeTable} {ks : List RigidTy} {k : RigidTy}
    (hk : k ∈ ks) : rigidTyPostorder k ⊆ (internKinds tt ks).kinds := by
  intro x hx
  exact (mem_insertAll rigidTyBEq_lawful).mpr (Or.inr (rigidTyPostorder_sub_postorderList hk hx))

/-! ### `Ty` ↔ `TyId` -/

theorem decodeType_encodeType_of_mem {tt : TypeTable} {ty : Ty} (h : ty ∈ tt.types) :
    decodeType tt (encodeType tt ty) = some ty :=
  nth?_lookupId_of_mem tyBEq_lawful h

/-- **Unconditional** `Ty` round trip: decoding against any table that has
interned `ty` recovers `ty`. -/
theorem decodeType_encodeType (tt : TypeTable) (ty : Ty) :
    decodeType (internTy tt ty) (encodeType (internTy tt ty) ty) = some ty :=
  decodeType_encodeType_of_mem (mem_insertIfAbsent_self tyBEq_lawful _ _)

/-! ## Part 3 — Round trips for every syntax node -/

/-- All `Ty` occurrences of a node are interned in `tt`. -/
abbrev Covers (tt : TypeTable) (tys : List Ty) : Prop := ∀ ty ∈ tys, ty ∈ tt.types

theorem Covers.append {tt : TypeTable} {a b : List Ty} (h : Covers tt (a ++ b)) :
    Covers tt a ∧ Covers tt b :=
  ⟨fun ty hy => h ty (List.mem_append_left _ hy), fun ty hy => h ty (List.mem_append_right _ hy)⟩

theorem Covers.flatMap {β : Type} {tt : TypeTable} {f : β → List Ty} {xs : List β}
    (h : Covers tt (xs.flatMap f)) : ∀ x ∈ xs, Covers tt (f x) :=
  fun x hx ty hy => h ty (List.mem_flatMap.mpr ⟨x, hx, hy⟩)

theorem Covers.single {tt : TypeTable} {ty : Ty} (h : Covers tt [ty]) : ty ∈ tt.types :=
  h ty (List.Mem.head _)

theorem roundtrip_projElem {tt : TypeTable} (e : ProjectionElem) (h : Covers tt (projElemTys e)) :
    decodeProjElem tt (encodeProjElem tt e) = some e := by
  cases e <;> simp only [encodeProjElem, decodeProjElem, projElemTys] at h ⊢
  all_goals first
    | rfl
    | rw [decodeType_encodeType_of_mem h.single]; rfl

theorem roundtrip_place {tt : TypeTable} (p : Place) (h : Covers tt (placeTys p)) :
    decodePlace tt (encodePlace tt p) = some p := by
  simp only [encodePlace, decodePlace]
  rw [decodeList_map _ _ _ (fun e he => roundtrip_projElem e (h.flatMap e he))]
  rfl

theorem roundtrip_operand {tt : TypeTable} (op : Operand) (h : Covers tt (operandTys op)) :
    decodeOperand tt (encodeOperand tt op) = some op := by
  cases op <;> simp only [encodeOperand, decodeOperand, operandTys] at h ⊢
  · rw [roundtrip_place _ h]; rfl
  · rw [roundtrip_place _ h]; rfl
  · rw [decodeType_encodeType_of_mem h.single]; rfl

theorem roundtrip_operands {tt : TypeTable} (ops : List Operand)
    (h : Covers tt (ops.flatMap operandTys)) :
    decodeList (decodeOperand tt) (ops.map (encodeOperand tt)) = some ops :=
  decodeList_map _ _ _ (fun o ho => roundtrip_operand o (h.flatMap o ho))

theorem roundtrip_aggKind {tt : TypeTable} (k : AggregateKind) (h : Covers tt (aggKindTys k)) :
    decodeAggKind tt (encodeAggKind tt k) = some k := by
  cases k <;> simp only [encodeAggKind, decodeAggKind, aggKindTys] at h ⊢
  all_goals first
    | rfl
    | rw [decodeType_encodeType_of_mem h.single]; rfl

theorem roundtrip_rvalue {tt : TypeTable} (rv : Rvalue) (h : Covers tt (rvalueTys rv)) :
    decodeRvalue tt (encodeRvalue tt rv) = some rv := by
  cases rv <;> simp only [encodeRvalue, decodeRvalue, rvalueTys] at h ⊢
  case use op => rw [roundtrip_operand op h]; rfl
  case «repeat» op n => rw [roundtrip_operand op h]; rfl
  case ref bk p => rw [roundtrip_place p h]; rfl
  case rawPtr m p => rw [roundtrip_place p h]; rfl
  case len p => rw [roundtrip_place p h]; rfl
  case cast k op t =>
    rw [roundtrip_operand op h.append.1, decodeType_encodeType_of_mem h.append.2.single]; rfl
  case binaryOp o l r =>
    rw [roundtrip_operand l h.append.1, roundtrip_operand r h.append.2]; rfl
  case nullaryOp o t => rw [decodeType_encodeType_of_mem h.single]; rfl
  case unaryOp o op => rw [roundtrip_operand op h]; rfl
  case discriminant p => rw [roundtrip_place p h]; rfl
  case aggregate k ops =>
    rw [roundtrip_aggKind k h.append.1, roundtrip_operands ops h.append.2]; rfl
  case shallowInitBox op t =>
    rw [roundtrip_operand op h.append.1, decodeType_encodeType_of_mem h.append.2.single]; rfl
  case copyForDeref p => rw [roundtrip_place p h]; rfl
  case wrapUnsafeBinder op t =>
    rw [roundtrip_operand op h.append.1, decodeType_encodeType_of_mem h.append.2.single]; rfl
  all_goals rfl

theorem roundtrip_intrinsic {tt : TypeTable} (i : NonDivergingIntrinsic)
    (h : Covers tt (intrinsicTys i)) : decodeIntrinsic tt (encodeIntrinsic tt i) = some i := by
  cases i <;> simp only [encodeIntrinsic, decodeIntrinsic, intrinsicTys] at h ⊢
  case assume op => rw [roundtrip_operand op h]; rfl
  case copyNonOverlapping a b c =>
    rw [roundtrip_operand a h.append.1.append.1, roundtrip_operand b h.append.1.append.2,
      roundtrip_operand c h.append.2]; rfl

theorem roundtrip_stmtKind {tt : TypeTable} (k : StatementKind) (h : Covers tt (stmtKindTys k)) :
    decodeStmtKind tt (encodeStmtKind tt k) = some k := by
  cases k <;> simp only [encodeStmtKind, decodeStmtKind, stmtKindTys] at h ⊢
  case assign p rv => rw [roundtrip_place p h.append.1, roundtrip_rvalue rv h.append.2]; rfl
  case setDiscriminant p v => rw [roundtrip_place p h]; rfl
  case deinit p => rw [roundtrip_place p h]; rfl
  case retag k p => rw [roundtrip_place p h]; rfl
  case placeMention p => rw [roundtrip_place p h]; rfl
  case intrinsic i => rw [roundtrip_intrinsic i h]; rfl
  case backwardIncompatibleDropHint p => rw [roundtrip_place p h]; rfl
  all_goals rfl

theorem roundtrip_stmt {tt : TypeTable} (s : Statement) (h : Covers tt (stmtTys s)) :
    decodeStmt tt (encodeStmt tt s) = some s := by
  simp only [encodeStmt, decodeStmt]; rw [roundtrip_stmtKind s.kind h]; rfl

theorem roundtrip_termKind {tt : TypeTable} (k : TerminatorKind) (h : Covers tt (termKindTys k)) :
    decodeTermKind tt (encodeTermKind tt k) = some k := by
  cases k <;> simp only [encodeTermKind, decodeTermKind, termKindTys] at h ⊢
  case switchInt d ts => rw [roundtrip_operand d h]; rfl
  case drop p t u => rw [roundtrip_place p h]; rfl
  case call f args d t u =>
    rw [roundtrip_operand f h.append.1.append.1, roundtrip_operands args h.append.1.append.2,
      roundtrip_place d h.append.2]; rfl
  case tailCall f args =>
    rw [roundtrip_operand f h.append.1, roundtrip_operands args h.append.2]; rfl
  case assert c e t u => rw [roundtrip_operand c h]; rfl
  all_goals rfl

theorem roundtrip_terminator {tt : TypeTable} (t : Terminator) (h : Covers tt (termKindTys t.kind)) :
    decodeTerminator tt (encodeTerminator tt t) = some t := by
  simp only [encodeTerminator, decodeTerminator]; rw [roundtrip_termKind t.kind h]; rfl

theorem roundtrip_block {tt : TypeTable} (b : BasicBlockData) (h : Covers tt (blockTys b)) :
    decodeBlock tt (encodeBlock tt b) = some b := by
  simp only [encodeBlock, decodeBlock, blockTys] at h ⊢
  rw [decodeList_map _ _ _ (fun s hs => roundtrip_stmt s (h.append.1.flatMap s hs)),
    roundtrip_terminator _ h.append.2]
  rfl

theorem roundtrip_body {tt : TypeTable} (b : CapturedMir) (h : Covers tt (bodyTys b)) :
    decodeBody tt (encodeBody tt b) = some b := by
  simp only [encodeBody, decodeBody, bodyTys] at h ⊢
  have hd : decodeList (decodeLocalDecl tt) (b.localDecls.map (encodeLocalDecl tt)) =
      some b.localDecls := by
    apply decodeList_map
    intro d hdm
    have : d.ty ∈ tt.types := h.append.1 d.ty (List.mem_map.mpr ⟨d, hdm, rfl⟩)
    simp only [encodeLocalDecl, decodeLocalDecl]
    rw [decodeType_encodeType_of_mem this]; rfl
  rw [hd, decodeList_map _ _ _ (fun bb hb => roundtrip_block bb (h.append.2.flatMap bb hb))]
  rfl

/-! ### Headline codec theorems (zero preconditions) -/

/-- The program table interns every `Ty` occurrence of the program. -/
theorem collectProgTypes_covers (p : V2026Prog) : Covers (collectProgTypes p) (progTys p) :=
  fun _ hy => mem_internTys hy

/-- **Unconditional** program round trip. -/
theorem decodeProg_encodeProg (p : V2026Prog) : decodeProg (encodeProg p) = some p := by
  simp only [encodeProg, decodeProg]
  rw [decodeList_map _ _ _ (fun b hb =>
    roundtrip_body b ((collectProgTypes_covers p).flatMap b hb))]
  rfl

/-- `encodeProg` is injective (it has a left inverse). -/
theorem encodeProg_injective {p q : V2026Prog} (h : encodeProg p = encodeProg q) : p = q := by
  have hp := decodeProg_encodeProg p
  rw [h, decodeProg_encodeProg q] at hp
  exact (Option.some.inj hp).symm

/-- **Unconditional** place round trip against its own collected table (and,
by `roundtrip_place`, against every extension of it). -/
theorem decodePlace_encodePlace (tt : TypeTable) (p : Place) :
    decodePlace (internTys tt (placeTys p)) (encodePlace (internTys tt (placeTys p)) p) = some p :=
  roundtrip_place p (fun _ hy => mem_internTys hy)

theorem decodeOperand_encodeOperand (tt : TypeTable) (op : Operand) :
    decodeOperand (internTys tt (operandTys op))
      (encodeOperand (internTys tt (operandTys op)) op) = some op :=
  roundtrip_operand op (fun _ hy => mem_internTys hy)

theorem decodeRvalue_encodeRvalue (tt : TypeTable) (rv : Rvalue) :
    decodeRvalue (internTys tt (rvalueTys rv)) (encodeRvalue (internTys tt (rvalueTys rv)) rv) =
      some rv :=
  roundtrip_rvalue rv (fun _ hy => mem_internTys hy)

theorem decodeStmt_encodeStmt (tt : TypeTable) (s : Statement) :
    decodeStmt (internTys tt (stmtTys s)) (encodeStmt (internTys tt (stmtTys s)) s) = some s :=
  roundtrip_stmt s (fun _ hy => mem_internTys hy)

theorem decodeTerminator_encodeTerminator (tt : TypeTable) (t : Terminator) :
    decodeTerminator (internTys tt (termKindTys t.kind))
      (encodeTerminator (internTys tt (termKindTys t.kind)) t) = some t :=
  roundtrip_terminator t (fun _ hy => mem_internTys hy)

theorem decodeBody_encodeBody (tt : TypeTable) (b : CapturedMir) :
    decodeBody (internTys tt (bodyTys b)) (encodeBody (internTys tt (bodyTys b)) b) = some b :=
  roundtrip_body b (fun _ hy => mem_internTys hy)

/-- Round trips are stable under table extension (multi-body programs and
call-cone narrowing share one growing table). -/
theorem roundtrip_body_of_extends {tt tt' : TypeTable} (b : CapturedMir)
    (hext : (internTys tt (bodyTys b)).Extends tt') :
    decodeBody tt' (encodeBody tt' b) = some b :=
  roundtrip_body b (fun _ hy => extends_types_mem hext (mem_internTys hy))

/-- The type table of every encoded program is `Good`. -/
theorem encodeProg_types_good (p : V2026Prog) : (encodeProg p).types.Good :=
  internKinds_good (internTys_good initTypeTable_good (progTys p)) (progTraitKinds p)

/-- Canonical interning: both tables are duplicate-free, nominal `TyId`
equality coincides with structural `Ty` equality on interned types, every
interned type's kinds (bottom-up) are interned, and the built-in kinds sit at
`KindId`s `0, 1, 2`. -/
theorem encodeProg_types_canonical (p : V2026Prog) :
    typesAreCanonical tyBEq (encodeProg p).types.types = true ∧
    typesAreCanonical rigidTyBEq (encodeProg p).types.kinds = true ∧
    (∀ (i j : TyId) (ty₁ ty₂ : Ty), nth? (encodeProg p).types.types i = some ty₁ →
      nth? (encodeProg p).types.types j = some ty₂ → (i = j ↔ ty₁ = ty₂)) ∧
    (∀ ty ∈ (encodeProg p).types.types, rigidTyPostorder ty.kind ⊆ (encodeProg p).types.kinds) ∧
    nth? (encodeProg p).types.kinds 0 = some (.tuple []) ∧
    nth? (encodeProg p).types.kinds 1 = some .bool ∧
    nth? (encodeProg p).types.kinds 2 = some (.uint .usize) := by
  have hg := encodeProg_types_good p
  obtain ⟨⟨l, hl⟩, _⟩ :=
    extends_trans (internTys_extends initTypeTable (progTys p)) (internKinds_extends _ (progTraitKinds p))
  refine ⟨hg.2.1, hg.1, ?_, hg.2.2, ?_, ?_, ?_⟩
  · intro i j ty₁ ty₂ hi hj
    constructor
    · intro e; subst e; rw [hi] at hj; exact Option.some.inj hj
    · intro e; subst e; exact nth?_injective_of_canonical tyBEq_lawful hg.2.1 hi hj
  all_goals
    show nth? (collectProgTypes p).kinds _ = _
    simp only [collectProgTypes]; rw [hl]; rfl

/-- Every `RigidTy` argument in every `CapturedMir.traitImpls` entry of `p` has
its full bottom-up post-order interned in `(encodeProg p).types.kinds`. -/
theorem encodeProg_traitImpl_kinds_interned (p : V2026Prog) (b : CapturedMir)
    (hb : b ∈ p.bodies) (ti : TraitImplEntry) (hti : ti ∈ b.traitImpls)
    (k : RigidTy) (hk : k ∈ ti.traitRef.args) :
    rigidTyPostorder k ⊆ (encodeProg p).types.kinds := by
  have hmem : k ∈ progTraitKinds p :=
    List.mem_flatMap.mpr ⟨b, hb, List.mem_flatMap.mpr ⟨ti, hti, hk⟩⟩
  exact mem_internKinds_postorder hmem

/-- Every trait-impl kind of `p` has its post-order interned. -/
theorem encodeProg_progTraitKinds_interned (p : V2026Prog) :
    ∀ k ∈ progTraitKinds p, rigidTyPostorder k ⊆ (encodeProg p).types.kinds :=
  fun _ hk => mem_internKinds_postorder hk

/-- Every `Ty` occurrence of `p` is interned in `(encodeProg p).types.types`. -/
theorem encodeProg_progTys_interned (p : V2026Prog) :
    ∀ ty ∈ progTys p, ty ∈ (encodeProg p).types.types :=
  fun ty hty => extends_types_mem (internKinds_extends _ (progTraitKinds p)) (collectProgTypes_covers p ty hty)

/-! ### Anti-laundering: constructor tags are preserved -/

/-- Constructor tag of a statement kind. -/
def stmtKindTag : StatementKind → Nat
  | .assign _ _ => 0 | .setDiscriminant _ _ => 1 | .deinit _ => 2 | .storageLive _ => 3
  | .storageDead _ => 4 | .retag _ _ => 5 | .placeMention _ => 6 | .intrinsic _ => 7
  | .coverage => 8 | .constEvalCounter => 9 | .backwardIncompatibleDropHint _ => 10 | .nop => 11

/-- Constructor tag of a reference statement kind. -/
def refStmtKindTag : RefStatementKind → Nat
  | .assign _ _ => 0 | .setDiscriminant _ _ => 1 | .deinit _ => 2 | .storageLive _ => 3
  | .storageDead _ => 4 | .retag _ _ => 5 | .placeMention _ => 6 | .intrinsic _ => 7
  | .coverage => 8 | .constEvalCounter => 9 | .backwardIncompatibleDropHint _ => 10 | .nop => 11

/-- Constructor tag of a terminator kind. -/
def termKindTag : TerminatorKind → Nat
  | .goto _ => 0 | .switchInt _ _ => 1 | .unwindResume => 2 | .unwindTerminate => 3
  | .return_ => 4 | .unreachable => 5 | .drop _ _ _ => 6 | .call _ _ _ _ _ => 7
  | .tailCall _ _ => 8 | .assert _ _ _ _ => 9 | .inlineAsm _ _ _ => 10

/-- Constructor tag of a reference terminator kind. -/
def refTermKindTag : RefTerminatorKind → Nat
  | .goto _ => 0 | .switchInt _ _ => 1 | .unwindResume => 2 | .unwindTerminate => 3
  | .return_ => 4 | .unreachable => 5 | .drop _ _ _ => 6 | .call _ _ _ _ _ => 7
  | .tailCall _ _ => 8 | .assert _ _ _ _ => 9 | .inlineAsm _ _ _ => 10

/-- Constructor tag of an rvalue. -/
def rvalueTag : Rvalue → Nat
  | .use _ => 0 | .repeat _ _ => 1 | .ref _ _ => 2 | .threadLocalRef _ => 3 | .rawPtr _ _ => 4
  | .len _ => 5 | .cast _ _ _ => 6 | .binaryOp _ _ _ => 7 | .nullaryOp _ _ => 8
  | .unaryOp _ _ => 9 | .discriminant _ => 10 | .aggregate _ _ => 11 | .shallowInitBox _ _ => 12
  | .copyForDeref _ => 13 | .wrapUnsafeBinder _ _ => 14

/-- Constructor tag of a reference rvalue. -/
def refRvalueTag : RefRvalue → Nat
  | .use _ => 0 | .repeat _ _ => 1 | .ref _ _ => 2 | .threadLocalRef _ => 3 | .rawPtr _ _ => 4
  | .len _ => 5 | .cast _ _ _ => 6 | .binaryOp _ _ _ => 7 | .nullaryOp _ _ => 8
  | .unaryOp _ _ => 9 | .discriminant _ => 10 | .aggregate _ _ => 11 | .shallowInitBox _ _ => 12
  | .copyForDeref _ => 13 | .wrapUnsafeBinder _ _ => 14

theorem encodeStmtKind_tag (tt : TypeTable) (k : StatementKind) :
    refStmtKindTag (encodeStmtKind tt k) = stmtKindTag k := by cases k <;> rfl

theorem encodeTermKind_tag (tt : TypeTable) (k : TerminatorKind) :
    refTermKindTag (encodeTermKind tt k) = termKindTag k := by cases k <;> rfl

theorem encodeRvalue_tag (tt : TypeTable) (rv : Rvalue) :
    refRvalueTag (encodeRvalue tt rv) = rvalueTag rv := by cases rv <;> rfl

/-- No statement is laundered into (or out of) a dormant `nop`, and every
statement / terminator / rvalue constructor is preserved by the encoder. -/
theorem encodeStmt_no_dormant_noops (tt : TypeTable) (s : Statement) :
    ((encodeStmt tt s).kind = .nop ↔ s.kind = .nop) ∧
    refStmtKindTag (encodeStmt tt s).kind = stmtKindTag s.kind := by
  refine ⟨?_, encodeStmtKind_tag tt s.kind⟩
  cases s with
  | mk k sp => cases k <;> simp [encodeStmt, encodeStmtKind]

/-- **`CodecRoundtripClaim`** (proved here; restated in
`Anneal.Mir.Correspondence.Claims`). -/
theorem codecRoundtripClaim_proof : CodecRoundtripClaim := by
  refine ⟨decodeProg_encodeProg, fun _ _ h => encodeProg_injective h, encodeProg_types_good,
    ?_, ?_, encodeProg_progTys_interned, encodeProg_progTraitKinds_interned⟩
  · exact fun p => (encodeProg_types_canonical p).2.2.1
  · exact fun p => (encodeProg_types_canonical p).2.2.2.2

end Anneal.Mir.Correspondence
