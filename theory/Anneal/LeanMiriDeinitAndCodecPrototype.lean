/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/
import Trusted
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Track P prototype: `V2026_06_01` ↔ `LeanMiri` codec, demand-time layout
queries, opt-in move deinitialization (`D1`–`D9`)

`[PROTOTYPE ONLY — OFF UNSTABLE]` (`merge_policy = no_merge_prototype`).

This module is self-contained and is not imported by `Anneal.lean`. It is
checked with

```
anneal-lean-run --mode file --concurrency 1 -- \
  lake env lean theory/Anneal/LeanMiriDeinitAndCodecPrototype.lean
```

Contents:

1. **Type-interning codec** (`encodeProg` / `decodeProg`) over the *real*
   `Trusted.Rustc.V2026_06_01.MirAst` syntax (every constructor of
   `ProjectionElem`, `Operand`, `AggregateKind`, `Rvalue`,
   `NonDivergingIntrinsic`, `StatementKind`, `TerminatorKind`, plus
   `Place`, `ConstOperand`, `Statement`, `Terminator`, `BasicBlockData`,
   `LocalDecl`, `CapturedMir`). Every `Ty` occurrence becomes a `TyId`
   into a canonical, duplicate-free `TypeTable.types`, and every structural
   `RigidTy` (including all children, in post-order, i.e. bottom-up) is
   interned into `TypeTable.kinds`, pre-seeded with `()`, `bool`, `usize`.
2. **Demand-time `LayoutQuery`** (`proofs-rs/lean-miri#64`): all
   `MiriRefMachine` layout hooks are answered on demand from
   `(TypeTable, LayoutTable)`; no eager per-type tables are materialized.
3. **Operational model** of `M_anneal` (eager, value-level move
   deinitialization) and `M_ref` (`LeanMiri` with the opt-in
   `deinitMovedPlace` flag and the deferred `pendingMoveDeinit` latch of the
   `d9b41b58b` 6-file patch: `evalOperand` → `readImmediate` /
   `copyRuntimePlaceNoValidate`), sharing one byte-level memory with real
   `AbstractByte`s, real Tree Borrows permissions (`TreeBorrowPerm`,
   `BorrowEntry`) and the real per-node transition `treeBorrowNodeAccess`.
4. Correspondence theorems, falsification witnesses, and the executable
   `D1`–`D9` canaries.
-/

namespace Anneal.LeanMiriDeinitAndCodecPrototype

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

set_option linter.constructorNameAsVariable false

/-! ## Part 0 — Decidable equality on the real `V2026_06_01` type syntax

`RigidTy` is a nested inductive (`List RigidTy` children), for which Lean's
`DecidableEq` deriving handler does not apply, so we give a structural
Boolean equality and prove it sound and complete (axiom-free modulo
`propext`). -/

deriving instance DecidableEq for UintTy
deriving instance DecidableEq for IntTy
deriving instance DecidableEq for FloatTy
deriving instance DecidableEq for Mutability
deriving instance DecidableEq for Safety
deriving instance DecidableEq for CallConv

mutual
/-- Structural Boolean equality on `RigidTy`. -/
def RigidTy.beq : RigidTy → RigidTy → Bool
  | .param i n, .param j m => decide (i = j) && decide (n = m)
  | .alias p a, .alias q b => decide (p = q) && RigidTy.beqList a b
  | .bool, .bool => true
  | .char, .char => true
  | .int w, .int v => decide (w = v)
  | .uint w, .uint v => decide (w = v)
  | .float w, .float v => decide (w = v)
  | .never, .never => true
  | .str, .str => true
  | .tuple a, .tuple b => RigidTy.beqList a b
  | .array e n, .array f m => RigidTy.beq e f && decide (n = m)
  | .slice e, .slice f => RigidTy.beq e f
  | .ref m p, .ref n q => decide (m = n) && RigidTy.beq p q
  | .rawPtr m p, .rawPtr n q => decide (m = n) && RigidTy.beq p q
  | .adt p a, .adt q b => decide (p = q) && RigidTy.beqList a b
  | .fnDef p a, .fnDef q b => decide (p = q) && RigidTy.beqList a b
  | .fnPtr i o s cc, .fnPtr j p t dd =>
      RigidTy.beqList i j && RigidTy.beq o p && decide (s = t) && decide (cc = dd)
  | .closure p a, .closure q b => decide (p = q) && RigidTy.beqList a b
  | .dynamic p, .dynamic q => decide (p = q)
  | .foreign p, .foreign q => decide (p = q)
  | .other r, .other s => decide (r = s)
  | _, _ => false
/-- Structural Boolean equality on `List RigidTy`. -/
def RigidTy.beqList : List RigidTy → List RigidTy → Bool
  | [], [] => true
  | a :: as, b :: bs => RigidTy.beq a b && RigidTy.beqList as bs
  | _, _ => false
end

mutual
theorem RigidTy.beq_refl : (a : RigidTy) → RigidTy.beq a a = true
  | .param _ _ => by simp [RigidTy.beq]
  | .alias _ a => by simp [RigidTy.beq, RigidTy.beqList_refl a]
  | .bool => rfl
  | .char => rfl
  | .int _ => by simp [RigidTy.beq]
  | .uint _ => by simp [RigidTy.beq]
  | .float _ => by simp [RigidTy.beq]
  | .never => rfl
  | .str => rfl
  | .tuple a => by simp [RigidTy.beq, RigidTy.beqList_refl a]
  | .array e _ => by simp [RigidTy.beq, RigidTy.beq_refl e]
  | .slice e => by simp [RigidTy.beq, RigidTy.beq_refl e]
  | .ref _ p => by simp [RigidTy.beq, RigidTy.beq_refl p]
  | .rawPtr _ p => by simp [RigidTy.beq, RigidTy.beq_refl p]
  | .adt _ a => by simp [RigidTy.beq, RigidTy.beqList_refl a]
  | .fnDef _ a => by simp [RigidTy.beq, RigidTy.beqList_refl a]
  | .fnPtr i o _ _ => by simp [RigidTy.beq, RigidTy.beqList_refl i, RigidTy.beq_refl o]
  | .closure _ a => by simp [RigidTy.beq, RigidTy.beqList_refl a]
  | .dynamic _ => by simp [RigidTy.beq]
  | .foreign _ => by simp [RigidTy.beq]
  | .other _ => by simp [RigidTy.beq]
theorem RigidTy.beqList_refl : (as : List RigidTy) → RigidTy.beqList as as = true
  | [] => rfl
  | a :: as => by simp [RigidTy.beqList, RigidTy.beq_refl a, RigidTy.beqList_refl as]
end

mutual
theorem RigidTy.eq_of_beq : (a b : RigidTy) → RigidTy.beq a b = true → a = b
  | .param i n, b, h => by
    cases b <;> simp [RigidTy.beq] at h
    obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl
  | .alias p a, b, h => by
    cases b <;> simp [RigidTy.beq] at h
    case alias q b' => obtain ⟨h1, h2⟩ := h; subst h1; rw [RigidTy.eq_of_beqList a b' h2]
  | .bool, b, h => by cases b <;> simp [RigidTy.beq] at h ⊢
  | .char, b, h => by cases b <;> simp [RigidTy.beq] at h ⊢
  | .int w, b, h => by cases b <;> simp [RigidTy.beq] at h ⊢; exact h
  | .uint w, b, h => by cases b <;> simp [RigidTy.beq] at h ⊢; exact h
  | .float w, b, h => by cases b <;> simp [RigidTy.beq] at h ⊢; exact h
  | .never, b, h => by cases b <;> simp [RigidTy.beq] at h ⊢
  | .str, b, h => by cases b <;> simp [RigidTy.beq] at h ⊢
  | .tuple a, b, h => by
    cases b <;> simp [RigidTy.beq] at h
    case tuple b' => rw [RigidTy.eq_of_beqList a b' h]
  | .array e n, b, h => by
    cases b <;> simp [RigidTy.beq] at h
    case array f m => obtain ⟨h1, h2⟩ := h; subst h2; rw [RigidTy.eq_of_beq e f h1]
  | .slice e, b, h => by
    cases b <;> simp [RigidTy.beq] at h
    case slice f => rw [RigidTy.eq_of_beq e f h]
  | .ref m p, b, h => by
    cases b <;> simp [RigidTy.beq] at h
    case ref n q => obtain ⟨h1, h2⟩ := h; subst h1; rw [RigidTy.eq_of_beq p q h2]
  | .rawPtr m p, b, h => by
    cases b <;> simp [RigidTy.beq] at h
    case rawPtr n q => obtain ⟨h1, h2⟩ := h; subst h1; rw [RigidTy.eq_of_beq p q h2]
  | .adt p a, b, h => by
    cases b <;> simp [RigidTy.beq] at h
    case adt q b' => obtain ⟨h1, h2⟩ := h; subst h1; rw [RigidTy.eq_of_beqList a b' h2]
  | .fnDef p a, b, h => by
    cases b <;> simp [RigidTy.beq] at h
    case fnDef q b' => obtain ⟨h1, h2⟩ := h; subst h1; rw [RigidTy.eq_of_beqList a b' h2]
  | .fnPtr i o s cc, b, h => by
    cases b <;> simp [RigidTy.beq] at h
    case fnPtr j p t dd =>
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      subst h3; subst h4
      rw [RigidTy.eq_of_beqList i j h1, RigidTy.eq_of_beq o p h2]
  | .closure p a, b, h => by
    cases b <;> simp [RigidTy.beq] at h
    case closure q b' => obtain ⟨h1, h2⟩ := h; subst h1; rw [RigidTy.eq_of_beqList a b' h2]
  | .dynamic p, b, h => by cases b <;> simp [RigidTy.beq] at h ⊢; exact h
  | .foreign p, b, h => by cases b <;> simp [RigidTy.beq] at h ⊢; exact h
  | .other r, b, h => by cases b <;> simp [RigidTy.beq] at h ⊢; exact h
theorem RigidTy.eq_of_beqList : (as bs : List RigidTy) → RigidTy.beqList as bs = true → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [RigidTy.beqList] at h
  | _ :: _, [], h => by simp [RigidTy.beqList] at h
  | a :: as, b :: bs, h => by
    simp [RigidTy.beqList] at h
    rw [RigidTy.eq_of_beq a b h.1, RigidTy.eq_of_beqList as bs h.2]
end

instance instDecidableEqRigidTy : DecidableEq RigidTy := fun a b =>
  if h : RigidTy.beq a b = true then isTrue (RigidTy.eq_of_beq a b h)
  else isFalse (fun e => h (e ▸ RigidTy.beq_refl a))

instance instDecidableEqTy : DecidableEq Ty := fun a b =>
  match a, b with
  | ⟨k₁, l₁⟩, ⟨k₂, l₂⟩ =>
    if h₁ : k₁ = k₂ then
      if h₂ : l₁ = l₂ then isTrue (by subst h₁; subst h₂; rfl)
      else isFalse (fun e => h₂ (congrArg Ty.layoutIdx e))
    else isFalse (fun e => h₁ (congrArg Ty.kind e))

/-! ## Part 1 — Generic canonical interning library -/

/-- Structural `0`-based list lookup. -/
def nth? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth? xs n

theorem nth?_append_left {α : Type} : ∀ {xs : List α} {i : Nat} {a : α} (l : List α),
    nth? xs i = some a → nth? (xs ++ l) i = some a
  | [], _, _, _, h => by simp [nth?] at h
  | x :: xs, 0, a, l, h => by simpa [nth?] using h
  | x :: xs, i + 1, a, l, h => by simp [nth?] at h ⊢; exact nth?_append_left l h

theorem mem_of_nth? {α : Type} : ∀ {ys : List α} {k : Nat} {b : α}, nth? ys k = some b → b ∈ ys
  | [], _, _, h => by simp [nth?] at h
  | y :: ys, 0, b, h => by simp [nth?] at h; subst h; exact List.Mem.head _
  | y :: ys, k + 1, b, h => by simp [nth?] at h; exact List.Mem.tail _ (mem_of_nth? h)

/-- Generic list decoder (`Option` traversal). -/
def decodeList {α β : Type} (f : β → Option α) : List β → Option (List α)
  | [] => some []
  | b :: bs =>
    match f b, decodeList f bs with
    | some a, some as => some (a :: as)
    | _, _ => none

theorem decodeList_map {α β : Type} (f : β → Option α) (g : α → β) :
    ∀ (xs : List α), (∀ x ∈ xs, f (g x) = some x) → decodeList f (xs.map g) = some xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map, decodeList]
    rw [h x (List.Mem.head _), decodeList_map f g xs (fun y hy => h y (List.Mem.tail _ hy))]

section Intern

variable {α : Type} [DecidableEq α]

/-- First index of `a` in `xs`. -/
def indexOf? : List α → α → Option Nat
  | [], _ => none
  | x :: xs, a => if x = a then some 0 else (indexOf? xs a).map (· + 1)

/-- Append `a` to `xs` unless it is already present (canonical interning). -/
def insertIfAbsent (a : α) : List α → List α
  | [] => [a]
  | x :: xs => if x = a then x :: xs else x :: insertIfAbsent a xs

/-- Intern every element of `ys` left to right. -/
def insertAll : List α → List α → List α
  | acc, [] => acc
  | acc, y :: ys => insertAll (insertIfAbsent y acc) ys

/-- Interned identifier of `a` in `xs` (`0` when absent; only used on interned
values, see `nth?_lookupId_of_mem`). -/
def lookupId (xs : List α) (a : α) : Nat := (indexOf? xs a).getD 0

/-- No duplicate entries (`typesAreCanonical` in `joshlf`'s PR #257). -/
def typesAreCanonical : List α → Bool
  | [] => true
  | x :: xs => (indexOf? xs x).isNone && typesAreCanonical xs

theorem nth?_of_indexOf? : ∀ {xs : List α} {a : α} {i : Nat},
    indexOf? xs a = some i → nth? xs i = some a
  | [], _, _, h => by simp [indexOf?] at h
  | x :: xs, a, i, h => by
    unfold indexOf? at h
    by_cases hx : x = a
    · simp [hx] at h; subst h; simp [nth?, hx]
    · simp [hx] at h
      obtain ⟨j, hj, rfl⟩ := h
      simp [nth?, nth?_of_indexOf? hj]

theorem indexOf?_isSome_of_mem : ∀ {xs : List α} {a : α}, a ∈ xs → ∃ i, indexOf? xs a = some i
  | [], _, h => by cases h
  | x :: xs, a, h => by
    unfold indexOf?
    by_cases hx : x = a
    · exact ⟨0, by simp [hx]⟩
    · have hm : a ∈ xs := by
        cases h with
        | head => exact absurd rfl hx
        | tail _ h' => exact h'
      obtain ⟨i, hi⟩ := indexOf?_isSome_of_mem hm
      exact ⟨i + 1, by simp [hx, hi]⟩

theorem indexOf?_eq_none_of_not_mem : ∀ {xs : List α} {a : α}, a ∉ xs → indexOf? xs a = none
  | [], _, _ => rfl
  | x :: xs, a, h => by
    unfold indexOf?
    have hx : x ≠ a := fun e => h (e ▸ List.Mem.head _)
    have hm : a ∉ xs := fun m => h (List.Mem.tail _ m)
    simp [hx, indexOf?_eq_none_of_not_mem hm]

theorem not_mem_of_indexOf?_eq_none : ∀ {xs : List α} {a : α}, indexOf? xs a = none → a ∉ xs := by
  intro xs a h hm
  obtain ⟨i, hi⟩ := indexOf?_isSome_of_mem hm
  rw [h] at hi; cases hi

theorem nth?_lookupId_of_mem {xs : List α} {a : α} (h : a ∈ xs) :
    nth? xs (lookupId xs a) = some a := by
  obtain ⟨i, hi⟩ := indexOf?_isSome_of_mem h
  simp [lookupId, hi, nth?_of_indexOf? hi]

theorem mem_insertIfAbsent : ∀ {a b : α} {xs : List α}, b ∈ insertIfAbsent a xs ↔ b = a ∨ b ∈ xs
  | a, b, [] => by simp [insertIfAbsent]
  | a, b, x :: xs => by
    unfold insertIfAbsent
    by_cases hx : x = a
    · subst hx; simp only [↓reduceIte]; constructor
      · intro h; exact Or.inr h
      · intro h; cases h with
        | inl h => subst h; exact List.Mem.head _
        | inr h => exact h
    · simp only [hx, ↓reduceIte, List.mem_cons]
      rw [mem_insertIfAbsent]
      constructor
      · intro h; rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · intro h; rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem mem_insertIfAbsent_self (a : α) (xs : List α) : a ∈ insertIfAbsent a xs :=
  mem_insertIfAbsent.mpr (Or.inl rfl)

theorem mem_insertIfAbsent_of_mem {a b : α} {xs : List α} (h : b ∈ xs) :
    b ∈ insertIfAbsent a xs :=
  mem_insertIfAbsent.mpr (Or.inr h)

theorem insertIfAbsent_prefix : ∀ (a : α) (xs : List α), ∃ l, insertIfAbsent a xs = xs ++ l
  | a, [] => ⟨[a], rfl⟩
  | a, x :: xs => by
    unfold insertIfAbsent
    by_cases hx : x = a
    · exact ⟨[], by simp [hx]⟩
    · obtain ⟨l, hl⟩ := insertIfAbsent_prefix a xs
      exact ⟨l, by simp [hx, hl]⟩

theorem canonical_insertIfAbsent : ∀ (a : α) (xs : List α),
    typesAreCanonical xs = true → typesAreCanonical (insertIfAbsent a xs) = true
  | a, [], _ => by simp [insertIfAbsent, typesAreCanonical, indexOf?]
  | a, x :: xs, h => by
    unfold insertIfAbsent
    by_cases hx : x = a
    · simpa [hx] using h
    · simp only [hx, ↓reduceIte]
      simp only [typesAreCanonical, Bool.and_eq_true, Option.isNone_iff_eq_none] at h ⊢
      refine ⟨?_, canonical_insertIfAbsent a xs h.2⟩
      apply indexOf?_eq_none_of_not_mem
      intro hm
      rcases mem_insertIfAbsent.mp hm with h' | h'
      · exact hx h'
      · exact not_mem_of_indexOf?_eq_none h.1 h'

theorem mem_insertAll : ∀ {acc ys : List α} {b : α}, b ∈ insertAll acc ys ↔ b ∈ acc ∨ b ∈ ys
  | acc, [], b => by simp [insertAll]
  | acc, y :: ys, b => by
    simp only [insertAll]
    rw [mem_insertAll, mem_insertIfAbsent]
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

theorem insertAll_prefix : ∀ (acc ys : List α), ∃ l, insertAll acc ys = acc ++ l
  | acc, [] => ⟨[], by simp [insertAll]⟩
  | acc, y :: ys => by
    obtain ⟨l₁, h₁⟩ := insertIfAbsent_prefix y acc
    obtain ⟨l₂, h₂⟩ := insertAll_prefix (insertIfAbsent y acc) ys
    exact ⟨l₁ ++ l₂, by simp only [insertAll]; rw [h₂, h₁, List.append_assoc]⟩

theorem canonical_insertAll : ∀ (acc ys : List α),
    typesAreCanonical acc = true → typesAreCanonical (insertAll acc ys) = true
  | _, [], h => h
  | acc, y :: ys, h => canonical_insertAll _ ys (canonical_insertIfAbsent y acc h)

theorem indexOf?_append_of_mem : ∀ {xs : List α} {a : α} (l : List α),
    a ∈ xs → indexOf? (xs ++ l) a = indexOf? xs a
  | [], _, _, h => by cases h
  | x :: xs, a, l, h => by
    simp only [List.cons_append, indexOf?]
    by_cases hx : x = a
    · simp [hx]
    · have hm : a ∈ xs := by
        cases h with
        | head => exact absurd rfl hx
        | tail _ h' => exact h'
      simp [hx, indexOf?_append_of_mem l hm]

/-- In a canonical list, equal entries sit at equal indices. -/
theorem nth?_injective_of_canonical : ∀ {xs : List α} {i j : Nat} {a : α},
    typesAreCanonical xs = true → nth? xs i = some a → nth? xs j = some a → i = j
  | [], _, _, _, _, h, _ => by simp [nth?] at h
  | x :: xs, 0, 0, _, _, _, _ => rfl
  | x :: xs, 0, j + 1, a, hc, hi, hj => by
    simp only [typesAreCanonical, Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
    simp [nth?] at hi hj; subst hi
    exact absurd (mem_of_nth? hj) (not_mem_of_indexOf?_eq_none hc.1)
  | x :: xs, i + 1, 0, a, hc, hi, hj => by
    simp only [typesAreCanonical, Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
    simp [nth?] at hi hj; subst hj
    exact absurd (mem_of_nth? hi) (not_mem_of_indexOf?_eq_none hc.1)
  | x :: xs, i + 1, j + 1, a, hc, hi, hj => by
    simp only [typesAreCanonical, Bool.and_eq_true] at hc
    simp [nth?] at hi hj
    rw [nth?_injective_of_canonical hc.2 hi hj]

end Intern

/-! ## Part 2 — Type tables and bottom-up (post-order) kind interning -/

/-- Interned `Ty` identifier (`Miri.MIR.TyId`). -/
abbrev TyId := Nat
/-- Interned structural `RigidTy` identifier. -/
abbrev KindId := Nat

/-- The single source of truth for types of a `RefProg`: `kinds` interns every
structural `RigidTy` (children before parents), `types` interns every `Ty`
occurrence (`kind` + compiler `LayoutIdx`). -/
structure TypeTable where
  /-- Canonical structural kinds, bottom-up (post-order). -/
  kinds : List RigidTy
  /-- Canonical `Ty` entries indexed by `TyId`. -/
  types : List Ty

mutual
/-- Post-order (children first) enumeration of all structural sub-kinds. -/
def RigidTy.postorder : RigidTy → List RigidTy
  | .param i n => [.param i n]
  | .alias p a => RigidTy.postorderList a ++ [.alias p a]
  | .bool => [.bool]
  | .char => [.char]
  | .int w => [.int w]
  | .uint w => [.uint w]
  | .float w => [.float w]
  | .never => [.never]
  | .str => [.str]
  | .tuple a => RigidTy.postorderList a ++ [.tuple a]
  | .array e n => RigidTy.postorder e ++ [.array e n]
  | .slice e => RigidTy.postorder e ++ [.slice e]
  | .ref m p => RigidTy.postorder p ++ [.ref m p]
  | .rawPtr m p => RigidTy.postorder p ++ [.rawPtr m p]
  | .adt p a => RigidTy.postorderList a ++ [.adt p a]
  | .fnDef p a => RigidTy.postorderList a ++ [.fnDef p a]
  | .fnPtr i o s cc => RigidTy.postorderList i ++ RigidTy.postorder o ++ [.fnPtr i o s cc]
  | .closure p a => RigidTy.postorderList a ++ [.closure p a]
  | .dynamic p => [.dynamic p]
  | .foreign p => [.foreign p]
  | .other r => [.other r]
/-- Post-order enumeration of a list of kinds. -/
def RigidTy.postorderList : List RigidTy → List RigidTy
  | [] => []
  | k :: ks => RigidTy.postorder k ++ RigidTy.postorderList ks
end

/-- Immediate structural children of a kind (every `RigidTy` constructor). -/
def RigidTy.children : RigidTy → List RigidTy
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

theorem RigidTy.mem_postorder_self (k : RigidTy) : k ∈ RigidTy.postorder k := by
  cases k <;> simp [RigidTy.postorder]

theorem RigidTy.mem_postorderList_of_mem : ∀ {c : RigidTy} {cs : List RigidTy},
    c ∈ cs → c ∈ RigidTy.postorderList cs
  | _, [], h => by cases h
  | c, k :: ks, h => by
    simp only [RigidTy.postorderList, List.mem_append]
    cases h with
    | head => exact Or.inl (RigidTy.mem_postorder_self _)
    | tail _ h' => exact Or.inr (RigidTy.mem_postorderList_of_mem h')

/-- Every immediate child of `k` occurs (strictly before `k`) in its post-order. -/
theorem RigidTy.children_mem_postorder (k : RigidTy) :
    ∀ c ∈ RigidTy.children k, c ∈ RigidTy.postorder k := by
  intro c hc
  cases k with
  | alias p a =>
    simp only [RigidTy.postorder]; exact List.mem_append_left _ (RigidTy.mem_postorderList_of_mem hc)
  | tuple a =>
    simp only [RigidTy.postorder]; exact List.mem_append_left _ (RigidTy.mem_postorderList_of_mem hc)
  | adt p a =>
    simp only [RigidTy.postorder]; exact List.mem_append_left _ (RigidTy.mem_postorderList_of_mem hc)
  | fnDef p a =>
    simp only [RigidTy.postorder]; exact List.mem_append_left _ (RigidTy.mem_postorderList_of_mem hc)
  | closure p a =>
    simp only [RigidTy.postorder]; exact List.mem_append_left _ (RigidTy.mem_postorderList_of_mem hc)
  | array e n =>
    simp only [RigidTy.children, List.mem_singleton] at hc; subst hc
    simp only [RigidTy.postorder]; exact List.mem_append_left _ (RigidTy.mem_postorder_self _)
  | slice e =>
    simp only [RigidTy.children, List.mem_singleton] at hc; subst hc
    simp only [RigidTy.postorder]; exact List.mem_append_left _ (RigidTy.mem_postorder_self _)
  | ref m e =>
    simp only [RigidTy.children, List.mem_singleton] at hc; subst hc
    simp only [RigidTy.postorder]; exact List.mem_append_left _ (RigidTy.mem_postorder_self _)
  | rawPtr m e =>
    simp only [RigidTy.children, List.mem_singleton] at hc; subst hc
    simp only [RigidTy.postorder]; exact List.mem_append_left _ (RigidTy.mem_postorder_self _)
  | fnPtr i o s cc =>
    simp only [RigidTy.children, List.mem_append, List.mem_singleton] at hc
    simp only [RigidTy.postorder]
    rcases hc with hc | hc
    · exact List.mem_append_left _ (List.mem_append_left _ (RigidTy.mem_postorderList_of_mem hc))
    · subst hc; exact List.mem_append_left _ (List.mem_append_right _ (RigidTy.mem_postorder_self _))
  | param _ _ => simp [RigidTy.children] at hc
  | bool => simp [RigidTy.children] at hc
  | char => simp [RigidTy.children] at hc
  | int _ => simp [RigidTy.children] at hc
  | uint _ => simp [RigidTy.children] at hc
  | float _ => simp [RigidTy.children] at hc
  | never => simp [RigidTy.children] at hc
  | str => simp [RigidTy.children] at hc
  | dynamic _ => simp [RigidTy.children] at hc
  | foreign _ => simp [RigidTy.children] at hc
  | other _ => simp [RigidTy.children] at hc

/-- Intern a `Ty`: all of its structural kinds bottom-up into `kinds`, then the
`Ty` itself into `types`. -/
def internTy (tt : TypeTable) (ty : Ty) : TypeTable :=
  { kinds := insertAll tt.kinds (RigidTy.postorder ty.kind)
    types := insertIfAbsent ty tt.types }

/-- Intern a list of `Ty` occurrences left to right. -/
def internTys : TypeTable → List Ty → TypeTable
  | tt, [] => tt
  | tt, ty :: tys => internTys (internTy tt ty) tys

/-- Pre-seeded built-in kinds (`KindId` `0 = ()`, `1 = bool`, `2 = usize`) for
`ExecutionMachine`'s `unitLayout` / `boolLayout` / `usizeLayout` queries. -/
def initTypeTable : TypeTable :=
  { kinds := [.tuple [], .bool, .uint .usize], types := [] }

/-- Table extension: both tables grow only by appending. -/
def TypeTable.Extends (tt tt' : TypeTable) : Prop :=
  (∃ l, tt'.kinds = tt.kinds ++ l) ∧ (∃ l, tt'.types = tt.types ++ l)

theorem TypeTable.Extends.refl (tt : TypeTable) : tt.Extends tt :=
  ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩

theorem TypeTable.Extends.trans {a b c : TypeTable} (h₁ : a.Extends b) (h₂ : b.Extends c) :
    a.Extends c := by
  obtain ⟨⟨l₁, k₁⟩, ⟨m₁, t₁⟩⟩ := h₁
  obtain ⟨⟨l₂, k₂⟩, ⟨m₂, t₂⟩⟩ := h₂
  exact ⟨⟨l₁ ++ l₂, by rw [k₂, k₁, List.append_assoc]⟩, ⟨m₁ ++ m₂, by rw [t₂, t₁, List.append_assoc]⟩⟩

theorem TypeTable.Extends.types_mem {a b : TypeTable} (h : a.Extends b) {ty : Ty}
    (hm : ty ∈ a.types) : ty ∈ b.types := by
  obtain ⟨_, ⟨l, hl⟩⟩ := h; rw [hl]; exact List.mem_append_left _ hm

theorem TypeTable.Extends.kinds_mem {a b : TypeTable} (h : a.Extends b) {k : RigidTy}
    (hm : k ∈ a.kinds) : k ∈ b.kinds := by
  obtain ⟨⟨l, hl⟩, _⟩ := h; rw [hl]; exact List.mem_append_left _ hm

theorem internTy_extends (tt : TypeTable) (ty : Ty) : tt.Extends (internTy tt ty) :=
  ⟨insertAll_prefix _ _, insertIfAbsent_prefix _ _⟩

theorem internTys_extends : ∀ (tt : TypeTable) (tys : List Ty), tt.Extends (internTys tt tys)
  | tt, [] => TypeTable.Extends.refl tt
  | tt, ty :: tys => (internTy_extends tt ty).trans (internTys_extends _ tys)

theorem mem_internTys : ∀ {tt : TypeTable} {tys : List Ty} {ty : Ty},
    ty ∈ tys → ty ∈ (internTys tt tys).types
  | _, [], _, h => by cases h
  | tt, t :: tys, ty, h => by
    simp only [internTys]
    cases h with
    | head => exact (internTys_extends _ tys).types_mem (mem_insertIfAbsent_self _ _)
    | tail _ h' => exact mem_internTys h'

/-- Table invariant: both tables canonical, and every interned `Ty` has its
kind and all of its kind's immediate children interned in `kinds`. -/
def TypeTable.Good (tt : TypeTable) : Prop :=
  typesAreCanonical tt.kinds = true ∧ typesAreCanonical tt.types = true ∧
  ∀ ty ∈ tt.types, RigidTy.postorder ty.kind ⊆ tt.kinds

theorem initTypeTable_good : initTypeTable.Good := by
  refine ⟨by decide, rfl, ?_⟩
  intro ty h; cases h

theorem internTy_good {tt : TypeTable} (h : tt.Good) (ty : Ty) : (internTy tt ty).Good := by
  obtain ⟨hk, ht, hc⟩ := h
  refine ⟨canonical_insertAll _ _ hk, canonical_insertIfAbsent _ _ ht, ?_⟩
  intro t htm x hx
  simp only [internTy] at htm ⊢
  rcases mem_insertIfAbsent.mp htm with e | e
  · subst e; exact mem_insertAll.mpr (Or.inr hx)
  · exact mem_insertAll.mpr (Or.inl (hc t e hx))

theorem internTys_good : ∀ {tt : TypeTable} (_ : tt.Good) (tys : List Ty), (internTys tt tys).Good
  | _, h, [] => h
  | _, h, ty :: tys => internTys_good (internTy_good h ty) tys

/-- Intern a list of structural `RigidTy`s (bottom-up post-order) into `kinds`
without adding `Ty` entries (used for `CapturedMir.traitImpls` type arguments). -/
def internKinds (tt : TypeTable) (ks : List RigidTy) : TypeTable :=
  { kinds := insertAll tt.kinds (RigidTy.postorderList ks), types := tt.types }

theorem internKinds_extends (tt : TypeTable) (ks : List RigidTy) :
    tt.Extends (internKinds tt ks) :=
  ⟨insertAll_prefix _ _, ⟨[], by simp [internKinds]⟩⟩

theorem internKinds_good {tt : TypeTable} (h : tt.Good) (ks : List RigidTy) :
    (internKinds tt ks).Good := by
  obtain ⟨hk, ht, hc⟩ := h
  refine ⟨canonical_insertAll _ _ hk, ht, ?_⟩
  intro t htm x hx
  exact mem_insertAll.mpr (Or.inl (hc t htm hx))

theorem RigidTy.postorder_sub_postorderList : ∀ {k : RigidTy} {ks : List RigidTy},
    k ∈ ks → RigidTy.postorder k ⊆ RigidTy.postorderList ks
  | _, [], h => by cases h
  | _, _ :: ks, h => by
    intro x hx
    simp only [RigidTy.postorderList, List.mem_append]
    cases h with
    | head => exact Or.inl hx
    | tail _ h' => exact Or.inr (RigidTy.postorder_sub_postorderList h' hx)

theorem mem_internKinds_postorder {tt : TypeTable} {ks : List RigidTy} {k : RigidTy}
    (hk : k ∈ ks) : RigidTy.postorder k ⊆ (internKinds tt ks).kinds := by
  intro x hx
  exact mem_insertAll.mpr (Or.inr (RigidTy.postorder_sub_postorderList hk hx))

/-! ### `Ty` ↔ `TyId` -/

/-- Encode a `Ty` as its interned `TyId`. -/
def encodeType (tt : TypeTable) (ty : Ty) : TyId := lookupId tt.types ty

/-- Decode a `TyId` (fails closed on out-of-bounds identifiers). -/
def decodeType (tt : TypeTable) (t : TyId) : Option Ty := nth? tt.types t

theorem decodeType_encodeType_of_mem {tt : TypeTable} {ty : Ty} (h : ty ∈ tt.types) :
    decodeType tt (encodeType tt ty) = some ty :=
  nth?_lookupId_of_mem h

/-- **Unconditional** `Ty` round trip: decoding against any table that has
interned `ty` recovers `ty`. -/
theorem decodeType_encodeType (tt : TypeTable) (ty : Ty) :
    decodeType (internTy tt ty) (encodeType (internTy tt ty) ty) = some ty :=
  decodeType_encodeType_of_mem (mem_insertIfAbsent_self _ _)

/-! ## Part 3 — Reference-indexed `V2026_06_01` syntax (`RefProg`) -/

/-- `ProjectionElem` with every `Ty` replaced by a `TyId`. -/
inductive RefProjectionElem : Type where
  | deref : RefProjectionElem
  | field (field : FieldIdx) (ty : TyId) : RefProjectionElem
  | index (idx : Local) : RefProjectionElem
  | constantIndex (offset : Nat) (minLength : Nat) (fromEnd : Bool) : RefProjectionElem
  | subslice (fromIdx : Nat) (toIdx : Nat) (fromEnd : Bool) : RefProjectionElem
  | downcast (variantName : Option String) (variant : VariantIdx) : RefProjectionElem
  | opaqueCast (ty : TyId) : RefProjectionElem
  | unwrapUnsafeBinder (ty : TyId) : RefProjectionElem

/-- Reference place. -/
structure RefPlace : Type where
  local_ : Local
  projection : List RefProjectionElem

/-- Reference constant operand. -/
structure RefConstOperand : Type where
  ty : TyId
  val : ConstValue

/-- Reference operand. -/
inductive RefOperand : Type where
  | copy (place : RefPlace) : RefOperand
  | move (place : RefPlace) : RefOperand
  | constant (c : RefConstOperand) : RefOperand

/-- Reference aggregate kind. -/
inductive RefAggregateKind : Type where
  | array (elemTy : TyId) : RefAggregateKind
  | tuple : RefAggregateKind
  | adt (defPath : DefPath) (variantIdx : VariantIdx) (activeField : Option FieldIdx) : RefAggregateKind
  | closure (defPath : DefPath) : RefAggregateKind
  | coroutine (defPath : DefPath) : RefAggregateKind
  | rawPtr (pointeeTy : TyId) (mutability : Mutability) : RefAggregateKind

/-- Reference rvalue (all 15 `Rvalue` constructors). -/
inductive RefRvalue : Type where
  | use (op : RefOperand) : RefRvalue
  | repeat (op : RefOperand) (count : Nat) : RefRvalue
  | ref (borrowKind : BorrowKind) (place : RefPlace) : RefRvalue
  | threadLocalRef (defPath : DefPath) : RefRvalue
  | rawPtr (mutability : Mutability) (place : RefPlace) : RefRvalue
  | len (place : RefPlace) : RefRvalue
  | cast (kind : CastKind) (op : RefOperand) (targetTy : TyId) : RefRvalue
  | binaryOp (op : BinOp) (lhs : RefOperand) (rhs : RefOperand) : RefRvalue
  | nullaryOp (op : NullOp) (ty : TyId) : RefRvalue
  | unaryOp (op : UnOp) (val : RefOperand) : RefRvalue
  | discriminant (place : RefPlace) : RefRvalue
  | aggregate (kind : RefAggregateKind) (operands : List RefOperand) : RefRvalue
  | shallowInitBox (op : RefOperand) (contentTy : TyId) : RefRvalue
  | copyForDeref (place : RefPlace) : RefRvalue
  | wrapUnsafeBinder (op : RefOperand) (targetTy : TyId) : RefRvalue

/-- Reference non-diverging intrinsic. -/
inductive RefNonDivergingIntrinsic : Type where
  | assume (op : RefOperand) : RefNonDivergingIntrinsic
  | copyNonOverlapping (src : RefOperand) (dst : RefOperand) (count : RefOperand) :
      RefNonDivergingIntrinsic

/-- Reference statement kind (all 12 `StatementKind` constructors). -/
inductive RefStatementKind : Type where
  | assign (place : RefPlace) (rvalue : RefRvalue) : RefStatementKind
  | setDiscriminant (place : RefPlace) (variantIdx : VariantIdx) : RefStatementKind
  | deinit (place : RefPlace) : RefStatementKind
  | storageLive (local_ : Local) : RefStatementKind
  | storageDead (local_ : Local) : RefStatementKind
  | retag (kind : RetagKind) (place : RefPlace) : RefStatementKind
  | placeMention (place : RefPlace) : RefStatementKind
  | intrinsic (intrinsic : RefNonDivergingIntrinsic) : RefStatementKind
  | coverage : RefStatementKind
  | constEvalCounter : RefStatementKind
  | backwardIncompatibleDropHint (place : RefPlace) : RefStatementKind
  | nop : RefStatementKind

/-- Reference statement. -/
structure RefStatement : Type where
  kind : RefStatementKind
  span : String

/-- Reference terminator kind (all 11 `TerminatorKind` constructors). -/
inductive RefTerminatorKind : Type where
  | goto (target : BasicBlockIdx) : RefTerminatorKind
  | switchInt (discr : RefOperand) (targets : SwitchTargets) : RefTerminatorKind
  | unwindResume : RefTerminatorKind
  | unwindTerminate : RefTerminatorKind
  | return_ : RefTerminatorKind
  | unreachable : RefTerminatorKind
  | drop (place : RefPlace) (target : BasicBlockIdx) (unwind : UnwindAction) : RefTerminatorKind
  | call (func : RefOperand) (args : List RefOperand) (destination : RefPlace)
      (target : Option BasicBlockIdx) (unwind : UnwindAction) : RefTerminatorKind
  | tailCall (func : RefOperand) (args : List RefOperand) : RefTerminatorKind
  | assert (cond : RefOperand) (expected : Bool) (target : BasicBlockIdx)
      (unwind : UnwindAction) : RefTerminatorKind
  | inlineAsm (template : String) (targets : List BasicBlockIdx) (unwind : UnwindAction) :
      RefTerminatorKind

/-- Reference terminator. -/
structure RefTerminator : Type where
  kind : RefTerminatorKind
  span : String

/-- Reference basic block. -/
structure RefBasicBlock : Type where
  statements : List RefStatement
  terminator : RefTerminator
  isCleanup : Bool

/-- Reference local declaration. -/
structure RefLocalDecl : Type where
  mutability : Mutability
  ty : TyId
  debugName : Option String

/-- Reference body: every `CapturedMir` field, with `TyId`-indexed syntax. -/
structure RefBody : Type where
  defPath : DefPath
  phase : MirPhaseTag
  role : ContractRole
  argCount : Nat
  localDecls : List RefLocalDecl
  basicBlocks : List RefBasicBlock
  fnAbi : FnAbi
  layouts : LayoutTable
  allocations : List CapturedAllocation
  typeParamCount : Nat
  genericParams : List GenericParamDef
  traitImpls : List TraitImplEntry

/-- Multi-body `V2026_06_01` program (`M_anneal` input). -/
structure V2026Prog : Type where
  bodies : List CapturedMir
  entry : Nat

/-- Multi-body reference program (`M_ref` input) with one shared type table. -/
structure RefProg : Type where
  bodies : List RefBody
  entry : Nat
  types : TypeTable

/-! ### `Ty` occurrences of every syntax node -/

def projElemTys : ProjectionElem → List Ty
  | .field _ ty => [ty]
  | .opaqueCast ty => [ty]
  | .unwrapUnsafeBinder ty => [ty]
  | _ => []

def placeTys (p : Place) : List Ty := p.projection.flatMap projElemTys

def operandTys : Operand → List Ty
  | .copy p => placeTys p
  | .move p => placeTys p
  | .constant c => [c.ty]

def aggKindTys : AggregateKind → List Ty
  | .array t => [t]
  | .rawPtr t _ => [t]
  | _ => []

def rvalueTys : Rvalue → List Ty
  | .use op => operandTys op
  | .repeat op _ => operandTys op
  | .ref _ p => placeTys p
  | .threadLocalRef _ => []
  | .rawPtr _ p => placeTys p
  | .len p => placeTys p
  | .cast _ op t => operandTys op ++ [t]
  | .binaryOp _ l r => operandTys l ++ operandTys r
  | .nullaryOp _ t => [t]
  | .unaryOp _ op => operandTys op
  | .discriminant p => placeTys p
  | .aggregate k ops => aggKindTys k ++ ops.flatMap operandTys
  | .shallowInitBox op t => operandTys op ++ [t]
  | .copyForDeref p => placeTys p
  | .wrapUnsafeBinder op t => operandTys op ++ [t]

def intrinsicTys : NonDivergingIntrinsic → List Ty
  | .assume op => operandTys op
  | .copyNonOverlapping a b c => operandTys a ++ operandTys b ++ operandTys c

def stmtKindTys : StatementKind → List Ty
  | .assign p rv => placeTys p ++ rvalueTys rv
  | .setDiscriminant p _ => placeTys p
  | .deinit p => placeTys p
  | .storageLive _ => []
  | .storageDead _ => []
  | .retag _ p => placeTys p
  | .placeMention p => placeTys p
  | .intrinsic i => intrinsicTys i
  | .coverage => []
  | .constEvalCounter => []
  | .backwardIncompatibleDropHint p => placeTys p
  | .nop => []

def stmtTys (s : Statement) : List Ty := stmtKindTys s.kind

def termKindTys : TerminatorKind → List Ty
  | .goto _ => []
  | .switchInt d _ => operandTys d
  | .unwindResume => []
  | .unwindTerminate => []
  | .return_ => []
  | .unreachable => []
  | .drop p _ _ => placeTys p
  | .call f args d _ _ => operandTys f ++ args.flatMap operandTys ++ placeTys d
  | .tailCall f args => operandTys f ++ args.flatMap operandTys
  | .assert c _ _ _ => operandTys c
  | .inlineAsm _ _ _ => []

def blockTys (b : BasicBlockData) : List Ty :=
  b.statements.flatMap stmtTys ++ termKindTys b.terminator.kind

def bodyTys (b : CapturedMir) : List Ty :=
  b.localDecls.map LocalDecl.ty ++ b.basicBlocks.flatMap blockTys

def progTys (p : V2026Prog) : List Ty := p.bodies.flatMap bodyTys

/-- Structural `RigidTy` arguments appearing in `CapturedMir.traitImpls`. -/
def bodyTraitKinds (b : CapturedMir) : List RigidTy :=
  b.traitImpls.flatMap (fun ti => ti.traitRef.args)

def progTraitKinds (p : V2026Prog) : List RigidTy :=
  p.bodies.flatMap bodyTraitKinds

/-! ### Encoder -/

def encodeProjElem (tt : TypeTable) : ProjectionElem → RefProjectionElem
  | .deref => .deref
  | .field f ty => .field f (encodeType tt ty)
  | .index i => .index i
  | .constantIndex o m e => .constantIndex o m e
  | .subslice f t e => .subslice f t e
  | .downcast n v => .downcast n v
  | .opaqueCast ty => .opaqueCast (encodeType tt ty)
  | .unwrapUnsafeBinder ty => .unwrapUnsafeBinder (encodeType tt ty)

def encodePlace (tt : TypeTable) (p : Place) : RefPlace :=
  ⟨p.local_, p.projection.map (encodeProjElem tt)⟩

def encodeOperand (tt : TypeTable) : Operand → RefOperand
  | .copy p => .copy (encodePlace tt p)
  | .move p => .move (encodePlace tt p)
  | .constant c => .constant ⟨encodeType tt c.ty, c.val⟩

def encodeAggKind (tt : TypeTable) : AggregateKind → RefAggregateKind
  | .array t => .array (encodeType tt t)
  | .tuple => .tuple
  | .adt p v f => .adt p v f
  | .closure p => .closure p
  | .coroutine p => .coroutine p
  | .rawPtr t m => .rawPtr (encodeType tt t) m

def encodeRvalue (tt : TypeTable) : Rvalue → RefRvalue
  | .use op => .use (encodeOperand tt op)
  | .repeat op n => .repeat (encodeOperand tt op) n
  | .ref bk p => .ref bk (encodePlace tt p)
  | .threadLocalRef d => .threadLocalRef d
  | .rawPtr m p => .rawPtr m (encodePlace tt p)
  | .len p => .len (encodePlace tt p)
  | .cast k op t => .cast k (encodeOperand tt op) (encodeType tt t)
  | .binaryOp o l r => .binaryOp o (encodeOperand tt l) (encodeOperand tt r)
  | .nullaryOp o t => .nullaryOp o (encodeType tt t)
  | .unaryOp o op => .unaryOp o (encodeOperand tt op)
  | .discriminant p => .discriminant (encodePlace tt p)
  | .aggregate k ops => .aggregate (encodeAggKind tt k) (ops.map (encodeOperand tt))
  | .shallowInitBox op t => .shallowInitBox (encodeOperand tt op) (encodeType tt t)
  | .copyForDeref p => .copyForDeref (encodePlace tt p)
  | .wrapUnsafeBinder op t => .wrapUnsafeBinder (encodeOperand tt op) (encodeType tt t)

def encodeIntrinsic (tt : TypeTable) : NonDivergingIntrinsic → RefNonDivergingIntrinsic
  | .assume op => .assume (encodeOperand tt op)
  | .copyNonOverlapping a b c =>
    .copyNonOverlapping (encodeOperand tt a) (encodeOperand tt b) (encodeOperand tt c)

def encodeStmtKind (tt : TypeTable) : StatementKind → RefStatementKind
  | .assign p rv => .assign (encodePlace tt p) (encodeRvalue tt rv)
  | .setDiscriminant p v => .setDiscriminant (encodePlace tt p) v
  | .deinit p => .deinit (encodePlace tt p)
  | .storageLive l => .storageLive l
  | .storageDead l => .storageDead l
  | .retag k p => .retag k (encodePlace tt p)
  | .placeMention p => .placeMention (encodePlace tt p)
  | .intrinsic i => .intrinsic (encodeIntrinsic tt i)
  | .coverage => .coverage
  | .constEvalCounter => .constEvalCounter
  | .backwardIncompatibleDropHint p => .backwardIncompatibleDropHint (encodePlace tt p)
  | .nop => .nop

def encodeStmt (tt : TypeTable) (s : Statement) : RefStatement :=
  ⟨encodeStmtKind tt s.kind, s.span⟩

def encodeTermKind (tt : TypeTable) : TerminatorKind → RefTerminatorKind
  | .goto t => .goto t
  | .switchInt d ts => .switchInt (encodeOperand tt d) ts
  | .unwindResume => .unwindResume
  | .unwindTerminate => .unwindTerminate
  | .return_ => .return_
  | .unreachable => .unreachable
  | .drop p t u => .drop (encodePlace tt p) t u
  | .call f args d t u =>
    .call (encodeOperand tt f) (args.map (encodeOperand tt)) (encodePlace tt d) t u
  | .tailCall f args => .tailCall (encodeOperand tt f) (args.map (encodeOperand tt))
  | .assert c e t u => .assert (encodeOperand tt c) e t u
  | .inlineAsm s ts u => .inlineAsm s ts u

def encodeTerminator (tt : TypeTable) (t : Terminator) : RefTerminator :=
  ⟨encodeTermKind tt t.kind, t.span⟩

def encodeBlock (tt : TypeTable) (b : BasicBlockData) : RefBasicBlock :=
  ⟨b.statements.map (encodeStmt tt), encodeTerminator tt b.terminator, b.isCleanup⟩

def encodeLocalDecl (tt : TypeTable) (d : LocalDecl) : RefLocalDecl :=
  ⟨d.mutability, encodeType tt d.ty, d.debugName⟩

def encodeBody (tt : TypeTable) (b : CapturedMir) : RefBody :=
  { defPath := b.defPath, phase := b.phase, role := b.role, argCount := b.argCount
    localDecls := b.localDecls.map (encodeLocalDecl tt)
    basicBlocks := b.basicBlocks.map (encodeBlock tt)
    fnAbi := b.fnAbi, layouts := b.layouts, allocations := b.allocations
    typeParamCount := b.typeParamCount, genericParams := b.genericParams
    traitImpls := b.traitImpls }

/-- The program's canonical type table (interning all `Ty` occurrences plus all
`CapturedMir.traitImpls` `RigidTy` arguments in bottom-up post-order). -/
def collectProgTypes (p : V2026Prog) : TypeTable :=
  internKinds (internTys initTypeTable (progTys p)) (progTraitKinds p)

/-- Total encoder `V2026Prog → RefProg`. -/
def encodeProg (p : V2026Prog) : RefProg :=
  let tt := collectProgTypes p
  ⟨p.bodies.map (encodeBody tt), p.entry, tt⟩

/-! ### Decoder -/

def decodeProjElem (tt : TypeTable) : RefProjectionElem → Option ProjectionElem
  | .deref => some .deref
  | .field f t => (decodeType tt t).map (.field f)
  | .index i => some (.index i)
  | .constantIndex o m e => some (.constantIndex o m e)
  | .subslice f t e => some (.subslice f t e)
  | .downcast n v => some (.downcast n v)
  | .opaqueCast t => (decodeType tt t).map .opaqueCast
  | .unwrapUnsafeBinder t => (decodeType tt t).map .unwrapUnsafeBinder

def decodePlace (tt : TypeTable) (p : RefPlace) : Option Place :=
  (decodeList (decodeProjElem tt) p.projection).map (fun proj => ⟨p.local_, proj⟩)

def decodeOperand (tt : TypeTable) : RefOperand → Option Operand
  | .copy p => (decodePlace tt p).map .copy
  | .move p => (decodePlace tt p).map .move
  | .constant c => (decodeType tt c.ty).map (fun ty => .constant ⟨ty, c.val⟩)

def decodeAggKind (tt : TypeTable) : RefAggregateKind → Option AggregateKind
  | .array t => (decodeType tt t).map .array
  | .tuple => some .tuple
  | .adt p v f => some (.adt p v f)
  | .closure p => some (.closure p)
  | .coroutine p => some (.coroutine p)
  | .rawPtr t m => (decodeType tt t).map (fun ty => .rawPtr ty m)

def decodeRvalue (tt : TypeTable) : RefRvalue → Option Rvalue
  | .use op => (decodeOperand tt op).map .use
  | .repeat op n => (decodeOperand tt op).map (fun o => .repeat o n)
  | .ref bk p => (decodePlace tt p).map (.ref bk)
  | .threadLocalRef d => some (.threadLocalRef d)
  | .rawPtr m p => (decodePlace tt p).map (.rawPtr m)
  | .len p => (decodePlace tt p).map .len
  | .cast k op t =>
    (decodeOperand tt op).bind (fun o => (decodeType tt t).map (fun ty => .cast k o ty))
  | .binaryOp o l r =>
    (decodeOperand tt l).bind (fun l' => (decodeOperand tt r).map (fun r' => .binaryOp o l' r'))
  | .nullaryOp o t => (decodeType tt t).map (.nullaryOp o)
  | .unaryOp o op => (decodeOperand tt op).map (.unaryOp o)
  | .discriminant p => (decodePlace tt p).map .discriminant
  | .aggregate k ops =>
    (decodeAggKind tt k).bind (fun k' => (decodeList (decodeOperand tt) ops).map (.aggregate k'))
  | .shallowInitBox op t =>
    (decodeOperand tt op).bind (fun o => (decodeType tt t).map (fun ty => .shallowInitBox o ty))
  | .copyForDeref p => (decodePlace tt p).map .copyForDeref
  | .wrapUnsafeBinder op t =>
    (decodeOperand tt op).bind (fun o => (decodeType tt t).map (fun ty => .wrapUnsafeBinder o ty))

def decodeIntrinsic (tt : TypeTable) : RefNonDivergingIntrinsic → Option NonDivergingIntrinsic
  | .assume op => (decodeOperand tt op).map .assume
  | .copyNonOverlapping a b c =>
    (decodeOperand tt a).bind (fun a' => (decodeOperand tt b).bind (fun b' =>
      (decodeOperand tt c).map (fun c' => .copyNonOverlapping a' b' c')))

def decodeStmtKind (tt : TypeTable) : RefStatementKind → Option StatementKind
  | .assign p rv => (decodePlace tt p).bind (fun p' => (decodeRvalue tt rv).map (.assign p'))
  | .setDiscriminant p v => (decodePlace tt p).map (fun p' => .setDiscriminant p' v)
  | .deinit p => (decodePlace tt p).map .deinit
  | .storageLive l => some (.storageLive l)
  | .storageDead l => some (.storageDead l)
  | .retag k p => (decodePlace tt p).map (.retag k)
  | .placeMention p => (decodePlace tt p).map .placeMention
  | .intrinsic i => (decodeIntrinsic tt i).map .intrinsic
  | .coverage => some .coverage
  | .constEvalCounter => some .constEvalCounter
  | .backwardIncompatibleDropHint p => (decodePlace tt p).map .backwardIncompatibleDropHint
  | .nop => some .nop

def decodeStmt (tt : TypeTable) (s : RefStatement) : Option Statement :=
  (decodeStmtKind tt s.kind).map (fun k => ⟨k, s.span⟩)

def decodeTermKind (tt : TypeTable) : RefTerminatorKind → Option TerminatorKind
  | .goto t => some (.goto t)
  | .switchInt d ts => (decodeOperand tt d).map (fun d' => .switchInt d' ts)
  | .unwindResume => some .unwindResume
  | .unwindTerminate => some .unwindTerminate
  | .return_ => some .return_
  | .unreachable => some .unreachable
  | .drop p t u => (decodePlace tt p).map (fun p' => .drop p' t u)
  | .call f args d t u =>
    (decodeOperand tt f).bind (fun f' => (decodeList (decodeOperand tt) args).bind (fun a' =>
      (decodePlace tt d).map (fun d' => .call f' a' d' t u)))
  | .tailCall f args =>
    (decodeOperand tt f).bind (fun f' => (decodeList (decodeOperand tt) args).map (.tailCall f'))
  | .assert c e t u => (decodeOperand tt c).map (fun c' => .assert c' e t u)
  | .inlineAsm s ts u => some (.inlineAsm s ts u)

def decodeTerminator (tt : TypeTable) (t : RefTerminator) : Option Terminator :=
  (decodeTermKind tt t.kind).map (fun k => ⟨k, t.span⟩)

def decodeBlock (tt : TypeTable) (b : RefBasicBlock) : Option BasicBlockData :=
  (decodeList (decodeStmt tt) b.statements).bind (fun ss =>
    (decodeTerminator tt b.terminator).map (fun t => ⟨ss, t, b.isCleanup⟩))

def decodeLocalDecl (tt : TypeTable) (d : RefLocalDecl) : Option LocalDecl :=
  (decodeType tt d.ty).map (fun ty => ⟨d.mutability, ty, d.debugName⟩)

def decodeBody (tt : TypeTable) (b : RefBody) : Option CapturedMir :=
  (decodeList (decodeLocalDecl tt) b.localDecls).bind (fun ds =>
    (decodeList (decodeBlock tt) b.basicBlocks).map (fun bbs =>
      { defPath := b.defPath, phase := b.phase, role := b.role, argCount := b.argCount
        localDecls := ds, basicBlocks := bbs, fnAbi := b.fnAbi, layouts := b.layouts
        allocations := b.allocations, typeParamCount := b.typeParamCount
        genericParams := b.genericParams, traitImpls := b.traitImpls }))

/-- Total decoder (fails closed on dangling `TyId`s). -/
def decodeProg (rp : RefProg) : Option V2026Prog :=
  (decodeList (decodeBody rp.types) rp.bodies).map (fun bs => ⟨bs, rp.entry⟩)

/-! ### Round-trip lemmas (relative to any table containing the occurrences) -/

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
  roundtrip_body b (fun _ hy => hext.types_mem (mem_internTys hy))

/-- Canonical interning: both tables are duplicate-free, nominal `TyId`
equality coincides with structural `Ty` equality on interned types, every
interned type's kinds (bottom-up) are interned, and the built-in kinds sit at
`KindId`s `0, 1, 2`. -/
theorem encodeProg_types_canonical (p : V2026Prog) :
    typesAreCanonical (encodeProg p).types.types = true ∧
    typesAreCanonical (encodeProg p).types.kinds = true ∧
    (∀ (i j : TyId) (ty₁ ty₂ : Ty), nth? (encodeProg p).types.types i = some ty₁ →
      nth? (encodeProg p).types.types j = some ty₂ → (i = j ↔ ty₁ = ty₂)) ∧
    (∀ ty ∈ (encodeProg p).types.types, RigidTy.postorder ty.kind ⊆ (encodeProg p).types.kinds) ∧
    nth? (encodeProg p).types.kinds 0 = some (.tuple []) ∧
    nth? (encodeProg p).types.kinds 1 = some .bool ∧
    nth? (encodeProg p).types.kinds 2 = some (.uint .usize) := by
  have hg := internKinds_good (internTys_good initTypeTable_good (progTys p)) (progTraitKinds p)
  obtain ⟨⟨l, hl⟩, _⟩ :=
    (internTys_extends initTypeTable (progTys p)).trans (internKinds_extends _ (progTraitKinds p))
  refine ⟨hg.2.1, hg.1, ?_, hg.2.2, ?_, ?_, ?_⟩
  · intro i j ty₁ ty₂ hi hj
    constructor
    · intro e; subst e; rw [hi] at hj; exact Option.some.inj hj
    · intro e; subst e; exact nth?_injective_of_canonical hg.2.1 hi hj
  all_goals
    show nth? (collectProgTypes p).kinds _ = _
    simp only [collectProgTypes]; rw [hl]; rfl

/-- Every `RigidTy` argument in every `CapturedMir.traitImpls` entry of `p` has
its full bottom-up `RigidTy.postorder` interned in `(encodeProg p).types.kinds`. -/
theorem encodeProg_traitImpl_kinds_interned (p : V2026Prog) (b : CapturedMir)
    (hb : b ∈ p.bodies) (ti : TraitImplEntry) (hti : ti ∈ b.traitImpls)
    (k : RigidTy) (hk : k ∈ ti.traitRef.args) :
    RigidTy.postorder k ⊆ (encodeProg p).types.kinds := by
  have hmem : k ∈ progTraitKinds p :=
    List.mem_flatMap.mpr ⟨b, hb, List.mem_flatMap.mpr ⟨ti, hti, hk⟩⟩
  exact mem_internKinds_postorder hmem

/-! ### Anti-laundering: constructor tags are preserved -/

def stmtKindTag : StatementKind → Nat
  | .assign _ _ => 0 | .setDiscriminant _ _ => 1 | .deinit _ => 2 | .storageLive _ => 3
  | .storageDead _ => 4 | .retag _ _ => 5 | .placeMention _ => 6 | .intrinsic _ => 7
  | .coverage => 8 | .constEvalCounter => 9 | .backwardIncompatibleDropHint _ => 10 | .nop => 11

def refStmtKindTag : RefStatementKind → Nat
  | .assign _ _ => 0 | .setDiscriminant _ _ => 1 | .deinit _ => 2 | .storageLive _ => 3
  | .storageDead _ => 4 | .retag _ _ => 5 | .placeMention _ => 6 | .intrinsic _ => 7
  | .coverage => 8 | .constEvalCounter => 9 | .backwardIncompatibleDropHint _ => 10 | .nop => 11

def termKindTag : TerminatorKind → Nat
  | .goto _ => 0 | .switchInt _ _ => 1 | .unwindResume => 2 | .unwindTerminate => 3
  | .return_ => 4 | .unreachable => 5 | .drop _ _ _ => 6 | .call _ _ _ _ _ => 7
  | .tailCall _ _ => 8 | .assert _ _ _ _ => 9 | .inlineAsm _ _ _ => 10

def refTermKindTag : RefTerminatorKind → Nat
  | .goto _ => 0 | .switchInt _ _ => 1 | .unwindResume => 2 | .unwindTerminate => 3
  | .return_ => 4 | .unreachable => 5 | .drop _ _ _ => 6 | .call _ _ _ _ _ => 7
  | .tailCall _ _ => 8 | .assert _ _ _ _ => 9 | .inlineAsm _ _ _ => 10

def rvalueTag : Rvalue → Nat
  | .use _ => 0 | .repeat _ _ => 1 | .ref _ _ => 2 | .threadLocalRef _ => 3 | .rawPtr _ _ => 4
  | .len _ => 5 | .cast _ _ _ => 6 | .binaryOp _ _ _ => 7 | .nullaryOp _ _ => 8
  | .unaryOp _ _ => 9 | .discriminant _ => 10 | .aggregate _ _ => 11 | .shallowInitBox _ _ => 12
  | .copyForDeref _ => 13 | .wrapUnsafeBinder _ _ => 14

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


/-! ## Part 4 — Demand-time `LayoutQuery` hook (`proofs-rs/lean-miri#64`)

`MiriRefMachine`'s `localLayout`, `scalarTypeClass`, `castTypeInfo`,
`pointeeTypes`, and `retagTypeShape` hooks are answered *on demand* from the
single source `(TypeTable, LayoutTable)`; nothing is pre-materialized. -/

theorem nth?_eq_getElem? {α : Type} : ∀ (xs : List α) (i : Nat), nth? xs i = xs[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => by simp [nth?, nth?_eq_getElem? xs i]

/-- `nth? L.entries` *is* Trusted's `LayoutTable.lookup`. -/
theorem nth?_entries_eq_lookup (L : LayoutTable) (i : Nat) : nth? L.entries i = L.lookup i := by
  simp [LayoutTable.lookup, Trusted.Sequence.get?, nth?_eq_getElem?]

/-- Scalar classification used by `scalarTypeClass` / `castTypeInfo`. -/
inductive ScalarClass : Type where
  | bool | char | int (signed : Bool) | float | ptr | unit
  deriving DecidableEq

/-- Scalar class of a kind (`none` for aggregates). -/
def scalarClassOfKind : RigidTy → Option ScalarClass
  | .bool => some .bool
  | .char => some .char
  | .int _ => some (.int true)
  | .uint _ => some (.int false)
  | .float _ => some .float
  | .ref _ _ => some .ptr
  | .rawPtr _ _ => some .ptr
  | .fnPtr _ _ _ _ => some .ptr
  | .tuple [] => some .unit
  | _ => none

/-- Retag shape (`retagTypeShape`). -/
inductive RetagShape : Type where
  | none | sharedRef (freeze : Bool) | mutRef | rawPtr
  deriving DecidableEq

def retagShapeOfKind : RigidTy → RetagShape
  | .ref .not p => .sharedRef (rigidTyIsFreeze defaultTyEqFuel p)
  | .ref .mut _ => .mutRef
  | .rawPtr _ _ => .rawPtr
  | _ => .none

/-- Table-independent synthesized layout (via Trusted's `RigidTy.computeLayout`),
used for pointees, array elements and sub-slices. -/
def pointeeLayoutOf (ptrBits : Nat) (k : RigidTy) : Option TypeLayout :=
  RigidTy.computeLayout ptrBits [] [] .none k

/-- Demand-time layout queries. -/
inductive LayoutQuery : Type where
  | localLayout (ty : TyId)
  | scalarTypeClass (ty : TyId)
  | castTypeInfo (src dst : TyId)
  | pointeeTypes (ty : TyId)
  | retagTypeShape (ty : TyId)
  | builtinLayout (k : KindId)

/-- Answers. -/
inductive LayoutAnswer : Type where
  | layout (kind : RigidTy) (l : TypeLayout)
  | scalar (c : ScalarClass) (sizeBytes : Nat)
  | cast (src dst : ScalarClass) (srcBytes dstBytes : Nat)
  | pointee (kind : KindId) (layout : Option TypeLayout)
  | retag (s : RetagShape)

/-- Results: answers, or fail-closed `missingHook` (dangling `TyId` /
`LayoutIdx` / un-interned pointee) and `blocked` (query not applicable). -/
inductive LayoutResult : Type where
  | ok (a : LayoutAnswer)
  | missingHook
  | blocked

/-- Single-source lookup of a `TyId`'s `Ty` and compiler layout. -/
def tyLayout (tt : TypeTable) (L : LayoutTable) (t : TyId) : Option (Ty × TypeLayout) :=
  match nth? tt.types t with
  | none => none
  | some ty =>
    match nth? L.entries ty.layoutIdx with
    | none => none
    | some l => some (ty, l)

/-- The demand-time query evaluator. -/
def evalLayoutQuery (tt : TypeTable) (L : LayoutTable) : LayoutQuery → LayoutResult
  | .localLayout t =>
    match tyLayout tt L t with
    | none => .missingHook
    | some (ty, l) => .ok (.layout ty.kind l)
  | .scalarTypeClass t =>
    match tyLayout tt L t with
    | none => .missingHook
    | some (ty, l) =>
      match scalarClassOfKind ty.kind with
      | none => .blocked
      | some c => .ok (.scalar c l.size.bytes)
  | .castTypeInfo s d =>
    match tyLayout tt L s, tyLayout tt L d with
    | some (sty, sl), some (dty, dl) =>
      match scalarClassOfKind sty.kind, scalarClassOfKind dty.kind with
      | some sc, some dc => .ok (.cast sc dc sl.size.bytes dl.size.bytes)
      | _, _ => .blocked
    | _, _ => .missingHook
  | .pointeeTypes t =>
    match nth? tt.types t with
    | none => .missingHook
    | some ty =>
      match ty.kind with
      | .ref _ pk | .rawPtr _ pk =>
        match indexOf? tt.kinds pk with
        | none => .missingHook
        | some k => .ok (.pointee k (pointeeLayoutOf L.pointerBits pk))
      | _ => .blocked
  | .retagTypeShape t =>
    match nth? tt.types t with
    | none => .missingHook
    | some ty => .ok (.retag (retagShapeOfKind ty.kind))
  | .builtinLayout k =>
    match nth? tt.kinds k with
    | none => .missingHook
    | some kind =>
      match pointeeLayoutOf L.pointerBits kind with
      | none => .blocked
      | some l => .ok (.layout kind l)

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
      have key : ∀ pk i, indexOf? tt.kinds pk = some i → indexOf? tt'.kinds pk = some i := by
        intro pk i hi; rw [hk, indexOf?_append_of_mem lk (mem_of_nth? (nth?_of_indexOf? hi)), hi]
      generalize ty.kind = kd at h ⊢
      cases kd with
      | ref m pk =>
        simp only at h ⊢
        cases hi : indexOf? tt.kinds pk with
        | none => simp [hi] at h
        | some i => simp only [hi] at h; simp only [key pk i hi, hptr]; exact h
      | rawPtr m pk =>
        simp only at h ⊢
        cases hi : indexOf? tt.kinds pk with
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

/-- Eager `O(|types|)` pre-materialization (the design `#64` replaces). -/
def eagerLayoutTable (tt : TypeTable) (L : LayoutTable) : List (Option (RigidTy × TypeLayout)) :=
  tt.types.map (fun ty => (nth? L.entries ty.layoutIdx).map (fun l => (ty.kind, l)))

theorem nth?_map {α β : Type} (f : α → β) : ∀ (xs : List α) (i : Nat),
    nth? (xs.map f) i = (nth? xs i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => nth?_map f xs i

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
    rcases hk with hk | hk <;> rw [hk] <;> simp only [RigidTy.postorder] <;>
      exact List.mem_append_left _ (RigidTy.mem_postorder_self pk)
  obtain ⟨i, hi⟩ := indexOf?_isSome_of_mem hpk
  refine ⟨i, ?_⟩
  simp only [evalLayoutQuery, h]
  rcases hk with hk | hk <;> rw [hk] <;> simp only [hi]


/-! ## Part 5 — Shared byte-level machine (`AbstractByte`, Tree Borrows)

Both `M_anneal` and `M_ref` run on `PState`: frames of local slots
(`imm` = LeanMiri `LocalValue.live (.immediate _)`, `mem` = `.live (.indirect
mplace)`), a byte heap of real `AbstractByte`s, and a Tree Borrows table of
real `BorrowEntry`s updated with Trusted's `treeBorrowNodeAccess`. The field
`pendingMoveDeinit` is LeanMiri's `MachineState.pendingMoveDeinit`
(`MachineHooks.lean` in the 6-file patch); `M_anneal` never sets it. -/

/-- Raw bytes. -/
abbrev Bytes := List AbstractByte

/-- Undefined-behavior reasons (canaries check *which* UB fires). -/
inductive UBReason : Type where
  | invalidUninitBytes | deadLocal | danglingPointer | outOfBounds | treeBorrows
  | invalidPointer | overlappingCopy | unreachable | divergingReturn | badControlFlow
  deriving DecidableEq

/-- The two fault poles (`.undefined` ↔ `.ub`, `.unsupported` ↔ `.blocked`). -/
inductive Fault : Type where
  | ub (why : UBReason)
  | unsupported
  deriving DecidableEq

/-- Resolved type: structural kind and compiler layout. -/
abbrev SemTy := RigidTy × TypeLayout

/-- Local slot. -/
inductive PSlot : Type where
  | dead
  | imm (b : Bytes)
  | mem (alloc : Nat)

/-- Memory place: allocation, byte window, and access provenance (`none` =
direct access to the local, i.e. through the allocation's root tag). -/
structure MPlace : Type where
  alloc : Nat
  offset : Nat
  size : Nat
  tag : Option Nat

/-- An assignment or call destination, evaluated **before** the rvalue or call
arguments (rustc `eval_rvalue_into_place` / `Call.evalCallTerminator` first
runs `eval_place(dest)`, and `copyRuntimePlaceNoValidate` receives an
already-resolved `RuntimePlace`). -/
inductive DestPlace : Type where
  | imm (l : Local)
  | mem (mp : MPlace)

/-- Call-stack frame (`retDest` caches the pre-resolved caller destination for
`TerminatorKind.call`, matching `Miri.Interpreter.Frame.returnPlace`). -/
structure PFrame : Type where
  body : Nat
  block : Nat
  stmt : Nat
  locals : List PSlot
  retDest : Option DestPlace := none

/-- Shared machine state. -/
structure PState : Type where
  frames : List PFrame
  heap : List (Option Bytes)
  borrows : List BorrowEntry
  nextTag : Nat
  pendingMoveDeinit : Bool

def uninitBytes (n : Nat) : Bytes := List.replicate n .uninit

def setNth? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v => (setNth? xs n v).map (x :: ·)

def sliceBytes (b : Bytes) (off len : Nat) : Bytes := (b.drop off).take len

def overwriteBytes (b : Bytes) (off : Nat) (w : Bytes) : Bytes :=
  b.take off ++ w ++ b.drop (off + w.length)

/-- LeanMiri `OpTy`: an already-loaded immediate or a reference to memory. -/
inductive OpTy : Type where
  | immediate (b : Bytes)
  | indirect (mp : MPlace)

/-- Tree Borrows relative position of an access through `tag` w.r.t. `e`. -/
def tbRelatedness (all : List BorrowEntry) (tag : Option Nat) (e : BorrowEntry) :
    TreeBorrowRelatedness :=
  match tag with
  | none => .foreignAccess
  | some t =>
    match isBorrowDescendantOrSelf all t e.tag with
    | true => .localAccess
    | false => .foreignAccess

def tbAccessAux (kind : TreeBorrowAccessKind) (all : List BorrowEntry) (alloc : Nat)
    (tag : Option Nat) (off len : Nat) : List BorrowEntry → Option (List BorrowEntry)
  | [] => some []
  | e :: es =>
    match tbAccessAux kind all alloc tag off len es with
    | none => none
    | some es' =>
      match Nat.beq e.targetLocal alloc && byteRangesOverlapBool e.rangeOffset e.rangeLen off len with
      | true =>
        let tr := treeBorrowNodeAccess kind (tbRelatedness all tag e) e.perm false
        match treeBorrowTransitionIsUB tr with
        | true => none
        | false => some (applyTreeBorrowTransition e tr :: es')
      | false => some (e :: es')

/-- Perform a Tree Borrows access of `kind` on every overlapping entry
(`none` = undefined behavior). -/
def tbAccess (kind : TreeBorrowAccessKind) (borrows : List BorrowEntry) (alloc : Nat)
    (tag : Option Nat) (off len : Nat) : Option (List BorrowEntry) :=
  tbAccessAux kind borrows alloc tag off len borrows

def heapGet (st : PState) (a : Nat) : Option Bytes :=
  match nth? st.heap a with
  | some (some b) => some b
  | _ => none

def putHeap (st : PState) (a : Nat) (b : Bytes) : Except Fault PState :=
  match setNth? st.heap a (some b) with
  | none => .error (.ub .danglingPointer)
  | some h => .ok { st with heap := h }

/-- Typed load with a Tree Borrows read access. -/
def loadMPlace (st : PState) (mp : MPlace) : Except Fault (Bytes × PState) :=
  match heapGet st mp.alloc with
  | none => .error (.ub .danglingPointer)
  | some b =>
    match Nat.ble (mp.offset + mp.size) b.length with
    | false => .error (.ub .outOfBounds)
    | true =>
      match tbAccess .read st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => .error (.ub .treeBorrows)
      | some bs => .ok (sliceBytes b mp.offset mp.size, { st with borrows := bs })

/-- Store with a Tree Borrows **write** access. -/
def storeMPlace (st : PState) (mp : MPlace) (w : Bytes) : Except Fault PState :=
  match heapGet st mp.alloc with
  | none => .error (.ub .danglingPointer)
  | some b =>
    match Nat.ble (mp.offset + mp.size) b.length && Nat.beq w.length mp.size with
    | false => .error (.ub .outOfBounds)
    | true =>
      match tbAccess .write st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => .error (.ub .treeBorrows)
      | some bs => putHeap { st with borrows := bs } mp.alloc (overwriteBytes b mp.offset w)

/-- The `deinitMovedPlace` write: `.uninit` over the moved window with **no**
Tree Borrows transition. -/
def deinitMPlaceRaw (st : PState) (mp : MPlace) : Except Fault PState :=
  match heapGet st mp.alloc with
  | none => .error (.ub .danglingPointer)
  | some b =>
    match Nat.ble (mp.offset + mp.size) b.length with
    | false => .error (.ub .outOfBounds)
    | true => putHeap st mp.alloc (overwriteBytes b mp.offset (uninitBytes mp.size))

def setLocalE (st : PState) (l : Local) (v : PSlot) : Except Fault PState :=
  match st.frames with
  | [] => .error .unsupported
  | fr :: rest =>
    match setNth? fr.locals l v with
    | none => .error (.ub .deadLocal)
    | some ls => .ok { st with frames := { fr with locals := ls } :: rest }

/-- Kinds kept as immediates (scalars, pointers, ZST unit); all others are
memory-backed. -/
def isImmKind : RigidTy → Bool
  | .bool | .char | .int _ | .uint _ | .float _ | .ref _ _ | .rawPtr _ _
  | .fnPtr _ _ _ _ | .fnDef _ _ | .never => true
  | .tuple [] => true
  | _ => false

/-- Validity of loaded bytes at a kind (`invalidUninitBytes` otherwise). -/
def validateBytes (k : RigidTy) (b : Bytes) : Bool :=
  match k with
  | .bool =>
    match decodeLittleEndianBytes b with
    | some (v, _) => Nat.beq b.length 1 && Nat.ble v 1
    | none => false
  | .char | .int _ | .uint _ | .float _ | .ref _ _ | .rawPtr _ _ | .fnPtr _ _ _ _ =>
    match decodeLittleEndianBytes b with
    | some _ => !(Nat.beq b.length 0)
    | none => false
  | _ => true

def checkValid (ty : SemTy) (b : Bytes) : Except Fault Unit :=
  match validateBytes ty.1 b with
  | true => .ok ()
  | false => .error (.ub .invalidUninitBytes)

/-- 8-byte little-endian pointer with `(alloc, tag)` provenance on every byte. -/
def ptrBytes (alloc tag off : Nat) : Bytes := encodeLittleEndianBytes off 8 (some (alloc, tag))

def decodePtr (b : Bytes) : Option (Nat × Nat × Nat) :=
  match Nat.beq b.length 8, decodeLittleEndianBytes b with
  | true, some (off, some (a, t)) => some (a, t, off)
  | _, _ => none

/-! ### Resolved ("semantic") syntax shared by both machines -/

inductive SemProj : Type where
  | deref
  | field (i : Nat) (ty : SemTy)
  | index (l : Local)
  | constantIndex (offset minLength : Nat) (fromEnd : Bool)
  | subslice (fromIdx toIdx : Nat) (fromEnd : Bool)
  | unsupported

structure SemPlace : Type where
  local_ : Local
  ty : SemTy
  projs : List SemProj

inductive SemOperand : Type where
  | copy (p : SemPlace)
  | move (p : SemPlace)
  | const (b : Bytes) (ty : SemTy)

inductive SemRvalue : Type where
  | use (op : SemOperand)
  | binaryOp (o : BinOp) (l r : SemOperand)
  | aggregate (ops : List SemOperand)
  | ref (mutbl : Bool) (p : SemPlace)
  | rawPtr (p : SemPlace)
  | unsupported

inductive SemStmt : Type where
  | assign (dest : SemPlace) (rv : SemRvalue)
  | deinit (p : SemPlace)
  | storageLive (l : Local) (ty : SemTy)
  | storageDead (l : Local)
  | nop
  | unsupported

structure ReturnSite : Type where
  dest : SemPlace
  target : Option Nat
  unwind : UnwindAction

inductive SemTerm : Type where
  | goto (bb : Nat)
  | ret (retTy : SemTy) (site : Option ReturnSite)
  | switchInt (d : SemOperand) (ts : SwitchTargets)
  | assert (c : SemOperand) (expected : Bool) (target : Nat) (unwind : UnwindAction)
  | call (callee : Option Nat) (calleeArgCount : Nat) (calleeLocals : List SemTy)
      (args : List SemOperand) (dest : SemPlace)
  | unwindResume (site : Option ReturnSite)
  | unreachable
  | unsupported

inductive Instr : Type where
  | stmt (ptrBits : Nat) (s : SemStmt)
  | term (ptrBits : Nat) (t : SemTerm)

/-! ### Places -/

def fieldOffset (l : TypeLayout) (i : Nat) : Option Nat :=
  match l.fields with
  | .arbitrary offsets _ => (nth? offsets i).map Size.bytes
  | .array stride _ => some (i * stride.bytes)
  | _ => none

def derefTarget (ptrBits : Nat) (b : Bytes) (ty : SemTy) : Except Fault (MPlace × SemTy) :=
  match ty.1 with
  | .ref _ pk | .rawPtr _ pk =>
    match pointeeLayoutOf ptrBits pk with
    | none => .error .unsupported
    | some pl =>
      match decodePtr b with
      | none => .error (.ub .invalidPointer)
      | some (a, t, off) => .ok (⟨a, off, pl.size.bytes, some t⟩, (pk, pl))
  | _ => .error .unsupported

def readUsizeLocal (fr : PFrame) (l : Local) : Except Fault Nat :=
  match nth? fr.locals l with
  | some (.imm b) =>
    match decodeLittleEndianBytes b with
    | some (v, _) => .ok v
    | none => .error (.ub .invalidUninitBytes)
  | some (.mem _) => .error .unsupported
  | _ => .error (.ub .deadLocal)

def elemAt (ptrBits : Nat) (mp : MPlace) (ty : SemTy) (idx : Nat) : Except Fault (MPlace × SemTy) :=
  match ty.1, ty.2.fields with
  | .array elem n, .array stride _ =>
    match Nat.blt idx n with
    | false => .error (.ub .outOfBounds)
    | true =>
      match pointeeLayoutOf ptrBits elem with
      | none => .error .unsupported
      | some el => .ok (⟨mp.alloc, mp.offset + idx * stride.bytes, el.size.bytes, mp.tag⟩, (elem, el))
  | _, _ => .error .unsupported

def walkProjs (ptrBits : Nat) (st : PState) (fr : PFrame) :
    MPlace → SemTy → List SemProj → Except Fault (MPlace × SemTy)
  | mp, ty, [] => .ok (mp, ty)
  | mp, ty, .field i fty :: rest =>
    match fieldOffset ty.2 i with
    | none => .error .unsupported
    | some fo => walkProjs ptrBits st fr ⟨mp.alloc, mp.offset + fo, fty.2.size.bytes, mp.tag⟩ fty rest
  | mp, ty, .constantIndex off _ fromEnd :: rest =>
    match ty.1 with
    | .array _ n =>
      match elemAt ptrBits mp ty (if fromEnd then n - off else off) with
      | .error e => .error e
      | .ok (mp', ty') => walkProjs ptrBits st fr mp' ty' rest
    | _ => .error .unsupported
  | mp, ty, .index l :: rest =>
    match readUsizeLocal fr l with
    | .error e => .error e
    | .ok idx =>
      match elemAt ptrBits mp ty idx with
      | .error e => .error e
      | .ok (mp', ty') => walkProjs ptrBits st fr mp' ty' rest
  | mp, ty, .subslice f t fromEnd :: rest =>
    match ty.1, ty.2.fields with
    | .array elem n, .array stride _ =>
      let hi := if fromEnd then n - t else t
      match Nat.ble f hi && Nat.ble hi n with
      | false => .error (.ub .outOfBounds)
      | true =>
        match pointeeLayoutOf ptrBits (.array elem (hi - f)) with
        | none => .error .unsupported
        | some kl =>
          walkProjs ptrBits st fr ⟨mp.alloc, mp.offset + f * stride.bytes, kl.size.bytes, mp.tag⟩
            (.array elem (hi - f), kl) rest
    | _, _ => .error .unsupported
  | mp, ty, .deref :: rest =>
    match heapGet st mp.alloc with
    | none => .error (.ub .danglingPointer)
    | some b =>
      match derefTarget ptrBits (sliceBytes b mp.offset mp.size) ty with
      | .error e => .error e
      | .ok (mp', ty') => walkProjs ptrBits st fr mp' ty' rest
  | _, _, .unsupported :: _ => .error .unsupported

/-- LeanMiri `evalPlaceToOp`: unprojected immediate locals yield
`.immediate`; everything in memory (including every `*ptr`) yields
`.indirect mplace`. Independent of `pendingMoveDeinit`. -/
def evalPlaceToOp (ptrBits : Nat) (st : PState) (p : SemPlace) : Except Fault (OpTy × SemTy) :=
  match st.frames with
  | [] => .error .unsupported
  | fr :: _ =>
    match nth? fr.locals p.local_ with
    | none => .error (.ub .deadLocal)
    | some .dead => .error (.ub .deadLocal)
    | some (.imm b) =>
      match p.projs with
      | [] => .ok (.immediate b, p.ty)
      | .deref :: rest =>
        match derefTarget ptrBits b p.ty with
        | .error e => .error e
        | .ok (mp, ty) =>
          match walkProjs ptrBits st fr mp ty rest with
          | .error e => .error e
          | .ok (mp', ty') => .ok (.indirect mp', ty')
      | _ :: _ => .error .unsupported
    | some (.mem a) =>
      match walkProjs ptrBits st fr ⟨a, 0, p.ty.2.size.bytes, none⟩ p.ty p.projs with
      | .error e => .error e
      | .ok (mp, ty) => .ok (.indirect mp, ty)

def readOpBytes (st : PState) : OpTy → Except Fault (Bytes × PState)
  | .immediate b => .ok (b, st)
  | .indirect mp => loadMPlace st mp

/-- Write a value to a place (direct local writes to memory-backed locals are
Tree Borrows writes through the root tag). -/
def writePlace (ptrBits : Nat) (st : PState) (dest : SemPlace) (b : Bytes) : Except Fault PState :=
  match evalPlaceToOp ptrBits st dest with
  | .error e => .error e
  | .ok (.immediate _, _) => setLocalE st dest.local_ (.imm b)
  | .ok (.indirect mp, _) => storeMPlace st mp b

/-- Resolve an assignment or call destination (and its type) against the current state. -/
def resolveDest (ptrBits : Nat) (st : PState) (dest : SemPlace) : Except Fault (DestPlace × SemTy) :=
  match evalPlaceToOp ptrBits st dest with
  | .error e => .error e
  | .ok (.immediate _, ty) => .ok (.imm dest.local_, ty)
  | .ok (.indirect mp, ty) => .ok (.mem mp, ty)

/-- Write to a pre-resolved destination (memory destinations are Tree Borrows
writes). -/
def writeDest (st : PState) (d : DestPlace) (b : Bytes) : Except Fault PState :=
  match d with
  | .imm l => setLocalE st l (.imm b)
  | .mem mp => storeMPlace st mp b

/-- `copyRuntimePlaceNoValidate`'s padded (memory-copy) branch is taken for
memory-repr values read from memory. -/
def usesMemoryPath (ty : SemTy) : OpTy → Bool
  | .indirect _ =>
    match ty.2.backendRepr with
    | .memory => true
    | _ => false
  | .immediate _ => false

def placesOverlap (a b : MPlace) : Bool :=
  Nat.beq a.alloc b.alloc && byteRangesOverlapBool a.offset a.size b.offset b.size

/-- Memory-copy path (`copy.memoryCopy`), rejecting overlapping source and
destination windows (`mem_copy(.., nonoverlapping = true)`). -/
def copyMemPath (st : PState) (src : MPlace) (d : DestPlace) : Except Fault PState :=
  match d with
  | .imm _ => .error .unsupported
  | .mem dmp =>
    match loadMPlace st src with
    | .error e => .error e
    | .ok (b, st₁) =>
      match placesOverlap src dmp with
      | true => .error (.ub .overlappingCopy)
      | false => storeMPlace st₁ dmp b

/-- Clear the `pendingMoveDeinit` latch. -/
def clearLatch (st : PState) : PState := { st with pendingMoveDeinit := false }

/-! ### `M_anneal`: eager, value-level move deinitialization (no latch) -/

def annealReadOperand (ptrBits : Nat) (st : PState) (op : SemOperand) :
    Except Fault (Bytes × PState) :=
  match op with
  | .const b ty =>
    match checkValid ty b with
    | .error e => .error e
    | .ok () => .ok (b, clearLatch st)
  | .copy p =>
    match evalPlaceToOp ptrBits (clearLatch st) p with
    | .error e => .error e
    | .ok (o, ty) =>
      match readOpBytes (clearLatch st) o with
      | .error e => .error e
      | .ok (b, st₁) =>
        match checkValid ty b with
        | .error e => .error e
        | .ok () => .ok (b, st₁)
  | .move p =>
    match evalPlaceToOp ptrBits (clearLatch st) p with
    | .error e => .error e
    | .ok (.immediate b, ty) =>
      match p.projs with
      | [] =>
        match setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b.length)) with
        | .error e => .error e
        | .ok st₁ =>
          match checkValid ty b with
          | .error e => .error e
          | .ok () => .ok (b, clearLatch st₁)
      | _ :: _ => .error .unsupported
    | .ok (.indirect mp, ty) =>
      match loadMPlace (clearLatch st) mp with
      | .error e => .error e
      | .ok (b, st₁) =>
        match checkValid ty b with
        | .error e => .error e
        | .ok () =>
          match deinitMPlaceRaw st₁ mp with
          | .error e => .error e
          | .ok st₂ => .ok (b, st₂)

def annealAssignUse (ptrBits : Nat) (st : PState) (op : SemOperand) (d : DestPlace) :
    Except Fault PState :=
  match op with
  | .const b ty =>
    match checkValid ty b with
    | .error e => .error e
    | .ok () => writeDest (clearLatch st) d b
  | .copy p =>
    match evalPlaceToOp ptrBits (clearLatch st) p with
    | .error e => .error e
    | .ok (o, ty) =>
      match o, usesMemoryPath ty o with
      | .indirect src, true => copyMemPath (clearLatch st) src d
      | _, _ =>
        match readOpBytes (clearLatch st) o with
        | .error e => .error e
        | .ok (b, st₁) =>
          match checkValid ty b with
          | .error e => .error e
          | .ok () => writeDest st₁ d b
  | .move p =>
    match evalPlaceToOp ptrBits (clearLatch st) p with
    | .error e => .error e
    | .ok (.immediate b, ty) =>
      match p.projs with
      | [] =>
        match setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b.length)) with
        | .error e => .error e
        | .ok st₁ =>
          match checkValid ty b with
          | .error e => .error e
          | .ok () => writeDest (clearLatch st₁) d b
      | _ :: _ => .error .unsupported
    | .ok (.indirect src, ty) =>
      match usesMemoryPath ty (.indirect src) with
      | true =>
        match copyMemPath (clearLatch st) src d with
        | .error e => .error e
        | .ok st₁ => deinitMPlaceRaw st₁ src
      | false =>
        match loadMPlace (clearLatch st) src with
        | .error e => .error e
        | .ok (b, st₁) =>
          match checkValid ty b with
          | .error e => .error e
          | .ok () =>
            match deinitMPlaceRaw st₁ src with
            | .error e => .error e
            | .ok st₂ => writeDest st₂ d b

/-! ### `M_ref`: LeanMiri with the `d9b41b58b` two-phase protocol -/

/-- `OperandMachine.evalOperand` with `deinitMovedPlace := dm`. -/
def refEvalOperand (dm : Bool) (ptrBits : Nat) (st : PState) (op : SemOperand) :
    Except Fault (OpTy × SemTy × PState) :=
  match op with
  | .const b ty => .ok (.immediate b, ty, if dm then clearLatch st else st)
  | .copy p =>
    match evalPlaceToOp ptrBits (if dm then clearLatch st else st) p with
    | .error e => .error e
    | .ok (o, ty) => .ok (o, ty, if dm then clearLatch st else st)
  | .move p =>
    match dm with
    | false =>
      match evalPlaceToOp ptrBits st p with
      | .error e => .error e
      | .ok (o, ty) => .ok (o, ty, st)
    | true =>
      match evalPlaceToOp ptrBits (clearLatch st) p with
      | .error e => .error e
      | .ok (.immediate b, ty) =>
        match p.projs with
        | [] =>
          match setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b.length)) with
          | .error e => .error e
          | .ok st₁ => .ok (.immediate b, ty, clearLatch st₁)
        | _ :: _ => .error .unsupported
      | .ok (.indirect mp, ty) =>
        .ok (.indirect mp, ty, { clearLatch st with pendingMoveDeinit := true })

/-- `takePendingMoveDeinit` (`ExecutionMachine.projectionHooks` /
`PlaceMachine.placeHooks`): read-and-clear the latch. -/
def takePendingMoveDeinit (dm : Bool) (st : PState) : Bool × PState :=
  (dm && st.pendingMoveDeinit, clearLatch st)

/-- `PlaceMachine.readImmediate`: consume the latch, read, and deinitialize an
indirect source **after** the read. -/
def refReadImmediate (dm : Bool) (st : PState) (o : OpTy) (ty : SemTy) :
    Except Fault (Bytes × PState) :=
  match readOpBytes (takePendingMoveDeinit dm st).2 o with
  | .error e => .error e
  | .ok (b, st₁) =>
    match checkValid ty b with
    | .error e => .error e
    | .ok () =>
      match (takePendingMoveDeinit dm st).1, o with
      | true, .indirect mp =>
        match deinitMPlaceRaw st₁ mp with
        | .error e => .error e
        | .ok st₂ => .ok (b, st₂)
      | _, _ => .ok (b, st₁)

/-- `Place.copyRuntimePlaceNoValidate`: consume the latch; immediate branch
deinitializes the source before the destination write, memory branch after
the copy. -/
def refCopyRuntimePlaceNoValidate (dm : Bool) (st : PState) (o : OpTy)
    (ty : SemTy) (d : DestPlace) : Except Fault PState :=
  match o, usesMemoryPath ty o with
  | .indirect src, true =>
    match copyMemPath (takePendingMoveDeinit dm st).2 src d with
    | .error e => .error e
    | .ok st₁ =>
      match (takePendingMoveDeinit dm st).1 with
      | true => deinitMPlaceRaw st₁ src
      | false => .ok st₁
  | _, _ =>
    match readOpBytes (takePendingMoveDeinit dm st).2 o with
    | .error e => .error e
    | .ok (b, st₁) =>
      match checkValid ty b with
      | .error e => .error e
      | .ok () =>
        match (takePendingMoveDeinit dm st).1, o with
        | true, .indirect src =>
          match deinitMPlaceRaw st₁ src with
          | .error e => .error e
          | .ok st₂ => writeDest st₂ d b
        | _, _ => writeDest st₁ d b

def twoPhaseReadOperand (dm : Bool) (ptrBits : Nat) (st : PState) (op : SemOperand) :
    Except Fault (Bytes × PState) :=
  match refEvalOperand dm ptrBits st op with
  | .error e => .error e
  | .ok (o, ty, st₁) => refReadImmediate dm st₁ o ty

def twoPhaseAssignUse (dm : Bool) (ptrBits : Nat) (st : PState) (op : SemOperand)
    (d : DestPlace) : Except Fault PState :=
  match refEvalOperand dm ptrBits st op with
  | .error e => .error e
  | .ok (o, ty, st₁) => refCopyRuntimePlaceNoValidate dm st₁ o ty d

/-- Evaluate and consume operands left to right with `f`. -/
def readOperandsWith (f : Nat → PState → SemOperand → Except Fault (Bytes × PState)) (pb : Nat) :
    PState → List SemOperand → Except Fault (List Bytes × PState)
  | st, [] => .ok ([], st)
  | st, op :: ops =>
    match f pb st op with
    | .error e => .error e
    | .ok (b, st₁) =>
      match readOperandsWith f pb st₁ ops with
      | .error e => .error e
      | .ok (bs, st₂) => .ok (b :: bs, st₂)

/-- How a machine evaluates and consumes operands. -/
structure OperandStrategy : Type where
  readOperand : Nat → PState → SemOperand → Except Fault (Bytes × PState)
  assignUse : Nat → PState → SemOperand → DestPlace → Except Fault PState
  /-- Call-argument evaluation (`Call.evalCalleeAndArgs` + `passArgument`), given the
  call's destination place; by default every argument is evaluated *and
  consumed* left to right through `readOperand` (the patched-`evalOperand`
  route that `M_ref` models). -/
  callArgs : Nat → PState → List SemOperand → SemPlace → Except Fault (List Bytes × PState) :=
    fun pb st ops _ => readOperandsWith readOperand pb st ops

def eagerStrategy : OperandStrategy :=
  { readOperand := annealReadOperand, assignUse := annealAssignUse }

def twoPhaseStrategy (dm : Bool) : OperandStrategy :=
  { readOperand := twoPhaseReadOperand dm, assignUse := twoPhaseAssignUse dm }

/-! ### Statements and terminators (shared) -/

def readOperands (S : OperandStrategy) (pb : Nat) :
    PState → List SemOperand → Except Fault (List Bytes × PState) :=
  readOperandsWith S.readOperand pb

def evalBinOpBytes (o : BinOp) (lb rb : Bytes) : Except Fault Bytes :=
  match decodeLittleEndianBytes lb, decodeLittleEndianBytes rb with
  | some (lv, _), some (rv, _) =>
    match o with
    | .add => .ok (encodeLittleEndianBytes (lv + rv) lb.length .none)
    | .sub => .ok (encodeLittleEndianBytes (lv + 2 ^ (8 * lb.length) - rv) lb.length .none)
    | .eq => .ok [.init (if lv = rv then 1 else 0) .none]
    | .ne => .ok [.init (if lv = rv then 0 else 1) .none]
    | .lt => .ok [.init (if lv < rv then 1 else 0) .none]
    | _ => .error .unsupported
  | _, _ => .error (.ub .invalidUninitBytes)

def buildAggregateAux (l : TypeLayout) : Nat → Bytes → List Bytes → Except Fault Bytes
  | _, acc, [] => .ok acc
  | i, acc, fb :: rest =>
    match fieldOffset l i with
    | none => .error .unsupported
    | some off => buildAggregateAux l (i + 1) (overwriteBytes acc off fb) rest

def buildAggregate (l : TypeLayout) (fields : List Bytes) : Except Fault Bytes :=
  buildAggregateAux l 0 (uninitBytes l.size.bytes) fields

/-- Taking a reference / raw pointer forces an immediate local into memory. -/
def forceAllocation (st : PState) (l : Local) : Except Fault PState :=
  match st.frames with
  | [] => .error .unsupported
  | fr :: rest =>
    match nth? fr.locals l with
    | some (.imm b) =>
      match setNth? fr.locals l (.mem st.heap.length) with
      | none => .error (.ub .deadLocal)
      | some ls => .ok { st with heap := st.heap ++ [some b], frames := { fr with locals := ls } :: rest }
    | some (.mem _) => .ok st
    | _ => .error (.ub .deadLocal)

def placeToMPlace (pb : Nat) (st : PState) (p : SemPlace) : Except Fault (MPlace × PState) :=
  match (match p.projs with
         | [] => forceAllocation st p.local_
         | _ :: _ => .ok st) with
  | .error e => .error e
  | .ok st₁ =>
    match evalPlaceToOp pb st₁ p with
    | .error e => .error e
    | .ok (.immediate _, _) => .error .unsupported
    | .ok (.indirect mp, _) => .ok (mp, st₁)

/-- Reference creation: a fresh tag (`.frozen` for `&`, `.reservedFrz false`
for `&mut`) after a reborrow read through the parent tag. -/
def createRef (st : PState) (mutbl : Bool) (mp : MPlace) : Except Fault (Bytes × PState) :=
  match tbAccess .read st.borrows mp.alloc mp.tag mp.offset mp.size with
  | none => .error (.ub .treeBorrows)
  | some bs =>
    let parent : Option Nat :=
      match mp.tag with
      | some pt => if pt = 0 then none else some pt
      | none => none
    let e : BorrowEntry :=
      { tag := st.nextTag, targetLocal := mp.alloc, targetProjection := []
        perm := if mutbl then .reservedFrz false else .frozen
        rangeOffset := mp.offset, rangeLen := mp.size, protector := none, parentTag := parent }
    .ok (ptrBytes mp.alloc st.nextTag mp.offset,
      { st with borrows := bs ++ [e], nextTag := st.nextTag + 1 })

def advance (st : PState) : PState :=
  match st.frames with
  | [] => st
  | fr :: rest => { st with frames := { fr with stmt := fr.stmt + 1 } :: rest }

def jump (st : PState) (bb : Nat) : PState :=
  match st.frames with
  | [] => st
  | fr :: rest => { st with frames := { fr with block := bb, stmt := 0 } :: rest }

def execStmt (S : OperandStrategy) (pb : Nat) (st : PState) : SemStmt → Except Fault PState
  | .assign dest rv =>
    match resolveDest pb st dest with
    | .error e => .error e
    | .ok (d, dty) =>
      match rv with
      | .use op => S.assignUse pb st op d
      | .binaryOp o l r =>
        match S.readOperand pb st l with
        | .error e => .error e
        | .ok (lb, st₁) =>
          match S.readOperand pb st₁ r with
          | .error e => .error e
          | .ok (rb, st₂) =>
            match evalBinOpBytes o lb rb with
            | .error e => .error e
            | .ok res => writeDest st₂ d res
      | .aggregate ops =>
        match readOperands S pb st ops with
        | .error e => .error e
        | .ok (bs, st₁) =>
          match buildAggregate dty.2 bs with
          | .error e => .error e
          | .ok b => writeDest st₁ d b
      | .ref mutbl p =>
        match placeToMPlace pb st p with
        | .error e => .error e
        | .ok (mp, st₁) =>
          match createRef st₁ mutbl mp with
          | .error e => .error e
          | .ok (b, st₂) => writeDest st₂ d b
      | .rawPtr p =>
        match placeToMPlace pb st p with
        | .error e => .error e
        | .ok (mp, st₁) => writeDest st₁ d (ptrBytes mp.alloc (mp.tag.getD 0) mp.offset)
      | .unsupported => .error .unsupported
  | .deinit p =>
    match evalPlaceToOp pb st p with
    | .error e => .error e
    | .ok (.immediate b, _) => setLocalE st p.local_ (.imm (uninitBytes b.length))
    | .ok (.indirect mp, _) => storeMPlace st mp (uninitBytes mp.size)
  | .storageLive l ty =>
    match isImmKind ty.1 with
    | true => setLocalE st l (.imm (uninitBytes ty.2.size.bytes))
    | false =>
      setLocalE { st with heap := st.heap ++ [some (uninitBytes ty.2.size.bytes)] } l
        (.mem st.heap.length)
  | .storageDead l =>
    match st.frames with
    | [] => .error .unsupported
    | fr :: _ =>
      match nth? fr.locals l with
      | some (.mem a) =>
        match setNth? st.heap a none with
        | none => .error (.ub .danglingPointer)
        | some h => setLocalE { st with heap := h } l .dead
      | _ => setLocalE st l .dead
  | .nop => .ok st
  | .unsupported => .error .unsupported

/-- One-step outcome. -/
inductive StepOut : Type where
  | running (st : PState)
  | returned (b : Bytes)
  | panicked
  | fault (f : Fault)

def freeFrameAllocs (heap : List (Option Bytes)) : List PSlot → List (Option Bytes)
  | [] => heap
  | .mem a :: rest => freeFrameAllocs ((setNth? heap a none).getD heap) rest
  | _ :: rest => freeFrameAllocs heap rest

def popFrame (st : PState) : PState :=
  match st.frames with
  | [] => st
  | fr :: rest => { st with frames := rest, heap := freeFrameAllocs st.heap fr.locals }

def allocLocals (argCount : Nat) (args : List Bytes) :
    Nat → List (Option Bytes) → List SemTy → List PSlot × List (Option Bytes)
  | _, heap, [] => ([], heap)
  | i, heap, ty :: tys =>
    let init : Bytes :=
      match Nat.ble 1 i && Nat.ble i argCount with
      | true => (nth? args (i - 1)).getD (uninitBytes ty.2.size.bytes)
      | false => uninitBytes ty.2.size.bytes
    match isImmKind ty.1 with
    | true =>
      let r := allocLocals argCount args (i + 1) heap tys
      (.imm init :: r.1, r.2)
    | false =>
      let r := allocLocals argCount args (i + 1) (heap ++ [some init]) tys
      (.mem heap.length :: r.1, r.2)

def findSwitchTarget (v : Nat) : List (Nat × Nat) → Nat → Nat
  | [], o => o
  | (c, t) :: rest, o => if v = c then t else findSwitchTarget v rest o

def execTerm (S : OperandStrategy) (pb : Nat) (st : PState) : SemTerm → StepOut
  | .goto bb => .running (jump st bb)
  | .ret retTy site =>
    match evalPlaceToOp pb st ⟨0, retTy, []⟩ with
    | .error e => .fault e
    | .ok (o, _) =>
      match readOpBytes st o with
      | .error e => .fault e
      | .ok (b, st₁) =>
        match checkValid retTy b with
        | .error e => .fault e
        | .ok () =>
          match site with
          | none => .returned b
          | some rs =>
            let wr :=
              match st₁.frames with
              | fr :: _ =>
                match fr.retDest with
                | some d => writeDest (popFrame st₁) d b
                | none => writePlace pb (popFrame st₁) rs.dest b
              | [] => writePlace pb (popFrame st₁) rs.dest b
            match wr with
            | .error e => .fault e
            | .ok st₃ =>
              match rs.target with
              | none => .fault (.ub .divergingReturn)
              | some t => .running (jump st₃ t)
  | .switchInt d ts =>
    match S.readOperand pb st d with
    | .error e => .fault e
    | .ok (b, st₁) =>
      match decodeLittleEndianBytes b with
      | none => .fault (.ub .invalidUninitBytes)
      | some (v, _) => .running (jump st₁ (findSwitchTarget v ts.branches ts.otherwise))
  | .assert c expected target unwind =>
    match S.readOperand pb st c with
    | .error e => .fault e
    | .ok (b, st₁) =>
      match decodeLittleEndianBytes b with
      | none => .fault (.ub .invalidUninitBytes)
      | some (v, _) =>
        match decide (Nat.beq v 1 = expected) with
        | true => .running (jump st₁ target)
        | false =>
          match unwind with
          | .cleanup bb => .running (jump st₁ bb)
          | _ => .panicked
  | .call callee argc calleeLocals args dest =>
    match resolveDest pb st dest with
    | .error e => .fault e
    | .ok (d, _) =>
      match S.callArgs pb st args dest with
      | .error e => .fault e
      | .ok (bs, st₁) =>
        match callee with
        | none => .fault .unsupported
        | some bi =>
          let r := allocLocals argc bs 0 st₁.heap calleeLocals
          .running { st₁ with frames := ⟨bi, 0, 0, r.1, some d⟩ :: st₁.frames, heap := r.2 }
  | .unwindResume site =>
    match site with
    | none => .panicked
    | some rs =>
      match rs.unwind with
      | .cleanup bb => .running (jump (popFrame st) bb)
      | _ => .panicked
  | .unreachable => .fault (.ub .unreachable)
  | .unsupported => .fault .unsupported

def runInstr (S : OperandStrategy) (st : PState) : Instr → StepOut
  | .stmt pb s =>
    match execStmt S pb st s with
    | .error f => .fault f
    | .ok st' => .running (advance st')
  | .term pb t => execTerm S pb st t


/-! ### The two-phase latch protocol is transparent when `deinitMoves = true` -/

theorem clearLatch_idem (st : PState) : clearLatch (clearLatch st) = clearLatch st := rfl

theorem clearLatch_set_true (st : PState) :
    clearLatch { clearLatch st with pendingMoveDeinit := true } = clearLatch st := rfl

theorem twoPhaseReadOperand_true_eq (pb : Nat) (st : PState) (op : SemOperand) :
    twoPhaseReadOperand true pb st op = annealReadOperand pb st op := by
  cases op with
  | const b ty =>
    simp only [twoPhaseReadOperand, refEvalOperand, refReadImmediate, takePendingMoveDeinit,
      readOpBytes, annealReadOperand, ite_true, clearLatch_idem]
    cases checkValid ty b <;> rfl
  | copy p =>
    simp only [twoPhaseReadOperand, refEvalOperand, annealReadOperand, ite_true]
    cases h : evalPlaceToOp pb (clearLatch st) p with
    | error e => rfl
    | ok r =>
      obtain ⟨o, ty⟩ := r
      simp only [refReadImmediate, takePendingMoveDeinit, clearLatch_idem]
      cases readOpBytes (clearLatch st) o with
      | error e => rfl
      | ok r' =>
        obtain ⟨b, st₁⟩ := r'
        simp only
        cases checkValid ty b <;> rfl
  | move p =>
    simp only [twoPhaseReadOperand, refEvalOperand, annealReadOperand]
    cases h : evalPlaceToOp pb (clearLatch st) p with
    | error e => rfl
    | ok r =>
      obtain ⟨o, ty⟩ := r
      cases o with
      | immediate b =>
        simp only
        cases hp : p.projs with
        | nil =>
          simp only
          cases setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b.length)) with
          | error e => rfl
          | ok st₁ =>
            simp only [refReadImmediate, takePendingMoveDeinit, readOpBytes, clearLatch_idem]
            cases checkValid ty b <;> rfl
        | cons _ _ => rfl
      | indirect mp =>
        simp only [refReadImmediate, takePendingMoveDeinit, readOpBytes, clearLatch_set_true]
        cases loadMPlace (clearLatch st) mp with
        | error e => rfl
        | ok r' =>
          obtain ⟨b, st₁⟩ := r'
          simp only
          cases checkValid ty b with
          | error e => rfl
          | ok u => rfl

theorem twoPhaseAssignUse_true_eq (pb : Nat) (st : PState) (op : SemOperand) (d : DestPlace) :
    twoPhaseAssignUse true pb st op d = annealAssignUse pb st op d := by
  cases op with
  | const b ty =>
    simp only [twoPhaseAssignUse, refEvalOperand, refCopyRuntimePlaceNoValidate,
      takePendingMoveDeinit, readOpBytes, annealAssignUse, ite_true, clearLatch_idem]
    cases checkValid ty b <;> rfl
  | copy p =>
    simp only [twoPhaseAssignUse, refEvalOperand, annealAssignUse, ite_true]
    cases h : evalPlaceToOp pb (clearLatch st) p with
    | error e => rfl
    | ok r =>
      obtain ⟨o, ty⟩ := r
      simp only [refCopyRuntimePlaceNoValidate, takePendingMoveDeinit, clearLatch_idem]
      cases o with
      | immediate b =>
        simp only [readOpBytes]
        cases checkValid ty b <;> rfl
      | indirect src =>
        cases hm : usesMemoryPath ty (.indirect src) with
        | true =>
          simp only
          cases copyMemPath (clearLatch st) src d <;> rfl
        | false =>
          simp only [readOpBytes]
          cases loadMPlace (clearLatch st) src with
          | error e => rfl
          | ok r' =>
            obtain ⟨b, st₁⟩ := r'
            simp only
            cases checkValid ty b <;> rfl
  | move p =>
    simp only [twoPhaseAssignUse, refEvalOperand, annealAssignUse]
    cases h : evalPlaceToOp pb (clearLatch st) p with
    | error e => rfl
    | ok r =>
      obtain ⟨o, ty⟩ := r
      cases o with
      | immediate b =>
        simp only
        cases hp : p.projs with
        | nil =>
          simp only
          cases setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b.length)) with
          | error e => rfl
          | ok st₁ =>
            simp only [refCopyRuntimePlaceNoValidate, takePendingMoveDeinit, readOpBytes,
              clearLatch_idem]
            cases checkValid ty b <;> rfl
        | cons _ _ => rfl
      | indirect src =>
        simp only [refCopyRuntimePlaceNoValidate, takePendingMoveDeinit, clearLatch_set_true]
        cases hm : usesMemoryPath ty (.indirect src) with
        | true =>
          simp only
          cases copyMemPath (clearLatch st) src d <;> rfl
        | false =>
          simp only [readOpBytes]
          cases loadMPlace (clearLatch st) src with
          | error e => rfl
          | ok r' =>
            obtain ⟨b, st₁⟩ := r'
            simp only
            cases checkValid ty b with
            | error e => rfl
            | ok u => rfl

/-- **Latch transparency**: with `deinitMoves = true` the LeanMiri two-phase
`evalOperand` → `readImmediate` / `copyRuntimePlaceNoValidate` protocol is
extensionally equal to `M_anneal`'s eager move deinitialization. -/
theorem twoPhaseStrategy_true_eq_eager : twoPhaseStrategy true = eagerStrategy := by
  have hR : twoPhaseReadOperand true = annealReadOperand := by
    funext pb st op; exact twoPhaseReadOperand_true_eq pb st op
  have hA : twoPhaseAssignUse true = annealAssignUse := by
    funext pb st op d; exact twoPhaseAssignUse_true_eq pb st op d
  simp only [twoPhaseStrategy, eagerStrategy, hR, hA]

/-- `deinitMovedPlace_false_id`: with `deinitMoves = false`, `Operand.move`
is *identical* to `Operand.copy` at `evalOperand` and at both consumers
(upstream `lean-miri` behavior: `copy_move_same`). -/
theorem deinitMovedPlace_false_id (pb : Nat) (st : PState) (p : SemPlace) (d : DestPlace) :
    refEvalOperand false pb st (.move p) = refEvalOperand false pb st (.copy p) ∧
    twoPhaseReadOperand false pb st (.move p) = twoPhaseReadOperand false pb st (.copy p) ∧
    twoPhaseAssignUse false pb st (.move p) d = twoPhaseAssignUse false pb st (.copy p) d := by
  have h : refEvalOperand false pb st (.move p) = refEvalOperand false pb st (.copy p) := by
    simp only [refEvalOperand, Bool.false_eq_true, ite_false]
  refine ⟨h, ?_, ?_⟩
  · simp only [twoPhaseReadOperand, h]
  · simp only [twoPhaseAssignUse, h]

/-- With `deinitMoves = false` the latch is never consulted by consumers. -/
theorem takePendingMoveDeinit_false (st : PState) : (takePendingMoveDeinit false st).1 = false := rfl

/-! ### Falsification variant: eager deinit inside `evalOperand` -/

/-- The rejected design: deinitialize an `.indirect mplace` *inside*
`evalOperand`, before any consumer has read it. -/
def eagerInEvalOperandReadOperand (ptrBits : Nat) (st : PState) (op : SemOperand) :
    Except Fault (Bytes × PState) :=
  match op with
  | .move p =>
    match evalPlaceToOp ptrBits (clearLatch st) p with
    | .error e => .error e
    | .ok (.indirect mp, ty) =>
      match deinitMPlaceRaw (clearLatch st) mp with
      | .error e => .error e
      | .ok st₁ => refReadImmediate true st₁ (.indirect mp) ty
    | .ok (.immediate _, _) => twoPhaseReadOperand true ptrBits st op
  | _ => twoPhaseReadOperand true ptrBits st op

def eagerInEvalOperandAssignUse (ptrBits : Nat) (st : PState) (op : SemOperand)
    (d : DestPlace) : Except Fault PState :=
  match op with
  | .move p =>
    match evalPlaceToOp ptrBits (clearLatch st) p with
    | .error e => .error e
    | .ok (.indirect mp, ty) =>
      match deinitMPlaceRaw (clearLatch st) mp with
      | .error e => .error e
      | .ok st₁ => refCopyRuntimePlaceNoValidate true st₁ (.indirect mp) ty d
    | .ok (.immediate _, _) => twoPhaseAssignUse true ptrBits st op d
  | _ => twoPhaseAssignUse true ptrBits st op d

def eagerInEvalOperandStrategy : OperandStrategy :=
  { readOperand := eagerInEvalOperandReadOperand, assignUse := eagerInEvalOperandAssignUse }

/-! ### Falsification variant: batched call-argument evaluation (`kani#5172`)

All argument `OpTy`s are evaluated first and consumed afterwards; the single
Boolean latch of an earlier `move` argument is overwritten by later
arguments' `evalOperand`. -/

def evalOperandsBatched (dm : Bool) (pb : Nat) :
    PState → List SemOperand → Except Fault (List (OpTy × SemTy) × PState)
  | st, [] => .ok ([], st)
  | st, op :: ops =>
    match refEvalOperand dm pb st op with
    | .error e => .error e
    | .ok (o, ty, st₁) =>
      match evalOperandsBatched dm pb st₁ ops with
      | .error e => .error e
      | .ok (rs, st₂) => .ok ((o, ty) :: rs, st₂)

def consumeBatched (dm : Bool) : PState → List (OpTy × SemTy) → Except Fault (List Bytes × PState)
  | st, [] => .ok ([], st)
  | st, (o, ty) :: rs =>
    match refReadImmediate dm st o ty with
    | .error e => .error e
    | .ok (b, st₁) =>
      match consumeBatched dm st₁ rs with
      | .error e => .error e
      | .ok (bs, st₂) => .ok (b :: bs, st₂)

def readOperandsBatched (dm : Bool) (pb : Nat) (st : PState) (ops : List SemOperand) :
    Except Fault (List Bytes × PState) :=
  match evalOperandsBatched dm pb st ops with
  | .error e => .error e
  | .ok (rs, st₁) => consumeBatched dm st₁ rs


/-! ## Part 6 — The two machines: fetch, resolve, step, run

`M_anneal` resolves deep `Ty`s against each body's `LayoutTable`; `M_ref`
resolves `TyId`s through the demand-time `evalLayoutQuery`. -/

/-! ### `M_anneal` resolution (deep `V2026_06_01` syntax) -/

def annealResolveTy (L : LayoutTable) (ty : Ty) : Option SemTy :=
  (nth? L.entries ty.layoutIdx).map (fun l => (ty.kind, l))

def annealResolveProj (L : LayoutTable) : ProjectionElem → Option SemProj
  | .deref => some .deref
  | .field i ty => (annealResolveTy L ty).map (.field i)
  | .index l => some (.index l)
  | .constantIndex o m e => some (.constantIndex o m e)
  | .subslice f t e => some (.subslice f t e)
  | .downcast _ _ => some .unsupported
  | .opaqueCast _ => some .unsupported
  | .unwrapUnsafeBinder _ => some .unsupported

def annealResolvePlace (b : CapturedMir) (p : Place) : Option SemPlace :=
  match nth? b.localDecls p.local_ with
  | none => none
  | some d =>
    match annealResolveTy b.layouts d.ty, decodeList (annealResolveProj b.layouts) p.projection with
    | some ty, some projs => some ⟨p.local_, ty, projs⟩
    | _, _ => none

def constSem (sty : Option SemTy) (v : ConstValue) : Option SemOperand :=
  match sty with
  | none => none
  | some ty =>
    match v with
    | .zeroSized => some (.const [] ty)
    | .scalar (.int si) => some (.const (encodeLittleEndianBytes si.bits si.sizeBytes .none) ty)
    | _ => none

def annealResolveOperand (b : CapturedMir) : Operand → Option SemOperand
  | .copy p => (annealResolvePlace b p).map .copy
  | .move p => (annealResolvePlace b p).map .move
  | .constant c => constSem (annealResolveTy b.layouts c.ty) c.val

def borrowIsMut : BorrowKind → Bool
  | .shared => false
  | .mut _ => true

def annealResolveRvalue (b : CapturedMir) : Rvalue → Option SemRvalue
  | .use op => (annealResolveOperand b op).map .use
  | .binaryOp o l r =>
    match annealResolveOperand b l, annealResolveOperand b r with
    | some l', some r' => some (.binaryOp o l' r')
    | _, _ => none
  | .aggregate _ ops => (decodeList (annealResolveOperand b) ops).map .aggregate
  | .ref bk p => (annealResolvePlace b p).map (.ref (borrowIsMut bk))
  | .rawPtr _ p => (annealResolvePlace b p).map .rawPtr
  | _ => some .unsupported

def annealResolveStmt (b : CapturedMir) (s : Statement) : SemStmt :=
  match s.kind with
  | .assign p rv =>
    match annealResolvePlace b p, annealResolveRvalue b rv with
    | some p', some rv' => .assign p' rv'
    | _, _ => .unsupported
  | .deinit p =>
    match annealResolvePlace b p with
    | some p' => .deinit p'
    | none => .unsupported
  | .storageLive l =>
    match (nth? b.localDecls l).bind (fun d => annealResolveTy b.layouts d.ty) with
    | some ty => .storageLive l ty
    | none => .unsupported
  | .storageDead l => .storageDead l
  | .nop => .nop
  | .coverage => .nop
  | .constEvalCounter => .nop
  | _ => .unsupported

def annealResolveLocals (b : CapturedMir) : Option (List SemTy) :=
  decodeList (fun d => annealResolveTy b.layouts d.ty) b.localDecls

/-- Callee of a `Call`: a constant `fnDef` resolved by `DefPath` among the
program's bodies (`none` = unresolved / external callee). -/
def fnDefPath? (k : RigidTy) : Option DefPath :=
  match k with
  | .fnDef path _ => some path
  | _ => none

def annealCallee (p : V2026Prog) (func : Operand) : Option Nat :=
  match func with
  | .constant c => (fnDefPath? c.ty.kind).bind (indexOf? (p.bodies.map CapturedMir.defPath))
  | _ => none

/-- Return / unwind site of the caller frame: `none` = resolution failure,
`some none` = root frame. -/
def annealSite (p : V2026Prog) (frames : List PFrame) : Option (Option ReturnSite) :=
  match frames with
  | [] => none
  | [_] => some none
  | _ :: caller :: _ =>
    match nth? p.bodies caller.body with
    | none => none
    | some cb =>
      match nth? cb.basicBlocks caller.block with
      | none => none
      | some bb =>
        match bb.terminator.kind with
        | .call _ _ dest target unwind =>
          (annealResolvePlace cb dest).map (fun d => some ⟨d, target, unwind⟩)
        | _ => none

def annealResolveTerm (p : V2026Prog) (frames : List PFrame) (b : CapturedMir)
    (t : Terminator) : SemTerm :=
  match t.kind with
  | .goto bb => .goto bb
  | .return_ =>
    match (nth? b.localDecls 0).bind (fun d => annealResolveTy b.layouts d.ty),
        annealSite p frames with
    | some ty, some site => .ret ty site
    | _, _ => .unsupported
  | .switchInt d ts =>
    match annealResolveOperand b d with
    | some d' => .switchInt d' ts
    | none => .unsupported
  | .assert c e tgt u =>
    match annealResolveOperand b c with
    | some c' => .assert c' e tgt u
    | none => .unsupported
  | .call f args dest _ _ =>
    match annealResolvePlace b dest, decodeList (annealResolveOperand b) args with
    | some dest', some args' =>
      match annealCallee p f with
      | none => .call none 0 [] args' dest'
      | some bi =>
        match (nth? p.bodies bi).bind (fun cb => (annealResolveLocals cb).map (cb.argCount, ·)) with
        | some (argc, tys) => .call (some bi) argc tys args' dest'
        | none => .unsupported
    | _, _ => .unsupported
  | .unwindResume =>
    match annealSite p frames with
    | some site => .unwindResume site
    | none => .unsupported
  | .unreachable => .unreachable
  | _ => .unsupported

def annealFetch (p : V2026Prog) (st : PState) : Except Fault Instr :=
  match st.frames with
  | [] => .error .unsupported
  | fr :: _ =>
    match nth? p.bodies fr.body with
    | none => .error .unsupported
    | some b =>
      match nth? b.basicBlocks fr.block with
      | none => .error (.ub .badControlFlow)
      | some bb =>
        match nth? bb.statements fr.stmt with
        | some s => .ok (.stmt b.layouts.pointerBits (annealResolveStmt b s))
        | none =>
          match Nat.beq fr.stmt bb.statements.length with
          | true => .ok (.term b.layouts.pointerBits (annealResolveTerm p st.frames b bb.terminator))
          | false => .error (.ub .badControlFlow)

/-- `M_anneal` small step. -/
def annealStep (p : V2026Prog) (st : PState) : StepOut :=
  match annealFetch p st with
  | .error f => .fault f
  | .ok i => runInstr eagerStrategy st i

/-! ### `M_ref` resolution (`TyId` syntax + demand-time `LayoutQuery`) -/

def refResolveTy (tt : TypeTable) (L : LayoutTable) (t : TyId) : Option SemTy :=
  match evalLayoutQuery tt L (.localLayout t) with
  | .ok (.layout k l) => some (k, l)
  | _ => none

def refResolveProj (tt : TypeTable) (L : LayoutTable) : RefProjectionElem → Option SemProj
  | .deref => some .deref
  | .field i t => (refResolveTy tt L t).map (.field i)
  | .index l => some (.index l)
  | .constantIndex o m e => some (.constantIndex o m e)
  | .subslice f t e => some (.subslice f t e)
  | .downcast _ _ => some .unsupported
  | .opaqueCast _ => some .unsupported
  | .unwrapUnsafeBinder _ => some .unsupported

def refResolvePlace (tt : TypeTable) (b : RefBody) (p : RefPlace) : Option SemPlace :=
  match nth? b.localDecls p.local_ with
  | none => none
  | some d =>
    match refResolveTy tt b.layouts d.ty, decodeList (refResolveProj tt b.layouts) p.projection with
    | some ty, some projs => some ⟨p.local_, ty, projs⟩
    | _, _ => none

def refResolveOperand (tt : TypeTable) (b : RefBody) : RefOperand → Option SemOperand
  | .copy p => (refResolvePlace tt b p).map .copy
  | .move p => (refResolvePlace tt b p).map .move
  | .constant c => constSem (refResolveTy tt b.layouts c.ty) c.val

def refResolveRvalue (tt : TypeTable) (b : RefBody) : RefRvalue → Option SemRvalue
  | .use op => (refResolveOperand tt b op).map .use
  | .binaryOp o l r =>
    match refResolveOperand tt b l, refResolveOperand tt b r with
    | some l', some r' => some (.binaryOp o l' r')
    | _, _ => none
  | .aggregate _ ops => (decodeList (refResolveOperand tt b) ops).map .aggregate
  | .ref bk p => (refResolvePlace tt b p).map (.ref (borrowIsMut bk))
  | .rawPtr _ p => (refResolvePlace tt b p).map .rawPtr
  | _ => some .unsupported

def refResolveStmt (tt : TypeTable) (b : RefBody) (s : RefStatement) : SemStmt :=
  match s.kind with
  | .assign p rv =>
    match refResolvePlace tt b p, refResolveRvalue tt b rv with
    | some p', some rv' => .assign p' rv'
    | _, _ => .unsupported
  | .deinit p =>
    match refResolvePlace tt b p with
    | some p' => .deinit p'
    | none => .unsupported
  | .storageLive l =>
    match (nth? b.localDecls l).bind (fun d => refResolveTy tt b.layouts d.ty) with
    | some ty => .storageLive l ty
    | none => .unsupported
  | .storageDead l => .storageDead l
  | .nop => .nop
  | .coverage => .nop
  | .constEvalCounter => .nop
  | _ => .unsupported

def refResolveLocals (tt : TypeTable) (b : RefBody) : Option (List SemTy) :=
  decodeList (fun d => refResolveTy tt b.layouts d.ty) b.localDecls

def refCallee (rp : RefProg) (func : RefOperand) : Option Nat :=
  match func with
  | .constant c =>
    ((nth? rp.types.types c.ty).bind (fun ty => fnDefPath? ty.kind)).bind
      (indexOf? (rp.bodies.map RefBody.defPath))
  | _ => none

def refSite (rp : RefProg) (frames : List PFrame) : Option (Option ReturnSite) :=
  match frames with
  | [] => none
  | [_] => some none
  | _ :: caller :: _ =>
    match nth? rp.bodies caller.body with
    | none => none
    | some cb =>
      match nth? cb.basicBlocks caller.block with
      | none => none
      | some bb =>
        match bb.terminator.kind with
        | .call _ _ dest target unwind =>
          (refResolvePlace rp.types cb dest).map (fun d => some ⟨d, target, unwind⟩)
        | _ => none

def refResolveTerm (rp : RefProg) (frames : List PFrame) (b : RefBody) (t : RefTerminator) :
    SemTerm :=
  match t.kind with
  | .goto bb => .goto bb
  | .return_ =>
    match (nth? b.localDecls 0).bind (fun d => refResolveTy rp.types b.layouts d.ty),
        refSite rp frames with
    | some ty, some site => .ret ty site
    | _, _ => .unsupported
  | .switchInt d ts =>
    match refResolveOperand rp.types b d with
    | some d' => .switchInt d' ts
    | none => .unsupported
  | .assert c e tgt u =>
    match refResolveOperand rp.types b c with
    | some c' => .assert c' e tgt u
    | none => .unsupported
  | .call f args dest _ _ =>
    match refResolvePlace rp.types b dest, decodeList (refResolveOperand rp.types b) args with
    | some dest', some args' =>
      match refCallee rp f with
      | none => .call none 0 [] args' dest'
      | some bi =>
        match (nth? rp.bodies bi).bind
            (fun cb => (refResolveLocals rp.types cb).map (cb.argCount, ·)) with
        | some (argc, tys) => .call (some bi) argc tys args' dest'
        | none => .unsupported
    | _, _ => .unsupported
  | .unwindResume =>
    match refSite rp frames with
    | some site => .unwindResume site
    | none => .unsupported
  | .unreachable => .unreachable
  | _ => .unsupported

def refFetch (rp : RefProg) (st : PState) : Except Fault Instr :=
  match st.frames with
  | [] => .error .unsupported
  | fr :: _ =>
    match nth? rp.bodies fr.body with
    | none => .error .unsupported
    | some b =>
      match nth? b.basicBlocks fr.block with
      | none => .error (.ub .badControlFlow)
      | some bb =>
        match nth? bb.statements fr.stmt with
        | some s => .ok (.stmt b.layouts.pointerBits (refResolveStmt rp.types b s))
        | none =>
          match Nat.beq fr.stmt bb.statements.length with
          | true => .ok (.term b.layouts.pointerBits (refResolveTerm rp st.frames b bb.terminator))
          | false => .error (.ub .badControlFlow)

/-- `M_ref`-style step with an arbitrary operand strategy (used for the
falsification variants). -/
def refStepCoreWith (S : OperandStrategy) (rp : RefProg) (st : PState) : StepOut :=
  match refFetch rp st with
  | .error f => .fault f
  | .ok i => runInstr S st i

/-- `M_ref` step on the shared core state (`ExecutionMachine.step` without
the step budget). -/
def refStepCore (dm : Bool) (rp : RefProg) (st : PState) : StepOut :=
  refStepCoreWith (twoPhaseStrategy dm) rp st

/-! ### Step budgets, outcomes, runs -/

/-- `M_ref` state: core state plus `stepsExecuted` / `maxSteps`
(`Limits.maxSteps`). -/
structure RefState : Type where
  core : PState
  stepsExecuted : Nat
  maxSteps : Nat

/-- `M_ref` outcome. -/
inductive RefOutcome : Type where
  | running (rs : RefState)
  | returned (b : Bytes)
  | panicked
  | ub (why : UBReason)
  | blocked
  | exhaustedStepLimit

def faultToRefOutcome : Fault → RefOutcome
  | .ub why => .ub why
  | .unsupported => .blocked

/-- `M_ref` step: the budget is checked first. -/
def refStep (dm : Bool) (rp : RefProg) (rs : RefState) : RefOutcome :=
  match Nat.blt rs.stepsExecuted rs.maxSteps with
  | false => .exhaustedStepLimit
  | true =>
    match refStepCore dm rp rs.core with
    | .running st' => .running ⟨st', rs.stepsExecuted + 1, rs.maxSteps⟩
    | .returned b => .returned b
    | .panicked => .panicked
    | .fault f => faultToRefOutcome f

def annealRun (p : V2026Prog) : Nat → PState → StepOut
  | 0, st => .running st
  | n + 1, st =>
    match annealStep p st with
    | .running st' => annealRun p n st'
    | o => o

def refRunFuel (dm : Bool) (rp : RefProg) : Nat → RefState → RefOutcome
  | 0, rs => .running rs
  | n + 1, rs =>
    match refStep dm rp rs with
    | .running rs' => refRunFuel dm rp n rs'
    | o => o

/-- Entry state from resolved entry-body local types. -/
def initFromLocals (entry : Nat) (argCount : Nat) (args : List Bytes) (tys : List SemTy) : PState :=
  let r := allocLocals argCount args 0 [] tys
  { frames := [⟨entry, 0, 0, r.1, none⟩], heap := r.2, borrows := [], nextTag := 1,
    pendingMoveDeinit := false }

def annealInit (p : V2026Prog) (args : List Bytes) : Except Fault PState :=
  match nth? p.bodies p.entry with
  | none => .error .unsupported
  | some b =>
    match annealResolveLocals b with
    | none => .error .unsupported
    | some tys => .ok (initFromLocals p.entry b.argCount args tys)

def refInit (rp : RefProg) (args : List Bytes) : Except Fault PState :=
  match nth? rp.bodies rp.entry with
  | none => .error .unsupported
  | some b =>
    match refResolveLocals rp.types b with
    | none => .error .unsupported
    | some tys => .ok (initFromLocals rp.entry b.argCount args tys)

/-- Observable result of a bounded run. -/
inductive Obs : Type where
  | returned (v : Option Nat) (len : Nat)
  | panicked
  | ub (why : UBReason)
  | unsupported
  | exhausted
  deriving DecidableEq

def bytesObs (b : Bytes) : Obs := .returned ((decodeLittleEndianBytes b).map Prod.fst) b.length

def stepOutObs : StepOut → Obs
  | .running _ => .exhausted
  | .returned b => bytesObs b
  | .panicked => .panicked
  | .fault (.ub why) => .ub why
  | .fault .unsupported => .unsupported

def refOutcomeObs : RefOutcome → Obs
  | .running _ => .exhausted
  | .returned b => bytesObs b
  | .panicked => .panicked
  | .ub why => .ub why
  | .blocked => .unsupported
  | .exhaustedStepLimit => .exhausted

/-- Run `M_anneal` for at most `fuel` steps. -/
def annealObs (p : V2026Prog) (args : List Bytes) (fuel : Nat) : Obs :=
  match annealInit p args with
  | .error (.ub why) => .ub why
  | .error .unsupported => .unsupported
  | .ok st => stepOutObs (annealRun p fuel st)

/-- Run `M_ref` (`deinitMoves := dm`) with step budget `maxSteps`. -/
def refObs (dm : Bool) (rp : RefProg) (args : List Bytes) (maxSteps : Nat) : Obs :=
  match refInit rp args with
  | .error (.ub why) => .ub why
  | .error .unsupported => .unsupported
  | .ok st => refOutcomeObs (refRunFuel dm rp (maxSteps + 1) ⟨st, 0, maxSteps⟩)



/-! ## Part 6b — Codec-driven resolution correspondence

`M_ref`'s demand-time resolution of `encodeProg p` coincides with
`M_anneal`'s deep resolution of `p`, for every program and every state. -/

theorem decodeList_map_congr {α β γ : Type} (f : β → Option α) (g : γ → β) (h : γ → Option α) :
    ∀ (xs : List γ), (∀ x ∈ xs, f (g x) = h x) → decodeList f (xs.map g) = decodeList h xs
  | [], _ => rfl
  | x :: xs, hx => by
    simp only [List.map, decodeList]
    rw [hx x (List.Mem.head _), decodeList_map_congr f g h xs (fun y hy => hx y (List.Mem.tail _ hy))]

theorem refResolveTy_encode {tt : TypeTable} {ty : Ty} (L : LayoutTable) (h : ty ∈ tt.types) :
    refResolveTy tt L (encodeType tt ty) = annealResolveTy L ty := by
  have hd : nth? tt.types (encodeType tt ty) = some ty := decodeType_encodeType_of_mem h
  simp only [refResolveTy, evalLayoutQuery, tyLayout, hd, annealResolveTy]
  cases nth? L.entries ty.layoutIdx <;> rfl

theorem refResolveProj_encode {tt : TypeTable} (L : LayoutTable) (e : ProjectionElem)
    (h : Covers tt (projElemTys e)) :
    refResolveProj tt L (encodeProjElem tt e) = annealResolveProj L e := by
  cases e <;> simp only [encodeProjElem, refResolveProj, annealResolveProj, projElemTys] at h ⊢
  case field i ty => rw [refResolveTy_encode L h.single]

/-- Every declared local type of `b` is interned. -/
abbrev DeclsCovered (tt : TypeTable) (b : CapturedMir) : Prop := ∀ d ∈ b.localDecls, d.ty ∈ tt.types

theorem encodeBody_layouts (tt : TypeTable) (b : CapturedMir) : (encodeBody tt b).layouts = b.layouts :=
  rfl

theorem nth?_encodeDecls (tt : TypeTable) (b : CapturedMir) (l : Nat) :
    nth? (encodeBody tt b).localDecls l = (nth? b.localDecls l).map (encodeLocalDecl tt) :=
  nth?_map _ _ _

theorem refResolvePlace_encode {tt : TypeTable} (b : CapturedMir) (p : Place)
    (hd : DeclsCovered tt b) (h : Covers tt (placeTys p)) :
    refResolvePlace tt (encodeBody tt b) (encodePlace tt p) = annealResolvePlace b p := by
  simp only [refResolvePlace, annealResolvePlace, encodePlace, nth?_encodeDecls, encodeBody_layouts]
  cases hn : nth? b.localDecls p.local_ with
  | none => rfl
  | some d =>
    simp only [Option.map_some, encodeLocalDecl]
    rw [refResolveTy_encode _ (hd d (mem_of_nth? hn)),
      decodeList_map_congr _ _ _ _ (fun e he => refResolveProj_encode _ e (h.flatMap e he))]

theorem refResolveOperand_encode {tt : TypeTable} (b : CapturedMir) (op : Operand)
    (hd : DeclsCovered tt b) (h : Covers tt (operandTys op)) :
    refResolveOperand tt (encodeBody tt b) (encodeOperand tt op) = annealResolveOperand b op := by
  cases op <;> simp only [encodeOperand, refResolveOperand, annealResolveOperand, operandTys] at h ⊢
  · rw [refResolvePlace_encode b _ hd h]
  · rw [refResolvePlace_encode b _ hd h]
  · rw [encodeBody_layouts, refResolveTy_encode _ h.single]

theorem refResolveOperands_encode {tt : TypeTable} (b : CapturedMir) (ops : List Operand)
    (hd : DeclsCovered tt b) (h : Covers tt (ops.flatMap operandTys)) :
    decodeList (refResolveOperand tt (encodeBody tt b)) (ops.map (encodeOperand tt)) =
      decodeList (annealResolveOperand b) ops :=
  decodeList_map_congr _ _ _ _ (fun o ho => refResolveOperand_encode b o hd (h.flatMap o ho))

theorem refResolveRvalue_encode {tt : TypeTable} (b : CapturedMir) (rv : Rvalue)
    (hd : DeclsCovered tt b) (h : Covers tt (rvalueTys rv)) :
    refResolveRvalue tt (encodeBody tt b) (encodeRvalue tt rv) = annealResolveRvalue b rv := by
  cases rv <;> simp only [encodeRvalue, refResolveRvalue, annealResolveRvalue, rvalueTys] at h ⊢
  case use op => rw [refResolveOperand_encode b op hd h]
  case ref bk p => rw [refResolvePlace_encode b p hd h]
  case rawPtr m p => rw [refResolvePlace_encode b p hd h]
  case binaryOp o l r =>
    rw [refResolveOperand_encode b l hd h.append.1, refResolveOperand_encode b r hd h.append.2]
  case aggregate k ops => rw [refResolveOperands_encode b ops hd h.append.2]

theorem refResolveStmt_encode {tt : TypeTable} (b : CapturedMir) (s : Statement)
    (hd : DeclsCovered tt b) (h : Covers tt (stmtTys s)) :
    refResolveStmt tt (encodeBody tt b) (encodeStmt tt s) = annealResolveStmt b s := by
  obtain ⟨k, sp⟩ := s
  simp only [stmtTys] at h
  cases k <;> simp only [encodeStmt, encodeStmtKind, refResolveStmt, annealResolveStmt,
    stmtKindTys] at h ⊢
  case assign p rv =>
    rw [refResolvePlace_encode b p hd h.append.1, refResolveRvalue_encode b rv hd h.append.2]
  case deinit p => rw [refResolvePlace_encode b p hd h]
  case storageLive l =>
    simp only [nth?_encodeDecls, encodeBody_layouts]
    cases hn : nth? b.localDecls l with
    | none => rfl
    | some d =>
      simp only [Option.map_some, Option.bind_some, encodeLocalDecl]
      rw [refResolveTy_encode _ (hd d (mem_of_nth? hn))]

theorem refResolveLocals_encode {tt : TypeTable} (b : CapturedMir) (hd : DeclsCovered tt b) :
    refResolveLocals tt (encodeBody tt b) = annealResolveLocals b := by
  simp only [refResolveLocals, annealResolveLocals, encodeBody]
  exact decodeList_map_congr _ _ _ _ (fun d hdm => by
    simp only [encodeLocalDecl]; exact refResolveTy_encode _ (hd d hdm))

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

theorem defPaths_encode (tt : TypeTable) (bs : List CapturedMir) :
    (bs.map (encodeBody tt)).map RefBody.defPath = bs.map CapturedMir.defPath := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map, ih]; rfl

theorem refSite_encode (p : V2026Prog) (frames : List PFrame) :
    refSite (encodeProg p) frames = annealSite p frames := by
  match frames with
  | [] => rfl
  | [_] => rfl
  | _ :: caller :: _ =>
    simp only [refSite, annealSite, encodeProg_bodies, nth?_map]
    cases hb : nth? p.bodies caller.body with
    | none => rfl
    | some cb =>
      have hcov := encodeProg_body_covered p cb (mem_of_nth? hb)
      simp only [Option.map_some, encodeBody, nth?_map]
      cases hbb : nth? cb.basicBlocks caller.block with
      | none => rfl
      | some bb =>
        have hbc := bodyCovered_block hcov (mem_of_nth? hbb)
        simp only [Option.map_some, encodeBlock, encodeTerminator]
        cases hk : bb.terminator.kind <;> simp only [encodeTermKind]
        case call f args dest target unwind =>
          have hdest : Covers (collectProgTypes p) (placeTys dest) := by
            have := hbc.append.2; rw [hk] at this; exact this.append.2
          rw [encodeProg_types]
          have := refResolvePlace_encode (tt := collectProgTypes p) cb dest
            (bodyCovered_decls hcov) hdest
          simp only [encodeBody] at this
          rw [this]

theorem refCallee_encode (p : V2026Prog) (f : Operand)
    (h : Covers (collectProgTypes p) (operandTys f)) :
    refCallee (encodeProg p) (encodeOperand (collectProgTypes p) f) = annealCallee p f := by
  cases f <;> simp only [encodeOperand, refCallee, annealCallee]
  case constant c =>
    simp only [operandTys] at h
    have hd : nth? (collectProgTypes p).types (encodeType (collectProgTypes p) c.ty) = some c.ty :=
      decodeType_encodeType_of_mem h.single
    rw [encodeProg_types, hd, encodeProg_bodies, defPaths_encode]
    rfl

theorem refResolveTerm_encode (p : V2026Prog) (frames : List PFrame) (b : CapturedMir)
    (hb : b ∈ p.bodies) (t : Terminator) (h : Covers (collectProgTypes p) (termKindTys t.kind)) :
    refResolveTerm (encodeProg p) frames (encodeBody (collectProgTypes p) b)
      (encodeTerminator (collectProgTypes p) t) = annealResolveTerm p frames b t := by
  have hcov := encodeProg_body_covered p b hb
  have hd := bodyCovered_decls hcov
  obtain ⟨k, sp⟩ := t
  simp only [termKindTys] at h
  cases k <;> simp only [encodeTerminator, encodeTermKind, refResolveTerm, annealResolveTerm,
    encodeProg_types] at h ⊢
  case return_ =>
    rw [refSite_encode]
    simp only [nth?_encodeDecls, encodeBody_layouts]
    cases hn : nth? b.localDecls 0 with
    | none => rfl
    | some d =>
      simp only [Option.map_some, Option.bind_some, encodeLocalDecl]
      rw [refResolveTy_encode _ (hd d (mem_of_nth? hn))]
  case switchInt d ts => rw [refResolveOperand_encode b d hd h]
  case assert c e tgt u => rw [refResolveOperand_encode b c hd h]
  case unwindResume => rw [refSite_encode]
  case call f args dest target unwind =>
    rw [refResolvePlace_encode b dest hd h.append.2,
        refResolveOperands_encode b args hd h.append.1.append.2]
    cases annealResolvePlace b dest with
    | none => rfl
    | some dest' =>
      cases decodeList (annealResolveOperand b) args with
      | none => rfl
      | some args' =>
        simp only
        rw [refCallee_encode p f h.append.1.append.1]
        cases hc : annealCallee p f with
        | none => rfl
        | some bi =>
          simp only [encodeProg_bodies, nth?_map]
          cases hcb : nth? p.bodies bi with
          | none => rfl
          | some cb =>
            simp only [Option.map_some, Option.bind_some]
            rw [refResolveLocals_encode cb
              (bodyCovered_decls (encodeProg_body_covered p cb (mem_of_nth? hcb)))]
            rfl

/-- **Fetch/resolve correspondence**: for every program and every state,
`M_ref`'s fetch of `encodeProg p` equals `M_anneal`'s fetch of `p`. -/
theorem refFetch_encodeProg (p : V2026Prog) (st : PState) :
    refFetch (encodeProg p) st = annealFetch p st := by
  rcases st with ⟨frames, heap, borrows, nextTag, pend⟩
  simp only [refFetch, annealFetch]
  cases frames with
  | nil => rfl
  | cons fr rest =>
    simp only [encodeProg_bodies, nth?_map]
    cases hb : nth? p.bodies fr.body with
    | none => rfl
    | some b =>
      have hmem := mem_of_nth? hb
      have hcov := encodeProg_body_covered p b hmem
      simp only [Option.map_some]
      simp only [encodeBody, nth?_map]
      cases hbb : nth? b.basicBlocks fr.block with
      | none => rfl
      | some bb =>
        have hbc := bodyCovered_block hcov (mem_of_nth? hbb)
        simp only [Option.map_some, encodeBlock, nth?_map, List.length_map]
        cases hs : nth? bb.statements fr.stmt with
        | some s =>
          simp only [Option.map_some]
          have := refResolveStmt_encode (tt := collectProgTypes p) b s (bodyCovered_decls hcov)
            (hbc.append.1.flatMap s (mem_of_nth? hs))
          simp only [encodeBody] at this
          rw [encodeProg_types, this]
        | none =>
          simp only [Option.map_none]
          cases Nat.beq fr.stmt bb.statements.length with
          | false => rfl
          | true =>
            have := refResolveTerm_encode p (fr :: rest) b hmem bb.terminator hbc.append.2
            simp only [encodeBody] at this
            rw [this]

/-- **Forward simulation (one step, every state)**: with `deinitMoves = true`,
`M_ref` on `encodeProg p` takes exactly `M_anneal`'s step on `p`. -/
theorem anneal_corresponds_to_miri_proto (p : V2026Prog) (st : PState) :
    refStepCore true (encodeProg p) st = annealStep p st := by
  simp only [refStepCore, refStepCoreWith, annealStep, refFetch_encodeProg,
    twoPhaseStrategy_true_eq_eager]

theorem encodeProg_entry (p : V2026Prog) : (encodeProg p).entry = p.entry := rfl

theorem refInit_encodeProg (p : V2026Prog) (args : List Bytes) :
    refInit (encodeProg p) args = annealInit p args := by
  simp only [refInit, annealInit, encodeProg_bodies, encodeProg_entry, encodeProg_types, nth?_map]
  cases hb : nth? p.bodies p.entry with
  | none => rfl
  | some b =>
    simp only [Option.map_some]
    rw [refResolveLocals_encode b (bodyCovered_decls (encodeProg_body_covered p b (mem_of_nth? hb)))]
    rfl

theorem refRunFuel_encode (p : V2026Prog) :
    ∀ (n k : Nat) (st : PState),
      refOutcomeObs (refRunFuel true (encodeProg p) (n + 1) ⟨st, k, k + n⟩) =
        stepOutObs (annealRun p n st)
  | 0, k, st => by
    have h0 : Nat.blt k (k + 0) = false := by
      cases h : Nat.blt k (k + 0) with
      | false => rfl
      | true => exact absurd (Nat.blt_eq.mp h) (by omega)
    simp only [refRunFuel, refStep, h0, refOutcomeObs, annealRun, stepOutObs]
  | n + 1, k, st => by
    have hlt : Nat.blt k (k + (n + 1)) = true := by
      simp only [Nat.blt_eq]; omega
    rw [refRunFuel.eq_2, annealRun.eq_2]
    have hstep : refStep true (encodeProg p) ⟨st, k, k + (n + 1)⟩ =
        (match annealStep p st with
         | .running st' => .running ⟨st', k + 1, k + (n + 1)⟩
         | .returned b => .returned b
         | .panicked => .panicked
         | .fault f => faultToRefOutcome f) := by
      simp only [refStep, hlt, anneal_corresponds_to_miri_proto]
    rw [hstep]
    cases annealStep p st with
    | running st' =>
      have hk : k + (n + 1) = (k + 1) + n := by omega
      simp only
      rw [hk]; exact refRunFuel_encode p n (k + 1) st'
    | returned b => rfl
    | panicked => rfl
    | fault f => cases f <;> rfl

/-- **Whole-program behavioral equivalence** (`deinitMoves = true`): for every
program, argument vector and step budget, `M_ref` on `encodeProg p` and
`M_anneal` on `p` produce the same observation. -/
theorem refObs_encodeProg (p : V2026Prog) (args : List Bytes) (n : Nat) :
    refObs true (encodeProg p) args n = annealObs p args n := by
  simp only [refObs, annealObs, refInit_encodeProg]
  cases annealInit p args with
  | error f => cases f <;> rfl
  | ok st =>
    simp only
    have := refRunFuel_encode p n 0 st
    simp only [Nat.zero_add] at this
    exact this

def faultObs : Fault → Obs
  | .ub why => .ub why
  | .unsupported => .unsupported

/-- **Bidirectional fault equivalence**: `M_anneal` reaches fault `f` iff
`M_ref` (`deinitMoves = true`) reaches the corresponding `.ub` / `.blocked`
outcome under some step budget. -/
theorem reachesResult_fault_iff_refReachesOutcome_proto (p : V2026Prog) (args : List Bytes)
    (f : Fault) :
    (∃ n, annealObs p args n = faultObs f) ↔ (∃ maxSteps, refObs true (encodeProg p) args maxSteps = faultObs f) := by
  simp only [refObs_encodeProg]

/-- Forward simulation of terminal behavior. -/
theorem behavior_transfer_proto (p : V2026Prog) (args : List Bytes) (n : Nat) (v : Option Nat)
    (len : Nat) (h : annealObs p args n = .returned v len) :
    refObs true (encodeProg p) args n = .returned v len := by
  rw [refObs_encodeProg]; exact h

/-- Simulation invariant: the reference core state *is* the Anneal state. -/
def SimulationInv (s : PState) (rs : RefState) : Prop := rs.core = s

/-- `SimulationInv` is a bijection (for fixed step counters) that is preserved
in both directions by every step (`deinitMoves = true`). -/
theorem simulationInv_bijective (p : V2026Prog) :
    (∀ s s' rs, SimulationInv s rs → SimulationInv s' rs → s = s') ∧
    (∀ s rs rs', SimulationInv s rs → SimulationInv s rs' →
      rs.stepsExecuted = rs'.stepsExecuted → rs.maxSteps = rs'.maxSteps → rs = rs') ∧
    (∀ s k m, ∃ rs, SimulationInv s rs ∧ rs.stepsExecuted = k ∧ rs.maxSteps = m) ∧
    (∀ s rs s', SimulationInv s rs → rs.stepsExecuted < rs.maxSteps →
      annealStep p s = .running s' →
      ∃ rs', refStep true (encodeProg p) rs = .running rs' ∧ SimulationInv s' rs') ∧
    (∀ s rs rs', SimulationInv s rs → refStep true (encodeProg p) rs = .running rs' →
      annealStep p s = .running rs'.core) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s s' rs h₁ h₂; exact h₁.symm.trans h₂
  · intro s rs rs' h₁ h₂ h₃ h₄
    cases rs; cases rs'; simp only [SimulationInv] at h₁ h₂ h₃ h₄; subst h₁ h₂ h₃ h₄; rfl
  · intro s k m; exact ⟨⟨s, k, m⟩, rfl, rfl, rfl⟩
  · intro s rs s' h hlt hs
    have hb : Nat.blt rs.stepsExecuted rs.maxSteps = true := Nat.blt_eq.mpr hlt
    refine ⟨⟨s', rs.stepsExecuted + 1, rs.maxSteps⟩, ?_, rfl⟩
    simp only [refStep, hb, anneal_corresponds_to_miri_proto, SimulationInv] at h ⊢
    rw [h, hs]
  · intro s rs rs' h hr
    simp only [refStep, SimulationInv] at h hr
    cases hb : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false => rw [hb] at hr; cases hr
    | true =>
      rw [hb] at hr; simp only [anneal_corresponds_to_miri_proto, h] at hr
      cases hs : annealStep p s <;> rw [hs] at hr <;> simp only at hr
      · cases hr; rfl
      · cases hr
      · cases hr
      · rename_i f; cases f <;> cases hr

/-- Well-formedness of a `V2026_06_01` program (`M_anneal` input): entry body
exists, every body is at `MirPhaseTag.runtimePostCleanup`, and every local
declaration resolves in its body's `LayoutTable`. -/
def ProgWellFormed (p : V2026Prog) : Prop :=
  p.entry < p.bodies.length ∧
  ∀ b ∈ p.bodies,
    b.phase = .runtimePostCleanup ∧ b.wellFormed = true ∧
    ∀ d ∈ b.localDecls, ∃ st, annealResolveTy b.layouts d.ty = some st

/-- Reference program well-formedness (`M_ref` input): canonical type table,
entry body in bounds, every body at `MirPhaseTag.runtimePostCleanup`, and
every local declaration `TyId` answers `.ok (.layout k l)` under demand-time
`evalLayoutQuery`. -/
def RefProgWellFormed (rp : RefProg) : Prop :=
  rp.types.Good ∧
  rp.entry < rp.bodies.length ∧
  ∀ rb ∈ rp.bodies,
    rb.phase = .runtimePostCleanup ∧
    ∀ rd ∈ rb.localDecls, ∃ k l, evalLayoutQuery rp.types rb.layouts (.localLayout rd.ty) = .ok (.layout k l)

/-- Encoding a well-formed `V2026Prog` produces a well-formed `RefProg`
(`WellFormed p → RefWellFormed (encodeProg p)`). -/
theorem refProgWellFormed_encodeProg (p : V2026Prog) (h : ProgWellFormed p) :
    RefProgWellFormed (encodeProg p) := by
  obtain ⟨hent, hb⟩ := h
  refine ⟨internKinds_good (internTys_good initTypeTable_good (progTys p)) (progTraitKinds p), ?_, ?_⟩
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
    cases hq : evalLayoutQuery (encodeProg p).types b.layouts (.localLayout (encodeType (collectProgTypes p) d.ty)) with
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


/-- Run a strategy variant of `M_ref` (no budget) for at most `fuel` steps. -/
def refRunWith (S : OperandStrategy) (rp : RefProg) : Nat → PState → StepOut
  | 0, st => .running st
  | n + 1, st =>
    match refStepCoreWith S rp st with
    | .running st' => refRunWith S rp n st'
    | o => o

def refObsWith (S : OperandStrategy) (rp : RefProg) (args : List Bytes) (fuel : Nat) : Obs :=
  match refInit rp args with
  | .error (.ub why) => .ub why
  | .error .unsupported => .unsupported
  | .ok st => stepOutObs (refRunWith S rp fuel st)

/-! ## Part 7 — Executable `D1`–`D9` canaries on real `V2026_06_01` bodies

Every canary is a real `CapturedMir` (`runtimePostCleanup`, real
`LocalDecl`/`Ty`/`LayoutTable`, layouts synthesized by Trusted's
`RigidTy.computeLayout`), executed by `M_anneal` and by `M_ref` on
`encodeProg p` (with `deinitMoves = true`), and decided by the kernel. -/

def fallbackLayout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def lay (k : RigidTy) : TypeLayout := (pointeeLayoutOf 64 k).getD fallbackLayout

def kU8 : RigidTy := .uint .u8
def kPair : RigidTy := .tuple [kU8, kU8]
def kArr4 : RigidTy := .array kU8 4
def kArr2 : RigidTy := .array kU8 2
def kMaybeUninit : RigidTy := .adt "core::mem::MaybeUninit" [kU8]

/-- The canaries' compiler layout table (`x86_64`). -/
def canaryLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true
    entries := [lay (.tuple []), lay kU8, lay .bool, lay kPair, lay kArr4,
      lay (.rawPtr .mut kU8), lay (.ref .not kU8), lay (.uint .usize), lay kArr2,
      lay (.fnDef "callee" []), lay (.fnDef "unresolved" []), lay kMaybeUninit,
      lay (.fnDef "panicky" [])] }

def tUnit : Ty := ⟨.tuple [], 0⟩
def tU8 : Ty := ⟨kU8, 1⟩
def tBool : Ty := ⟨.bool, 2⟩
def tPair : Ty := ⟨kPair, 3⟩
def tArr4 : Ty := ⟨kArr4, 4⟩
def tRaw : Ty := ⟨.rawPtr .mut kU8, 5⟩
def tRef : Ty := ⟨.ref .not kU8, 6⟩
def tArr2 : Ty := ⟨kArr2, 8⟩
def tFnCallee : Ty := ⟨.fnDef "callee" [], 9⟩
def tFnUnresolved : Ty := ⟨.fnDef "unresolved" [], 10⟩
def tMU : Ty := ⟨kMaybeUninit, 11⟩
def tFnPanicky : Ty := ⟨.fnDef "panicky" [], 12⟩

def mkBody (path : DefPath) (argCount : Nat) (locals : List Ty) (blocks : List BasicBlockData) :
    CapturedMir :=
  { defPath := path, phase := .runtimePostCleanup, role := .subject, argCount := argCount
    localDecls := locals.map (fun ty => ⟨.mut, ty, none⟩), basicBlocks := blocks
    fnAbi := ⟨[], ⟨lay (.tuple []), .ignore⟩, .rust, true⟩, layouts := canaryLayouts
    allocations := [] }

def stmt (k : StatementKind) : Statement := ⟨k, ""⟩
def asg (dst : Place) (rv : Rvalue) : Statement := stmt (.assign dst rv)
def blk (ss : List Statement) (t : TerminatorKind) (cleanup : Bool := false) : BasicBlockData :=
  ⟨ss, ⟨t, ""⟩, cleanup⟩
def loc (l : Nat) : Place := ⟨l, []⟩
def fld (l i : Nat) (ty : Ty) : Place := ⟨l, [.field i ty]⟩
def drf (l : Nat) : Place := ⟨l, [.deref]⟩
def cU8 (n : Nat) : Operand := .constant ⟨tU8, .scalar (.int ⟨n, 1⟩)⟩
def cBool (b : Bool) : Operand := .constant ⟨tBool, .scalar (.int ⟨if b then 1 else 0, 1⟩)⟩
def cUnit : Operand := .constant ⟨tUnit, .zeroSized⟩
def prog1 (b : CapturedMir) : V2026Prog := ⟨[b], 0⟩

/-- Both machines on one program: `M_anneal` and `M_ref` (`deinitMoves = true`). -/
def bothObs (p : V2026Prog) : Obs × Obs :=
  (annealObs p [] 40, refObs true (encodeProg p) [] 40)

/-! ### `D1` — direct local move (PR #257 `D6` / `D9`) -/

def d1MoveThenRead : V2026Prog := prog1 <| mkBody "d1" 0 [tU8, tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 7)), asg (loc 2) (.use (.move (loc 1))),
        asg (loc 0) (.use (.copy (loc 1)))] .return_]

theorem canary_D1_direct_move_ub :
    bothObs d1MoveThenRead = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

/-- Non-vacuity witness for `ProgWellFormed` and `RefProgWellFormed`. -/
theorem refProgWellFormed_nonvacuous :
    ProgWellFormed d1MoveThenRead ∧ RefProgWellFormed (encodeProg d1MoveThenRead) := by
  have hwf : ProgWellFormed d1MoveThenRead := by
    refine ⟨by decide, ?_⟩
    intro b hb
    simp only [d1MoveThenRead, prog1, List.mem_singleton] at hb
    subst hb
    refine ⟨rfl, rfl, ?_⟩
    intro d hd
    simp only [mkBody, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with ⟨ty, rfl | rfl | rfl, rfl⟩ <;> exact ⟨(kU8, lay kU8), rfl⟩
  exact ⟨hwf, refProgWellFormed_encodeProg d1MoveThenRead hwf⟩

def d1ZstMove : V2026Prog := prog1 <| mkBody "d1z" 0 [tUnit, tUnit, tUnit]
  [blk [asg (loc 1) (.use cUnit), asg (loc 2) (.use (.move (loc 1))),
        asg (loc 0) (.use (.copy (loc 1)))] .return_]

theorem canary_D1_zst_unit_move_ok :
    bothObs d1ZstMove = (.returned (some 0) 0, .returned (some 0) 0) := by decide

/-! ### `D2` — partial field move -/

def d2Prog (reread : Bool) : V2026Prog := prog1 <| mkBody "d2" 0 [tU8, tPair, tU8]
  [blk [asg (loc 1) (.aggregate .tuple [cU8 1, cU8 2]),
        asg (loc 2) (.use (.move (fld 1 0 tU8))),
        asg (loc 0) (.use (.copy (fld 1 (if reread then 0 else 1) tU8)))] .return_]

theorem canary_D2_partial_field_move_sibling_ok :
    bothObs (d2Prog false) = (.returned (some 2) 1, .returned (some 2) 1) := by decide

theorem canary_D2_partial_field_move_reread_ub :
    bothObs (d2Prog true) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

/-! ### `D3` — move then re-initialize -/

def d3Prog : V2026Prog := prog1 <| mkBody "d3" 0 [tU8, tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 2) (.use (.move (loc 1))),
        asg (loc 1) (.use (cU8 99)), asg (loc 0) (.use (.copy (loc 1)))] .return_]

theorem canary_D3_move_then_reinit_ok :
    bothObs d3Prog = (.returned (some 99) 1, .returned (some 99) 1) := by decide

/-! ### `D4` — copy keeps the source; left-to-right binary operands (PR #257 `D7a`–`D7c`) -/

def d4Prog (rv : Rvalue) : V2026Prog := prog1 <| mkBody "d4" 0 [tU8, tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 2) (.use (.copy (loc 1))), asg (loc 0) rv] .return_]

theorem canary_D4_copy_keeps_source :
    bothObs (d4Prog (.use (.copy (loc 1)))) = (.returned (some 5) 1, .returned (some 5) 1) := by
  decide

theorem canary_D4_copy_then_move_ok :
    bothObs (d4Prog (.binaryOp .add (.copy (loc 1)) (.move (loc 1)))) =
      (.returned (some 10) 1, .returned (some 10) 1) := by decide

theorem canary_D4_move_then_copy_ub :
    bothObs (d4Prog (.binaryOp .add (.move (loc 1)) (.copy (loc 1)))) =
      (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

theorem canary_D4_move_then_move_ub :
    bothObs (d4Prog (.binaryOp .add (.move (loc 1)) (.move (loc 1)))) =
      (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

/-! ### `D5` — indirect move through `*ptr` with a sibling `.frozen` borrow -/

/-- `_1 = 5; _3 = &_1; _2 = &raw mut _1; <s>; _0 = <rv>` -/
def d5Prog (s : Statement) (rv : Rvalue) : V2026Prog := prog1 <| mkBody "d5" 0
  [tU8, tU8, tRaw, tRef, tU8]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 3) (.ref .shared (loc 1)),
        asg (loc 2) (.rawPtr .mut (loc 1)), s, asg (loc 0) rv] .return_]

theorem canary_D5_indirect_move_delivers_value :
    bothObs (d5Prog (asg (loc 4) (.use (.move (drf 2)))) (.use (.copy (loc 4)))) =
      (.returned (some 5) 1, .returned (some 5) 1) := by decide

theorem canary_D5_indirect_move_reread_ub :
    bothObs (d5Prog (asg (loc 4) (.use (.move (drf 2)))) (.use (.copy (drf 2)))) =
      (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

/-- After `move (*_2)` the sibling shared borrow `_3` is still `.frozen`: reading
`*_3` passes Tree Borrows and only fails on the moved (uninit) bytes. -/
theorem canary_D5_move_preserves_sibling_frozen :
    bothObs (d5Prog (asg (loc 4) (.use (.move (drf 2)))) (.use (.copy (drf 3)))) =
      (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

/-- Contrast: `*_2 = 9` is a foreign write that disables `_3`. -/
theorem canary_D5_assign_disables_sibling_frozen :
    bothObs (d5Prog (asg (drf 2) (.use (cU8 9))) (.use (.copy (drf 3)))) =
      (.ub .treeBorrows, .ub .treeBorrows) := by decide

/-- Contrast: `Deinit(*_2)` is also a Tree Borrows write. -/
theorem canary_D5_deinit_disables_sibling_frozen :
    bothObs (d5Prog (stmt (.deinit (drf 2))) (.use (.copy (drf 3)))) =
      (.ub .treeBorrows, .ub .treeBorrows) := by decide

/-! ### `D6` — self-moves (PR #257 `D8`) -/

def d6Direct : V2026Prog := prog1 <| mkBody "d6a" 0 [tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 1) (.use (.move (loc 1))),
        asg (loc 0) (.use (.copy (loc 1)))] .return_]

def d6Indirect : V2026Prog := prog1 <| mkBody "d6b" 0 [tU8, tU8, tRaw]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 2) (.rawPtr .mut (loc 1)),
        asg (drf 2) (.use (.move (drf 2))), asg (loc 0) (.use (.copy (loc 1)))] .return_]

def d6Swap : V2026Prog := prog1 <| mkBody "d6c" 0 [tU8, tPair]
  [blk [asg (loc 1) (.aggregate .tuple [cU8 1, cU8 2]),
        asg (loc 1) (.aggregate .tuple [.move (fld 1 1 tU8), .move (fld 1 0 tU8)]),
        asg (loc 0) (.use (.copy (fld 1 0 tU8)))] .return_]

theorem canary_D6_direct_self_move_ok :
    bothObs d6Direct = (.returned (some 5) 1, .returned (some 5) 1) := by decide

theorem canary_D6_indirect_self_move_ok :
    bothObs d6Indirect = (.returned (some 5) 1, .returned (some 5) 1) := by decide

theorem canary_D6_field_swap_self_aggregate_ok :
    bothObs d6Swap = (.returned (some 2) 1, .returned (some 2) 1) := by decide

/-! ### `D7` — call-argument moves and `kani#5172` ordering -/

def d7Callee : CapturedMir := mkBody "callee" 2 [tU8, tU8, tRaw]
  [blk [asg (loc 0) (.use (.copy (drf 2)))] .return_]

def d7Prog (arg : Operand) : V2026Prog := ⟨[mkBody "caller" 0 [tU8, tU8, tRaw]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 2) (.rawPtr .mut (loc 1))]
     (.call (.constant ⟨tFnCallee, .zeroSized⟩) [arg, .copy (loc 2)] (loc 0) (some 1) .continue_),
   blk [] .return_], d7Callee], 0⟩

/-- `_1` is deinitialized in the caller before `callee` runs: the callee's
aliasing read through the raw pointer is UB. -/
theorem canary_D7_call_arg_move_deinit_before_callee :
    bothObs (d7Prog (.move (loc 1))) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by
  decide

theorem canary_D7_call_arg_copy_ok :
    bothObs (d7Prog (.copy (loc 1))) = (.returned (some 5) 1, .returned (some 5) 1) := by decide

def d7Unresolved (arg : Operand) : V2026Prog := prog1 <| mkBody "caller" 0 [tU8, tU8]
  [blk [] (.call (.constant ⟨tFnUnresolved, .zeroSized⟩) [arg] (loc 0) (some 1) .continue_),
   blk [] .return_]

/-- `kani#5172`: the uninitialized argument faults with UB *before* the
unresolved callee is reported `.unsupported`. -/
theorem canary_D7_uninit_arg_ub_before_unsupported :
    bothObs (d7Unresolved (.move (loc 1))) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by
  decide

theorem canary_D7_unresolved_callee_unsupported :
    bothObs (d7Unresolved (cU8 1)) = (.unsupported, .unsupported) := by decide

/-- `Call` destination `*_2` is resolved at call entry (before `move _2`
deinitializes `_2`), matching `Miri.Interpreter.Call.evalCallTerminator`
(`Call.lean:453`). When `callee` returns `42`, it writes through the
pre-resolved `*_2` into `_1`, and the caller returns `42`. -/
def d7DestCallee : CapturedMir := mkBody "callee" 1 [tU8, tRaw]
  [blk [asg (loc 0) (.use (cU8 42))] .return_]

def d7DestBeforeArgMove : V2026Prog := ⟨[mkBody "caller" 0 [tU8, tU8, tRaw]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 2) (.rawPtr .mut (loc 1))]
     (.call (.constant ⟨tFnCallee, .zeroSized⟩) [.move (loc 2)] (drf 2) (some 1) .continue_),
   blk [asg (loc 0) (.use (.copy (loc 1)))] .return_], d7DestCallee], 0⟩

theorem canary_D7_call_dest_resolved_before_arg_move :
    bothObs d7DestBeforeArgMove = (.returned (some 42) 1, .returned (some 42) 1) := by
  decide

/-- An invalid `Call` destination (`*_2` where `_2` is uninitialized) faults
with `.ub .invalidPointer` at call entry *before* evaluating arguments or
reporting `.unsupported` on an unresolved callee. -/
def d7BadDestBeforeUnresolved : V2026Prog := prog1 <| mkBody "caller" 0 [tU8, tU8, tRaw]
  [blk [] (.call (.constant ⟨tFnUnresolved, .zeroSized⟩) [cU8 1] (drf 2) (some 1) .continue_),
   blk [] .return_]

theorem canary_D7_call_bad_dest_ub_before_unsupported :
    bothObs d7BadDestBeforeUnresolved = (.ub .invalidPointer, .ub .invalidPointer) := by
  decide

/-! ### `D8` — unwind / cleanup paths -/

def d8Assert (cleanupRead : Nat) : V2026Prog := prog1 <| mkBody "d8" 0 [tU8, tBool, tU8]
  [blk [asg (loc 1) (.use (cBool false)), asg (loc 2) (.use (cU8 7))]
     (.assert (.move (loc 1)) true 1 (.cleanup 2)),
   blk [asg (loc 0) (.use (cU8 0))] .return_,
   blk [asg (loc 0) (.use (.copy (loc cleanupRead)))] .unwindResume true]

theorem canary_D8_assert_cleanup_moved_cond_ub :
    bothObs (d8Assert 1) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

theorem canary_D8_assert_cleanup_unmoved_ok :
    bothObs (d8Assert 2) = (.panicked, .panicked) := by decide

def d8Panicky : CapturedMir := mkBody "panicky" 1 [tU8, tU8] [blk [] .unwindResume]

def d8Call (cleanupRead : Nat) : V2026Prog := ⟨[mkBody "caller" 0 [tU8, tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 2) (.use (cU8 6))]
     (.call (.constant ⟨tFnPanicky, .zeroSized⟩) [.move (loc 1)] (loc 0) (some 1) (.cleanup 2)),
   blk [] .return_,
   blk [asg (loc 0) (.use (.copy (loc cleanupRead)))] .unwindResume true], d8Panicky], 0⟩

theorem canary_D8_unwinding_call_moved_arg_ub :
    bothObs (d8Call 1) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by decide

theorem canary_D8_unwinding_call_unmoved_ok :
    bothObs (d8Call 2) = (.panicked, .panicked) := by decide

/-! ### `D9` — array element / `ConstantIndex` / `Subslice` moves -/

def d9Prog (s : Statement) (readIdx : Nat) : V2026Prog := prog1 <| mkBody "d9" 0
  [tU8, tArr4, tU8, tArr2]
  [blk [asg (loc 1) (.aggregate (.array tU8) [cU8 10, cU8 11, cU8 12, cU8 13]), s,
        asg (loc 0) (.use (.copy ⟨1, [.constantIndex readIdx 4 false]⟩))] .return_]

def d9MoveElem : Statement := asg (loc 2) (.use (.move ⟨1, [.constantIndex 1 4 false]⟩))
def d9MoveSub : Statement := asg (loc 3) (.use (.move ⟨1, [.subslice 1 3 false]⟩))

theorem canary_D9_elem_move_neighbors_ok :
    bothObs (d9Prog d9MoveElem 0) = (.returned (some 10) 1, .returned (some 10) 1) ∧
    bothObs (d9Prog d9MoveElem 3) = (.returned (some 13) 1, .returned (some 13) 1) := by
  decide

theorem canary_D9_elem_move_reread_ub :
    bothObs (d9Prog d9MoveElem 1) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by
  decide

theorem canary_D9_subslice_move_window :
    bothObs (d9Prog d9MoveSub 0) = (.returned (some 10) 1, .returned (some 10) 1) ∧
    bothObs (d9Prog d9MoveSub 3) = (.returned (some 13) 1, .returned (some 13) 1) ∧
    bothObs (d9Prog d9MoveSub 1) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) ∧
    bothObs (d9Prog d9MoveSub 2) = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by
  decide


/-! ## Part 8 — Falsification witnesses (non-vacuity / mutant separation) -/

/-- `MaybeUninit<u8>` byte copy after a move: no UB in either machine at the
copy, but the copied bytes differ, so a later typed read separates them. -/
def maybeUninitProg : V2026Prog := prog1 <| mkBody "mu" 0 [tU8, tMU, tMU, tMU]
  [blk [asg (loc 1) (.aggregate (.adt "core::mem::MaybeUninit" 0 none) [cU8 42]),
        asg (loc 2) (.use (.move (loc 1))),
        asg (loc 3) (.use (.copy (loc 1))),
        asg (loc 0) (.use (.copy (fld 3 0 tU8)))] .return_]

/-- **`deinitMoves = false` breaks the correspondence**: on use-after-move
(`D1`) and on a `MaybeUninit` byte copy, upstream `lean-miri` (moves are copies)
returns a value where `M_anneal` faults. -/
theorem correspondence_fails_when_deinitMoves_false :
    annealObs d1MoveThenRead [] 40 = .ub .invalidUninitBytes ∧
    refObs false (encodeProg d1MoveThenRead) [] 40 = .returned (some 7) 1 ∧
    annealObs maybeUninitProg [] 40 = .ub .invalidUninitBytes ∧
    refObs false (encodeProg maybeUninitProg) [] 40 = .returned (some 42) 1 ∧
    refObs true (encodeProg maybeUninitProg) [] 40 = .ub .invalidUninitBytes := by
  decide

/-- Hence no `deinitMoves = false` analogue of `refObs_encodeProg` exists. -/
theorem no_correspondence_when_deinitMoves_false :
    ¬ ∀ (p : V2026Prog) (args : List Bytes) (n : Nat),
      refObs false (encodeProg p) args n = annealObs p args n := by
  intro h
  have := h d1MoveThenRead [] 40
  rw [correspondence_fails_when_deinitMoves_false.1,
    correspondence_fails_when_deinitMoves_false.2.1] at this
  cases this

/-- The program `_1 = 5; _3 = &_1; _2 = &raw mut _1; _4 = move (*_2); _0 = _4`. -/
def d5MoveDeliver : V2026Prog :=
  d5Prog (asg (loc 4) (.use (.move (drf 2)))) (.use (.copy (loc 4)))

/-- **Eager indirect deinit is falsified**: deinitializing the `.indirect
mplace` inside `evalOperand` (before `readImmediate` /
`copyRuntimePlaceNoValidate`) turns a valid indirect move into a spurious
`invalidUninitBytes` fault. -/
theorem eager_indirect_deinit_falsified :
    annealObs d5MoveDeliver [] 40 = .returned (some 5) 1 ∧
    refObs true (encodeProg d5MoveDeliver) [] 40 = .returned (some 5) 1 ∧
    refObsWith eagerInEvalOperandStrategy (encodeProg d5MoveDeliver) [] 40 =
      .ub .invalidUninitBytes := by
  decide

theorem eagerInEvalOperandStrategy_ne_eager : eagerInEvalOperandStrategy ≠ eagerStrategy := by
  intro h
  have h1 := eager_indirect_deinit_falsified.2.2
  have h2 := eager_indirect_deinit_falsified.2.1
  rw [h] at h1
  have e : refObsWith eagerStrategy (encodeProg d5MoveDeliver) [] 40 =
      refObs true (encodeProg d5MoveDeliver) [] 40 := by decide
  rw [e, h2] at h1
  cases h1

/-- The `D7` caller state just before the call (`_1` in memory, `_2 = &raw mut _1`). -/
def d7PreCallState : Option PState :=
  match annealInit (d7Prog (.move (loc 1))) [] with
  | .ok st =>
    match annealRun (d7Prog (.move (loc 1))) 2 st with
    | .running st' => some st'
    | _ => none
  | .error _ => none

def d7ArgOps : List SemOperand :=
  [.move ⟨1, (kU8, lay kU8), []⟩, .copy ⟨2, (.rawPtr .mut kU8, lay (.rawPtr .mut kU8)), []⟩]

/-- Is `_1`'s memory (allocation `a`, 1 byte) still initialized? -/
def byteInit (st : PState) (a : Nat) : Bool :=
  match heapGet st a with
  | some [AbstractByte.init _ _] => true
  | _ => false

def argsKeepSource (r : Except Fault (List Bytes × PState)) : Bool :=
  match r with
  | .ok (_, st) => byteInit st 0
  | .error _ => false

/-- **`kani#5172` call-argument ordering**: consuming each argument right after
its `evalOperand` (as `M_ref` does) deinitializes the moved argument, whereas
batching all `evalOperand`s before consumption lets the second argument's
`evalOperand` clobber the single-Boolean `pendingMoveDeinit` latch, so the
moved argument stays initialized (a missed use-after-move). -/
theorem batched_call_args_lose_move_deinit :
    (d7PreCallState.map fun st => argsKeepSource (readOperands (twoPhaseStrategy true) 64 st d7ArgOps)) =
      some false ∧
    (d7PreCallState.map fun st => argsKeepSource (readOperandsBatched true 64 st d7ArgOps)) =
      some true := by
  decide

/-! ### Upstream LeanMiri call-argument path (`Miri/Interpreter/Call.lean`)

A faithful model of `Call.evalCalleeAndArgs` + `Call.passArgument` under the
6-file `d9b41b58b` patch (which does not touch `Call.lean`):

* `evalFnCallArgumentAt` (`Call.lean:164-175`) sends `.Copy` / `.Constant`
  through the patched `evalOperandAt`, which yields a *lazy* `OpTy`
  (`FnArg.Copy`). It sends `.Move place` through `evalPlace` + `placeToOp`
  without calling `evalOperand`. If the move places and the destination are
  `moveDefinitelyDisjoint`, an indirect place becomes `FnArg.InPlace` and an
  immediate becomes `FnArg.Copy`, with **no deinit**. Otherwise the place is
  force-allocated and passed `InPlace`.
* `evalCallTerminator` evaluates the destination place first, then *all*
  arguments, then (`initFnCall`) runs `passArgument` per argument. The copy is
  `copyAllowTransmute` (the lazy read). It is followed, for `InPlace`
  arguments, by `protectArgument` =
  `TypedRetag.protectInPlaceFunctionArgument`, which ends in
  `writeUninit place` (Miri `machine.rs`
  `protect_in_place_function_argument`). The protector retag is not modeled;
  the uninit write is modeled as the same Tree-Borrows-silent deinit. -/

/-- `Miri.Interpreter.Call.FnArg`. -/
inductive FnArgM : Type where
  | copyOp (o : OpTy) (ty : SemTy)
  | inPlace (mp : MPlace) (ty : SemTy)

def localsDistinct : List Local → Bool
  | [] => true
  | l :: ls => !(ls.contains l) && localsDistinct ls

/-- `Call.moveDefinitelyDisjoint`: move-argument places and the destination
have pairwise distinct locals and no leading `Deref`. -/
def moveDefinitelyDisjoint (args : List SemOperand) (dest : SemPlace) : Bool :=
  let places := args.filterMap (fun a => match a with | .move p => some p | _ => none) ++ [dest]
  places.all (fun p => match p.projs with | .deref :: _ => false | _ => true) &&
    localsDistinct (places.map SemPlace.local_)

/-- `Call.evalFnCallArgumentAt` (patched `evalOperandAt` for non-moves). -/
def leanMiriEvalFnCallArg (pb : Nat) (disjoint : Bool) (st : PState) :
    SemOperand → Except Fault (FnArgM × PState)
  | .move p =>
    match disjoint with
    | true =>
      match evalPlaceToOp pb st p with
      | .error e => .error e
      | .ok (.indirect mp, ty) => .ok (.inPlace mp ty, st)
      | .ok (.immediate b, ty) => .ok (.copyOp (.immediate b) ty, st)
    | false =>
      match placeToMPlace pb st p with
      | .error e => .error e
      | .ok (mp, st₁) =>
        match evalPlaceToOp pb st₁ p with
        | .error e => .error e
        | .ok (_, ty) => .ok (.inPlace mp ty, st₁)
  | op =>
    match refEvalOperand true pb st op with
    | .error e => .error e
    | .ok (o, ty, st₁) => .ok (.copyOp o ty, st₁)

def leanMiriEvalFnCallArgs (pb : Nat) (disjoint : Bool) :
    PState → List SemOperand → Except Fault (List FnArgM × PState)
  | st, [] => .ok ([], st)
  | st, op :: ops =>
    match leanMiriEvalFnCallArg pb disjoint st op with
    | .error e => .error e
    | .ok (fa, st₁) =>
      match leanMiriEvalFnCallArgs pb disjoint st₁ ops with
      | .error e => .error e
      | .ok (fas, st₂) => .ok (fa :: fas, st₂)

/-- `Call.passArgument` for every argument, in order: the (lazy) copy, then the
in-place protection's `writeUninit` (`TypedRetag.lean:201` →
`TypedMachineBindings.lean:17` `PlaceMachine.writeMemory access (fun _ => false)
.uninit`, which runs `accessHooks.beforeMemoryWrite`, i.e. a Tree Borrows
`.Write` via `storeMPlace`). -/
def leanMiriPassArgs : PState → List FnArgM → Except Fault (List Bytes × PState)
  | st, [] => .ok ([], st)
  | st, .copyOp o ty :: rest =>
    match refReadImmediate true st o ty with
    | .error e => .error e
    | .ok (b, st₁) =>
      match leanMiriPassArgs st₁ rest with
      | .error e => .error e
      | .ok (bs, st₂) => .ok (b :: bs, st₂)
  | st, .inPlace mp ty :: rest =>
    match loadMPlace st mp with
    | .error e => .error e
    | .ok (b, st₁) =>
      match checkValid ty b with
      | .error e => .error e
      | .ok () =>
        match storeMPlace st₁ mp (uninitBytes mp.size) with
        | .error e => .error e
        | .ok st₂ =>
          match leanMiriPassArgs st₂ rest with
          | .error e => .error e
          | .ok (bs, st₃) => .ok (b :: bs, st₃)

def leanMiriCallArgsUpstream (pb : Nat) (st : PState) (args : List SemOperand) (dest : SemPlace) :
    Except Fault (List Bytes × PState) :=
  match leanMiriEvalFnCallArgs pb (moveDefinitelyDisjoint args dest) st args with
  | .error e => .error e
  | .ok (fas, st₁) => leanMiriPassArgs st₁ fas

/-- `M_ref` with the *unpatched* `Call.lean` argument path (everything else as
patched by `d9b41b58b`). -/
def leanMiriUpstreamCallStrategy : OperandStrategy :=
  { readOperand := twoPhaseReadOperand true, assignUse := twoPhaseAssignUse true,
    callArgs := leanMiriCallArgsUpstream }

def tFnCalleeImm : Ty := ⟨.fnDef "calleeImm" [], 9⟩

/-- `_1 = 5; _2 = calleeImm(move _1); _0 = copy _1` with `_1` an immediate
(never borrowed) local. -/
def d7ImmProg : V2026Prog := ⟨[mkBody "caller" 0 [tU8, tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 5))]
     (.call (.constant ⟨tFnCalleeImm, .zeroSized⟩) [.move (loc 1)] (loc 2) (some 1) .continue_),
   blk [asg (loc 0) (.use (.copy (loc 1)))] .return_],
  mkBody "calleeImm" 1 [tU8, tU8] [blk [asg (loc 0) (.use (.copy (loc 1)))] .return_]], 0⟩

/-- Same-call `move _1` followed by `copy _1`: `_1 = 5; _0 = calleeAdd(move _1, copy _1)`.
Because `moveDefinitelyDisjoint` (`Call.lean:156-157`) only collects `.Move`
places and ignores `.Copy` places, `disjoint = true`, so unpatched `Call.lean`
fails to deinitialize `_1` on arg 0 and lets arg 1 (`copy _1`) read `5` in the
same call! -/
def d7MoveThenCopySameCallProg : V2026Prog := ⟨[mkBody "caller" 0 [tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 5))]
     (.call (.constant ⟨tFnCalleeImm, .zeroSized⟩) [.move (loc 1), .copy (loc 1)] (loc 0) (some 1) .continue_),
   blk [] .return_],
  mkBody "calleeImm" 2 [tU8, tU8, tU8]
    [blk [asg (loc 0) (.binaryOp .add (.copy (loc 1)) (.copy (loc 2)))] .return_]], 0⟩

theorem canary_D7_call_move_then_copy_arg_ub :
    bothObs d7MoveThenCopySameCallProg = (.ub .invalidUninitBytes, .ub .invalidUninitBytes) := by
  decide

/-- `_1 = 5; _3 = &_1; _2 = &raw mut _1; _4 = calleeImm(move (*_2)); _0 = copy (*_3)`.
Because `.move (drf 2)` has a leading `.deref`, `moveDefinitelyDisjoint` is
`false` (`Call.lean:160`), so `move (*_2)` is passed `.InPlace`. In `M_anneal`
and `M_ref`, moving `*_2` into the call preserves the sibling `.frozen` borrow
`_3` (reading `*_3` passes Tree Borrows and faults on `.invalidUninitBytes`),
whereas `protectInPlaceFunctionArgument`'s `writeUninit` (`TypedRetag.lean:201`
→ `PlaceMachine.writeMemory`) performs a foreign Tree Borrows `.Write` through
`_2`'s tag that disables `_3` (`.ub .treeBorrows`). -/
def d7MoveDerefSiblingFrozenProg : V2026Prog := ⟨[mkBody "caller" 0
  [tU8, tU8, tRaw, tRef, tU8]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 3) (.ref .shared (loc 1)),
        asg (loc 2) (.rawPtr .mut (loc 1))]
     (.call (.constant ⟨tFnCalleeImm, .zeroSized⟩) [.move (drf 2)] (loc 4) (some 1) .continue_),
   blk [asg (loc 0) (.use (.copy (drf 3)))] .return_],
  mkBody "calleeImm" 1 [tU8, tU8] [blk [asg (loc 0) (.use (.copy (loc 1)))] .return_]], 0⟩

theorem call_inPlace_writeUninit_disables_sibling_frozen :
    annealObs d7MoveDerefSiblingFrozenProg [] 40 = .ub .invalidUninitBytes ∧
    refObs true (encodeProg d7MoveDerefSiblingFrozenProg) [] 40 = .ub .invalidUninitBytes ∧
    refObsWith leanMiriUpstreamCallStrategy (encodeProg d7MoveDerefSiblingFrozenProg) [] 40 =
      .ub .treeBorrows := by
  decide

/-- **The 7th-file requirement, stated precisely (corrects B2, extended in B3).**
(1) On `D7` (the moved argument `_1` is memory-backed because `_2 = &raw mut
_1`), the unpatched `Call.lean` path *agrees* with `M_anneal`: the `InPlace`
argument is deinitialized by `protectInPlaceFunctionArgument` before the callee
runs, so the callee's raw-pointer read is UB.
(2) The genuine value-level divergences are on `.immediate → FnArg.Copy`:
    (a) in `d7ImmProg`, a moved immediate argument is still readable in the
        caller after the call returns (`5` vs UB);
    (b) in `d7MoveThenCopySameCallProg`, `call f(move _1, copy _1)` has
        `moveDefinitelyDisjoint = true` (because `moveDefinitelyDisjoint`
        ignores `.Copy` arguments), so `copy _1` in the same call reads `5` and
        returns `10` instead of faulting with `.ub .invalidUninitBytes`! -/
theorem call_move_arg_upstream_call_path :
    annealObs (d7Prog (.move (loc 1))) [] 40 = .ub .invalidUninitBytes ∧
    refObsWith leanMiriUpstreamCallStrategy (encodeProg (d7Prog (.move (loc 1)))) [] 40 =
      .ub .invalidUninitBytes ∧
    annealObs d7ImmProg [] 40 = .ub .invalidUninitBytes ∧
    refObs true (encodeProg d7ImmProg) [] 40 = .ub .invalidUninitBytes ∧
    refObsWith leanMiriUpstreamCallStrategy (encodeProg d7ImmProg) [] 40 = .returned (some 5) 1 ∧
    refObsWith leanMiriUpstreamCallStrategy (encodeProg d7MoveThenCopySameCallProg) [] 40 =
      .returned (some 10) 1 := by
  decide

/-- Hence the unpatched call path is not the reference strategy. -/
theorem leanMiriUpstreamCallStrategy_ne_eager : leanMiriUpstreamCallStrategy ≠ eagerStrategy := by
  intro h
  have h1 := call_move_arg_upstream_call_path.2.2.2.2.1
  rw [h] at h1
  have e : refObsWith eagerStrategy (encodeProg d7ImmProg) [] 40 =
      refObs true (encodeProg d7ImmProg) [] 40 := by decide
  rw [e, call_move_arg_upstream_call_path.2.2.2.1] at h1
  cases h1

/-! ## Part 9 — Tree Borrows: moving out of `*ptr` is not a write -/

deriving instance DecidableEq for TreeBorrowPerm

theorem setLocalE_borrows {st st' : PState} {l : Local} {v : PSlot}
    (h : setLocalE st l v = .ok st') : st'.borrows = st.borrows := by
  unfold setLocalE at h
  cases hf : st.frames with
  | nil => rw [hf] at h; cases h
  | cons fr rest =>
    rw [hf] at h; simp only at h
    cases hs : setNth? fr.locals l v with
    | none => rw [hs] at h; cases h
    | some ls => rw [hs] at h; cases h; rfl

theorem putHeap_borrows {st st' : PState} {a : Nat} {b : Bytes}
    (h : putHeap st a b = .ok st') : st'.borrows = st.borrows := by
  unfold putHeap at h
  cases hs : setNth? st.heap a (some b) with
  | none => rw [hs] at h; cases h
  | some hp => rw [hs] at h; cases h; rfl

theorem deinitMPlaceRaw_borrows {st st' : PState} {mp : MPlace}
    (h : deinitMPlaceRaw st mp = .ok st') : st'.borrows = st.borrows := by
  unfold deinitMPlaceRaw at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some b =>
    rw [hg] at h; simp only at h
    cases hb : Nat.ble (mp.offset + mp.size) b.length with
    | false => rw [hb] at h; cases h
    | true => rw [hb] at h; exact putHeap_borrows h

/-- A Tree Borrows **read** never changes a `.frozen` node (child or foreign). -/
theorem treeBorrowNodeAccess_read_frozen (rel : TreeBorrowRelatedness) :
    treeBorrowNodeAccess .read rel .frozen false = .transition .frozen := by
  cases rel <;> rfl

theorem tbAccessAux_read_preserves_frozen (all : List BorrowEntry) (a : Nat) (tag : Option Nat)
    (off len : Nat) :
    ∀ (es es' : List BorrowEntry), tbAccessAux .read all a tag off len es = some es' →
      ∀ i e, nth? es i = some e → e.perm = .frozen →
        ∃ e', nth? es' i = some e' ∧ e'.tag = e.tag ∧ e'.perm = .frozen
  | [], _, _, i, e, hi, _ => by simp [nth?] at hi
  | x :: xs, es', h, i, e, hi, hf => by
    simp only [tbAccessAux] at h
    cases hr : tbAccessAux .read all a tag off len xs with
    | none => rw [hr] at h; cases h
    | some xs' =>
      rw [hr] at h; simp only at h
      cases i with
      | succ j =>
        simp only [nth?] at hi
        obtain ⟨e', h1, h2, h3⟩ := tbAccessAux_read_preserves_frozen all a tag off len xs xs' hr j e hi hf
        cases hc : (Nat.beq x.targetLocal a && byteRangesOverlapBool x.rangeOffset x.rangeLen off len) <;>
          rw [hc] at h <;> simp only at h
        · cases h; exact ⟨e', h1, h2, h3⟩
        · cases hub : treeBorrowTransitionIsUB
              (treeBorrowNodeAccess .read (tbRelatedness all tag x) x.perm false) <;>
            rw [hub] at h <;> simp only at h
          · cases h; exact ⟨e', h1, h2, h3⟩
          · cases h
      | zero =>
        simp only [nth?, Option.some.injEq] at hi; subst hi
        cases hc : (Nat.beq x.targetLocal a && byteRangesOverlapBool x.rangeOffset x.rangeLen off len) <;>
          rw [hc] at h <;> simp only at h
        · cases h; exact ⟨x, rfl, rfl, hf⟩
        · rw [hf, treeBorrowNodeAccess_read_frozen] at h
          simp only [treeBorrowTransitionIsUB] at h
          cases h
          exact ⟨_, rfl, rfl, rfl⟩

theorem loadMPlace_preserves_frozen {st st' : PState} {mp : MPlace} {b : Bytes}
    (h : loadMPlace st mp = .ok (b, st')) :
    ∀ i e, nth? st.borrows i = some e → e.perm = .frozen →
      ∃ e', nth? st'.borrows i = some e' ∧ e'.tag = e.tag ∧ e'.perm = .frozen := by
  unfold loadMPlace at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some bs =>
    rw [hg] at h; simp only at h
    cases hb : Nat.ble (mp.offset + mp.size) bs.length with
    | false => rw [hb] at h; cases h
    | true =>
      rw [hb] at h; simp only at h
      cases ht : tbAccess .read st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => rw [ht] at h; cases h
      | some bs' =>
        rw [ht] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact tbAccessAux_read_preserves_frozen _ _ _ _ _ _ _ ht

/-- **`deinitMovedPlace_preserves_tb_tags`**: evaluating `Operand.move p`
(in particular `move (*ptr)`) through the two-phase protocol leaves the Tree
Borrows table *exactly* as the corresponding `Operand.copy p` (a pure read)
does, so every `.frozen` tag — e.g. a sibling shared borrow — stays
`.frozen`; only the moved bytes become `.uninit`. -/
theorem deinitMovedPlace_preserves_tb_tags (pb : Nat) (st : PState) (p : SemPlace) (b : Bytes)
    (st₁ : PState) (h : twoPhaseReadOperand true pb st (.move p) = .ok (b, st₁)) :
    (∃ st₂, twoPhaseReadOperand true pb st (.copy p) = .ok (b, st₂) ∧ st₂.borrows = st₁.borrows) ∧
    (∀ i e, nth? st.borrows i = some e → e.perm = .frozen →
      ∃ e', nth? st₁.borrows i = some e' ∧ e'.tag = e.tag ∧ e'.perm = .frozen) := by
  rw [twoPhaseReadOperand_true_eq] at h ⊢
  simp only [annealReadOperand] at h ⊢
  cases he : evalPlaceToOp pb (clearLatch st) p with
  | error e => rw [he] at h; cases h
  | ok r =>
    obtain ⟨o, ty⟩ := r
    rw [he] at h
    cases o with
    | immediate bb =>
      simp only at h
      cases hp : p.projs with
      | cons _ _ => rw [hp] at h; cases h
      | nil =>
        rw [hp] at h; simp only at h
        cases hs : setLocalE (clearLatch st) p.local_ (.imm (uninitBytes bb.length)) with
        | error e => rw [hs] at h; cases h
        | ok st₃ =>
          rw [hs] at h; simp only at h
          cases hv : checkValid ty bb with
          | error e => rw [hv] at h; cases h
          | ok u =>
            rw [hv] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hb3 := setLocalE_borrows hs
            refine ⟨⟨clearLatch st, by simp [readOpBytes, hv], ?_⟩, ?_⟩
            · simp only [clearLatch]; exact hb3.symm
            · intro i e hi hf
              refine ⟨e, ?_, rfl, hf⟩
              show nth? st₃.borrows i = some e
              rw [hb3]; exact hi
    | indirect mp =>
      simp only at h
      cases hl : loadMPlace (clearLatch st) mp with
      | error e => rw [hl] at h; cases h
      | ok r' =>
        obtain ⟨bb, st₃⟩ := r'
        rw [hl] at h; simp only at h
        cases hv : checkValid ty bb with
        | error e => rw [hv] at h; cases h
        | ok u =>
          rw [hv] at h; simp only at h
          cases hd : deinitMPlaceRaw st₃ mp with
          | error e => rw [hd] at h; cases h
          | ok st₄ =>
            rw [hd] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hb4 := deinitMPlaceRaw_borrows hd
            refine ⟨⟨st₃, by simp [readOpBytes, hl, hv], hb4.symm⟩, ?_⟩
            intro i e hi hf
            obtain ⟨e', h1, h2, h3⟩ := loadMPlace_preserves_frozen hl i e hi hf
            exact ⟨e', by rw [hb4]; exact h1, h2, h3⟩

/-- A `.frozen` entry is left *literally unchanged* by any Tree Borrows read. -/
theorem tbAccessAux_read_frozen_unchanged (all : List BorrowEntry) (a : Nat) (tag : Option Nat)
    (off len : Nat) :
    ∀ (es es' : List BorrowEntry), tbAccessAux .read all a tag off len es = some es' →
      ∀ i e, nth? es i = some e → e.perm = .frozen → nth? es' i = some e
  | [], _, _, i, e, hi, _ => by simp [nth?] at hi
  | x :: xs, es', h, i, e, hi, hf => by
    simp only [tbAccessAux] at h
    cases hr : tbAccessAux .read all a tag off len xs with
    | none => rw [hr] at h; cases h
    | some xs' =>
      rw [hr] at h; simp only at h
      cases i with
      | succ j =>
        simp only [nth?] at hi
        have ih := tbAccessAux_read_frozen_unchanged all a tag off len xs xs' hr j e hi hf
        cases hc : (Nat.beq x.targetLocal a && byteRangesOverlapBool x.rangeOffset x.rangeLen off len) <;>
          rw [hc] at h <;> simp only at h
        · cases h; exact ih
        · cases hub : treeBorrowTransitionIsUB
              (treeBorrowNodeAccess .read (tbRelatedness all tag x) x.perm false) <;>
            rw [hub] at h <;> simp only at h
          · cases h; exact ih
          · cases h
      | zero =>
        simp only [nth?, Option.some.injEq] at hi; subst hi
        cases hc : (Nat.beq x.targetLocal a && byteRangesOverlapBool x.rangeOffset x.rangeLen off len) <;>
          rw [hc] at h <;> simp only at h
        · cases h; rfl
        · rw [hf, treeBorrowNodeAccess_read_frozen] at h
          simp only [treeBorrowTransitionIsUB] at h
          cases h
          cases x; simp only at hf; subst hf; rfl

/-- Entries not overlapping an access window are left *literally unchanged*
by any Tree Borrows access (read or write). -/
theorem tbAccessAux_nonoverlap_unchanged (kind : TreeBorrowAccessKind) (all : List BorrowEntry)
    (a : Nat) (tag : Option Nat) (off len : Nat) :
    ∀ (es es' : List BorrowEntry), tbAccessAux kind all a tag off len es = some es' →
      ∀ i e, nth? es i = some e →
        (Nat.beq e.targetLocal a && byteRangesOverlapBool e.rangeOffset e.rangeLen off len) = false →
        nth? es' i = some e
  | [], _, _, i, e, hi, _ => by simp [nth?] at hi
  | x :: xs, es', h, i, e, hi, hno => by
    simp only [tbAccessAux] at h
    cases hr : tbAccessAux kind all a tag off len xs with
    | none => rw [hr] at h; cases h
    | some xs' =>
      rw [hr] at h; simp only at h
      cases i with
      | succ j =>
        simp only [nth?] at hi
        have ih := tbAccessAux_nonoverlap_unchanged kind all a tag off len xs xs' hr j e hi hno
        cases hc : (Nat.beq x.targetLocal a && byteRangesOverlapBool x.rangeOffset x.rangeLen off len) <;>
          rw [hc] at h <;> simp only at h
        · cases h; exact ih
        · cases hub : treeBorrowTransitionIsUB
              (treeBorrowNodeAccess kind (tbRelatedness all tag x) x.perm false) <;>
            rw [hub] at h <;> simp only at h
          · cases h; exact ih
          · cases h
      | zero =>
        simp only [nth?, Option.some.injEq] at hi; subst hi
        rw [hno] at h; simp only at h
        cases h; rfl

theorem loadMPlace_frozen_unchanged {st st' : PState} {mp : MPlace} {b : Bytes}
    (h : loadMPlace st mp = .ok (b, st')) (i : Nat) (e : BorrowEntry)
    (hi : nth? st.borrows i = some e) (hf : e.perm = .frozen) : nth? st'.borrows i = some e := by
  unfold loadMPlace at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some bs =>
    rw [hg] at h; simp only at h
    cases hb : Nat.ble (mp.offset + mp.size) bs.length with
    | false => rw [hb] at h; cases h
    | true =>
      rw [hb] at h; simp only at h
      cases ht : tbAccess .read st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => rw [ht] at h; cases h
      | some bs' =>
        rw [ht] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact tbAccessAux_read_frozen_unchanged _ _ _ _ _ _ _ ht i e hi hf

theorem storeMPlace_nonoverlap_unchanged {st st' : PState} {mp : MPlace} {w : Bytes}
    (h : storeMPlace st mp w = .ok st') (i : Nat) (e : BorrowEntry)
    (hi : nth? st.borrows i = some e)
    (hno : (Nat.beq e.targetLocal mp.alloc &&
      byteRangesOverlapBool e.rangeOffset e.rangeLen mp.offset mp.size) = false) :
    nth? st'.borrows i = some e := by
  unfold storeMPlace at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some bs =>
    rw [hg] at h; simp only at h
    cases hb : (Nat.ble (mp.offset + mp.size) bs.length && Nat.beq w.length mp.size) with
    | false => rw [hb] at h; cases h
    | true =>
      rw [hb] at h; simp only at h
      cases ht : tbAccess .write st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => rw [ht] at h; cases h
      | some bs' =>
        rw [ht] at h; simp only at h
        rw [putHeap_borrows h]
        exact tbAccessAux_nonoverlap_unchanged _ _ _ _ _ _ _ _ ht i e hi hno

/-- Does a Tree Borrows entry overlap a pre-resolved destination window? -/
def entryOverlapsDest (e : BorrowEntry) : DestPlace → Bool
  | .imm _ => false
  | .mem mp =>
    Nat.beq e.targetLocal mp.alloc && byteRangesOverlapBool e.rangeOffset e.rangeLen mp.offset mp.size

theorem writeDest_nonoverlap_unchanged {st st' : PState} {d : DestPlace} {b : Bytes}
    (h : writeDest st d b = .ok st') (i : Nat) (e : BorrowEntry)
    (hi : nth? st.borrows i = some e) (hno : entryOverlapsDest e d = false) :
    nth? st'.borrows i = some e := by
  cases d with
  | imm l => simp only [writeDest] at h; rw [setLocalE_borrows h]; exact hi
  | mem mp => exact storeMPlace_nonoverlap_unchanged h i e hi hno

/-- **`deinitMovedPlace_assignUse_preserves_tb_tags`** (`StatementKind.assign
dest (move p)` through `copyRuntimePlaceNoValidate`): for *every* state, source
place and pre-resolved destination, a successful move leaves every `.frozen`
Tree Borrows entry that does not overlap the destination window *literally
unchanged* — the move's read is a read and its deinit is not a Tree Borrows
access; only the destination store can touch overlapping entries (as it must,
and exactly as the corresponding `copy` would). -/
theorem deinitMovedPlace_assignUse_preserves_tb_tags (pb : Nat) (st : PState) (p : SemPlace)
    (d : DestPlace) (st₁ : PState) (h : twoPhaseAssignUse true pb st (.move p) d = .ok st₁) :
    ∀ i e, nth? st.borrows i = some e → e.perm = .frozen → entryOverlapsDest e d = false →
      nth? st₁.borrows i = some e := by
  intro i e hi hf hno
  rw [twoPhaseAssignUse_true_eq] at h
  simp only [annealAssignUse] at h
  cases he : evalPlaceToOp pb (clearLatch st) p with
  | error err => rw [he] at h; cases h
  | ok r =>
    obtain ⟨o, ty⟩ := r
    rw [he] at h
    cases o with
    | immediate bb =>
      simp only at h
      cases hp : p.projs with
      | cons _ _ => rw [hp] at h; cases h
      | nil =>
        rw [hp] at h; simp only at h
        cases hs : setLocalE (clearLatch st) p.local_ (.imm (uninitBytes bb.length)) with
        | error err => rw [hs] at h; cases h
        | ok st₂ =>
          rw [hs] at h; simp only at h
          cases hv : checkValid ty bb with
          | error err => rw [hv] at h; cases h
          | ok u =>
            rw [hv] at h; simp only at h
            have hb₂ := setLocalE_borrows hs
            exact writeDest_nonoverlap_unchanged h i e (by
              show nth? st₂.borrows i = some e; rw [hb₂]; exact hi) hno
    | indirect src =>
      simp only at h
      cases hm : usesMemoryPath ty (.indirect src) with
      | true =>
        rw [hm] at h; simp only at h
        cases hc : copyMemPath (clearLatch st) src d with
        | error err => rw [hc] at h; cases h
        | ok st₂ =>
          rw [hc] at h; simp only at h
          rw [deinitMPlaceRaw_borrows h]
          cases d with
          | imm l => simp only [copyMemPath] at hc; cases hc
          | mem dmp =>
            simp only [copyMemPath] at hc
            cases hl : loadMPlace (clearLatch st) src with
            | error err => rw [hl] at hc; cases hc
            | ok r' =>
              obtain ⟨bb, st₃⟩ := r'
              rw [hl] at hc; simp only at hc
              have h3 := loadMPlace_frozen_unchanged hl i e hi hf
              cases hov : placesOverlap src dmp with
              | true => rw [hov] at hc; cases hc
              | false =>
                rw [hov] at hc; simp only at hc
                exact storeMPlace_nonoverlap_unchanged hc i e h3 hno
      | false =>
        rw [hm] at h; simp only at h
        cases hl : loadMPlace (clearLatch st) src with
        | error err => rw [hl] at h; cases h
        | ok r' =>
          obtain ⟨bb, st₃⟩ := r'
          rw [hl] at h; simp only at h
          have h3 := loadMPlace_frozen_unchanged hl i e hi hf
          cases hv : checkValid ty bb with
          | error err => rw [hv] at h; cases h
          | ok u =>
            rw [hv] at h; simp only at h
            cases hd : deinitMPlaceRaw st₃ src with
            | error err => rw [hd] at h; cases h
            | ok st₄ =>
              rw [hd] at h; simp only at h
              exact writeDest_nonoverlap_unchanged h i e
                (by rw [deinitMPlaceRaw_borrows hd]; exact h3) hno

/-- A Tree Borrows **write** through a tag that is foreign to an overlapping,
unprotected `.frozen` entry disables it. -/
theorem treeBorrowNodeAccess_foreign_write_frozen :
    treeBorrowNodeAccess .write .foreignAccess .frozen false = .transition .disabled := rfl

theorem tbAccessAux_write_disables_foreign_frozen (all : List BorrowEntry) (a : Nat)
    (tag : Option Nat) (off len : Nat) (e : BorrowEntry) (es es' : List BorrowEntry)
    (h : tbAccessAux .write all a tag off len (e :: es) = some es')
    (hf : e.perm = .frozen) (hl : e.targetLocal = a)
    (ho : byteRangesOverlapBool e.rangeOffset e.rangeLen off len = true)
    (hrel : tbRelatedness all tag e = .foreignAccess) :
    ∃ e' rest, es' = e' :: rest ∧ e'.tag = e.tag ∧ e'.perm = .disabled := by
  simp only [tbAccessAux] at h
  cases hr : tbAccessAux .write all a tag off len es with
  | none => rw [hr] at h; cases h
  | some xs' =>
    rw [hr] at h
    have hc : (Nat.beq e.targetLocal a && byteRangesOverlapBool e.rangeOffset e.rangeLen off len) =
        true := by simp [hl, ho]
    simp only [hc, hrel, hf, treeBorrowNodeAccess_foreign_write_frozen,
      treeBorrowTransitionIsUB] at h
    cases h
    exact ⟨_, _, rfl, rfl, rfl⟩

/-- Permissions of the borrow table after a run (for state-level canaries). -/
def borrowPerms : StepOut → List TreeBorrowPerm
  | .running st => st.borrows.map BorrowEntry.perm
  | _ => []

/-- Run the `D5` prefix (`_1 = 5; _3 = &_1; _2 = &raw mut _1`) then one more
statement. -/
def d5PermsAfter (s : Statement) (steps : Nat) : List TreeBorrowPerm :=
  let p := d5Prog s (.use (.copy (loc 4)))
  match annealInit p [] with
  | .ok st => borrowPerms (annealRun p steps st)
  | .error _ => []

/-- **`assign_or_deinit_stmt_kills_sibling_frozen`**: in the `D5` state the
sibling shared borrow is `.frozen`; `StatementKind.assign (*_2)` and
`StatementKind.deinit (*_2)` disable it, while `_4 = move (*_2)` keeps it
`.frozen` (state-level, both machines). -/
theorem assign_or_deinit_stmt_kills_sibling_frozen :
    d5PermsAfter (asg (loc 4) (.use (.move (drf 2)))) 3 = [.frozen] ∧
    d5PermsAfter (asg (loc 4) (.use (.move (drf 2)))) 4 = [.frozen] ∧
    d5PermsAfter (asg (drf 2) (.use (cU8 9))) 4 = [.disabled] ∧
    d5PermsAfter (stmt (.deinit (drf 2))) 4 = [.disabled] := by
  decide

/-! ## Part 10 — `MiriMoveDeinitWiringClaim` for the prototype -/

/-- **`miriMoveDeinitWiring_proto`** (`withValidation` / `operandHooks` /
`takePendingMoveDeinit` invariants): (1) the reference strategy threads the same
`deinitMoves` flag to `evalOperand` and both consumers; (2) non-move operands
always reset the latch; (3) an indirect move sets it; (4) an unprojected
immediate move replaces the local by `.uninit` and resets it; (5)
`takePendingMoveDeinit` returns `deinitMoves && latch` and clears the latch;
(6) with `deinitMoves = false` the latch is never consulted. -/
theorem miriMoveDeinitWiring_proto (dm : Bool) (pb : Nat) (st : PState) :
    (twoPhaseStrategy dm).readOperand = twoPhaseReadOperand dm ∧
    (twoPhaseStrategy dm).assignUse = twoPhaseAssignUse dm ∧
    (∀ b ty o ty' st', refEvalOperand true pb st (.const b ty) = .ok (o, ty', st') →
      st'.pendingMoveDeinit = false) ∧
    (∀ p o ty st', refEvalOperand true pb st (.copy p) = .ok (o, ty, st') →
      st'.pendingMoveDeinit = false) ∧
    (∀ p mp ty st', refEvalOperand true pb st (.move p) = .ok (.indirect mp, ty, st') →
      st'.pendingMoveDeinit = true) ∧
    (∀ p b ty st', refEvalOperand true pb st (.move p) = .ok (.immediate b, ty, st') →
      st'.pendingMoveDeinit = false ∧ p.projs = []) ∧
    ((takePendingMoveDeinit dm st).1 = (dm && st.pendingMoveDeinit) ∧
      (takePendingMoveDeinit dm st).2.pendingMoveDeinit = false) ∧
    (takePendingMoveDeinit false st).1 = false := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ⟨rfl, rfl⟩, rfl⟩
  · intro b ty o ty' st' h
    simp only [refEvalOperand, ite_true, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl⟩ := h; rfl
  · intro p o ty st' h
    simp only [refEvalOperand, ite_true] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r => rw [he] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  · intro p mp ty st' h
    simp only [refEvalOperand] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, ty₀⟩ := r
      rw [he] at h
      cases o with
      | immediate b =>
        simp only at h
        cases hp : p.projs with
        | cons _ _ => rw [hp] at h; cases h
        | nil =>
          rw [hp] at h; simp only at h
          cases hs : setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b.length)) with
          | error e => rw [hs] at h; cases h
          | ok st₁ => rw [hs] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h; cases h.1
      | indirect mp₀ =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  · intro p b ty st' h
    simp only [refEvalOperand] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, ty₀⟩ := r
      rw [he] at h
      cases o with
      | immediate b₀ =>
        simp only at h
        cases hp : p.projs with
        | cons _ _ => rw [hp] at h; cases h
        | nil =>
          rw [hp] at h; simp only at h
          cases hs : setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b₀.length)) with
          | error e => rw [hs] at h; cases h
          | ok st₁ =>
            rw [hs] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl⟩
      | indirect mp₀ => simp only [Except.ok.injEq, Prod.mk.injEq] at h; cases h.1


/-! ## Part 10b — Live `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand` bridge
and formal proof of Finding 5

1. For unprojected root locals (`place.projection = []`), live
   `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand` deinitializes the moved
   slot to `.uninit` (`set? locals l .uninit`) while `.copy` preserves `locals`.
2. For any projected place (`place.projection = e :: es`, including `.deref` and
   `.field`), live `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand` treats
   `.move` **identically** to `.copy` (kernel-proving Finding 5 of
   `PROTOTYPE_REPORT.md` §3). -/

theorem trusted_evalOperand_root_move_deinits
    (locals locals' : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (l : Local) (v : Trusted.Rustc.V2026_06_01.MirSemantics.Value)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable)
    (callerLocals : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (localDecls : List LocalDecl)
    (hget : Trusted.Sequence.get? locals l = some (.init v))
    (hset : Trusted.Sequence.set? locals l .uninit = some locals') :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand locals (.move ⟨l, []⟩)
      borrows globals layouts callerLocals localDecls = .ok v locals' ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand locals (.copy ⟨l, []⟩)
      borrows globals layouts callerLocals localDecls = .ok v locals := by
  constructor
  · simp [Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand, hget, hset]
  · simp [Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand, hget,
      Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue]

theorem trusted_evalOperand_projected_move_eq_copy
    (locals : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (l : Local) (e : ProjectionElem) (es : List ProjectionElem)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable)
    (callerLocals : List Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot)
    (localDecls : List LocalDecl) :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand locals (.move ⟨l, e :: es⟩)
      borrows globals layouts callerLocals localDecls =
    Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand locals (.copy ⟨l, e :: es⟩)
      borrows globals layouts callerLocals localDecls := by
  cases e <;> rfl


/-! ## Part 10c — A1 hardening: fail-closed pointer constants, destination-first
assignments, and a non-vacuity witness for the assignment Tree Borrows theorem -/

/-- Pointer constants (`ConstValue.scalar (.ptr ..)`) refer to *global*
allocations, which the shared machine does not model; resolving them into the
heap of stack locals would let a constant forge a pointer to a local (allocation
ids of globals and stack locals are different namespaces). They therefore fail
closed in both machines. -/
theorem constSem_ptr_fails_closed (sty : Option SemTy) (p : ProvenancePtr) (sz : Nat) :
    constSem sty (.scalar (.ptr p sz)) = none := by
  cases sty <;> rfl

/-- `_1 = (7, 8); _2 = const ptr{alloc 0, off 0}; _0 = copy (*_2)`: under the
B1 resolution this read the stack local `_1` (heap allocation `0`) through a
*global* pointer constant and returned `7`; it now fails closed. -/
def constPtrForgeProg : V2026Prog := prog1 <| mkBody "constptr" 0 [tU8, tPair, tRaw]
  [blk [asg (loc 1) (.aggregate .tuple [cU8 7, cU8 8]),
        asg (loc 2) (.use (.constant ⟨tRaw, .scalar (.ptr ⟨0, 0⟩ 8)⟩)),
        asg (loc 0) (.use (.copy (drf 2)))] .return_]

theorem canary_const_ptr_fails_closed :
    bothObs constPtrForgeProg = (.unsupported, .unsupported) := by decide

/-- The `D5` state just before `_4 = move (*_2)` (`_1` in memory with a sibling
`.frozen` shared borrow `_3` and the raw pointer `_2`). -/
def d5PreMoveState : Option PState :=
  let p := d5Prog (asg (loc 4) (.use (.move (drf 2)))) (.use (.copy (loc 4)))
  match annealInit p [] with
  | .ok st =>
    match annealRun p 3 st with
    | .running st' => some st'
    | _ => none
  | .error _ => none

def d5MoveOp : SemOperand := .move ⟨2, (.rawPtr .mut kU8, lay (.rawPtr .mut kU8)), [.deref]⟩

/-- Executable check of all premises and the conclusion of
`deinitMovedPlace_assignUse_preserves_tb_tags` on the `D5` move. -/
def tbAssignWitness : Bool :=
  match d5PreMoveState with
  | some st =>
    match twoPhaseAssignUse true 64 st d5MoveOp (.imm 4), nth? st.borrows 0 with
    | .ok st₁, some e =>
      decide (e.perm = .frozen) && !(entryOverlapsDest e (.imm 4)) &&
        decide ((nth? st₁.borrows 0).map BorrowEntry.perm = some .frozen) &&
        decide (st₁.borrows.length = st.borrows.length)
    | _, _ => false
  | none => false

/-- Non-vacuity: the premises of `deinitMovedPlace_assignUse_preserves_tb_tags`
are satisfiable (the `D5` move into `_4` succeeds with a sibling `.frozen`
borrow that does not overlap the destination, which stays `.frozen`). -/
theorem deinitMovedPlace_assignUse_preserves_tb_tags_nonvacuous : tbAssignWitness = true := by
  decide

/-! ## Part 10d — Step-boundary latch invariant (`pendingMoveDeinit = false`) -/

theorem setLocalE_latch {st st' : PState} {l : Local} {v : PSlot}
    (h : setLocalE st l v = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold setLocalE at h
  cases hf : st.frames with
  | nil => rw [hf] at h; cases h
  | cons fr rest =>
    rw [hf] at h; simp only at h
    cases hs : setNth? fr.locals l v with
    | none => rw [hs] at h; cases h
    | some ls => rw [hs] at h; cases h; rfl

theorem putHeap_latch {st st' : PState} {a : Nat} {b : Bytes}
    (h : putHeap st a b = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold putHeap at h
  cases hs : setNth? st.heap a (some b) with
  | none => rw [hs] at h; cases h
  | some hp => rw [hs] at h; cases h; rfl

theorem loadMPlace_latch {st st' : PState} {mp : MPlace} {b : Bytes}
    (h : loadMPlace st mp = .ok (b, st')) : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold loadMPlace at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some bs =>
    rw [hg] at h; simp only at h
    cases hb : Nat.ble (mp.offset + mp.size) bs.length with
    | false => rw [hb] at h; cases h
    | true =>
      rw [hb] at h
      cases ht : tbAccess .read st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => rw [ht] at h; cases h
      | some bs' => rw [ht] at h; cases h; rfl

theorem storeMPlace_latch {st st' : PState} {mp : MPlace} {b : Bytes}
    (h : storeMPlace st mp b = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold storeMPlace at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some bs =>
    rw [hg] at h; simp only at h
    cases hb : (Nat.ble (mp.offset + mp.size) bs.length && Nat.beq b.length mp.size) with
    | false => rw [hb] at h; cases h
    | true =>
      rw [hb] at h; simp only at h
      cases ht : tbAccess .write st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => rw [ht] at h; cases h
      | some bs' => rw [ht] at h; simp only at h; have hl := putHeap_latch h; exact hl

theorem deinitMPlaceRaw_latch {st st' : PState} {mp : MPlace}
    (h : deinitMPlaceRaw st mp = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold deinitMPlaceRaw at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some b =>
    rw [hg] at h; simp only at h
    cases hb : Nat.ble (mp.offset + mp.size) b.length with
    | false => rw [hb] at h; cases h
    | true => rw [hb] at h; exact putHeap_latch h

theorem writeDest_latch {st st' : PState} {d : DestPlace} {b : Bytes}
    (h : writeDest st d b = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  cases d with
  | imm l => exact setLocalE_latch h
  | mem mp => exact storeMPlace_latch h

theorem readOpBytes_latch {st st' : PState} {o : OpTy} {b : Bytes}
    (h : readOpBytes st o = .ok (b, st')) : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  cases o with
  | immediate _ => cases h; rfl
  | indirect mp => exact loadMPlace_latch h

theorem copyMemPath_latch {st st' : PState} {src : MPlace} {d : DestPlace}
    (h : copyMemPath st src d = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  cases d with
  | imm _ => cases h
  | mem dmp =>
    simp only [copyMemPath] at h
    cases hl : loadMPlace st src with
    | error e => rw [hl] at h; cases h
    | ok r =>
      rw [hl] at h; simp only at h
      cases ho : placesOverlap src dmp with
      | true => rw [ho] at h; cases h
      | false => rw [ho] at h; exact (storeMPlace_latch h).trans (loadMPlace_latch hl)

/-- Every successful `twoPhaseReadOperand true` (and `annealReadOperand`) step
leaves `pendingMoveDeinit = false`, regardless of the incoming latch state. -/
theorem twoPhaseReadOperand_true_latch_clear (pb : Nat) (st st' : PState)
    (op : SemOperand) (b : Bytes)
    (h : twoPhaseReadOperand true pb st op = .ok (b, st')) :
    st'.pendingMoveDeinit = false := by
  rw [twoPhaseReadOperand_true_eq] at h
  cases op with
  | const cb ty =>
    simp only [annealReadOperand] at h
    cases hv : checkValid ty cb <;> rw [hv] at h <;> cases h; rfl
  | copy p =>
    simp only [annealReadOperand] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, ty⟩ := r; rw [he] at h; simp only at h
      cases hr : readOpBytes (clearLatch st) o with
      | error e => rw [hr] at h; cases h
      | ok r' =>
        obtain ⟨rb, st₁⟩ := r'; rw [hr] at h; simp only at h
        cases hv : checkValid ty rb <;> rw [hv] at h <;> cases h
        exact readOpBytes_latch hr
  | move p =>
    simp only [annealReadOperand] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, ty⟩ := r; rw [he] at h
      cases o with
      | immediate bb =>
        simp only at h
        cases hp : p.projs with
        | cons _ _ => rw [hp] at h; cases h
        | nil =>
          rw [hp] at h; simp only at h
          cases hs : setLocalE (clearLatch st) p.local_ (.imm (uninitBytes bb.length)) with
          | error e => rw [hs] at h; cases h
          | ok st₁ =>
            rw [hs] at h; simp only at h
            cases hv : checkValid ty bb <;> rw [hv] at h <;> cases h; rfl
      | indirect mp =>
        simp only at h
        cases hl : loadMPlace (clearLatch st) mp with
        | error e => rw [hl] at h; cases h
        | ok r' =>
          obtain ⟨bb, st₁⟩ := r'; rw [hl] at h; simp only at h
          cases hv : checkValid ty bb with
          | error e => rw [hv] at h; cases h
          | ok u =>
            rw [hv] at h; simp only at h
            cases hd : deinitMPlaceRaw st₁ mp with
            | error e => rw [hd] at h; cases h
            | ok st₂ =>
              rw [hd] at h; cases h
              exact (deinitMPlaceRaw_latch hd).trans (loadMPlace_latch hl)

/-- Every successful `twoPhaseAssignUse true` (and `annealAssignUse`) step
leaves `pendingMoveDeinit = false`, regardless of the incoming latch state. -/
theorem twoPhaseAssignUse_true_latch_clear (pb : Nat) (st st' : PState)
    (op : SemOperand) (d : DestPlace)
    (h : twoPhaseAssignUse true pb st op d = .ok st') :
    st'.pendingMoveDeinit = false := by
  rw [twoPhaseAssignUse_true_eq] at h
  cases op with
  | const cb ty =>
    simp only [annealAssignUse] at h
    cases hv : checkValid ty cb with
    | error e => rw [hv] at h; cases h
    | ok u => rw [hv] at h; exact writeDest_latch h
  | copy p =>
    simp only [annealAssignUse] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, ty⟩ := r; rw [he] at h
      cases o with
      | immediate bb =>
        simp only [readOpBytes] at h
        cases hv : checkValid ty bb with
        | error e => rw [hv] at h; cases h
        | ok u => rw [hv] at h; exact writeDest_latch h
      | indirect src =>
        simp only at h
        cases hm : usesMemoryPath ty (.indirect src) with
        | true => rw [hm] at h; exact copyMemPath_latch h
        | false =>
          rw [hm] at h; simp only [readOpBytes] at h
          cases hl : loadMPlace (clearLatch st) src with
          | error e => rw [hl] at h; cases h
          | ok r' =>
            obtain ⟨bb, st₁⟩ := r'; rw [hl] at h; simp only at h
            cases hv : checkValid ty bb with
            | error e => rw [hv] at h; cases h
            | ok u => rw [hv] at h; exact (writeDest_latch h).trans (loadMPlace_latch hl)
  | move p =>
    simp only [annealAssignUse] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, ty⟩ := r; rw [he] at h
      cases o with
      | immediate bb =>
        simp only at h
        cases hp : p.projs with
        | cons _ _ => rw [hp] at h; cases h
        | nil =>
          rw [hp] at h; simp only at h
          cases hs : setLocalE (clearLatch st) p.local_ (.imm (uninitBytes bb.length)) with
          | error e => rw [hs] at h; cases h
          | ok st₁ =>
            rw [hs] at h; simp only at h
            cases hv : checkValid ty bb with
            | error e => rw [hv] at h; cases h
            | ok u => rw [hv] at h; exact writeDest_latch h
      | indirect src =>
        simp only at h
        cases hm : usesMemoryPath ty (.indirect src) with
        | true =>
          rw [hm] at h; simp only at h
          cases hc : copyMemPath (clearLatch st) src d with
          | error e => rw [hc] at h; cases h
          | ok st₁ => rw [hc] at h; exact (deinitMPlaceRaw_latch h).trans (copyMemPath_latch hc)
        | false =>
          rw [hm] at h; simp only at h
          cases hl : loadMPlace (clearLatch st) src with
          | error e => rw [hl] at h; cases h
          | ok r' =>
            obtain ⟨bb, st₁⟩ := r'; rw [hl] at h; simp only at h
            cases hv : checkValid ty bb with
            | error e => rw [hv] at h; cases h
            | ok u =>
              rw [hv] at h; simp only at h
              cases hd : deinitMPlaceRaw st₁ src with
              | error e => rw [hd] at h; cases h
              | ok st₂ =>
                rw [hd] at h
                exact (writeDest_latch h).trans ((deinitMPlaceRaw_latch hd).trans (loadMPlace_latch hl))

theorem forceAllocation_latch {st st' : PState} {l : Local}
    (h : forceAllocation st l = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold forceAllocation at h
  cases hf : st.frames with
  | nil => rw [hf] at h; cases h
  | cons fr rest =>
    rw [hf] at h; simp only at h
    cases hn : nth? fr.locals l with
    | none => rw [hn] at h; cases h
    | some sl =>
      rw [hn] at h
      cases sl with
      | dead => cases h
      | mem _ => cases h; rfl
      | imm b =>
        simp only at h
        cases hs : setNth? fr.locals l (.mem st.heap.length) with
        | none => rw [hs] at h; cases h
        | some ls => rw [hs] at h; cases h; rfl

theorem placeToMPlace_latch {pb : Nat} {st st' : PState} {p : SemPlace} {mp : MPlace}
    (h : placeToMPlace pb st p = .ok (mp, st')) : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold placeToMPlace at h
  cases hp : p.projs with
  | nil =>
    rw [hp] at h; simp only at h
    cases hf : forceAllocation st p.local_ with
    | error e => rw [hf] at h; cases h
    | ok st₁ =>
      rw [hf] at h; simp only at h
      cases he : evalPlaceToOp pb st₁ p with
      | error e => rw [he] at h; cases h
      | ok r =>
        obtain ⟨o, _⟩ := r; rw [he] at h
        cases o <;> cases h
        exact forceAllocation_latch hf
  | cons _ _ =>
    rw [hp] at h; simp only at h
    cases he : evalPlaceToOp pb st p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, _⟩ := r; rw [he] at h
      cases o <;> cases h; rfl

theorem createRef_latch {st st' : PState} {mutbl : Bool} {mp : MPlace} {b : Bytes}
    (h : createRef st mutbl mp = .ok (b, st')) : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold createRef at h
  cases ht : tbAccess .read st.borrows mp.alloc mp.tag mp.offset mp.size with
  | none => rw [ht] at h; cases h
  | some bs => rw [ht] at h; cases h; rfl

theorem writePlace_latch {pb : Nat} {st st' : PState} {dest : SemPlace} {b : Bytes}
    (h : writePlace pb st dest b = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold writePlace at h
  cases he : evalPlaceToOp pb st dest with
  | error e => rw [he] at h; cases h
  | ok r =>
    obtain ⟨o, _⟩ := r; rw [he] at h
    cases o with
    | immediate _ => exact setLocalE_latch h
    | indirect _ => exact storeMPlace_latch h

theorem readOperandsWith_true_latch_clear (pb : Nat) :
    ∀ (st st' : PState) (ops : List SemOperand) (bs : List Bytes),
      st.pendingMoveDeinit = false →
      readOperandsWith (twoPhaseReadOperand true) pb st ops = .ok (bs, st') →
      st'.pendingMoveDeinit = false
  | st, st', [], bs, h0, h => by simp only [readOperandsWith] at h; cases h; exact h0
  | st, st', op :: ops, bs, _, h => by
    simp only [readOperandsWith] at h
    cases hr : twoPhaseReadOperand true pb st op with
    | error e => rw [hr] at h; cases h
    | ok r =>
      obtain ⟨b, st₁⟩ := r; rw [hr] at h; simp only at h
      cases hrs : readOperandsWith (twoPhaseReadOperand true) pb st₁ ops with
      | error e => rw [hrs] at h; cases h
      | ok r' =>
        obtain ⟨bs', st₂⟩ := r'; rw [hrs] at h; cases h
        exact readOperandsWith_true_latch_clear pb st₁ st' ops bs'
          (twoPhaseReadOperand_true_latch_clear pb st st₁ op b hr) hrs

theorem advance_latch (st : PState) : (advance st).pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold advance; cases st.frames <;> rfl

theorem jump_latch (st : PState) (bb : Nat) : (jump st bb).pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold jump; cases st.frames <;> rfl

theorem popFrame_latch (st : PState) : (popFrame st).pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold popFrame; cases st.frames <;> rfl

theorem execStmt_true_latch_clear (pb : Nat) (st st' : PState) (s : SemStmt)
    (h0 : st.pendingMoveDeinit = false)
    (h : execStmt (twoPhaseStrategy true) pb st s = .ok st') :
    st'.pendingMoveDeinit = false := by
  cases s with
  | assign dest rv =>
    simp only [execStmt] at h
    cases hd : resolveDest pb st dest with
    | error e => rw [hd] at h; cases h
    | ok rd =>
      obtain ⟨d, dty⟩ := rd; rw [hd] at h; simp only at h
      cases rv with
      | use op => exact twoPhaseAssignUse_true_latch_clear pb st st' op d h
      | binaryOp o l r =>
        simp only [twoPhaseStrategy] at h
        cases hl : twoPhaseReadOperand true pb st l with
        | error e => rw [hl] at h; cases h
        | ok rl =>
          obtain ⟨lb, st₁⟩ := rl; rw [hl] at h; simp only at h
          cases hr : twoPhaseReadOperand true pb st₁ r with
          | error e => rw [hr] at h; cases h
          | ok rr =>
            obtain ⟨rb, st₂⟩ := rr; rw [hr] at h; simp only at h
            cases hb : evalBinOpBytes o lb rb with
            | error e => rw [hb] at h; cases h
            | ok res =>
              rw [hb] at h
              exact (writeDest_latch h).trans (twoPhaseReadOperand_true_latch_clear pb st₁ st₂ r rb hr)
      | aggregate ops =>
        simp only [readOperands, twoPhaseStrategy] at h
        cases hrs : readOperandsWith (twoPhaseReadOperand true) pb st ops with
        | error e => rw [hrs] at h; cases h
        | ok ro =>
          obtain ⟨bs, st₁⟩ := ro; rw [hrs] at h; simp only at h
          cases ha : buildAggregate dty.2 bs with
          | error e => rw [ha] at h; cases h
          | ok b =>
            rw [ha] at h
            exact (writeDest_latch h).trans (readOperandsWith_true_latch_clear pb st st₁ ops bs h0 hrs)
      | ref mutbl p =>
        simp only at h
        cases hp : placeToMPlace pb st p with
        | error e => rw [hp] at h; cases h
        | ok rp =>
          obtain ⟨mp, st₁⟩ := rp; rw [hp] at h; simp only at h
          cases hc : createRef st₁ mutbl mp with
          | error e => rw [hc] at h; cases h
          | ok rc =>
            obtain ⟨b, st₂⟩ := rc; rw [hc] at h
            exact (writeDest_latch h).trans ((createRef_latch hc).trans ((placeToMPlace_latch hp).trans h0))
      | rawPtr p =>
        simp only at h
        cases hp : placeToMPlace pb st p with
        | error e => rw [hp] at h; cases h
        | ok rp =>
          obtain ⟨mp, st₁⟩ := rp; rw [hp] at h
          exact (writeDest_latch h).trans ((placeToMPlace_latch hp).trans h0)
      | unsupported => cases h
  | deinit p =>
    simp only [execStmt] at h
    cases he : evalPlaceToOp pb st p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, _⟩ := r; rw [he] at h
      cases o with
      | immediate _ => exact (setLocalE_latch h).trans h0
      | indirect _ => exact (storeMPlace_latch h).trans h0
  | storageLive l ty =>
    simp only [execStmt] at h
    cases hi : isImmKind ty.1 with
    | true => rw [hi] at h; exact (setLocalE_latch h).trans h0
    | false =>
      rw [hi] at h; simp only at h
      have hl := setLocalE_latch h
      exact hl.trans h0
  | storageDead l =>
    simp only [execStmt] at h
    cases hf : st.frames with
    | nil => rw [hf] at h; cases h
    | cons fr rest =>
      rw [hf] at h; simp only at h
      cases hn : nth? fr.locals l with
      | none => rw [hn] at h; exact (setLocalE_latch h).trans h0
      | some sl =>
        rw [hn] at h
        cases sl with
        | dead => exact (setLocalE_latch h).trans h0
        | imm _ => exact (setLocalE_latch h).trans h0
        | mem a =>
          simp only at h
          cases hs : setNth? st.heap a none with
          | none => rw [hs] at h; cases h
          | some hp => rw [hs] at h; have hl := setLocalE_latch h; exact hl.trans h0
  | nop => cases h; exact h0
  | unsupported => cases h

theorem execTerm_true_latch_clear (pb : Nat) (st st' : PState) (t : SemTerm)
    (h0 : st.pendingMoveDeinit = false)
    (h : execTerm (twoPhaseStrategy true) pb st t = .running st') :
    st'.pendingMoveDeinit = false := by
  cases t with
  | goto bb => cases h; rw [jump_latch]; exact h0
  | ret retTy site =>
    simp only [execTerm] at h
    cases he : evalPlaceToOp pb st ⟨0, retTy, []⟩ with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, _⟩ := r; rw [he] at h; simp only at h
      cases hr : readOpBytes st o with
      | error e => rw [hr] at h; cases h
      | ok ro =>
        obtain ⟨b, st₁⟩ := ro; rw [hr] at h; simp only at h
        have h1 : st₁.pendingMoveDeinit = false := (readOpBytes_latch hr).trans h0
        cases hv : checkValid retTy b with
        | error e => rw [hv] at h; cases h
        | ok u =>
          rw [hv] at h; simp only at h
          cases site with
          | none => cases h
          | some rs =>
            simp only at h
            have hwr : ∀ st₃, (match st₁.frames with
                | fr :: _ =>
                  match fr.retDest with
                  | some d => writeDest (popFrame st₁) d b
                  | none => writePlace pb (popFrame st₁) rs.dest b
                | [] => writePlace pb (popFrame st₁) rs.dest b) = .ok st₃ →
                st₃.pendingMoveDeinit = false := by
              intro st₃ hw
              cases hf : st₁.frames with
              | nil => rw [hf] at hw; exact (writePlace_latch hw).trans ((popFrame_latch st₁).trans h1)
              | cons fr _ =>
                rw [hf] at hw; simp only at hw
                cases hd : fr.retDest with
                | none => rw [hd] at hw; exact (writePlace_latch hw).trans ((popFrame_latch st₁).trans h1)
                | some d => rw [hd] at hw; exact (writeDest_latch hw).trans ((popFrame_latch st₁).trans h1)
            cases hw : (match st₁.frames with
                | fr :: _ =>
                  match fr.retDest with
                  | some d => writeDest (popFrame st₁) d b
                  | none => writePlace pb (popFrame st₁) rs.dest b
                | [] => writePlace pb (popFrame st₁) rs.dest b) with
            | error e => rw [hw] at h; cases h
            | ok st₃ =>
              rw [hw] at h; simp only at h
              cases ht : rs.target with
              | none => rw [ht] at h; cases h
              | some tgt => rw [ht] at h; cases h; rw [jump_latch]; exact hwr st₃ hw
  | switchInt d ts =>
    simp only [execTerm, twoPhaseStrategy] at h
    cases hr : twoPhaseReadOperand true pb st d with
    | error e => rw [hr] at h; cases h
    | ok r =>
      obtain ⟨b, st₁⟩ := r; rw [hr] at h; simp only at h
      cases hd : decodeLittleEndianBytes b with
      | none => rw [hd] at h; cases h
      | some p => rw [hd] at h; cases h; rw [jump_latch]; exact twoPhaseReadOperand_true_latch_clear pb st st₁ d b hr
  | assert c expected target unwind =>
    simp only [execTerm, twoPhaseStrategy] at h
    cases hr : twoPhaseReadOperand true pb st c with
    | error e => rw [hr] at h; cases h
    | ok r =>
      obtain ⟨b, st₁⟩ := r; rw [hr] at h; simp only at h
      have h1 := twoPhaseReadOperand_true_latch_clear pb st st₁ c b hr
      cases hd : decodeLittleEndianBytes b with
      | none => rw [hd] at h; cases h
      | some p =>
        rw [hd] at h; simp only at h
        cases hc : decide (Nat.beq p.1 1 = expected) with
        | true => rw [hc] at h; cases h; rw [jump_latch]; exact h1
        | false =>
          rw [hc] at h; simp only at h
          cases hu : unwind <;> rw [hu] at h <;> cases h
          rw [jump_latch]; exact h1
  | call callee argc calleeLocals args dest =>
    simp only [execTerm, twoPhaseStrategy] at h
    cases hd : resolveDest pb st dest with
    | error e => rw [hd] at h; cases h
    | ok rd =>
      rw [hd] at h; simp only at h
      cases hrs : readOperandsWith (twoPhaseReadOperand true) pb st args with
      | error e => rw [hrs] at h; cases h
      | ok ro =>
        obtain ⟨bs, st₁⟩ := ro; rw [hrs] at h; simp only at h
        cases callee with
        | none => cases h
        | some bi =>
          cases h
          exact readOperandsWith_true_latch_clear pb st st₁ args bs h0 hrs
  | unwindResume site =>
    simp only [execTerm] at h
    cases site with
    | none => cases h
    | some rs =>
      simp only at h
      cases hu : rs.unwind <;> rw [hu] at h <;> cases h
      rw [jump_latch, popFrame_latch]; exact h0
  | unreachable => cases h
  | unsupported => cases h

/-- **Whole-step latch invariant (`M_ref` and `M_anneal`)**: starting from any
state with `pendingMoveDeinit = false`, every `.running` step of `refStepCore
true (encodeProg p)` and `annealStep p` leaves `pendingMoveDeinit = false`. -/
theorem refStepCore_true_preserves_latch_clear (p : V2026Prog) (st st' : PState)
    (h0 : st.pendingMoveDeinit = false)
    (h : refStepCore true (encodeProg p) st = .running st') :
    st'.pendingMoveDeinit = false := by
  simp only [refStepCore, refStepCoreWith] at h
  cases hf : refFetch (encodeProg p) st with
  | error e => rw [hf] at h; cases h
  | ok i =>
    rw [hf] at h
    cases i with
    | stmt pb s =>
      simp only [runInstr] at h
      cases hs : execStmt (twoPhaseStrategy true) pb st s with
      | error e => rw [hs] at h; cases h
      | ok st₁ =>
        rw [hs] at h; cases h
        rw [advance_latch]; exact execStmt_true_latch_clear pb st st₁ s h0 hs
    | term pb t =>
      exact execTerm_true_latch_clear pb st st' t h0 h

theorem annealStep_preserves_latch_clear (p : V2026Prog) (st st' : PState)
    (h0 : st.pendingMoveDeinit = false)
    (h : annealStep p st = .running st') :
    st'.pendingMoveDeinit = false := by
  rw [← anneal_corresponds_to_miri_proto] at h
  exact refStepCore_true_preserves_latch_clear p st st' h0 h

/-! ### Reachable-state latch invariant (entry states + bounded runs)

B3's whole-step invariant is relative to a clear incoming latch; closing it
under the entry states and the run loops makes it a property of **every
reachable** `M_anneal` / `M_ref` statement-boundary state: `pendingMoveDeinit`
latched by phase 1 (`evalOperand`) is always consumed by phase 2
(`readImmediate` / `copyRuntimePlaceNoValidate`) inside the same step. -/

theorem annealInit_latch_clear (p : V2026Prog) (args : List Bytes) (st : PState)
    (h : annealInit p args = .ok st) : st.pendingMoveDeinit = false := by
  unfold annealInit at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

theorem refInit_latch_clear (rp : RefProg) (args : List Bytes) (st : PState)
    (h : refInit rp args = .ok st) : st.pendingMoveDeinit = false := by
  unfold refInit at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

theorem annealRun_preserves_latch_clear (p : V2026Prog) :
    ∀ (n : Nat) (st st' : PState), st.pendingMoveDeinit = false →
      annealRun p n st = .running st' → st'.pendingMoveDeinit = false
  | 0, st, st', h0, h => by
    rw [annealRun.eq_1] at h
    cases h; exact h0
  | n + 1, st, st', h0, h => by
    rw [annealRun.eq_2] at h
    cases hs : annealStep p st with
    | running st₁ =>
      rw [hs] at h
      exact annealRun_preserves_latch_clear p n st₁ st'
        (annealStep_preserves_latch_clear p st st₁ h0 hs) h
    | returned b => rw [hs] at h; cases h
    | panicked => rw [hs] at h; cases h
    | fault f => rw [hs] at h; cases h

theorem refStep_true_preserves_latch_clear (p : V2026Prog) (rs rs' : RefState)
    (h0 : rs.core.pendingMoveDeinit = false)
    (h : refStep true (encodeProg p) rs = .running rs') :
    rs'.core.pendingMoveDeinit = false := by
  unfold refStep at h
  cases hb : Nat.blt rs.stepsExecuted rs.maxSteps with
  | false => rw [hb] at h; cases h
  | true =>
    rw [hb] at h
    cases hc : refStepCore true (encodeProg p) rs.core with
    | running st' =>
      rw [hc] at h; cases h
      exact refStepCore_true_preserves_latch_clear p rs.core st' h0 hc
    | returned b => rw [hc] at h; cases h
    | panicked => rw [hc] at h; cases h
    | fault f =>
      rw [hc] at h
      cases f with
      | ub why => cases h
      | unsupported => cases h

theorem refRunFuel_true_preserves_latch_clear (p : V2026Prog) :
    ∀ (n : Nat) (rs rs' : RefState), rs.core.pendingMoveDeinit = false →
      refRunFuel true (encodeProg p) n rs = .running rs' → rs'.core.pendingMoveDeinit = false
  | 0, rs, rs', h0, h => by
    rw [refRunFuel.eq_1] at h
    cases h; exact h0
  | n + 1, rs, rs', h0, h => by
    rw [refRunFuel.eq_2] at h
    cases hs : refStep true (encodeProg p) rs with
    | running rs₁ =>
      rw [hs] at h
      exact refRunFuel_true_preserves_latch_clear p n rs₁ rs'
        (refStep_true_preserves_latch_clear p rs rs₁ h0 hs) h
    | returned b => rw [hs] at h; cases h
    | panicked => rw [hs] at h; cases h
    | ub why => rw [hs] at h; cases h
    | blocked => rw [hs] at h; cases h
    | exhaustedStepLimit => rw [hs] at h; cases h

/-- **Reachable-state latch invariant (`M_anneal`)**: every `.running` state of a
bounded run from an entry state has `pendingMoveDeinit = false`. -/
theorem annealReachable_latch_clear (p : V2026Prog) (args : List Bytes) (n : Nat)
    (st₀ st : PState) (hi : annealInit p args = .ok st₀)
    (hr : annealRun p n st₀ = .running st) : st.pendingMoveDeinit = false :=
  annealRun_preserves_latch_clear p n st₀ st (annealInit_latch_clear p args st₀ hi) hr

/-- **Reachable-state latch invariant (`M_ref`, `deinitMoves = true`)**: every
`.running` state of a bounded `refRunFuel` from an entry state of
`encodeProg p` (any step budget) has `pendingMoveDeinit = false`. -/
theorem refReachable_latch_clear (p : V2026Prog) (args : List Bytes) (n maxSteps : Nat)
    (st₀ : PState) (rs : RefState) (hi : refInit (encodeProg p) args = .ok st₀)
    (hr : refRunFuel true (encodeProg p) n ⟨st₀, 0, maxSteps⟩ = .running rs) :
    rs.core.pendingMoveDeinit = false :=
  refRunFuel_true_preserves_latch_clear p n ⟨st₀, 0, maxSteps⟩ rs
    (refInit_latch_clear (encodeProg p) args st₀ hi) hr

/-- Executable non-vacuity check for the reachable-state latch invariant on the
`D5` indirect move `_4 = move (*_2)`: (1) the pre-move state is reachable in both
machines (`annealInit` + 3 `annealRun` steps, and `refInit (encodeProg p)` + 3
`refRunFuel` steps reach the same state with a clear latch); (2) phase 1 of
`M_ref` (`refEvalOperand true`) **sets** the latch mid-step, so the invariant is
not a constant (a mutant step that stopped after phase 1 would leak it); and
(3) the full `M_ref` step consumes it again. -/
def reachableLatchWitness : Bool :=
  let p := d5Prog (asg (loc 4) (.use (.move (drf 2)))) (.use (.copy (loc 4)))
  match d5PreMoveState, refInit (encodeProg p) [] with
  | some st, .ok r₀ =>
    match refRunFuel true (encodeProg p) 3 ⟨r₀, 0, 100⟩, refEvalOperand true 64 st d5MoveOp,
        refStepCore true (encodeProg p) st with
    | .running rs, .ok (.indirect _, _, stMid), .running st' =>
      decide (rs.core.frames.length = st.frames.length) &&
        decide (rs.core.heap.length = st.heap.length) &&
        decide (rs.core.borrows.length = st.borrows.length) && decide (rs.stepsExecuted = 3) &&
        !rs.core.pendingMoveDeinit && !st.pendingMoveDeinit && stMid.pendingMoveDeinit &&
        !st'.pendingMoveDeinit
    | _, _, _ => false
  | _, _ => false

theorem reachable_latch_clear_nonvacuous : reachableLatchWitness = true := by
  decide

/-! ## Part 11 — Axiom guards (kernel axioms ⊆ {propext, Quot.sound}) -/

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.decodeType_encodeType' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeType_encodeType

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.decodePlace_encodePlace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decodePlace_encodePlace

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.decodeOperand_encodeOperand' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeOperand_encodeOperand

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.decodeRvalue_encodeRvalue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeRvalue_encodeRvalue

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.decodeStmt_encodeStmt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeStmt_encodeStmt

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.decodeTerminator_encodeTerminator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeTerminator_encodeTerminator

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.decodeBody_encodeBody' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeBody_encodeBody

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.decodeProg_encodeProg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeProg_encodeProg

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.encodeProg_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encodeProg_injective

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.encodeProg_types_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encodeProg_types_canonical

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.encodeStmt_no_dormant_noops' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms encodeStmt_no_dormant_noops

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.encodeTermKind_tag' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms encodeTermKind_tag

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.encodeRvalue_tag' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms encodeRvalue_tag

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.roundtrip_body_of_extends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundtrip_body_of_extends

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.layoutQuery_scalar_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms layoutQuery_scalar_iff

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.layoutQuery_zst_unit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms layoutQuery_zst_unit

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.layoutQuery_oob_fails_closed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms layoutQuery_oob_fails_closed

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.layoutQuery_dangling_layout_fails_closed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms layoutQuery_dangling_layout_fails_closed

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.layoutQuery_mono_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms layoutQuery_mono_prefix

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.layoutQuery_agrees_with_eager' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms layoutQuery_agrees_with_eager

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.layoutQuery_pointee_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms layoutQuery_pointee_total

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.twoPhaseStrategy_true_eq_eager' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoPhaseStrategy_true_eq_eager

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.deinitMovedPlace_false_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deinitMovedPlace_false_id

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.anneal_corresponds_to_miri_proto' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms anneal_corresponds_to_miri_proto

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.refFetch_encodeProg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refFetch_encodeProg

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.refObs_encodeProg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refObs_encodeProg

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.reachesResult_fault_iff_refReachesOutcome_proto' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reachesResult_fault_iff_refReachesOutcome_proto

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.behavior_transfer_proto' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms behavior_transfer_proto

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.simulationInv_bijective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulationInv_bijective

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.correspondence_fails_when_deinitMoves_false' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms correspondence_fails_when_deinitMoves_false

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.no_correspondence_when_deinitMoves_false' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms no_correspondence_when_deinitMoves_false

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.eager_indirect_deinit_falsified' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms eager_indirect_deinit_falsified

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.eagerInEvalOperandStrategy_ne_eager' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms eagerInEvalOperandStrategy_ne_eager

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.batched_call_args_lose_move_deinit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms batched_call_args_lose_move_deinit

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.deinitMovedPlace_preserves_tb_tags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deinitMovedPlace_preserves_tb_tags

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.tbAccessAux_write_disables_foreign_frozen' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms tbAccessAux_write_disables_foreign_frozen

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.assign_or_deinit_stmt_kills_sibling_frozen' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms assign_or_deinit_stmt_kills_sibling_frozen

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.miriMoveDeinitWiring_proto' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms miriMoveDeinitWiring_proto

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.encodeProg_traitImpl_kinds_interned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encodeProg_traitImpl_kinds_interned

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.refProgWellFormed_encodeProg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refProgWellFormed_encodeProg

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.refProgWellFormed_nonvacuous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refProgWellFormed_nonvacuous

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.deinitMovedPlace_assignUse_preserves_tb_tags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deinitMovedPlace_assignUse_preserves_tb_tags

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.trusted_evalOperand_root_move_deinits' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms trusted_evalOperand_root_move_deinits

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.trusted_evalOperand_projected_move_eq_copy' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms trusted_evalOperand_projected_move_eq_copy

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D1_direct_move_ub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D1_direct_move_ub

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D1_zst_unit_move_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D1_zst_unit_move_ok

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D2_partial_field_move_sibling_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D2_partial_field_move_sibling_ok

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D2_partial_field_move_reread_ub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D2_partial_field_move_reread_ub

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D3_move_then_reinit_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D3_move_then_reinit_ok

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D4_copy_keeps_source' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D4_copy_keeps_source

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D4_copy_then_move_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D4_copy_then_move_ok

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D4_move_then_copy_ub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D4_move_then_copy_ub

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D4_move_then_move_ub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D4_move_then_move_ub

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D5_indirect_move_delivers_value' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D5_indirect_move_delivers_value

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D5_indirect_move_reread_ub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D5_indirect_move_reread_ub

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D5_move_preserves_sibling_frozen' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D5_move_preserves_sibling_frozen

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D5_assign_disables_sibling_frozen' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D5_assign_disables_sibling_frozen

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D5_deinit_disables_sibling_frozen' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D5_deinit_disables_sibling_frozen

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D6_direct_self_move_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D6_direct_self_move_ok

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D6_indirect_self_move_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D6_indirect_self_move_ok

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D6_field_swap_self_aggregate_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D6_field_swap_self_aggregate_ok

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D7_call_arg_move_deinit_before_callee' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D7_call_arg_move_deinit_before_callee

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D7_call_arg_copy_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D7_call_arg_copy_ok

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D7_uninit_arg_ub_before_unsupported' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D7_uninit_arg_ub_before_unsupported

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D7_unresolved_callee_unsupported' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D7_unresolved_callee_unsupported

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D8_assert_cleanup_moved_cond_ub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D8_assert_cleanup_moved_cond_ub

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D8_assert_cleanup_unmoved_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D8_assert_cleanup_unmoved_ok

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D8_unwinding_call_moved_arg_ub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D8_unwinding_call_moved_arg_ub

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D8_unwinding_call_unmoved_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D8_unwinding_call_unmoved_ok

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D9_elem_move_neighbors_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D9_elem_move_neighbors_ok

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D9_elem_move_reread_ub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D9_elem_move_reread_ub

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D9_subslice_move_window' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D9_subslice_move_window

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.constSem_ptr_fails_closed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms constSem_ptr_fails_closed

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_const_ptr_fails_closed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_const_ptr_fails_closed

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.deinitMovedPlace_assignUse_preserves_tb_tags_nonvacuous' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms deinitMovedPlace_assignUse_preserves_tb_tags_nonvacuous

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.tbAccessAux_read_frozen_unchanged' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms tbAccessAux_read_frozen_unchanged

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.tbAccessAux_nonoverlap_unchanged' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms tbAccessAux_nonoverlap_unchanged

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.writeDest_nonoverlap_unchanged' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms writeDest_nonoverlap_unchanged

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D7_call_dest_resolved_before_arg_move' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D7_call_dest_resolved_before_arg_move

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D7_call_bad_dest_ub_before_unsupported' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D7_call_bad_dest_ub_before_unsupported

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.call_move_arg_upstream_call_path' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms call_move_arg_upstream_call_path

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.leanMiriUpstreamCallStrategy_ne_eager' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms leanMiriUpstreamCallStrategy_ne_eager

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.twoPhaseReadOperand_true_latch_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoPhaseReadOperand_true_latch_clear

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.twoPhaseAssignUse_true_latch_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoPhaseAssignUse_true_latch_clear

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.canary_D7_call_move_then_copy_arg_ub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_D7_call_move_then_copy_arg_ub

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.call_inPlace_writeUninit_disables_sibling_frozen' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms call_inPlace_writeUninit_disables_sibling_frozen

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.refStepCore_true_preserves_latch_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refStepCore_true_preserves_latch_clear

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.annealStep_preserves_latch_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms annealStep_preserves_latch_clear

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.annealInit_latch_clear' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms annealInit_latch_clear

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.refInit_latch_clear' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms refInit_latch_clear

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.annealReachable_latch_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms annealReachable_latch_clear

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.refReachable_latch_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refReachable_latch_clear

/-- info: 'Anneal.LeanMiriDeinitAndCodecPrototype.reachable_latch_clear_nonvacuous' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms reachable_latch_clear_nonvacuous

/-! ## Part 12 — Whole-environment audit

Every declaration of this module (not only the guarded headline theorems) is
checked here: its transitive axioms must be ⊆ `{propext, Quot.sound}` (no
`sorryAx`, no `Lean.ofReduceBool`, no `Classical.choice`). A violation makes
this file fail to elaborate. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pre := `Anneal.LeanMiriDeinitAndCodecPrototype
  let names := env.constants.map₂.foldl (init := (#[] : Array Name)) fun acc n _ =>
    if pre.isPrefixOf n then acc.push n else acc
  let mut bad : Array (Name × Name) := #[]
  for n in names do
    let axs ← collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Quot.sound do
        bad := bad.push (n, a)
  unless bad.isEmpty do
    throwError m!"forbidden axioms in prototype environment: {bad}"
  unless names.size ≥ 300 do
    throwError m!"environment audit saw only {names.size} declarations"

end Anneal.LeanMiriDeinitAndCodecPrototype
