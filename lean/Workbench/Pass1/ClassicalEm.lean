-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Tactics

/-!
# Foundation-Locked Classical Excluded Middle & Choice (`Workbench.Pass1.ClassicalEm`)

Anneal's 51 locked `Init.*` foundation modules exclude `Init.Classical`, and
`TrustedBoundary.allowedTheoryTacticKinds` excludes `by_cases`. This module
derives Diaconescu's theorem (`prop_em : p ∨ ¬ p`), double-negation elimination
(`of_not_not`), proof by contradiction (`by_contra`), and existential witness
selection (`chooseExists` / `chooseExists_spec`) directly from `Init.Core`
using only `[propext, Classical.choice]` and allowed Pass-1 tactics (`0`
`._unsafe_rec`).

Usage in Pass-1 proofs (replacing `by_cases h : P`):
```lean
cases prop_em P with
| inl h => ...
| inr h => ...
```
-/

namespace Workbench.Pass1.ClassicalEm

noncomputable def chooseSub {α : Sort u} {P : α → Prop}
    (h : Nonempty (Subtype P)) : α :=
  (Classical.choice h).1

theorem chooseSub_spec {α : Sort u} {P : α → Prop}
    (h : Nonempty (Subtype P)) : P (chooseSub h) :=
  (Classical.choice h).2

private noncomputable def chooseBool (P : Bool → Prop)
    (h : Nonempty (Subtype P)) : Bool :=
  (Classical.choice h).1

private theorem chooseBool_spec (P : Bool → Prop)
    (h : Nonempty (Subtype P)) : P (chooseBool P h) :=
  (Classical.choice h).2

private theorem chooseBool_congr {P Q : Bool → Prop} (hPQ : P = Q)
    (hP : Nonempty (Subtype P)) (hQ : Nonempty (Subtype Q)) :
    chooseBool P hP = chooseBool Q hQ := by
  subst hPQ
  rfl

private theorem bool_eq_or_ne (a b : Bool) : a = b ∨ a ≠ b := by
  cases a with
  | false =>
    cases b with
    | false => exact Or.inl rfl
    | true => exact Or.inr (fun h => by nomatch h)
  | true =>
    cases b with
    | false => exact Or.inr (fun h => by nomatch h)
    | true => exact Or.inl rfl

/-- Diaconescu's theorem (`p ∨ ¬ p`) over `prelude` + `Init.Core` without
`Init.Classical`, replacing banned `by_cases` via `cases prop_em p`. -/
theorem prop_em (p : Prop) : p ∨ ¬ p := by
  let U (x : Bool) : Prop := x = true ∨ p
  let V (x : Bool) : Prop := x = false ∨ p
  have exU : Nonempty (Subtype U) := ⟨⟨true, Or.inl rfl⟩⟩
  have exV : Nonempty (Subtype V) := ⟨⟨false, Or.inl rfl⟩⟩
  have hu : U (chooseBool U exU) := chooseBool_spec U exU
  have hv : V (chooseBool V exV) := chooseBool_spec V exV
  cases bool_eq_or_ne (chooseBool U exU) (chooseBool V exV) with
  | inr hne =>
    refine Or.inr ?_
    intro hp
    have hUV : U = V := by
      funext x
      exact propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩
    exact hne (chooseBool_congr hUV exU exV)
  | inl heq =>
    cases hu with
    | inr hp => exact Or.inl hp
    | inl hut =>
      cases hv with
      | inr hp => exact Or.inl hp
      | inl hvf =>
        rw [hut, hvf] at heq
        nomatch heq

theorem of_not_not {p : Prop} (hnn : ¬ ¬ p) : p := by
  cases prop_em p with
  | inl hp => exact hp
  | inr hnp => exact False.elim (hnn hnp)

theorem by_contra {p : Prop} (h : ¬ p → False) : p :=
  of_not_not h

theorem imp_iff_not_or (p q : Prop) : (p → q) ↔ (¬ p ∨ q) := by
  constructor
  · intro hpq
    cases prop_em p with
    | inl hp => exact Or.inr (hpq hp)
    | inr hnp => exact Or.inl hnp
  · intro h hp
    cases h with
    | inl hnp => exact False.elim (hnp hp)
    | inr hq => exact hq

theorem not_and_iff_or_not (p q : Prop) : ¬ (p ∧ q) ↔ (¬ p ∨ ¬ q) := by
  constructor
  · intro hna
    cases prop_em p with
    | inr hnp => exact Or.inl hnp
    | inl hp =>
      exact Or.inr (fun hq => hna ⟨hp, hq⟩)
  · intro hor hpq
    cases hor with
    | inl hnp => exact hnp hpq.1
    | inr hnq => exact hnq hpq.2

noncomputable def chooseExists {α : Sort u} {P : α → Prop}
    (h : ∃ x : α, P x) : α :=
  chooseSub (by cases h with | intro w hw => exact ⟨⟨w, hw⟩⟩)

theorem chooseExists_spec {α : Sort u} {P : α → Prop}
    (h : ∃ x : α, P x) : P (chooseExists h) :=
  chooseSub_spec (by cases h with | intro w hw => exact ⟨⟨w, hw⟩⟩)

end Workbench.Pass1.ClassicalEm
