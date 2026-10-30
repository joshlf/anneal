-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted

/-!
# Pass Composition, `Partial` Lemmas, and Verification Bridge Theorems

This module proves the foundational algebraic properties that fall out of
`Trusted.Partial` and `Trusted.Language` (`Trusted.Refinement`):

1. **`Partial` lattice and functorial laws (`Partial.map`,
   `Partial.monotone_map`, `ub_top`, `ub_le_iff`, `pure_le_pure_iff`,
   `not_ub_le_pure`):**
   `Partial.map` lifts monotone behavior maps to `Partial`, `Partial.ub`
   (`defined := False`) is the top element of `Partial B`, `Partial.ub ≤ p`
   holds if and only if `¬ p.defined`, and `Partial.pure` embeds `B`
   order-isomorphically into `Partial B`.
2. **Specification and well-formedness characterizations (`le_specOn_iff`,
   `le_wellFormedOn_iff`, `le_wellFormed_iff`, `wellFormed_le_wellFormedOn`,
   `specOn_le_wellFormedOn`, `spec_le_wellFormed`, `pure_le_wellFormed`,
   `not_specOn_le_wellFormed_of_not_pre`):**
   Refining `L.SpecOn pre post` is equivalent to definedness and `post q` on
   `pre q`, every `L.SpecOn pre post` refines `L.WellFormedOn pre`, and any
   `L.SpecOn pre post` whose precondition `pre q` fails at some query `q`
   refutes unconditional `L.WellFormed`.
3. **Transitive pass composition (`pass_trans`, `Compiles.comp`,
   `Abstracts.comp`), cross-pass verification (`Compiler.SoundOn.verify`,
   `verify_through_passes`), and specification weakening
   (`Compiler.Verified.mono`):**
   Because `Partial` internalizes definedness into `≤`, composing compiler
   passes (`Compiles`) and verifier abstractions (`Abstracts`) reduces directly
   to `Preorder.le_trans` and `Monotone`.

Because `trusted/audit/` enforces Statement (`ci.type`) vs. Proof (`ci.value?`)
Origin Separation, these theorems live outside `trusted/` and are invoked only
inside proof terms (`ci.value?`).
-/

namespace Anneal

open Trusted

/-- Identity mapping on any behavior domain is monotone. -/
theorem monotone_id {B : Type u} [Preorder B] : Monotone (fun b : B => b) :=
  fun _ _ h => h

/-- Composition of two monotone mappings is monotone. -/
theorem monotone_comp {A : Type u} {B : Type v} {C : Type w}
    [Preorder A] [Preorder B] [Preorder C]
    {g : B → C} {f : A → B}
    (hg : Monotone g) (hf : Monotone f) :
    Monotone (fun a => g (f a)) :=
  fun _ _ h => hg (hf h)

/-- Lifting a monotone map `f : B₁ → B₂` via `Partial.map` yields a monotone
    map `Partial B₁ → Partial B₂`. -/
theorem Partial.monotone_map {B₁ : Type u} {B₂ : Type v}
    [Preorder B₁] [Preorder B₂]
    {f : B₁ → B₂} (hf : Monotone f) :
    Monotone (Partial.map f) := by
  intro p₁ p₂ hp hdef₂
  cases hp hdef₂ with
  | intro hdef₁ hle =>
    exact ⟨hdef₁, hf hle⟩

/-- `Partial.ub` (`defined := False`) is the top element of `Partial B`: every
    partial value `p : Partial B` refines `Partial.ub`. -/
theorem ub_top {B : Type u} [Preorder B] (p : Partial B) :
    p ≤ Partial.ub :=
  fun h => False.elim h

/-- `Partial.ub` refines a partial value `p : Partial B` if and only if `p` is
    undefined (`¬ p.defined`). -/
theorem ub_le_iff {B : Type u} [Preorder B] (p : Partial B) :
    Partial.ub ≤ p ↔ ¬ p.defined :=
  ⟨fun h hdef => (h hdef).1, fun hnot hdef => False.elim (hnot hdef)⟩

/-- On unconditionally defined values (`Partial.pure`), the `Partial B`
    refinement preorder coincides with the underlying preorder on `B`. -/
theorem pure_le_pure_iff {B : Type u} [Preorder B] (b₁ b₂ : B) :
    Partial.pure b₁ ≤ Partial.pure b₂ ↔ b₁ ≤ b₂ := by
  constructor
  · intro h
    cases h True.intro with
    | intro _ hle => exact hle
  · intro hle _
    exact ⟨True.intro, hle⟩

/-- Undefined behavior (`Partial.ub`) never refines a defined specification
    (`Partial.pure b`). -/
theorem not_ub_le_pure {B : Type u} [Preorder B] (b : B) :
    ¬ ((@Partial.ub B) ≤ Partial.pure b) :=
  fun h => (ub_le_iff (Partial.pure b)).mp h True.intro

/-- Refining `L.SpecOn pre post` is equivalent to being defined and satisfying
    `post q` at every query `q` where `pre q` holds. -/
theorem le_specOn_iff {L : Language} (b : L.Behavior)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    b ≤ L.SpecOn pre post ↔
      ∀ q, pre q → ∃ h : (b q).defined, ∀ out, (b q).val h out → post q out :=
  ⟨fun h => h, fun h => h⟩

/-- Refining `L.WellFormedOn pre` is equivalent to being defined at every query
    `q` satisfying `pre q`. -/
theorem le_wellFormedOn_iff {L : Language} (b : L.Behavior)
    (pre : L.Query → Prop) :
    b ≤ L.WellFormedOn pre ↔ ∀ q, pre q → (b q).defined := by
  constructor
  · intro h q hpre
    exact (h q hpre).1
  · intro h q hpre
    exact ⟨h q hpre, fun _ _ => True.intro⟩

/-- Refining `L.WellFormed` is equivalent to being defined at every query
    `q : L.Query`. -/
theorem le_wellFormed_iff {L : Language} (b : L.Behavior) :
    b ≤ L.WellFormed ↔ ∀ q, (b q).defined := by
  constructor
  · intro h q
    exact (le_wellFormedOn_iff b (fun _ => True)).mp h q True.intro
  · intro h
    exact (le_wellFormedOn_iff b (fun _ => True)).mpr (fun q _ => h q)

/-- Unconditional well-formedness (`L.WellFormed`) refines conditional
    well-formedness (`L.WellFormedOn pre`) for any precondition `pre`. -/
theorem wellFormed_le_wellFormedOn {L : Language} (pre : L.Query → Prop) :
    L.WellFormed ≤ L.WellFormedOn pre :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-- Every conditional specification `L.SpecOn pre post` refines baseline
    conditional well-formedness `L.WellFormedOn pre` on the same precondition
    `pre`. -/
theorem specOn_le_wellFormedOn {L : Language}
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.SpecOn pre post ≤ L.WellFormedOn pre :=
  fun _ hpre => ⟨hpre, fun _ _ => True.intro⟩

/-- Every unconditional specification `L.Spec post` refines `L.WellFormed`. -/
theorem spec_le_wellFormed {L : Language} (post : L.Query → L.Out → Prop) :
    L.Spec post ≤ L.WellFormed :=
  specOn_le_wellFormedOn (fun _ => True) post

/-- Any specification built from `Partial.pure` at every query (`L.Spec post`)
    refines `L.WellFormed`. -/
theorem pure_le_wellFormed {L : Language} (post : L.Query → L.Out → Prop) :
    (fun q => Partial.pure (post q)) ≤ L.WellFormed :=
  spec_le_wellFormed post

/-- If `pre q` fails at any query `q`, `L.SpecOn pre post` does not refine
    unconditional `L.WellFormed`: placing a functional precondition in
    `.defined` (`pre`) weakens definedness outside `pre` and is rejected as a
    standalone safe-function specification. -/
theorem not_specOn_le_wellFormed_of_not_pre {L : Language}
    {pre : L.Query → Prop} {post : L.Query → L.Out → Prop}
    {q : L.Query} (hnot : ¬ pre q) :
    ¬ (L.SpecOn pre post ≤ L.WellFormed) :=
  fun hwf => hnot ((le_wellFormed_iff (L.SpecOn pre post)).mp hwf q)

/-- Transitive composition of two pass refinements (`Compiles` or `Abstracts`).

    Because `Partial` internalizes definedness into the refinement preorder
    `≤`, composing `b₃ ≤ π₁ b₂` and `b₂ ≤ π₂ b₁` under a monotone mapping `π₁`
    requires only `Preorder.le_trans` and `Monotone`. -/
theorem pass_trans
    {B₁ : Type u} {B₂ : Type v} {B₃ : Type w}
    [Preorder B₁] [Preorder B₂] [Preorder B₃]
    {π₂ : B₁ → B₂} {π₁ : B₂ → B₃}
    (h_mono₁ : Monotone π₁)
    {b₁ : B₁} {b₂ : B₂} {b₃ : B₃}
    (h₂₃ : b₃ ≤ π₁ b₂)
    (h₁₂ : b₂ ≤ π₂ b₁) :
    b₃ ≤ π₁ (π₂ b₁) :=
  Preorder.le_trans h₂₃ (h_mono₁ h₁₂)

/-- Pipeline-ordered composition of two compilation passes: if `p₁` compiles to
    `p₂` under `π₁` (`Compiles L₁ L₂ π₁ p₁ p₂`), `p₂` compiles to `p₃` under
    `π₂` (`Compiles L₂ L₃ π₂ p₂ p₃`), and `π₂` is monotone, then `p₁` compiles
    to `p₃` under `fun b => π₂ (π₁ b)`. -/
theorem Compiles.comp
    {L₁ L₂ L₃ : Language}
    {π₁ : L₁.Behavior → L₂.Behavior} {π₂ : L₂.Behavior → L₃.Behavior}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : Compiles L₁ L₂ π₁ p₁ p₂)
    (h₂₃ : Compiles L₂ L₃ π₂ p₂ p₃)
    (h_mono₂ : Monotone π₂) :
    Compiles L₁ L₃ (fun b => π₂ (π₁ b)) p₁ p₃ :=
  pass_trans h_mono₂ h₂₃ h₁₂

/-- Pipeline-ordered composition of two verification abstraction passes: if `s`
    is abstracted by `v₁` under `π₁` (`Abstracts L₁ L_src π₁ v₁ s`), `v₁` is
    abstracted by `v₂` under `π₂` (`Abstracts L₂ L₁ π₂ v₂ v₁`), and `π₁` is
    monotone, then `s` is abstracted by `v₂` under `fun b => π₁ (π₂ b)`. -/
theorem Abstracts.comp
    {L₂ L₁ L_src : Language}
    {π₂ : L₂.Behavior → L₁.Behavior} {π₁ : L₁.Behavior → L_src.Behavior}
    {v₂ : L₂.Prog} {v₁ : L₁.Prog} {s : L_src.Prog}
    (h₁ : Abstracts L₁ L_src π₁ v₁ s)
    (h₂ : Abstracts L₂ L₁ π₂ v₂ v₁)
    (h_mono₁ : Monotone π₁) :
    Abstracts L₂ L_src (fun b => π₁ (π₂ b)) v₂ s :=
  pass_trans h_mono₁ h₁ h₂

/-- Discharge `C.Verified s spec` directly from compiler soundness on `s`
    (`C.SoundOn s`) and a source-level refinement proof (`L_src.sem s ≤
    spec`). -/
theorem Compiler.SoundOn.verify
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_comp : C.SoundOn s)
    (h_src : L_src.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨h_src, h_comp.2, Preorder.le_trans h_comp.2 (h_comp.1 h_src)⟩

/-- Cross-pass verification bridge theorem: discharges `C.Verified s (π_v spec)`
    from:
    1. A proof on the verifier's model (`L_v.sem v ≤ spec`),
    2. An `Abstracts` pass relating `v` and `s` under `π_v`
       (`L_src.sem s ≤ π_v (L_v.sem v)`),
    3. Monotonicity of the verifier behavior mapping (`Monotone π_v`), and
    4. Compiler soundness on `s` (`C.SoundOn s`). -/
theorem verify_through_passes
    {L_v L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {π_v : L_v.Behavior → L_src.Behavior} {spec : L_v.Behavior}
    {v : L_v.Prog} {s : L_src.Prog}
    (h_proof : L_v.sem v ≤ spec)
    (h_abs : Abstracts L_v L_src π_v v s)
    (h_mono_v : Monotone π_v)
    (h_comp : C.SoundOn s) :
    C.Verified s (π_v spec) :=
  Compiler.SoundOn.verify h_comp (Preorder.le_trans h_abs (h_mono_v h_proof))

/-- Monotonicity of `Compiler.Verified` in the specification argument: if `s`
    satisfies `C.Verified s spec₁`, `spec₁ ≤ spec₂`, and `C.π` is monotone, then
    `s` also satisfies `C.Verified s spec₂`.

    In particular, proving `C.Verified s spec` for any specification `spec` that
    refines `L_src.WellFormedOn pre` immediately yields the baseline safety
    obligation `C.Verified s (L_src.WellFormedOn pre)`. -/
theorem Compiler.Verified.mono
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec₁ spec₂ : L_src.Behavior}
    (h_ver : C.Verified s spec₁)
    (h_le : spec₁ ≤ spec₂)
    (h_mono : Monotone C.π) :
    C.Verified s spec₂ :=
  ⟨Preorder.le_trans h_ver.1 h_le,
   h_ver.2.1,
   Preorder.le_trans h_ver.2.2 (h_mono h_le)⟩

end Anneal
