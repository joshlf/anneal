-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Core
import Trusted.Refinement

/-!
# Core Meta-Theorems and Compositional Lifts (`Anneal.Refinement`)

Proves the foundational zero-axiom meta-theorems over `Trusted.Refinement`:
1. `BehaviorCodec` identity, composition, monotonicity, and observable spine
   preservation (`obs_encodeOut_of_decodeOut`, resolving `TENSION-1`),
2. Reflexivity and transitive composition of `Compiles`, `ProductiveCompiles`,
   and `Abstracts`, direct observable spine transfer
   (`compiles_transfers_spineSpecOn_directly`), and the two-sided proof-gated
   compilation and abstraction sandwich theorems
   (`verified_through_abstraction_and_compilation`,
   `verifiedOn_through_abstraction_and_compilation`),
3. Backward reflection of `ProductiveOn` along a `BehaviorCodec`
   (`productiveOn_of_compiles`) and the Free Determinism Corollary
   (`verifiedOn_deterministic_singleton`),
4. Relational 2-safety / $k$-safety product lifting (`Language.prod`,
   `BehaviorCodec.prod`, `Compiles.prod`), and
5. Positive per-obligation waiver isolation
   (`waived_obligation_isolates_sibling`,
   `strictUnitTheorem_rejects_duplicate_ids`, and
   `strictUnitTheorem_rejects_drifted_artifact`, resolving `TENSION-4`).
-/

namespace Anneal

open Trusted

/-!
## 1. `SpecOn`, `WellFormedOn`, and `WellFormed` Lattice Lemmas
-/

/-- Refining `L.SpecOn pre post` is equivalent to being defined on `pre` and
    satisfying `post q` on every outcome in `(b q).val`. -/
theorem le_specOn_iff {SemObs : Type} {L : Language SemObs} (b : L.Behavior)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    b ≤ L.SpecOn pre post ↔
      ∀ q, pre q → ∃ h : (b q).defined, ∀ o, (b q).val h o → post q o := by
  constructor
  · intro hle q hpre
    exact hle q hpre
  · intro h q hpre
    exact h q hpre

/-- Refining `L.WellFormedOn pre` is equivalent to `(b q).defined` holding at
    every query `q` satisfying `pre q`. -/
theorem le_wellFormedOn_iff {SemObs : Type} {L : Language SemObs}
    (b : L.Behavior) (pre : L.Query → Prop) :
    b ≤ L.WellFormedOn pre ↔ ∀ q, pre q → (b q).defined := by
  constructor
  · intro h q hpre
    exact (h q hpre).1
  · intro h q hpre
    exact ⟨h q hpre, fun _ _ => True.intro⟩

/-- Refining `L.WellFormed` is equivalent to `(b q).defined` holding at every
    query `q`. -/
theorem le_wellFormed_iff {SemObs : Type} {L : Language SemObs}
    (b : L.Behavior) :
    b ≤ L.WellFormed ↔ ∀ q, (b q).defined := by
  constructor
  · intro h q
    exact (h q True.intro).1
  · intro h q _
    exact ⟨h q, fun _ _ => True.intro⟩

/-- Every conditional specification `L.SpecOn pre post` refines conditional
    well-formedness `L.WellFormedOn pre` on the same precondition `pre`. -/
theorem specOn_le_wellFormedOn {SemObs : Type} {L : Language SemObs}
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.SpecOn pre post ≤ L.WellFormedOn pre :=
  fun _ hpre => ⟨hpre, fun _ _ => True.intro⟩

/-- Every unconditional specification `L.Spec post` refines `L.WellFormed`. -/
theorem spec_le_wellFormed {SemObs : Type} {L : Language SemObs}
    (post : L.Query → L.Out → Prop) :
    L.Spec post ≤ L.WellFormed :=
  specOn_le_wellFormedOn (fun _ => True) post

/-- Contravariance of `SpecOn` in its precondition `pre`: strengthening the
    precondition (`∀ q, pre₂ q → pre₁ q`) weakens the specification
    (`L.SpecOn pre₁ post ≤ L.SpecOn pre₂ post`). -/
theorem specOn_mono_pre {SemObs : Type} {L : Language SemObs}
    {pre₁ pre₂ : L.Query → Prop} (post : L.Query → L.Out → Prop)
    (himp : ∀ q, pre₂ q → pre₁ q) :
    L.SpecOn pre₁ post ≤ L.SpecOn pre₂ post :=
  fun q hpre₂ => ⟨himp q hpre₂, fun _ h => h⟩

/-- Unconditional `L.WellFormed` refines `L.WellFormedOn pre` for any
    precondition `pre`. -/
theorem wellFormed_le_wellFormedOn {SemObs : Type} {L : Language SemObs}
    (pre : L.Query → Prop) :
    L.WellFormed ≤ L.WellFormedOn pre :=
  specOn_mono_pre (fun _ _ => True) (fun _ _ => True.intro)

/-!
## 1b. `BehaviorCodec` Algebra and `TENSION-1` Spine Theorems
-/

/-- Identity `BehaviorCodec` on any language `L`. -/
def BehaviorCodec.id {SemObs : Type} (L : Language SemObs) :
    BehaviorCodec L L where
  encodeQuery q := q
  decodeQuery q := q
  encodeOut o   := o
  decodeOut o   := some o
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := by cases h; rfl

/-- Sequential composition of `BehaviorCodec L₁ L₂` and
    `BehaviorCodec L₂ L₃`. -/
def BehaviorCodec.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    (c₁ : BehaviorCodec L₁ L₂) (c₂ : BehaviorCodec L₂ L₃) :
    BehaviorCodec L₁ L₃ where
  encodeQuery q₁ := c₂.encodeQuery (c₁.encodeQuery q₁)
  decodeQuery q₃ := c₁.decodeQuery (c₂.decodeQuery q₃)
  encodeOut o₁   := c₂.encodeOut (c₁.encodeOut o₁)
  decodeOut o₃   :=
    match c₂.decodeOut o₃ with
    | some o₂ => c₁.decodeOut o₂
    | none    => none
  decodeQuery_encodeQuery q₁ := by
    rw [c₂.decodeQuery_encodeQuery, c₁.decodeQuery_encodeQuery]
  decodeOut_encodeOut o₁ := by
    rw [c₂.decodeOut_encodeOut]
    exact c₁.decodeOut_encodeOut o₁
  obs_decodeOut o₃ o₁ h := by
    cases h₂ : c₂.decodeOut o₃ with
    | none =>
      rw [h₂] at h
      cases h
    | some o₂ =>
      rw [h₂] at h
      exact Eq.trans (c₂.obs_decodeOut o₃ o₂ h₂) (c₁.obs_decodeOut o₂ o₁ h)

/-- Every `BehaviorCodec.toMorphism` is automatically `Monotone`. -/
theorem BehaviorCodec.toMorphism_monotone {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂) :
    Monotone c.toMorphism := by
  intro b₁ b₂ hle q₂ hdef₂
  cases hle (c.decodeQuery q₂) hdef₂ with
  | intro hdef₁ hval =>
    refine ⟨hdef₁, ?_⟩
    intro o₂ ⟨o₁, hdec, ho₁⟩
    exact ⟨o₁, hdec, hval o₁ ho₁⟩

/-- Fundamental `TENSION-1` theorem: every target outcome `o₂` that decodes to
    `some o₁` has the exact same observable spine in `L₂` as the canonical
    encoding `c.encodeOut o₁` (`L₂.obs o₂ = L₂.obs (c.encodeOut o₁)`), while
    allowing `o₂` and `c.encodeOut o₁` to differ on non-observable concrete
    slack (caller-saved scratch registers, dead flags, uninitialized padding
    bytes, or redundant limbs). -/
theorem BehaviorCodec.obs_encodeOut_of_decodeOut {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂)
    {o₂ : L₂.Out} {o₁ : L₁.Out} (h : c.decodeOut o₂ = some o₁) :
    L₂.obs o₂ = L₂.obs (c.encodeOut o₁) := by
  have h₁ := c.obs_decodeOut o₂ o₁ h
  have h₂ := c.obs_decodeOut (c.encodeOut o₁) o₁ (c.decodeOut_encodeOut o₁)
  exact Eq.trans h₁ (Eq.symm h₂)

/-- When `L₂` has no unobserved slack (`Language.mkSimple`, where
    `L₂.obs = id`), `obs_encodeOut_of_decodeOut` specializes definitionally to
    strict partial bijection `o₂ = c.encodeOut o₁`. -/
theorem BehaviorCodec.encodeOut_of_decodeOut_of_obs_id {Out : Type}
    {L₁ : Language Out} {Prog₂ Query₂ : Type}
    {sem₂ : Prog₂ → Behavior Query₂ Out}
    (c : BehaviorCodec L₁ (Language.mkSimple Prog₂ Query₂ Out sem₂))
    {o₂ : Out} {o₁ : L₁.Out} (h : c.decodeOut o₂ = some o₁) :
    o₂ = c.encodeOut o₁ :=
  BehaviorCodec.obs_encodeOut_of_decodeOut c h

/-- Canary theorem (`TENSION-1`): the rogue-offset codec
    (`decodeOut 0 = some 42`) is algebraically impossible on any simple `Nat`
    language sharing the observable value spine. -/
theorem rogue_offset_codec_impossible
    {Prog₁ Query₁ Prog₂ Query₂ : Type}
    {sem₁ : Prog₁ → Behavior Query₁ Nat}
    {sem₂ : Prog₂ → Behavior Query₂ Nat}
    (c : BehaviorCodec
      (Language.mkSimple Prog₁ Query₁ Nat sem₁)
      (Language.mkSimple Prog₂ Query₂ Nat sem₂))
    (h_dec : c.decodeOut 0 = some 42) :
    False := by
  have h_obs : (0 : Nat) = 42 := c.obs_decodeOut 0 42 h_dec
  cases h_obs

/-- Canary theorem (`TENSION-1`): a bijective value-permutation codec
    (`decodeOut 0 = some 1`) is also algebraically impossible when the
    observable value spine is preserved. -/
theorem rogue_permutation_codec_impossible
    {Prog₁ Query₁ Prog₂ Query₂ : Type}
    {sem₁ : Prog₁ → Behavior Query₁ Nat}
    {sem₂ : Prog₂ → Behavior Query₂ Nat}
    (c : BehaviorCodec
      (Language.mkSimple Prog₁ Query₁ Nat sem₁)
      (Language.mkSimple Prog₂ Query₂ Nat sem₂))
    (h_dec : c.decodeOut 0 = some 1) :
    False := by
  have h_obs : (0 : Nat) = 1 := c.obs_decodeOut 0 1 h_dec
  cases h_obs

/-!
## 2. Transitive Compilation, Abstraction, and Productivity Reflection
-/

/-- Reflexivity of `Compiles` under `BehaviorCodec.id L`. -/
theorem Compiles.refl {SemObs : Type} (L : Language SemObs) (p : L.Prog) :
    Compiles L L (BehaviorCodec.id L) p p := by
  intro q hdef
  refine ⟨hdef, ?_⟩
  intro o ho
  exact ⟨o, rfl, ho⟩

/-- Reflexivity of `Abstracts` under `BehaviorCodec.id L`. -/
theorem Abstracts.refl {SemObs : Type} (L : Language SemObs) (p : L.Prog) :
    Abstracts L L (BehaviorCodec.id L) p p :=
  Compiles.refl L p

/-- Transitive composition of downward/horizontal `Compiles` passes. -/
theorem Compiles.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    {c₁ : BehaviorCodec L₁ L₂} {c₂ : BehaviorCodec L₂ L₃}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : Compiles L₁ L₂ c₁ p₁ p₂)
    (h₂₃ : Compiles L₂ L₃ c₂ p₂ p₃) :
    Compiles L₁ L₃ (BehaviorCodec.comp c₁ c₂) p₁ p₃ := by
  intro q₃ hdef₁
  cases h₁₂ (c₂.decodeQuery q₃) hdef₁ with
  | intro hdef₂ hval₂ =>
    cases h₂₃ q₃ hdef₂ with
    | intro hdef₃ hval₃ =>
      refine ⟨hdef₃, ?_⟩
      intro o₃ ho₃
      cases hval₃ o₃ ho₃ with
      | intro o₂ h₂ =>
        cases h₂ with
        | intro hdec₂ ho₂ =>
          cases hval₂ o₂ ho₂ with
          | intro o₁ h₁ =>
            cases h₁ with
            | intro hdec₁ ho₁ =>
              refine ⟨o₁, ?_, ho₁⟩
              dsimp [BehaviorCodec.comp]
              rw [hdec₂]
              exact hdec₁

/-- Transitive composition of miracle-free `ProductiveCompiles` passes. -/
theorem ProductiveCompiles.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    {c₁ : BehaviorCodec L₁ L₂} {c₂ : BehaviorCodec L₂ L₃}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : ProductiveCompiles L₁ L₂ c₁ p₁ p₂)
    (h₂₃ : ProductiveCompiles L₂ L₃ c₂ p₂ p₃) :
    ProductiveCompiles L₁ L₃ (BehaviorCodec.comp c₁ c₂) p₁ p₃ :=
  ⟨Compiles.comp h₁₂.1 h₂₃.1,
   fun q₁ hex₁ => h₂₃.2 (c₁.encodeQuery q₁) (h₁₂.2 q₁ hex₁)⟩

/-- Direct spine specification transfer (`EXPLOIT-2` defense): `Compiles`
    transfers a spine-anchored specification `L₁.SpineSpecOn pre obsPost`
    directly to `L₂.SpineSpecOn` on `L₂.obs o₂`, eliminating `c.decodeOut` from
    the target theorem statement. -/
theorem compiles_transfers_spineSpecOn_directly {SemObs : Type}
    {L₁ L₂ : Language SemObs}
    {c : BehaviorCodec L₁ L₂}
    {s : L₁.Prog} {t : L₂.Prog}
    {pre : L₁.Query → Prop} {obsPost : L₁.Query → SemObs → Prop}
    (h_spec : L₁.sem s ≤ L₁.SpineSpecOn pre obsPost)
    (h_comp : Compiles L₁ L₂ c s t) :
    L₂.sem t ≤
      L₂.SpineSpecOn
        (fun q₂ => pre (c.decodeQuery q₂))
        (fun q₂ obsVal => obsPost (c.decodeQuery q₂) obsVal) := by
  intro q₂ hpre₂
  cases h_spec (c.decodeQuery q₂) hpre₂ with
  | intro hdef₁ hpost₁ =>
    cases h_comp q₂ hdef₁ with
    | intro hdef₂ hle₂ =>
      refine ⟨hdef₂, ?_⟩
      intro o₂ ho₂
      cases hle₂ o₂ ho₂ with
      | intro o₁ h₁ =>
        cases h₁ with
        | intro hdec ho₁ =>
          have h_obs_eq : L₂.obs o₂ = L₁.obs o₁ :=
            c.obs_decodeOut o₂ o₁ hdec
          have h_src_obs : obsPost (c.decodeQuery q₂) (L₁.obs o₁) :=
            hpost₁ o₁ ho₁
          dsimp [Language.SpineSpecOn, Language.SpecOn]
          rw [h_obs_eq]
          exact h_src_obs

/-- Two-sided sandwich theorem (`INV-1.6`): composing upward abstraction
    `Abstracts L_v L_src c_v v s`, abstract specification `L_v.sem v ≤ spec`,
    and downward compilation `Compiles L_src L_tgt c_c s t` yields target
    refinement `L_tgt.sem t ≤ (c_v.comp c_c).toMorphism spec` with the
    intermediate language `L_src` canceled out. -/
theorem verified_through_abstraction_and_compilation {SemObs : Type}
    {L_v L_src L_tgt : Language SemObs}
    {c_v : BehaviorCodec L_v L_src} {c_c : BehaviorCodec L_src L_tgt}
    {v : L_v.Prog} {s : L_src.Prog} {t : L_tgt.Prog}
    {spec : L_v.Behavior}
    (h_abs  : Abstracts L_v L_src c_v v s)
    (h_spec : L_v.sem v ≤ spec)
    (h_comp : Compiles L_src L_tgt c_c s t) :
    L_tgt.sem t ≤ (BehaviorCodec.comp c_v c_c).toMorphism spec := by
  have h_src_spec : L_src.sem s ≤ c_v.toMorphism spec :=
    Preorder.le_trans h_abs (BehaviorCodec.toMorphism_monotone c_v h_spec)
  have h_tgt_step : L_tgt.sem t ≤ c_c.toMorphism (c_v.toMorphism spec) :=
    Preorder.le_trans h_comp (BehaviorCodec.toMorphism_monotone c_c h_src_spec)
  intro q₃ hdef
  cases h_tgt_step q₃ hdef with
  | intro hdef₃ hval₃ =>
    refine ⟨hdef₃, ?_⟩
    intro o₃ ho₃
    cases hval₃ o₃ ho₃ with
    | intro o₂ h₂ =>
      cases h₂ with
      | intro hdec₂ hmid =>
        cases hmid with
        | intro o₁ h₁ =>
          cases h₁ with
          | intro hdec₁ ho₁ =>
            refine ⟨o₁, ?_, ho₁⟩
            dsimp [BehaviorCodec.comp]
            rw [hdec₂]
            exact hdec₁

/-- Backward productivity reflection along a `BehaviorCodec`: if `s` is defined
    on `pre`, `t` compiles `s` under `c`, and `t` is productive on
    `pre ∘ c.decodeQuery`, then `s` is automatically productive on `pre`. -/
theorem productiveOn_of_compiles {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) {s : L₁.Prog} {t : L₂.Prog}
    {pre : L₁.Query → Prop}
    (h_def      : ∀ q₁, pre q₁ → (L₁.sem s q₁).defined)
    (h_comp     : Compiles L₁ L₂ c s t)
    (h_prod_tgt : L₂.ProductiveOn (fun q₂ => pre (c.decodeQuery q₂)) t) :
    L₁.ProductiveOn pre s := by
  intro q₁ hpre₁
  have hdec_q : c.decodeQuery (c.encodeQuery q₁) = q₁ :=
    c.decodeQuery_encodeQuery q₁
  have hpre₂ : pre (c.decodeQuery (c.encodeQuery q₁)) :=
    Eq.mpr (congrArg pre hdec_q) hpre₁
  have hdef_map : (L₁.sem s (c.decodeQuery (c.encodeQuery q₁))).defined :=
    h_def (c.decodeQuery (c.encodeQuery q₁)) hpre₂
  cases h_prod_tgt (c.encodeQuery q₁) hpre₂ with
  | intro hdef₂ hout₂ =>
    cases hout₂ with
    | intro o₂ ho₂ =>
      cases h_comp (c.encodeQuery q₁) hdef_map with
      | intro _ hle =>
        cases hle o₂ ho₂ with
        | intro o₁ h₁ =>
          cases h₁ with
          | intro _ ho₁ =>
            have hex :
                ∃ h : (L₁.sem s (c.decodeQuery (c.encodeQuery q₁))).defined,
                  ∃ o, (L₁.sem s (c.decodeQuery (c.encodeQuery q₁))).val h o :=
              ⟨hdef_map, o₁, ho₁⟩
            exact Eq.mp
              (congrArg
                (fun q => ∃ h : (L₁.sem s q).defined, ∃ o, (L₁.sem s q).val h o)
                hdec_q)
              hex

/-- Complete two-sided sandwich verification theorem (`GAP-1` & `GAP-3`): pairs
    `verified_through_abstraction_and_compilation` with target `ProductiveOn`
    and reflects productivity back to `L_src`. -/
theorem verifiedOn_through_abstraction_and_compilation {SemObs : Type}
    {L_v L_src L_tgt : Language SemObs}
    {c_v : BehaviorCodec L_v L_src} {c_c : BehaviorCodec L_src L_tgt}
    {v : L_v.Prog} {s : L_src.Prog} {t : L_tgt.Prog}
    {pre : L_v.Query → Prop} {post : L_v.Query → L_v.Out → Prop}
    (h_abs      : Abstracts L_v L_src c_v v s)
    (h_spec     : L_v.sem v ≤ L_v.SpecOn pre post)
    (h_comp     : Compiles L_src L_tgt c_c s t)
    (h_prod_tgt : L_tgt.ProductiveOn
      (fun q₃ => pre ((BehaviorCodec.comp c_v c_c).decodeQuery q₃)) t) :
    L_src.ProductiveOn (fun q₂ => pre (c_v.decodeQuery q₂)) s ∧
    L_tgt.sem t ≤
      (BehaviorCodec.comp c_v c_c).toMorphism (L_v.SpecOn pre post) := by
  have h_def_src :
      ∀ q₂, pre (c_v.decodeQuery q₂) → (L_src.sem s q₂).defined := by
    intro q₂ hpre₂
    cases h_spec (c_v.decodeQuery q₂) hpre₂ with
    | intro hdef_v _ =>
      cases h_abs q₂ hdef_v with
      | intro hdef_s _ => exact hdef_s
  exact ⟨productiveOn_of_compiles c_c h_def_src h_comp h_prod_tgt,
    verified_through_abstraction_and_compilation h_abs h_spec h_comp⟩

/-- Free Determinism Corollary (`INV-1.3`): when `prog` satisfies `VerifiedOn`
    against a singleton postcondition `fun q o => o = target q`, `prog` is
    defined, non-empty, and uniquely equals `target q` at every query in
    `pre`. -/
theorem verifiedOn_deterministic_singleton {SemObs : Type}
    {L : Language SemObs} {dom pre : L.Query → Prop}
    {target : L.Query → L.Out} {prog : L.Prog}
    (h : L.VerifiedOn dom pre (fun q o => o = target q) prog)
    {q : L.Query} (hpre : pre q) :
    ∃ hdef : (L.sem prog q).defined,
      (L.sem prog q).val hdef (target q) ∧
      ∀ o, (L.sem prog q).val hdef o → o = target q := by
  cases h.2.1 q hpre with
  | intro hdef hout =>
    cases hout with
    | intro w hw =>
      cases h.2.2 q hpre with
      | intro _ hpost =>
        have hw_eq : w = target q := hpost w hw
        rw [hw_eq] at hw
        exact ⟨hdef, hw, hpost⟩

/-!
## 3. Relational 2-Safety Product Lift (`Language.prod`, `BehaviorCodec.prod`)
-/

/-- Product of two languages `L₁` and `L₂` for relational 2-safety verification
    (constant-time equivalence, non-interference, determinism, or monotonicity).
    Imposes zero tax on 1-safety tools because `Language.prod` is itself an
    ordinary `Trusted.Language`. -/
abbrev Language.prod {Obs₁ Obs₂ : Type}
    (L₁ : Language Obs₁) (L₂ : Language Obs₂) :
    Language (Obs₁ × Obs₂) where
  Prog  := L₁.Prog × L₂.Prog
  Query := L₁.Query × L₂.Query
  Out   := L₁.Out × L₂.Out
  obs o := (L₁.obs o.1, L₂.obs o.2)
  sem p q := {
    defined := (L₁.sem p.1 q.1).defined ∧ (L₂.sem p.2 q.2).defined
    val     := fun h o =>
      (L₁.sem p.1 q.1).val h.1 o.1 ∧ (L₂.sem p.2 q.2).val h.2 o.2
  }

/-- Product of two `BehaviorCodec`s. -/
def BehaviorCodec.prod {Obs₁ Obs₂ : Type}
    {L₁ L₁' : Language Obs₁} {L₂ L₂' : Language Obs₂}
    (c₁ : BehaviorCodec L₁ L₁') (c₂ : BehaviorCodec L₂ L₂') :
    BehaviorCodec (Language.prod L₁ L₂) (Language.prod L₁' L₂') where
  encodeQuery q := (c₁.encodeQuery q.1, c₂.encodeQuery q.2)
  decodeQuery q := (c₁.decodeQuery q.1, c₂.decodeQuery q.2)
  encodeOut o   := (c₁.encodeOut o.1, c₂.encodeOut o.2)
  decodeOut o   :=
    match c₁.decodeOut o.1, c₂.decodeOut o.2 with
    | some o₁, some o₂ => some (o₁, o₂)
    | _, _             => none
  decodeQuery_encodeQuery q := by
    cases q
    dsimp
    rw [c₁.decodeQuery_encodeQuery, c₂.decodeQuery_encodeQuery]
  decodeOut_encodeOut o := by
    cases o
    dsimp
    rw [c₁.decodeOut_encodeOut, c₂.decodeOut_encodeOut]
  obs_decodeOut o' o h := by
    cases o'; cases o
    dsimp [Language.prod] at h ⊢
    cases h₁ : c₁.decodeOut _ with
    | none => rw [h₁] at h; cases h
    | some v₁ =>
      rw [h₁] at h
      cases h₂ : c₂.decodeOut _ with
      | none => rw [h₂] at h; cases h
      | some v₂ =>
        rw [h₂] at h
        injection h with hv
        injection hv with eq₁ eq₂
        subst eq₁; subst eq₂
        rw [c₁.obs_decodeOut _ _ h₁, c₂.obs_decodeOut _ _ h₂]

/-- Two 1-safety `Compiles` proofs automatically lift to the relational product
    language `Language.prod`. -/
theorem Compiles.prod {Obs₁ Obs₂ : Type}
    {L₁ L₁' : Language Obs₁} {L₂ L₂' : Language Obs₂}
    {c₁ : BehaviorCodec L₁ L₁'} {c₂ : BehaviorCodec L₂ L₂'}
    {p₁ : L₁.Prog} {p₁' : L₁'.Prog}
    {p₂ : L₂.Prog} {p₂' : L₂'.Prog}
    (h₁ : Compiles L₁ L₁' c₁ p₁ p₁')
    (h₂ : Compiles L₂ L₂' c₂ p₂ p₂') :
    Compiles (Language.prod L₁ L₂) (Language.prod L₁' L₂')
      (BehaviorCodec.prod c₁ c₂) (p₁, p₂) (p₁', p₂') := by
  intro q' hdef
  cases h₁ q'.1 hdef.1 with
  | intro hdef₁' hval₁' =>
    cases h₂ q'.2 hdef.2 with
    | intro hdef₂' hval₂' =>
      refine ⟨⟨hdef₁', hdef₂'⟩, ?_⟩
      intro o' ho'
      cases hval₁' o'.1 ho'.1 with
      | intro o₁ h₁ =>
        cases h₁ with
        | intro hdec₁ hv₁ =>
          cases hval₂' o'.2 ho'.2 with
          | intro o₂ h₂ =>
            cases h₂ with
            | intro hdec₂ hv₂ =>
              refine ⟨(o₁, o₂), ?_, ⟨hv₁, hv₂⟩⟩
              dsimp [BehaviorCodec.prod]
              rw [hdec₁, hdec₂]

/-!
## 4. Non-Exploding Waiver Isolation, In-Kernel `StrictUnitTheorem`
   Completeness, Domain-Intrinsic `Language.Verified`, and Paired Canary
   Squeeze (`TENSION-4`)
-/

/-- Resolution of `TENSION-4` (`INV-1.9`): waiving a broken work-in-progress
    obligation `ob_wip` (`id := "fn_wip"`, even with `ob_wip.prop = False`) in
    `VerificationUnit` has zero logical impact on any unwaived sibling
    obligation `ob_crit` (`id = "fn_critical"`). -/
theorem waived_obligation_isolates_sibling
    (policy : TrustPolicy String)
    (ob_wip ob_crit : Obligation String)
    (h_crit_id : ob_crit.id = "fn_critical")
    (h_unit : UnitTheorem {
      policy      := policy
      waived      := ["fn_wip"]
      obligations := [ob_wip, ob_crit]
    }) :
    ob_crit.prop := by
  have h_ob2 : ob_crit.id ∈ ["fn_wip"] ∨ ob_crit.prop := h_unit.2.2.2.1
  rw [h_crit_id] at h_ob2
  cases h_ob2 with
  | inl h_in =>
    exact False.elim ((by decide : "fn_critical" ∉ ["fn_wip"]) h_in)
  | inr h_prop =>
    exact h_prop

/-- `StrictUnitTheorem` rejects duplicate obligation IDs
    (`EXPLOIT-6` defense). -/
theorem strictUnitTheorem_rejects_duplicate_ids
    (policy : TrustPolicy String) (waived : List String)
    (ob₁ ob₂ : Obligation String)
    (h_id₁ : ob₁.id = "dup_id") (h_id₂ : ob₂.id = "dup_id") :
    ¬ StrictUnitTheorem {
      policy      := policy
      waived      := waived
      obligations := [ob₁, ob₂]
    } := by
  intro h_strict
  have h_neq : ob₁.id ≠ ob₂.id := h_strict.2.2.1.1.1
  rw [h_id₁, h_id₂] at h_neq
  exact h_neq rfl

/-- `StrictUnitTheorem` rejects any `EmittedArtifact` whose `contents` and
    `expected` strings diverge (`probe_d1` / `EXPLOIT-6` defense). -/
theorem strictUnitTheorem_rejects_drifted_artifact
    (ob : Obligation String) :
    ¬ StrictUnitTheorem {
      policy      := TrustPolicy.strict
      waived      := []
      obligations := [ob]
      artifacts   := [{ path := "out.s", contents := "ret", expected := "ud2" }]
    } := by
  intro h_strict
  have h_eq : "ret" = "ud2" := h_strict.2.2.2.1
  exact (by decide : "ret" ≠ "ud2") h_eq

/-- `StrictUnitTheorem` rejects any verification unit with a non-empty `waived`
    list (`u.waived ≠ []`), regardless of `u.policy` (eliminating external
    `trusted/audit` Check 5 on `StrictUnitTheorem`). -/
theorem strictUnitTheorem_rejects_nonempty_waivers {Id : Type}
    (u : VerificationUnit Id) (h_waived : u.waived ≠ []) :
    ¬ StrictUnitTheorem u :=
  fun ⟨_, h_nil, _, _⟩ => h_waived h_nil

/-- Even if `u.policy` permits all waivers (`⟨fun _ => True⟩`),
    `StrictUnitTheorem` rejects any unit with a non-empty `waived` list. -/
theorem strictUnitTheorem_rejects_permissive_policy_with_waiver {Id : Type}
    (obs : List (Obligation Id)) (w : Id) (ws : List Id)
    (arts : List EmittedArtifact) :
    ¬ StrictUnitTheorem {
        policy      := ⟨fun _ => True⟩
        waived      := w :: ws
        obligations := obs
        artifacts   := arts
      } := by
  intro ⟨_, h_nil, _, _⟩
  cases h_nil

/-- Helper lemma: when `waived = []`, `AllHold` over the per-obligation
    disjunction `ob.id ∈ [] ∨ ob.prop` forces every obligation proposition
    `ob.prop` in `obs` to hold constructively. -/
theorem allHold_obligations_of_waived_nil {Id : Type}
    (obs : List (Obligation Id))
    (h : AllHold (obs.map (fun ob => ob.id ∈ ([] : List Id) ∨ ob.prop))) :
    AllHold (obs.map Obligation.prop) := by
  induction obs with
  | nil => exact trivial
  | cons ob rest ih =>
    refine ⟨?_, ih h.2⟩
    cases h.1 with
    | inl h_in   => nomatch h_in
    | inr h_prop => exact h_prop

/-- Under `StrictUnitTheorem u`, every obligation in `u.obligations` holds
    constructively (`AllHold (u.obligations.map Obligation.prop)`) regardless of
    `u.policy`. -/
theorem strictUnitTheorem_forces_all_obligations_hold {Id : Type}
    {u : VerificationUnit Id} (h : StrictUnitTheorem u) :
    AllHold (u.obligations.map Obligation.prop) := by
  have h_disj := h.1.2.2
  rw [h.2.1] at h_disj
  exact allHold_obligations_of_waived_nil u.obligations h_disj

/-- Extract `f x` from `AllHold (xs.map f)` and `x ∈ xs`. -/
theorem AllHold.of_mem_map {α : Type} (f : α → Prop) {xs : List α} {x : α}
    (h_all : AllHold (xs.map f)) (h_mem : x ∈ xs) : f x := by
  induction xs with
  | nil => cases h_mem
  | cons _ _ ih =>
    cases h_mem with
    | head _ => exact h_all.1
    | tail _ h_tail => exact ih h_all.2 h_tail

/-- Whenever `L.dom` is inhabited at `q₀` (`L.dom q₀`), 3-argument `L.Verified`
    forces `∃ q, pre q` (eliminating the right branch `∀ q, ¬ L.dom q`). -/
theorem verified_forces_inhabited_pre_of_inhabited_dom {SemObs : Type}
    (L : Language SemObs) {pre : L.Query → Prop}
    {post : L.Query → L.Out → Prop} {prog : L.Prog}
    (q₀ : L.Query) (hdom₀ : L.dom q₀)
    (h : L.Verified pre post prog) :
    ∃ q, pre q := by
  cases h.1 with
  | inl h_wit   => exact h_wit
  | inr h_empty => exact False.elim (h_empty q₀ hdom₀)

/-- `(L.withDom dom').Verified` is judgmentally equal (`rfl`) to
    `L.VerifiedOn dom'`. -/
theorem withDom_verified_rfl {SemObs : Type} (L : Language SemObs)
    (dom' pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) :
    (L.withDom dom').Verified pre post prog =
      L.VerifiedOn dom' pre post prog := rfl

/-- `Language.mapObs` commutes definitionally (`rfl`) with
    `Language.withDom`. -/
theorem mapObs_withDom_comm {SemObs₁ SemObs₂ : Type}
    (f : SemObs₁ → SemObs₂) (L : Language SemObs₁)
    (dom' : L.Query → Prop) :
    Language.mapObs f (L.withDom dom') =
      (Language.mapObs f L).withDom dom' := rfl

/-- **Two-Sided Canary Squeeze 1
    (`verifiedWithCanariesOn_refutes_trivial_post`):**
    If `badProg ∈ badProgs` is productive on `pre`, then
    `L.VerifiedWithCanariesOn dom pre (fun _ _ => True) prog badProgs` is
    provably `False`. -/
theorem verifiedWithCanariesOn_refutes_trivial_post {SemObs : Type}
    (L : Language SemObs)
    {dom pre : L.Query → Prop} {prog badProg : L.Prog}
    {badProgs : List L.Prog}
    (h_mem : badProg ∈ badProgs)
    (h_prod_bad : L.ProductiveOn pre badProg) :
    ¬ L.VerifiedWithCanariesOn dom pre (fun _ _ => True) prog badProgs := by
  intro ⟨h_ver_good, _, h_canaries⟩
  have h_not_ver_bad : ¬ L.VerifiedOn dom pre (fun _ _ => True) badProg :=
    AllHold.of_mem_map (L.RefutedOn dom pre (fun _ _ => True))
      h_canaries h_mem
  have h_spec_bad : L.sem badProg ≤ L.SpecOn pre (fun _ _ => True) := by
    intro q h_pre
    cases h_prod_bad q h_pre with
    | intro h_def _ =>
      exact ⟨h_def, fun _ _ => trivial⟩
  exact h_not_ver_bad ⟨h_ver_good.1, h_prod_bad, h_spec_bad⟩

theorem verifiedWithCanaries_refutes_trivial_post {SemObs : Type}
    (L : Language SemObs)
    {pre : L.Query → Prop} {prog badProg : L.Prog}
    {badProgs : List L.Prog}
    (h_mem : badProg ∈ badProgs)
    (h_prod_bad : L.ProductiveOn pre badProg) :
    ¬ L.VerifiedWithCanaries pre (fun _ _ => True) prog badProgs :=
  verifiedWithCanariesOn_refutes_trivial_post L h_mem h_prod_bad

/-- **Two-Sided Canary Squeeze 2
    (`verifiedSpineWithCanariesOn_refutes_subsingleton_semObs`):**
    If `badProg ∈ badProgs` is productive on `pre` and `∀ x y : SemObs, x = y`
    (as when `SemObs = Unit`), then
    `L.VerifiedSpineWithCanariesOn dom pre obsPost prog badProgs` is provably
    `False` for EVERY `obsPost`! -/
theorem verifiedSpineWithCanariesOn_refutes_subsingleton_semObs
    {SemObs : Type} (L : Language SemObs)
    (h_sub : ∀ x y : SemObs, x = y)
    {dom pre : L.Query → Prop} {obsPost : L.Query → SemObs → Prop}
    {prog badProg : L.Prog} {badProgs : List L.Prog}
    (h_mem : badProg ∈ badProgs)
    (h_prod_bad : L.ProductiveOn pre badProg) :
    ¬ L.VerifiedSpineWithCanariesOn dom pre obsPost prog badProgs := by
  intro ⟨h_ver_good, _, h_canaries⟩
  have h_not_ver_bad : ¬ L.VerifiedSpineOn dom pre obsPost badProg :=
    AllHold.of_mem_map
      (L.RefutedOn dom pre (fun q o => obsPost q (L.obs o)))
      h_canaries h_mem
  have h_spec_bad : L.sem badProg ≤ L.SpineSpecOn pre obsPost := by
    intro q h_pre
    cases h_ver_good.2.1 q h_pre with
    | intro h_def_good h_out_good =>
      cases h_out_good with
      | intro o_good h_val_good =>
        cases h_ver_good.2.2 q h_pre with
        | intro _ h_post_good =>
          have h_obs_good : obsPost q (L.obs o_good) :=
            h_post_good o_good h_val_good
          cases h_prod_bad q h_pre with
          | intro h_def_bad _ =>
            refine ⟨h_def_bad, fun o_bad _ => ?_⟩
            exact Eq.mp
              (congrArg (obsPost q) (h_sub (L.obs o_good) (L.obs o_bad)))
              h_obs_good
  exact h_not_ver_bad ⟨h_ver_good.1, h_prod_bad, h_spec_bad⟩

theorem verifiedSpineWithCanaries_refutes_subsingleton_semObs
    {SemObs : Type} (L : Language SemObs)
    (h_sub : ∀ x y : SemObs, x = y)
    {pre : L.Query → Prop} {obsPost : L.Query → SemObs → Prop}
    {prog badProg : L.Prog} {badProgs : List L.Prog}
    (h_mem : badProg ∈ badProgs)
    (h_prod_bad : L.ProductiveOn pre badProg) :
    ¬ L.VerifiedSpineWithCanaries pre obsPost prog badProgs :=
  verifiedSpineWithCanariesOn_refutes_subsingleton_semObs
    L h_sub h_mem h_prod_bad

/-!
## 5. Partial Compilation Impossibility Trilemma, `Partial.bind` Monad Laws,
   and the Conditioning Triad (`Behavior.when` ⊣ `Behavior.given`,
   `Behavior.require`, `Language.semIfCompiled`, `Language.semPartial`)
-/

/-- Forward composition of `CompilesPartial` along `Partial.bind`. -/
theorem CompilesPartial.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    {c₁ : BehaviorCodec L₁ L₂} {c₂ : BehaviorCodec L₂ L₃}
    {p₁ : L₁.Prog} {p₂? : Partial L₂.Prog} {f₂ : L₂.Prog → Partial L₃.Prog}
    (h₁₂ : CompilesPartial L₁ L₂ c₁ p₁ p₂?)
    (h₂₃ : ∀ h : p₂?.defined,
      CompilesPartial L₂ L₃ c₂ (p₂?.val h) (f₂ (p₂?.val h))) :
    CompilesPartial L₁ L₃ (BehaviorCodec.comp c₁ c₂) p₁
      (Partial.bind p₂? f₂) :=
  fun ⟨h₁, h₂⟩ => Compiles.comp (h₁₂ h₁) (h₂₃ h₁ h₂)

/-- Forward composition of `ProductiveCompilesPartial` along `Partial.bind`. -/
theorem ProductiveCompilesPartial.comp {SemObs : Type}
    {L₁ L₂ L₃ : Language SemObs}
    {c₁ : BehaviorCodec L₁ L₂} {c₂ : BehaviorCodec L₂ L₃}
    {p₁ : L₁.Prog} {p₂? : Partial L₂.Prog} {f₂ : L₂.Prog → Partial L₃.Prog}
    (h₁₂ : ProductiveCompilesPartial L₁ L₂ c₁ p₁ p₂?)
    (h₂₃ : ∀ h : p₂?.defined,
      ProductiveCompilesPartial L₂ L₃ c₂ (p₂?.val h) (f₂ (p₂?.val h))) :
    ProductiveCompilesPartial L₁ L₃ (BehaviorCodec.comp c₁ c₂) p₁
      (Partial.bind p₂? f₂) :=
  fun ⟨h₁, h₂⟩ => ProductiveCompiles.comp (h₁₂ h₁) (h₂₃ h₁ h₂)

/-- Lift a total `Compiles` proof to `CompilesPartial` over `Partial.pure`. -/
theorem Compiles.to_compilesPartial {SemObs : Type}
    {L_src L_tgt : Language SemObs} {c : BehaviorCodec L_src L_tgt}
    {s : L_src.Prog} {t : L_tgt.Prog}
    (h : Compiles L_src L_tgt c s t) :
    CompilesPartial L_src L_tgt c s (Partial.pure t) :=
  fun _ => h

/-- Dependent-elimination helper for `Option.toPartial`: reduces proving
    `CompilesPartial L_src L_tgt c s (Option.toPartial o)` to proving
    `Compiles L_src L_tgt c s t` for `o = some t`. -/
theorem CompilesPartial.of_option {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    {c : BehaviorCodec L_src L_tgt}
    {s : L_src.Prog} {o : Option L_tgt.Prog}
    (h : ∀ t, o = some t → Compiles L_src L_tgt c s t) :
    CompilesPartial L_src L_tgt c s (Option.toPartial o) := by
  cases o with
  | none   => intro hdef; exact False.elim hdef
  | some t => intro _; exact h t rfl

/-- Dependent-elimination helper for `ProductiveCompilesPartial` over
    `Option.toPartial`. -/
theorem ProductiveCompilesPartial.of_option {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    {c : BehaviorCodec L_src L_tgt}
    {s : L_src.Prog} {o : Option L_tgt.Prog}
    (h : ∀ t, o = some t → ProductiveCompiles L_src L_tgt c s t) :
    ProductiveCompilesPartial L_src L_tgt c s (Option.toPartial o) := by
  cases o with
  | none   => intro hdef; exact False.elim hdef
  | some t => intro _; exact h t rfl

/-- Forward transfer of `Language.ProductiveOn` across `ProductiveCompiles`
    whenever `c.encodeQuery (c.decodeQuery q₂) = q₂` holds on `pre`. -/
theorem ProductiveCompiles.productiveOn {SemObs : Type}
    {L₁ L₂ : Language SemObs} {c : BehaviorCodec L₁ L₂}
    {pre : L₁.Query → Prop} {s : L₁.Prog} {t : L₂.Prog}
    (h_enc_dec : ∀ q₂, pre (c.decodeQuery q₂) →
      c.encodeQuery (c.decodeQuery q₂) = q₂)
    (h_prod₁ : L₁.ProductiveOn pre s)
    (h_pcomp : ProductiveCompiles L₁ L₂ c s t) :
    L₂.ProductiveOn (fun q₂ => pre (c.decodeQuery q₂)) t := by
  intro q₂ hpre₂
  have hex₂ := h_pcomp.2 (c.decodeQuery q₂) (h_prod₁ (c.decodeQuery q₂) hpre₂)
  rw [h_enc_dec q₂ hpre₂] at hex₂
  exact hex₂

/-- Mutual refinement (`a ≤ b ∧ b ≤ a`) in a `Preorder`. -/
def RefinesEquiv {α : Type u} [Preorder α] (a b : α) : Prop :=
  a ≤ b ∧ b ≤ a

/-- **Impossibility Trilemma Part 1 (`dummy_ub_falsifies_compiles`):**
    If a total compiler maps a rejected source program `s` (which is defined at
    query `q₁`) to a dummy target program `t_dummy` that is undefined at
    `c.encodeQuery q₁` (`Partial.ub` / `⊤`), then
    `Compiles L_src L_tgt c s t_dummy` is falsified. -/
theorem dummy_ub_falsifies_compiles {SemObs : Type}
    {L_src L_tgt : Language SemObs} {c : BehaviorCodec L_src L_tgt}
    {s : L_src.Prog} {t_dummy : L_tgt.Prog} {q₁ : L_src.Query}
    (h_src_def : (L_src.sem s q₁).defined)
    (h_tgt_ub : ¬ (L_tgt.sem t_dummy (c.encodeQuery q₁)).defined) :
    ¬ Compiles L_src L_tgt c s t_dummy := by
  intro h_comp
  have h_m_def : (c.toMorphism (L_src.sem s) (c.encodeQuery q₁)).defined := by
    dsimp [BehaviorCodec.toMorphism]
    rw [c.decodeQuery_encodeQuery q₁]
    exact h_src_def
  cases h_comp (c.encodeQuery q₁) h_m_def with
  | intro h_t_def _ => exact h_tgt_ub h_t_def

/-- **Impossibility Trilemma Part 2
    (`dummy_bot_falsifies_productiveCompiles`):**
    If a total compiler maps a rejected source program `s` (which is productive
    at query `q₁`) to a dummy target program `t_dummy` with an empty outcome set
    at `c.encodeQuery q₁` (`Partial.bot` / `⊥`), then
    `ProductiveCompiles L_src L_tgt c s t_dummy` is falsified. -/
theorem dummy_bot_falsifies_productiveCompiles {SemObs : Type}
    {L_src L_tgt : Language SemObs} {c : BehaviorCodec L_src L_tgt}
    {s : L_src.Prog} {t_dummy : L_tgt.Prog} {q₁ : L_src.Query}
    (h_src_prod :
      ∃ h₁ : (L_src.sem s q₁).defined, ∃ o₁, (L_src.sem s q₁).val h₁ o₁)
    (h_tgt_bot :
      ∀ h₂ : (L_tgt.sem t_dummy (c.encodeQuery q₁)).defined,
        ∀ o₂, ¬ (L_tgt.sem t_dummy (c.encodeQuery q₁)).val h₂ o₂) :
    ¬ ProductiveCompiles L_src L_tgt c s t_dummy := by
  intro ⟨_, h_prod⟩
  cases h_prod q₁ h_src_prod with
  | intro h₂ hout₂ =>
    cases hout₂ with
    | intro o₂ ho₂ => exact h_tgt_bot h₂ o₂ ho₂

/-- **Impossibility Trilemma Part 3
    (`no_single_dummy_target_for_disjoint_rejected_progs`):**
    If two rejected source programs `s₁` and `s₂` are both productive at `q₁`
    with disjoint valid outcomes, then no single target program `t_dummy` can
    simultaneously satisfy `ProductiveCompiles` on `s₁` and `Compiles` on
    `s₂`. -/
theorem no_single_dummy_target_for_disjoint_rejected_progs {SemObs : Type}
    {L_src L_tgt : Language SemObs} {c : BehaviorCodec L_src L_tgt}
    {s₁ s₂ : L_src.Prog} {q₁ : L_src.Query}
    (h_prod₁ :
      ∃ h₁ : (L_src.sem s₁ q₁).defined, ∃ o₁, (L_src.sem s₁ q₁).val h₁ o₁)
    (h_def₂ : (L_src.sem s₂ q₁).defined)
    (h_disj :
      ∀ (h₁ : (L_src.sem s₁ q₁).defined) (h₂ : (L_src.sem s₂ q₁).defined) o₁,
        (L_src.sem s₁ q₁).val h₁ o₁ → ¬ (L_src.sem s₂ q₁).val h₂ o₁) :
    ¬ ∃ t_dummy : L_tgt.Prog,
      ProductiveCompiles L_src L_tgt c s₁ t_dummy ∧
      Compiles L_src L_tgt c s₂ t_dummy := by
  intro hex
  cases hex with
  | intro t_dummy hboth =>
    cases hboth.1.2 q₁ h_prod₁ with
    | intro h_t_def hout₂ =>
      cases hout₂ with
      | intro o₂ ho₂ =>
        cases h_prod₁ with
        | intro h_s₁_def _ =>
          have hm₁ :
              (c.toMorphism (L_src.sem s₁) (c.encodeQuery q₁)).defined := by
            dsimp [BehaviorCodec.toMorphism]
            rw [c.decodeQuery_encodeQuery q₁]
            exact h_s₁_def
          have hm₂ :
              (c.toMorphism (L_src.sem s₂) (c.encodeQuery q₁)).defined := by
            dsimp [BehaviorCodec.toMorphism]
            rw [c.decodeQuery_encodeQuery q₁]
            exact h_def₂
          cases hboth.1.1 (c.encodeQuery q₁) hm₁ with
          | intro _ hval₁ =>
            cases hboth.2 (c.encodeQuery q₁) hm₂ with
            | intro _ hval₂ =>
              cases hval₁ o₂ ho₂ with
              | intro o₁ h₁ =>
                cases hval₂ o₂ ho₂ with
                | intro o₁' h₂ =>
                  cases h₁ with
                  | intro hdec₁ hs₁ =>
                    cases h₂ with
                    | intro hdec₂ hs₂ =>
                      rw [hdec₁] at hdec₂
                      cases hdec₂
                      let q₁' := c.decodeQuery (c.encodeQuery q₁)
                      have h_eq_q : q₁' = q₁ :=
                        c.decodeQuery_encodeQuery q₁
                      have h_ex :
                          ∃ (h₁ : (L_src.sem s₁ q₁').defined)
                            (h₂ : (L_src.sem s₂ q₁').defined),
                            (L_src.sem s₁ q₁').val h₁ o₁ ∧
                            (L_src.sem s₂ q₁').val h₂ o₁ :=
                        ⟨hm₁, hm₂, hs₁, hs₂⟩
                      have h_ex_q₁ :
                          ∃ (h₁ : (L_src.sem s₁ q₁).defined)
                            (h₂ : (L_src.sem s₂ q₁).defined),
                            (L_src.sem s₁ q₁).val h₁ o₁ ∧
                            (L_src.sem s₂ q₁).val h₂ o₁ :=
                        Eq.mp
                          (congrArg
                            (fun q =>
                              ∃ (h₁ : (L_src.sem s₁ q).defined)
                                (h₂ : (L_src.sem s₂ q).defined),
                                (L_src.sem s₁ q).val h₁ o₁ ∧
                                (L_src.sem s₂ q).val h₂ o₁)
                            h_eq_q)
                          h_ex
                      cases h_ex_q₁ with
                      | intro h₁' hex₂ =>
                        cases hex₂ with
                        | intro h₂' hboth_val =>
                          exact h_disj h₁' h₂' o₁ hboth_val.1 hboth_val.2

/-- Structural equivalence on `Partial α` without requiring `[Preorder α]`. -/
def Partial.Equiv {α : Type u} (x y : Partial α) : Prop :=
  (x.defined ↔ y.defined) ∧
  ∀ (hx : x.defined) (hy : y.defined), x.val hx = y.val hy

/-- Inverse projection from `Partial α` to `Option α` given decidable
    definedness. -/
def Partial.toOption {α : Type u} (x : Partial α) [Decidable x.defined] :
    Option α :=
  if h : x.defined then some (x.val h) else none

theorem Partial.ub_top {α : Type u} [Preorder α] (x : Partial α) :
    x ≤ (Partial.ub : Partial α) :=
  fun h => False.elim h

theorem Partial.bot_le {β : Type u} (x : Partial (β → Prop)) :
    (Partial.bot : Partial (β → Prop)) ≤ x :=
  fun _ => ⟨trivial, fun _ h => False.elim h⟩

theorem Partial.Equiv.refl {α : Type u} (x : Partial α) : Partial.Equiv x x :=
  ⟨Iff.rfl, fun _ _ => rfl⟩

theorem Partial.Equiv.symm {α : Type u} {x y : Partial α}
    (h : Partial.Equiv x y) : Partial.Equiv y x :=
  ⟨h.1.symm, fun hy hx => (h.2 hx hy).symm⟩

theorem Partial.Equiv.trans {α : Type u} {x y z : Partial α}
    (h₁ : Partial.Equiv x y) (h₂ : Partial.Equiv y z) : Partial.Equiv x z :=
  ⟨h₁.1.trans h₂.1, fun hx hz =>
    let hy := h₁.1.mp hx
    (h₁.2 hx hy).trans (h₂.2 hy hz)⟩

theorem Partial.bind_pure_left {α : Type u} {β : Type v}
    (a : α) (f : α → Partial β) :
    Partial.Equiv (Partial.bind (Partial.pure a) f) (f a) :=
  ⟨⟨fun ⟨_, h⟩ => h, fun h => ⟨trivial, h⟩⟩, fun _ _ => rfl⟩

theorem Partial.bind_pure_right {α : Type u} (x : Partial α) :
    Partial.Equiv (Partial.bind x Partial.pure) x :=
  ⟨⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩, fun _ _ => rfl⟩

theorem Partial.bind_assoc {α : Type u} {β : Type v} {γ : Type w}
    (x : Partial α) (f : α → Partial β) (g : β → Partial γ) :
    Partial.Equiv
      (Partial.bind (Partial.bind x f) g)
      (Partial.bind x (fun a => Partial.bind (f a) g)) :=
  ⟨⟨fun ⟨⟨hx, hf⟩, hg⟩ => ⟨hx, ⟨hf, hg⟩⟩,
    fun ⟨hx, ⟨hf, hg⟩⟩ => ⟨⟨hx, hf⟩, hg⟩⟩,
   fun _ _ => rfl⟩

theorem Partial.ub_bind {α : Type u} {β : Type v} (f : α → Partial β) :
    Partial.Equiv (Partial.bind (Partial.ub : Partial α) f) Partial.ub :=
  ⟨⟨fun ⟨h, _⟩ => h, fun h => False.elim h⟩, fun ⟨h, _⟩ _ => False.elim h⟩

theorem Partial.bind_ub {α : Type u} {β : Type v} (x : Partial α) :
    Partial.Equiv
      (Partial.bind x (fun _ => (Partial.ub : Partial β)))
      Partial.ub :=
  ⟨⟨fun ⟨_, h⟩ => h, fun h => False.elim h⟩, fun ⟨_, h⟩ _ => False.elim h⟩

@[simp]
theorem Option.toPartial_some {α : Type u} (a : α) :
    Option.toPartial (some a) = Partial.pure a := rfl

@[simp]
theorem Option.toPartial_none {α : Type u} :
    Option.toPartial (@none α) = Partial.ub := rfl

theorem Option.toPartial_defined_iff {α : Type u} (o : Option α) :
    (Option.toPartial o).defined ↔ ∃ a, o = some a := by
  cases o with
  | none => exact ⟨fun h => False.elim h, fun ⟨_, h⟩ => by cases h⟩
  | some a => exact ⟨fun _ => ⟨a, rfl⟩, fun _ => trivial⟩

theorem Option.some_eq_iff_toPartial {α : Type u} (o : Option α) (a : α) :
    o = some a ↔
      ∃ h : (Option.toPartial o).defined, (Option.toPartial o).val h = a := by
  cases o with
  | none =>
    constructor
    · intro h; cases h
    · intro ⟨h, _⟩; exact False.elim h
  | some x =>
    constructor
    · intro h
      cases h
      exact ⟨trivial, rfl⟩
    · intro ⟨_, h⟩
      exact congrArg some h

theorem Option.toOption_toPartial {α : Type u} (o : Option α)
    [inst : Decidable (Option.toPartial o).defined] :
    Partial.toOption (Option.toPartial o) = o := by
  cases o with
  | none =>
    cases inst with
    | isFalse _ => rfl
    | isTrue h  => exact False.elim h
  | some a =>
    cases inst with
    | isFalse h => exact False.elim (h trivial)
    | isTrue _  => rfl

namespace Behavior

/-- **1. Angelic Program Gating (`Behavior.when`, left adjoint on the LHS of
    `≤`):**
    When `¬ P`, `Behavior.when P b q` collapses to `Partial.bot` (`⊥`). -/
def when {Query Out : Type}
    (P : Prop) (b : Behavior Query Out) : Behavior Query Out :=
  fun q => {
    defined := P → (b q).defined
    val     := fun h o => ∃ hp : P, (b q).val (h hp) o
  }

/-- **2. Precondition Specification Gating (`Behavior.given`, right adjoint on
    the RHS of `≤`):**
    When `¬ P`, `Behavior.given P spec q` collapses to `Partial.ub` (`⊤`). -/
def given {Query Out : Type}
    (P : Prop) (spec : Behavior Query Out) : Behavior Query Out :=
  fun q => {
    defined := P ∧ (spec q).defined
    val     := fun h => (spec q).val h.2
  }

/-- **3. Demonic Program Gating (`Behavior.require`, on the LHS of `≤`):**
    When `¬ P`, `Behavior.require P b q` collapses to `Partial.ub` (`⊤`),
    forcing `P` to hold at every defined query of any specification it
    refines. -/
def require {Query Out : Type}
    (P : Prop) (b : Behavior Query Out) : Behavior Query Out :=
  fun q => {
    defined := P ∧ (b q).defined
    val     := fun h => (b q).val h.2
  }

/-- Definitional identity (`rfl`): conjoining a proposition `P` into the
    query precondition of `L.SpecOn` is identical to `Behavior.given P`. -/
theorem specOn_and_eq_given {SemObs : Type} (L : Language SemObs) (P : Prop)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.SpecOn (fun q => P ∧ pre q) post =
      Behavior.given P (L.SpecOn pre post) := rfl

/-- Definitional identity (`rfl`): conjoining a proposition `P` into the
    query precondition of `L.WellFormedOn` is identical to
    `Behavior.given P`. -/
theorem wellFormedOn_and_eq_given {SemObs : Type} (L : Language SemObs)
    (P : Prop) (pre : L.Query → Prop) :
    L.WellFormedOn (fun q => P ∧ pre q) =
      Behavior.given P (L.WellFormedOn pre) := rfl

/-- Universal property of `Behavior.when` on the left-hand side of `≤`. -/
theorem when_le_iff {Query Out : Type} {P : Prop}
    {b spec : Behavior Query Out} :
    Behavior.when P b ≤ spec ↔ (P → b ≤ spec) := by
  constructor
  · intro h hp q hspec
    cases h q hspec with
    | intro hdef hval =>
      exact ⟨hdef hp, fun o ho => hval o ⟨hp, ho⟩⟩
  · intro h q hspec
    refine ⟨fun hp => (h hp q hspec).1, ?_⟩
    intro o ⟨hp, ho⟩
    exact (h hp q hspec).2 o ho

/-- Universal property of `Behavior.given` on the right-hand side of `≤`. -/
theorem le_given_iff {Query Out : Type} {P : Prop}
    {b spec : Behavior Query Out} :
    b ≤ Behavior.given P spec ↔ (P → b ≤ spec) := by
  constructor
  · intro h hp q hspec
    exact h q ⟨hp, hspec⟩
  · intro h q ⟨hp, hspec⟩
    exact h hp q hspec

/-- **The Conditioning Galois Connection (`Behavior.when P` ⊣
    `Behavior.given P`):**
    `Behavior.when P b ≤ spec ↔ (P → b ≤ spec) ↔ b ≤ Behavior.given P spec`. -/
theorem when_given_adjunction {Query Out : Type} (P : Prop)
    (b spec : Behavior Query Out) :
    (Behavior.when P b ≤ spec ↔ (P → b ≤ spec)) ∧
    ((P → b ≤ spec) ↔ b ≤ Behavior.given P spec) :=
  ⟨when_le_iff, le_given_iff.symm⟩

theorem when_le_iff_le_given {Query Out : Type} (P : Prop)
    (b spec : Behavior Query Out) :
    Behavior.when P b ≤ spec ↔ b ≤ Behavior.given P spec :=
  when_le_iff.trans le_given_iff.symm

theorem le_of_le_given_of_true {Query Out : Type} {P : Prop}
    {b spec : Behavior Query Out} (hle : b ≤ Behavior.given P spec) (hp : P) :
    b ≤ spec :=
  le_given_iff.mp hle hp

/-- Universal property of `Behavior.require` on the left-hand side of `≤`. -/
theorem require_le_iff {Query Out : Type} {P : Prop}
    {b spec : Behavior Query Out} :
    Behavior.require P b ≤ spec ↔
      (∀ q, (spec q).defined → P) ∧ (P → b ≤ spec) := by
  constructor
  · intro h
    refine ⟨fun q hspec => (h q hspec).1.1, fun hp q hspec => ?_⟩
    cases h q hspec with
    | intro hreq hval => exact ⟨hreq.2, hval⟩
  · intro ⟨hP, hb⟩ q hspec
    have hp : P := hP q hspec
    cases hb hp q hspec with
    | intro hdef hval => exact ⟨⟨hp, hdef⟩, hval⟩

theorem require_le_iff_of_defined {Query Out : Type} {P : Prop}
    {b spec : Behavior Query Out} {q₀ : Query} (hq₀ : (spec q₀).defined) :
    Behavior.require P b ≤ spec ↔ P ∧ b ≤ spec := by
  rw [require_le_iff]
  exact ⟨fun ⟨hP, hb⟩ => ⟨hP q₀ hq₀, hb (hP q₀ hq₀)⟩,
         fun ⟨hp, hb⟩ => ⟨fun _ _ => hp, fun _ => hb⟩⟩

/-- **Definitional Commutation of `BehaviorCodec.toMorphism` with
    `Behavior.given` (`rfl`):**
    Because `c.toMorphism` is a structured relational Kan extension, pushing a
    `Behavior.given P`-gated specification through `c.toMorphism` commutes with
    `Behavior.given P` by literal `rfl`. -/
theorem toMorphism_given {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (P : Prop) (spec : L₁.Behavior) :
    c.toMorphism (Behavior.given P spec) =
      Behavior.given P (c.toMorphism spec) := rfl

/-- **Definitional Commutation of `BehaviorCodec.toMorphism` with
    `Behavior.require` (`rfl`):** -/
theorem toMorphism_require {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (P : Prop) (b : L₁.Behavior) :
    c.toMorphism (Behavior.require P b) =
      Behavior.require P (c.toMorphism b) := rfl

/-- Mutual refinement commutation of `BehaviorCodec.toMorphism` with
    `Behavior.when`. -/
theorem toMorphism_when_equiv {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (P : Prop) (b : L₁.Behavior) :
    RefinesEquiv
      (c.toMorphism (Behavior.when P b))
      (Behavior.when P (c.toMorphism b)) := by
  constructor
  · intro q₂ hdef
    refine ⟨fun hp => hdef hp, ?_⟩
    intro o₂ ⟨o₁, hdec, hp, ho₁⟩
    exact ⟨hp, o₁, hdec, ho₁⟩
  · intro q₂ hdef
    refine ⟨fun hp => hdef hp, ?_⟩
    intro o₂ ⟨hp, o₁, hdec, ho₁⟩
    exact ⟨o₁, hdec, hp, ho₁⟩

end Behavior

/-- **Dependent Angelic Lifting (`Language.semIfCompiled`):**
    Lifts `L.sem` over a partial program `p? : Partial L.Prog` (dependent
    generalization of `Behavior.when`). When `¬ p?.defined`, it evaluates to
    `Partial.bot` (`⊥`). -/
def Language.semIfCompiled {SemObs : Type} (L : Language SemObs)
    (p? : Partial L.Prog) : L.Behavior :=
  fun q => {
    defined := ∀ h : p?.defined, (L.sem (p?.val h) q).defined
    val     := fun hdef o =>
      ∃ h : p?.defined, (L.sem (p?.val h) q).val (hdef h) o
  }

/-- **Dependent Demonic Lifting (`Language.semPartial`):**
    Lifts `L.sem` over a partial program `p? : Partial L.Prog` via
    `Partial.bind` (dependent generalization of `Behavior.require`). When
    `¬ p?.defined`, it evaluates to `Partial.ub` (`⊤`). -/
def Language.semPartial {SemObs : Type} (L : Language SemObs)
    (p? : Partial L.Prog) : L.Behavior :=
  fun q => Partial.bind p? (fun p => L.sem p q)

theorem Language.semIfCompiled_const_eq_when {SemObs : Type}
    (L : Language SemObs) (P : Prop) (p : L.Prog) :
    Language.semIfCompiled L { defined := P, val := fun _ => p } =
      Behavior.when P (L.sem p) := rfl

theorem Language.semIfCompiled_pure {SemObs : Type}
    (L : Language SemObs) (p : L.Prog) :
    RefinesEquiv (Language.semIfCompiled L (Partial.pure p)) (L.sem p) := by
  constructor
  · intro q hdef
    exact ⟨fun _ => hdef, fun o ⟨_, ho⟩ => ho⟩
  · intro q hdef
    exact ⟨hdef trivial, fun o ho => ⟨trivial, ho⟩⟩

theorem Language.semPartial_pure {SemObs : Type}
    (L : Language SemObs) (p : L.Prog) :
    RefinesEquiv (Language.semPartial L (Partial.pure p)) (L.sem p) := by
  constructor
  · intro q hdef
    exact ⟨⟨trivial, hdef⟩, fun _ ho => ho⟩
  · intro q ⟨_, hdef⟩
    exact ⟨hdef, fun _ ho => ho⟩

theorem Language.semIfCompiled_le_iff {SemObs : Type}
    (L : Language SemObs) (p? : Partial L.Prog) (spec : L.Behavior) :
    Language.semIfCompiled L p? ≤ spec ↔
      ∀ h : p?.defined, L.sem (p?.val h) ≤ spec := by
  constructor
  · intro hle h q hspec
    cases hle q hspec with
    | intro hdef hval =>
      exact ⟨hdef h, fun o ho => hval o ⟨h, ho⟩⟩
  · intro h q hspec
    refine ⟨fun hp => (h hp q hspec).1, ?_⟩
    intro o ⟨hp, ho⟩
    exact (h hp q hspec).2 o ho

theorem Language.semPartial_le_iff {SemObs : Type}
    (L : Language SemObs) (p? : Partial L.Prog) (spec : L.Behavior) :
    Language.semPartial L p? ≤ spec ↔
      (∀ q, (spec q).defined → p?.defined) ∧
      (∀ h : p?.defined, L.sem (p?.val h) ≤ spec) := by
  constructor
  · intro hle
    refine ⟨fun q hspec => (hle q hspec).1.1, fun hp q hspec => ?_⟩
    cases hle q hspec with
    | intro hpart hval => exact ⟨hpart.2, hval⟩
  · intro ⟨hP, hsem⟩ q hspec
    have hp : p?.defined := hP q hspec
    cases hsem hp q hspec with
    | intro hdef hval => exact ⟨⟨hp, hdef⟩, hval⟩

theorem Language.semIfCompiled_le_semPartial {SemObs : Type}
    (L : Language SemObs) (p? : Partial L.Prog) :
    Language.semIfCompiled L p? ≤ Language.semPartial L p? := by
  intro q ⟨_, hq⟩
  exact ⟨fun _ => hq, fun o ⟨_, ho⟩ => ho⟩

/-- `CompilesPartial` is constructively equivalent to `semIfCompiled` refining
    `c.toMorphism (L₁.sem p₁)`. -/
theorem compilesPartial_iff_semIfCompiled_le {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂)
    (p₁ : L₁.Prog) (p₂? : Partial L₂.Prog) :
    CompilesPartial L₁ L₂ c p₁ p₂? ↔
      Language.semIfCompiled L₂ p₂? ≤ c.toMorphism (L₁.sem p₁) :=
  (Language.semIfCompiled_le_iff L₂ p₂? (c.toMorphism (L₁.sem p₁))).symm

theorem noDupIds_foldr_snd {Id : Type} :
    ∀ (ids : List Id),
      (ids.foldr
        (fun id (acc : Prop × List Id) =>
          (AllHold (acc.2.map (fun id' => id ≠ id')) ∧ acc.1, id :: acc.2))
        (True, [])).2 = ids
  | []        => rfl
  | id :: ids => congrArg (id :: ·) (noDupIds_foldr_snd ids)

@[simp]
theorem noDupIds_nil {Id : Type} : NoDupIds ([] : List Id) ↔ True :=
  ⟨fun _ => trivial, fun _ => trivial⟩

@[simp]
theorem noDupIds_cons_iff {Id : Type} (id : Id) (ids : List Id) :
    NoDupIds (id :: ids) ↔
      AllHold (ids.map (fun id' => id ≠ id')) ∧ NoDupIds ids := by
  dsimp [NoDupIds]
  rw [noDupIds_foldr_snd ids]


/-!
## `BB-8`: Proof-Gated Partial & Total Compilers, PME Discharge, Certificate
   Checkers & Artifact Binding
-/


/-- A (potentially partial) compilation pass from `L_src` to `L_tgt` coupled via
    `BehaviorCodec`:
    - `compile s` returns `Partial L_tgt.Prog`, where `(compile s).defined` is
      the compile-time admission proposition (holding when pass `C` accepts
      `s` and failing when `C` rejects `s` due to a Post-Monomorphization Error,
      register-pressure spill limit, ABI immediate width bound, or unsupported
      feature).
    - Total compiler passes are embedded with zero proof or definitional tax via
      `PassCompiler.ofTotal` (`Partial.pure (compile s)`).
    - Computable `Option`-returning compiler passes are embedded via
      `PassCompiler.ofOption` (`Option.toPartial (compile s)`). -/
structure PassCompiler {SemObs : Type} (L_src L_tgt : Language SemObs) where
  compile : L_src.Prog → Partial L_tgt.Prog
  codec   : BehaviorCodec L_src L_tgt

/-- Lift a total compilation function `compile : L_src.Prog → L_tgt.Prog` into
    `PassCompiler` via `Partial.pure`. Because `(Partial.pure t).defined = True`
    and `(Partial.pure t).val _ = t` hold by `rfl`, total passes pay zero
    ergonomic or proof overhead. -/
abbrev PassCompiler.ofTotal {SemObs : Type} {L_src L_tgt : Language SemObs}
    (compile : L_src.Prog → L_tgt.Prog)
    (codec : BehaviorCodec L_src L_tgt) : PassCompiler L_src L_tgt where
  compile s := Partial.pure (compile s)
  codec     := codec

/-- Lift a computable `Option`-returning compilation function
    `compile : L_src.Prog → Option L_tgt.Prog` into `PassCompiler` via
    `Option.toPartial`. -/
abbrev PassCompiler.ofOption {SemObs : Type} {L_src L_tgt : Language SemObs}
    (compile : L_src.Prog → Option L_tgt.Prog)
    (codec : BehaviorCodec L_src L_tgt) : PassCompiler L_src L_tgt where
  compile s := Option.toPartial (compile s)
  codec     := codec

/-- Identity `PassCompiler` on `L`. -/
abbrev PassCompiler.id {SemObs : Type} (L : Language SemObs) :
    PassCompiler L L :=
  PassCompiler.ofTotal (fun s => s) (BehaviorCodec.id L)

/-- Extract the compiled target program when `C.compile s` is defined, with
    `h` discharged automatically for total and decidable multi-stage pipelines.
    Because `(C.compile s).defined : Prop` satisfies definitional proof
    irrelevance in Lean's kernel, `C.compileVal s h₁` and `C.compileVal s h₂`
    are judgmentally equal (`rfl`) for any `h₁, h₂`. -/
abbrev PassCompiler.compileVal {SemObs : Type} {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt) (s : L_src.Prog)
    (h : (C.compile s).defined := by
      repeat (first | trivial | assumption | refine ⟨?_, ?_⟩ | decide)) :
    L_tgt.Prog :=
  (C.compile s).val h

/-- Sequential composition of two `PassCompiler` stages via `Partial.bind`
    (Kleisli composition in `Partial`) and `BehaviorCodec.comp`. -/
def PassCompiler.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    (C₁₂ : PassCompiler L₁ L₂) (C₂₃ : PassCompiler L₂ L₃) :
    PassCompiler L₁ L₃ where
  compile s := Partial.bind (C₁₂.compile s) C₂₃.compile
  codec     := BehaviorCodec.comp C₁₂.codec C₂₃.codec

@[simp]
theorem PassCompiler.ofTotal_defined {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (compile : L_src.Prog → L_tgt.Prog)
    (codec : BehaviorCodec L_src L_tgt) (s : L_src.Prog) :
    ((PassCompiler.ofTotal compile codec).compile s).defined = True := rfl

@[simp]
theorem PassCompiler.ofTotal_compileVal {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (compile : L_src.Prog → L_tgt.Prog)
    (codec : BehaviorCodec L_src L_tgt) (s : L_src.Prog)
    (h : ((PassCompiler.ofTotal compile codec).compile s).defined := trivial) :
    (PassCompiler.ofTotal compile codec).compileVal s h = compile s := rfl

@[simp]
theorem PassCompiler.comp_defined {SemObs : Type}
    {L₁ L₂ L₃ : Language SemObs}
    (C₁₂ : PassCompiler L₁ L₂) (C₂₃ : PassCompiler L₂ L₃) (s : L₁.Prog) :
    ((PassCompiler.comp C₁₂ C₂₃).compile s).defined =
      (∃ h₁ : (C₁₂.compile s).defined,
        (C₂₃.compile ((C₁₂.compile s).val h₁)).defined) := rfl

@[simp]
theorem PassCompiler.comp_compileVal {SemObs : Type}
    {L₁ L₂ L₃ : Language SemObs}
    (C₁₂ : PassCompiler L₁ L₂) (C₂₃ : PassCompiler L₂ L₃) (s : L₁.Prog)
    (h : ((PassCompiler.comp C₁₂ C₂₃).compile s).defined) :
    (PassCompiler.comp C₁₂ C₂₃).compileVal s h =
      C₂₃.compileVal (C₁₂.compileVal s h.1) h.2 := rfl

/-- Universal conditional compilation soundness on `s` (`CompilesPartial`):
    whenever `C.compile s` is defined (`h : (C.compile s).defined`), the
    compiled target `(C.compile s).val h` refines `s` under `C.codec`. -/
abbrev PassCompiler.SoundOn {SemObs : Type} {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  CompilesPartial L_src L_tgt C.codec s (C.compile s)

/-- Universal miracle-free conditional compilation soundness on `s`
    (`ProductiveCompilesPartial`). -/
abbrev PassCompiler.ProductiveSoundOn {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  ProductiveCompilesPartial L_src L_tgt C.codec s (C.compile s)

/-- **Universal Compiler Pass Non-Vacuity
    (`PassCompiler.SoundPartialCompilerOn`):**
    Applies `Trusted.NonVacuousOn` at `Query := L_src.Prog` to prevent an
    `alwaysRejectCompiler` (`compile _ := Partial.ub`) from vacuously claiming
    pass-wide soundness over an inhabited program domain `domProg`:
    1. `NonVacuousOn domProg admitted` holds (the admitted program subset is
       inhabited within `domProg`, or `domProg` itself is provably empty),
    2. Every `s` satisfying `admitted s` compiles (`(C.compile s).defined`), and
    3. Every program `s` satisfies `C.ProductiveSoundOn s`. -/
def PassCompiler.SoundPartialCompilerOn {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt)
    (domProg admitted : L_src.Prog → Prop) : Prop :=
  NonVacuousOn domProg admitted ∧
  (∀ s, admitted s → (C.compile s).defined) ∧
  (∀ s, C.ProductiveSoundOn s)

/-- **Mode 1 (`PassCompiler.VerifiedOn` — Guaranteed Compilation & Target
    Refinement, `INV-1.6` & `EXPLOIT-8` Defense):**
    Combines source `L_src.VerifiedOn dom pre post s` with positive compilation
    `∃ h : (C.compile s).defined, Compiles L_src L_tgt C.codec s`
    `((C.compile s).val h)`. Requires compilation to succeed
    (`(C.compile s).defined`), blocking the trivial `alwaysRejectCompiler`
    (`compile _ := Partial.ub`). -/
def PassCompiler.VerifiedOn {SemObs : Type} {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) : Prop :=
  L_src.VerifiedOn dom pre post s ∧
  ∃ h : (C.compile s).defined,
    Compiles L_src L_tgt C.codec s ((C.compile s).val h)

/-- Alias for Mode 1 (`PassCompiler.VerifiedOn`) emphasizing guaranteed
    compilation. -/
abbrev PassCompiler.VerifiedTotalOn {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) : Prop :=
  C.VerifiedOn dom pre post s

/-- Extract the compilation definedness witness `(C.compile s).defined : Prop`
    from `C.VerifiedOn dom pre post s`. -/
theorem PassCompiler.VerifiedOn.defined {SemObs : Type}
    {L_src L_tgt : Language SemObs} {C : PassCompiler L_src L_tgt}
    {dom pre : L_src.Query → Prop} {post : L_src.Query → L_src.Out → Prop}
    {s : L_src.Prog}
    (h : C.VerifiedOn dom pre post s) :
    (C.compile s).defined :=
  match h.2 with
  | ⟨hdef, _⟩ => hdef

/-- Extract the `Compiles` proof for any `h_def : (C.compile s).defined` from
    `C.VerifiedOn dom pre post s` (using `Prop` proof irrelevance on
    `h_def`). -/
theorem PassCompiler.VerifiedOn.compiles {SemObs : Type}
    {L_src L_tgt : Language SemObs} {C : PassCompiler L_src L_tgt}
    {dom pre : L_src.Query → Prop} {post : L_src.Query → L_src.Out → Prop}
    {s : L_src.Prog}
    (h : C.VerifiedOn dom pre post s)
    (h_def : (C.compile s).defined := h.defined) :
    Compiles L_src L_tgt C.codec s (C.compileVal s h_def) :=
  match h.2 with
  | ⟨_, hcomp⟩ => hcomp

/-- **Mode 1 Two-Sided (`PassCompiler.BiVerifiedOn`, `GAP-1`, `EXPLOIT-1` &
    `EXPLOIT-8` Defense):**
    Couples `PassCompiler.VerifiedOn` with target `ProductiveOn`, refuting both
    miraculous/over-constrained targets (`initState = False` or `1 = 0`) and
    always-rejecting partial compilers (`compile _ := Partial.ub`). -/
def PassCompiler.BiVerifiedOn {SemObs : Type} {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) : Prop :=
  C.VerifiedOn dom pre post s ∧
  ∀ h : (C.compile s).defined,
    L_tgt.ProductiveOn
      (fun q₂ => pre (C.codec.decodeQuery q₂))
      ((C.compile s).val h)

/-- Alias for Mode 1 Two-Sided (`PassCompiler.BiVerifiedOn`). -/
abbrev PassCompiler.BiVerifiedTotalOn {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) : Prop :=
  C.BiVerifiedOn dom pre post s

/-- Extract the compilation definedness witness `(C.compile s).defined : Prop`
    from `C.BiVerifiedOn dom pre post s`. -/
theorem PassCompiler.BiVerifiedOn.defined {SemObs : Type}
    {L_src L_tgt : Language SemObs} {C : PassCompiler L_src L_tgt}
    {dom pre : L_src.Query → Prop} {post : L_src.Query → L_src.Out → Prop}
    {s : L_src.Prog}
    (h : C.BiVerifiedOn dom pre post s) :
    (C.compile s).defined :=
  h.1.defined

/-- **Mode 2 (`PassCompiler.VerifiedIfCompiledOn` — Unconditional Source
    `VerifiedOn`, Conditional Target `CompilesPartial`, `EXPLOIT-9A` Defense):**
    Requires `L_src.VerifiedOn dom pre post s` unconditionally at the source
    level (so a program with source UB is rejected even if `C` fails to compile
    it), and requires `CompilesPartial` whenever `C.compile s` is defined. -/
def PassCompiler.VerifiedIfCompiledOn {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) : Prop :=
  L_src.VerifiedOn dom pre post s ∧
  C.SoundOn s

/-- **Mode 2 Two-Sided (`PassCompiler.BiVerifiedIfCompiledOn`):**
    Requires `L_src.VerifiedOn dom pre post s` unconditionally at the source
    level and both `Compiles` and target `ProductiveOn` whenever `C.compile s`
    is defined. -/
def PassCompiler.BiVerifiedIfCompiledOn {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) : Prop :=
  L_src.VerifiedOn dom pre post s ∧
  ∀ h : (C.compile s).defined,
    Compiles L_src L_tgt C.codec s ((C.compile s).val h) ∧
    L_tgt.ProductiveOn
      (fun q₂ => pre (C.codec.decodeQuery q₂))
      ((C.compile s).val h)

/-- **Mode 3 (`PassCompiler.VerifiedWhenCompiledOn` — Source and Target
    Conditioned on Compile-Time Admissibility `adm : Prop`, `EXPLOIT-9B` &
    `EXPLOIT-10` Defense):**
    Models Post-Monomorphization Errors (PMEs) and generic functions whose
    source safety itself depends on compile-time admission `adm : Prop` (such
    as `MonoAdmitted sys tySizes prog` or `CompileAdmitted s`):
    1. `NonVacuousOn dom pre` is checked on the runtime domain `dom` and runtime
       precondition `pre` *outside* `adm` (preventing a false `adm` from
       masking a contradictory runtime precondition `x > 10 ∧ x < 5`,
       `EXPLOIT-9B`),
    2. Under `adm`, `s` is productive on `pre`,
    3. `L_src.sem s ≤ Behavior.given adm (L_src.SpecOn pre post)`,
    4. Successful compilation implies `adm` (`(C.compile s).defined → adm`), and
    5. Whenever `h : (C.compile s).defined`, `(C.compile s).val h` compiles
       `s`. -/
def PassCompiler.VerifiedWhenCompiledOn {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt)
    (adm : Prop)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) : Prop :=
  NonVacuousOn dom pre ∧
  (adm → L_src.ProductiveOn pre s) ∧
  L_src.sem s ≤ Behavior.given adm (L_src.SpecOn pre post) ∧
  ((C.compile s).defined → adm) ∧
  C.SoundOn s

/-- **Mode 3 Two-Sided (`PassCompiler.BiVerifiedWhenCompiledOn`):**
    Couples `PassCompiler.VerifiedWhenCompiledOn` with conditional target
    `ProductiveOn` whenever `C.compile s` is defined. -/
def PassCompiler.BiVerifiedWhenCompiledOn {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt)
    (adm : Prop)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) : Prop :=
  NonVacuousOn dom pre ∧
  (adm → L_src.ProductiveOn pre s) ∧
  L_src.sem s ≤ Behavior.given adm (L_src.SpecOn pre post) ∧
  ((C.compile s).defined → adm) ∧
  ∀ h : (C.compile s).defined,
    Compiles L_src L_tgt C.codec s ((C.compile s).val h) ∧
    L_tgt.ProductiveOn
      (fun q₂ => pre (C.codec.decodeQuery q₂))
      ((C.compile s).val h)

/-- Proof-Gated Target Soundness Theorem (`INV-1.6`): when `C.VerifiedOn` holds,
    the compiled target program `C.compileVal s h_def` refines the mapped
    specification `C.codec.toMorphism (L_src.SpecOn pre post)` with intermediate
    semantics eliminated by preorder transitivity. Because `h_def` defaults to
    `h.defined` and `(C.compile s).defined : Prop` is proof-irrelevant, callers
    never need to unpack an existential witness. -/
theorem proof_gated_pipeline_sound {SemObs : Type}
    {L_src L_tgt : Language SemObs} (C : PassCompiler L_src L_tgt)
    {dom pre : L_src.Query → Prop} {post : L_src.Query → L_src.Out → Prop}
    {s : L_src.Prog}
    (h : C.VerifiedOn dom pre post s)
    (h_def : (C.compile s).defined := h.defined) :
    L_tgt.sem (C.compileVal s h_def) ≤
      C.codec.toMorphism (L_src.SpecOn pre post) :=
  Preorder.le_trans (h.compiles h_def)
    (BehaviorCodec.toMorphism_monotone C.codec h.1.2.2)

/-- Two-sided Proof-Gated Target Soundness Theorem (`GAP-1`): when
    `C.BiVerifiedOn` holds, `C.compileVal s h_def` is both productive on
    `pre ∘ C.codec.decodeQuery` and refines the mapped specification. -/
theorem proof_gated_biPipeline_sound {SemObs : Type}
    {L_src L_tgt : Language SemObs} (C : PassCompiler L_src L_tgt)
    {dom pre : L_src.Query → Prop} {post : L_src.Query → L_src.Out → Prop}
    {s : L_src.Prog}
    (h : C.BiVerifiedOn dom pre post s)
    (h_def : (C.compile s).defined := h.defined) :
    L_tgt.ProductiveOn (fun q₂ => pre (C.codec.decodeQuery q₂))
      (C.compileVal s h_def) ∧
    L_tgt.sem (C.compileVal s h_def) ≤
      C.codec.toMorphism (L_src.SpecOn pre post) :=
  ⟨h.2 h_def, proof_gated_pipeline_sound C h.1 h_def⟩

/-- Conditional Target Soundness Theorem for Mode 2 (`BiVerifiedIfCompiledOn`):
    whenever compilation succeeds (`h_def : (C.compile s).defined`), the
    compiled target artifact `C.compileVal s h_def` is productive and refines
    the mapped specification, and unconditionally
    `Language.semIfCompiled L_tgt (C.compile s)` refines the mapped
    specification. -/
theorem proof_gated_biPipeline_sound_ifCompiled {SemObs : Type}
    {L_src L_tgt : Language SemObs} (C : PassCompiler L_src L_tgt)
    {dom pre : L_src.Query → Prop} {post : L_src.Query → L_src.Out → Prop}
    {s : L_src.Prog}
    (h : C.BiVerifiedIfCompiledOn dom pre post s) :
    Language.semIfCompiled L_tgt (C.compile s) ≤
      C.codec.toMorphism (L_src.SpecOn pre post) ∧
    ∀ h_def : (C.compile s).defined,
      L_tgt.ProductiveOn
        (fun q₂ => pre (C.codec.decodeQuery q₂))
        (C.compileVal s h_def) ∧
      L_tgt.sem (C.compileVal s h_def) ≤
        C.codec.toMorphism (L_src.SpecOn pre post) := by
  refine ⟨?_, ?_⟩
  · refine (Language.semIfCompiled_le_iff L_tgt (C.compile s) _).mpr ?_
    intro h_def
    exact Preorder.le_trans (h.2 h_def).1
      (BehaviorCodec.toMorphism_monotone C.codec h.1.2.2)
  · intro h_def
    exact ⟨(h.2 h_def).2,
      Preorder.le_trans (h.2 h_def).1
        (BehaviorCodec.toMorphism_monotone C.codec h.1.2.2)⟩

/-- Conservative extension theorem for `PassCompiler.ofTotal`: `VerifiedOn` is
    equivalent to `L_src.VerifiedOn dom pre post s` conjoined with
    `Compiles L_src L_tgt codec s (compile s)`. -/
theorem PassCompiler.ofTotal_verifiedOn_iff {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (compile : L_src.Prog → L_tgt.Prog)
    (codec : BehaviorCodec L_src L_tgt)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) :
    (PassCompiler.ofTotal compile codec).VerifiedOn dom pre post s ↔
      L_src.VerifiedOn dom pre post s ∧
      Compiles L_src L_tgt codec s (compile s) :=
  ⟨fun ⟨hv, _, hc⟩ => ⟨hv, hc⟩,
   fun ⟨hv, hc⟩ => ⟨hv, trivial, hc⟩⟩

/-- Conservative extension theorem for `PassCompiler.ofTotal`: `BiVerifiedOn` is
    equivalent to the exact total-compiler obligation. -/
theorem PassCompiler.ofTotal_biVerifiedOn_iff {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (compile : L_src.Prog → L_tgt.Prog)
    (codec : BehaviorCodec L_src L_tgt)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) :
    (PassCompiler.ofTotal compile codec).BiVerifiedOn dom pre post s ↔
      L_src.VerifiedOn dom pre post s ∧
      Compiles L_src L_tgt codec s (compile s) ∧
      L_tgt.ProductiveOn
        (fun q₂ => pre (codec.decodeQuery q₂))
        (compile s) :=
  ⟨fun ⟨⟨hv, _, hc⟩, hprod⟩ => ⟨hv, hc, hprod trivial⟩,
   fun ⟨hv, hc, hprod⟩ => ⟨⟨hv, trivial, hc⟩, fun _ => hprod⟩⟩

/-- Conservative extension theorem for `PassCompiler.ofOption`: `SoundOn`
    unfolds directly to
    `∀ t, compile s = some t → Compiles L_src L_tgt codec s t`. -/
theorem PassCompiler.ofOption_soundOn_iff {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (compile : L_src.Prog → Option L_tgt.Prog)
    (codec : BehaviorCodec L_src L_tgt) (s : L_src.Prog) :
    (PassCompiler.ofOption compile codec).SoundOn s ↔
      ∀ t, compile s = some t → Compiles L_src L_tgt codec s t := by
  constructor
  · intro hs t heq
    cases (Option.some_eq_iff_toPartial (compile s) t).mp heq with
    | intro hdef hval =>
      rw [← hval]
      exact hs hdef
  · intro hs hdef
    exact hs ((Option.toPartial (compile s)).val hdef)
      ((Option.some_eq_iff_toPartial (compile s) _).mpr ⟨hdef, rfl⟩)

/-- Conservative extension theorem for `PassCompiler.ofOption`:
    `VerifiedIfCompiledOn` is equivalent to `L_src.VerifiedOn` plus
    `∀ t, compile s = some t → Compiles L_src L_tgt codec s t`. -/
theorem PassCompiler.ofOption_verifiedIfCompiledOn_iff {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (compile : L_src.Prog → Option L_tgt.Prog)
    (codec : BehaviorCodec L_src L_tgt)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) :
    (PassCompiler.ofOption compile codec).VerifiedIfCompiledOn dom pre post s ↔
      L_src.VerifiedOn dom pre post s ∧
      ∀ t, compile s = some t → Compiles L_src L_tgt codec s t :=
  ⟨fun ⟨hv, hs⟩ =>
     ⟨hv, (PassCompiler.ofOption_soundOn_iff compile codec s).mp hs⟩,
   fun ⟨hv, hs⟩ =>
     ⟨hv, (PassCompiler.ofOption_soundOn_iff compile codec s).mpr hs⟩⟩

/-- Mode 1 (`VerifiedOn`) is equivalent to guaranteed compilation
    `(C.compile s).defined` conjoined with Mode 2 (`VerifiedIfCompiledOn`). -/
theorem PassCompiler.verifiedOn_iff_defined_and_ifCompiled {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) :
    C.VerifiedOn dom pre post s ↔
      (C.compile s).defined ∧ C.VerifiedIfCompiledOn dom pre post s :=
  ⟨fun ⟨hv, hdef, hc⟩ => ⟨hdef, hv, fun _ => hc⟩,
   fun ⟨hdef, hv, hif⟩ => ⟨hv, hdef, hif hdef⟩⟩

/-- Mode 1 Two-Sided (`BiVerifiedOn`) is equivalent to guaranteed compilation
    `(C.compile s).defined` conjoined with Mode 2 (`BiVerifiedIfCompiledOn`). -/
theorem PassCompiler.biVerifiedOn_iff_defined_and_ifCompiled {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) :
    C.BiVerifiedOn dom pre post s ↔
      (C.compile s).defined ∧ C.BiVerifiedIfCompiledOn dom pre post s :=
  ⟨fun ⟨⟨hv, hdef, hc⟩, hprod⟩ => ⟨hdef, hv, fun h => ⟨hc, hprod h⟩⟩,
   fun ⟨hdef, hv, hif⟩ => ⟨⟨hv, hdef, (hif hdef).1⟩, fun h => (hif h).2⟩⟩

/-- Constructing `Mode 3` (`BiVerifiedWhenCompiledOn`) from conditional source
    obligations `adm → L_src.ProductiveOn pre s` and
    `adm → L_src.sem s ≤ L_src.SpecOn pre post`. -/
theorem PassCompiler.biVerifyWhenCompiled_of_cond {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    {C : PassCompiler L_src L_tgt}
    {adm : Prop}
    {dom pre : L_src.Query → Prop} {post : L_src.Query → L_src.Out → Prop}
    {s : L_src.Prog}
    (h_nonvac : NonVacuousOn dom pre)
    (h_prod_cond : adm → L_src.ProductiveOn pre s)
    (h_spec_cond : adm → L_src.sem s ≤ L_src.SpecOn pre post)
    (h_adm_of_comp : (C.compile s).defined → adm)
    (h_tgt :
      ∀ h : (C.compile s).defined,
        Compiles L_src L_tgt C.codec s ((C.compile s).val h) ∧
        L_tgt.ProductiveOn
          (fun q₂ => pre (C.codec.decodeQuery q₂))
          ((C.compile s).val h)) :
    C.BiVerifiedWhenCompiledOn adm dom pre post s :=
  ⟨h_nonvac, h_prod_cond,
   Behavior.le_given_iff.mpr h_spec_cond,
   h_adm_of_comp, h_tgt⟩

/-- **Crown Jewel Target-Level Discharge Theorem
    (`PassCompiler.BiVerifiedWhenCompiledOn.target_discharges_adm`):**
    Suppose `s` is verified in Mode 3
    (`C.BiVerifiedWhenCompiledOn adm dom pre post s`), where source productivity
    and safety are gated on `adm : Prop` (such as `CompileAdmitted s` or
    `MonoAdmitted sys tySizes prog`), and compilation succeeds
    (`h_comp : (C.compile s).defined`).
    Then:
    1. `adm` is **automatically discharged** (`h_adm : adm`),
    2. `s` satisfies the **un-gated** source `L_src.VerifiedOn dom pre post s`,
    3. `s` satisfies the **un-gated** Mode 1 `C.BiVerifiedOn dom pre post s`,
       and
    4. The compiled target artifact `C.compileVal s h_comp` is unconditionally
       productive on `pre ∘ C.codec.decodeQuery` and refines
       `C.codec.toMorphism (L_src.SpecOn pre post)` with `adm` completely
       discharged! -/
theorem PassCompiler.BiVerifiedWhenCompiledOn.target_discharges_adm
    {SemObs : Type} {L_src L_tgt : Language SemObs}
    {C : PassCompiler L_src L_tgt}
    {adm : Prop}
    {dom pre : L_src.Query → Prop} {post : L_src.Query → L_src.Out → Prop}
    {s : L_src.Prog}
    (h_when : C.BiVerifiedWhenCompiledOn adm dom pre post s)
    (h_comp : (C.compile s).defined := by
      repeat (first | trivial | assumption | refine ⟨?_, ?_⟩ | decide)) :
    adm ∧
    L_src.VerifiedOn dom pre post s ∧
    C.BiVerifiedOn dom pre post s ∧
    L_tgt.ProductiveOn
      (fun q₂ => pre (C.codec.decodeQuery q₂))
      (C.compileVal s h_comp) ∧
    L_tgt.sem (C.compileVal s h_comp) ≤
      C.codec.toMorphism (L_src.SpecOn pre post) := by
  have h_adm : adm := h_when.2.2.2.1 h_comp
  have h_prod_src : L_src.ProductiveOn pre s := h_when.2.1 h_adm
  have h_spec_src : L_src.sem s ≤ L_src.SpecOn pre post :=
    Behavior.le_of_le_given_of_true h_when.2.2.1 h_adm
  have h_ver_src : L_src.VerifiedOn dom pre post s :=
    ⟨h_when.1, h_prod_src, h_spec_src⟩
  have h_tgt := h_when.2.2.2.2 h_comp
  have h_biver : C.BiVerifiedOn dom pre post s :=
    ⟨⟨h_ver_src, h_comp, h_tgt.1⟩, fun h => (h_when.2.2.2.2 h).2⟩
  have h_spec_tgt :
      L_tgt.sem (C.compileVal s h_comp) ≤
        C.codec.toMorphism (L_src.SpecOn pre post) :=
    Preorder.le_trans h_tgt.1
      (BehaviorCodec.toMorphism_monotone C.codec h_spec_src)
  exact ⟨h_adm, h_ver_src, h_biver, h_tgt.2, h_spec_tgt⟩

/-- Direct one-sided Target-Level PME Discharge
    (`target_discharges_compileAdmitted`) for conditional source `VerifiedOn` +
    `CompilesPartial`. -/
theorem target_discharges_compileAdmitted {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt)
    {dom pre : L_src.Query → Prop} {post : L_src.Query → L_src.Out → Prop}
    {s : L_src.Prog} {CompileAdmitted : Prop}
    (h_src_cond :
      CompileAdmitted → L_src.VerifiedOn dom pre post s)
    (h_comp : CompilesPartial L_src L_tgt C.codec s (C.compile s))
    (h_adm_of_comp : (C.compile s).defined → CompileAdmitted)
    (h_def : (C.compile s).defined := by
      repeat (first | trivial | assumption | refine ⟨?_, ?_⟩ | decide)) :
    CompileAdmitted ∧
    L_src.VerifiedOn dom pre post s ∧
    C.VerifiedOn dom pre post s ∧
    L_tgt.sem (C.compileVal s h_def) ≤
      C.codec.toMorphism (L_src.SpecOn pre post) := by
  have h_adm : CompileAdmitted := h_adm_of_comp h_def
  have h_src : L_src.VerifiedOn dom pre post s := h_src_cond h_adm
  have h_ver : C.VerifiedOn dom pre post s := ⟨h_src, h_def, h_comp h_def⟩
  exact ⟨h_adm, h_src, h_ver, proof_gated_pipeline_sound C h_ver h_def⟩

/-- Composition of `PassCompiler.SoundOn` along `PassCompiler.comp`. -/
theorem PassCompiler.SoundOn.comp {SemObs : Type}
    {L₁ L₂ L₃ : Language SemObs}
    {C₁₂ : PassCompiler L₁ L₂} {C₂₃ : PassCompiler L₂ L₃}
    {p₁ : L₁.Prog}
    (h₁₂ : C₁₂.SoundOn p₁)
    (h₂₃ : ∀ h : (C₁₂.compile p₁).defined,
      C₂₃.SoundOn ((C₁₂.compile p₁).val h)) :
    (PassCompiler.comp C₁₂ C₂₃).SoundOn p₁ :=
  CompilesPartial.comp h₁₂ h₂₃

/-- Composition of `PassCompiler.ProductiveSoundOn` along
    `PassCompiler.comp`. -/
theorem PassCompiler.ProductiveSoundOn.comp {SemObs : Type}
    {L₁ L₂ L₃ : Language SemObs}
    {C₁₂ : PassCompiler L₁ L₂} {C₂₃ : PassCompiler L₂ L₃}
    {p₁ : L₁.Prog}
    (h₁₂ : C₁₂.ProductiveSoundOn p₁)
    (h₂₃ : ∀ h : (C₁₂.compile p₁).defined,
      C₂₃.ProductiveSoundOn ((C₁₂.compile p₁).val h)) :
    (PassCompiler.comp C₁₂ C₂₃).ProductiveSoundOn p₁ :=
  ProductiveCompilesPartial.comp h₁₂ h₂₃

/-- Stage-wise composition of `PassCompiler.VerifiedIfCompiledOn` across
    `PassCompiler.comp C₁₂ C₂₃`. -/
theorem PassCompiler.VerifiedIfCompiledOn.comp {SemObs : Type}
    {L₁ L₂ L₃ : Language SemObs}
    {C₁₂ : PassCompiler L₁ L₂} {C₂₃ : PassCompiler L₂ L₃}
    {dom pre : L₁.Query → Prop} {post : L₁.Query → L₁.Out → Prop}
    {p₁ : L₁.Prog}
    (h₁₂ : C₁₂.VerifiedIfCompiledOn dom pre post p₁)
    (h₂₃ : ∀ h : (C₁₂.compile p₁).defined,
      C₂₃.SoundOn ((C₁₂.compile p₁).val h)) :
    (PassCompiler.comp C₁₂ C₂₃).VerifiedIfCompiledOn dom pre post p₁ :=
  ⟨h₁₂.1, CompilesPartial.comp h₁₂.2 h₂₃⟩

/-- Stage-wise composition of `PassCompiler.VerifiedOn` across
    `PassCompiler.comp C₁₂ C₂₃`. -/
theorem PassCompiler.VerifiedOn.comp {SemObs : Type}
    {L₁ L₂ L₃ : Language SemObs}
    {C₁₂ : PassCompiler L₁ L₂} {C₂₃ : PassCompiler L₂ L₃}
    {dom pre : L₁.Query → Prop} {post : L₁.Query → L₁.Out → Prop}
    {p₁ : L₁.Prog}
    (h₁₂ : C₁₂.VerifiedOn dom pre post p₁)
    (h_def₂₃ : ∀ h : (C₁₂.compile p₁).defined,
      (C₂₃.compile ((C₁₂.compile p₁).val h)).defined)
    (h_comp₂₃ : ∀ (h₁ : (C₁₂.compile p₁).defined)
        (h₂ : (C₂₃.compile ((C₁₂.compile p₁).val h₁)).defined),
      Compiles L₂ L₃ C₂₃.codec
        ((C₁₂.compile p₁).val h₁)
        ((C₂₃.compile ((C₁₂.compile p₁).val h₁)).val h₂)) :
    (PassCompiler.comp C₁₂ C₂₃).VerifiedOn dom pre post p₁ := by
  cases h₁₂.2 with
  | intro h₁ hc₁ =>
    have h₂ := h_def₂₃ h₁
    exact ⟨h₁₂.1, ⟨h₁, h₂⟩, Compiles.comp hc₁ (h_comp₂₃ h₁ h₂)⟩

/-- Stage-wise composition of `PassCompiler.BiVerifiedOn` across
    `PassCompiler.comp C₁₂ C₂₃`. -/
theorem PassCompiler.BiVerifiedOn.comp {SemObs : Type}
    {L₁ L₂ L₃ : Language SemObs}
    {C₁₂ : PassCompiler L₁ L₂} {C₂₃ : PassCompiler L₂ L₃}
    {dom pre : L₁.Query → Prop} {post : L₁.Query → L₁.Out → Prop}
    {p₁ : L₁.Prog}
    (h₁₂ : C₁₂.BiVerifiedOn dom pre post p₁)
    (h_def₂₃ : ∀ h : (C₁₂.compile p₁).defined,
      (C₂₃.compile ((C₁₂.compile p₁).val h)).defined)
    (h_comp₂₃ : ∀ (h₁ : (C₁₂.compile p₁).defined)
        (h₂ : (C₂₃.compile ((C₁₂.compile p₁).val h₁)).defined),
      Compiles L₂ L₃ C₂₃.codec
        ((C₁₂.compile p₁).val h₁)
        ((C₂₃.compile ((C₁₂.compile p₁).val h₁)).val h₂) ∧
      L₃.ProductiveOn
        (fun q₃ => pre (C₁₂.codec.decodeQuery (C₂₃.codec.decodeQuery q₃)))
        ((C₂₃.compile ((C₁₂.compile p₁).val h₁)).val h₂)) :
    (PassCompiler.comp C₁₂ C₂₃).BiVerifiedOn dom pre post p₁ := by
  cases h₁₂.1.2 with
  | intro h₁ hc₁ =>
    have h₂ := h_def₂₃ h₁
    exact ⟨⟨h₁₂.1.1, ⟨h₁, h₂⟩, Compiles.comp hc₁ (h_comp₂₃ h₁ h₂).1⟩,
      fun ⟨h₁', h₂'⟩ => (h_comp₂₃ h₁' h₂').2⟩

/-- Canaries verifying vacuity protection across Modes 1 and 2: -/
def canaryRejectingCompiler {SemObs : Type} (L : Language SemObs) :
    PassCompiler L L where
  compile _ := Partial.ub
  codec     := BehaviorCodec.id L

theorem canary_rejecting_compiler_not_verifiedOn {SemObs : Type}
    (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop) (s : L.Prog) :
    ¬ (canaryRejectingCompiler L).VerifiedOn dom pre post s :=
  fun ⟨_, hdef, _⟩ => hdef

theorem canary_rejecting_compiler_not_biVerifiedOn {SemObs : Type}
    (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop) (s : L.Prog) :
    ¬ (canaryRejectingCompiler L).BiVerifiedOn dom pre post s :=
  fun ⟨⟨_, hdef, _⟩, _⟩ => hdef

theorem canary_mode2_rejects_source_ub_even_when_uncompilable {SemObs : Type}
    (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop) (s : L.Prog)
    (q₀ : L.Query) (hpre₀ : pre q₀)
    (hub₀ : ¬ (L.sem s q₀).defined) :
    ¬ (canaryRejectingCompiler L).BiVerifiedIfCompiledOn dom pre post s := by
  intro ⟨⟨_, h_prod, _⟩, _⟩
  cases h_prod q₀ hpre₀ with
  | intro hdef₀ _ => exact hub₀ hdef₀

/-- Kernel WHNF boolean certificate checker (`LRAT`, `Alethe`, `Farkas`, `SOS`,
    `egglog`, `regalloc2` TV) that discharges `L.VerifiedOn` by `rfl` without
    `native_decide`. -/
structure CertChecker {SemObs : Type} (L : Language SemObs) (Cert : Type) where
  check       : L.Prog → Cert → Bool
  dom         : L.Prog → L.Query → Prop
  pre         : L.Prog → L.Query → Prop
  post        : L.Prog → L.Query → L.Out → Prop
  check_sound : ∀ p cert,
    check p cert = true → L.VerifiedOn (dom p) (pre p) (post p) p

namespace Challenger4

/-!
## 1. In-Kernel `StrictUnitTheorem` Completeness (Eliminating `trusted/audit`
   Check 5)
-/

/-- When `waived = []`, the disjunctive obligation check
    `AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))` forces
    every obligation proposition `ob.prop` in `obligations` to hold
    unconditionally. -/
theorem allHold_prop_of_waived_nil {Id : Type} :
    ∀ (obligations : List (Obligation Id)),
      AllHold (obligations.map (fun ob => ob.id ∈ ([] : List Id) ∨ ob.prop)) →
      AllHold (obligations.map Obligation.prop)
  | [], _ => trivial
  | _ :: rest, ⟨h_head, h_tail⟩ =>
      match h_head with
      | .inl h_in => nomatch h_in
      | .inr h_prop => ⟨h_prop, allHold_prop_of_waived_nil rest h_tail⟩

/-- **In-Kernel `StrictUnitTheorem` Completeness Theorem:**
    Any proof of `StrictUnitTheorem u` establishes inside the Lean kernel—
    regardless of `u.policy`—that:
    1. `u.waived = []` (zero obligations are waived),
    2. `u.obligations ≠ []` (the obligation list is non-empty),
    3. `NoDupIds (u.obligations.map Obligation.id)` (all obligation IDs are
       pairwise distinct),
    4. `AllHold (u.obligations.map Obligation.prop)` (every obligation holds
       constructively without waivers), and
    5. `AllHold (u.artifacts.map EmittedArtifact.holds)` (every emitted artifact
       equals its expected disk string). -/
theorem strictUnitTheorem_complete {Id : Type} {u : VerificationUnit Id}
    (h : StrictUnitTheorem u) :
    u.waived = [] ∧
    u.obligations ≠ [] ∧
    NoDupIds (u.obligations.map Obligation.id) ∧
    AllHold (u.obligations.map Obligation.prop) ∧
    AllHold (u.artifacts.map EmittedArtifact.holds) := by
  have h_waived : u.waived = [] := h.2.1
  have h_disj :
      AllHold (u.obligations.map (fun ob => ob.id ∈ u.waived ∨ ob.prop)) :=
    h.1.2.2
  rw [h_waived] at h_disj
  exact ⟨h_waived, h.1.1, h.2.2.1,
    allHold_prop_of_waived_nil u.obligations h_disj, h.2.2.2⟩

/-- Even if `u.policy` permits all waivers (`isAllowed _ := True`),
    `StrictUnitTheorem` rejects any unit with a non-empty `waived` list. -/
theorem strictUnitTheorem_rejects_any_nonempty_waived_list {Id : Type}
    (w : Id) (ws : List Id) (obligations : List (Obligation Id))
    (artifacts : List EmittedArtifact) :
    ¬ StrictUnitTheorem {
        policy      := ⟨fun _ => True⟩
        waived      := w :: ws
        obligations := obligations
        artifacts   := artifacts
      } := by
  intro h
  cases h.2.1

/-!
## 2. Constructor-Gated `Obligation` & End-to-End Artifact Binding
   (`probe_d1` Defense)
-/

/-- End-to-end single-source artifact binding theorem: when `StrictUnitTheorem`
    holds on a unit containing `Obligation.productiveCompiles` and an
    `EmittedArtifact` whose `contents` is `emitTarget t`, the kernel guarantees
    both miracle-free compilation `ProductiveCompiles L_src L_tgt c s t` and
    exact byte identity `emitTarget t = expectedDiskBytes`. -/
theorem strictUnitTheorem_binds_emitted_artifact_to_compiled_target
    {Id SemObs : Type} {L_src L_tgt : Language SemObs}
    (c : BehaviorCodec L_src L_tgt)
    (s : L_src.Prog) (t : L_tgt.Prog)
    (emitTarget : L_tgt.Prog → String)
    (id : Id) (path expectedDiskBytes : String)
    (h_strict : StrictUnitTheorem {
      obligations := [Obligation.productiveCompiles id L_src L_tgt c s t]
      artifacts   := [{
        path     := path
        contents := emitTarget t
        expected := expectedDiskBytes
      }]
    }) :
    ProductiveCompiles L_src L_tgt c s t ∧
    emitTarget t = expectedDiskBytes := by
  have h_comp := strictUnitTheorem_complete h_strict
  exact ⟨h_comp.2.2.2.1.1, h_comp.2.2.2.2.1⟩

/-!
## 3. Structural Domain Locking via `Language.dom` and `Language.withDom`
   (`probe_e3` Defense)
-/

/-- 3-argument `L.Verified` and `L.VerifiedSpine` lock the non-vacuity domain
    to `L.dom`, preventing callers from passing a spoofed `dom` argument at the
    theorem or obligation site. -/
theorem verified_locks_language_dom {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) (prog : L.Prog) :
    L.Verified pre post prog ↔ L.VerifiedOn L.dom pre post prog :=
  ⟨fun h => h, fun h => h⟩

/-- On any language with the default structural domain (`L.dom = fun _ => True`)
    and an inhabited query type (`q₀ : L.Query`), a contradictory precondition
    (`∀ q, ¬ pre q`) is unconditionally rejected by 3-argument `L.Verified`. -/
theorem verified_rejects_contradictory_pre_on_default_dom {SemObs : Type}
    (L : Language SemObs) (q₀ : L.Query) (h_dom : L.dom q₀)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) (prog : L.Prog)
    (h_contra : ∀ q, ¬ pre q) :
    ¬ L.Verified pre post prog := by
  intro h_ver
  cases h_ver.1 with
  | inl hex =>
    cases hex with
    | intro q hq => exact h_contra q hq
  | inr h_no_dom =>
    exact h_no_dom q₀ h_dom

/-- Attaching an uninhabited structural domain (`∀ q, ¬ dom q`, such as
    `BB1.BoundaryDom` for `fn absurd(x: Infallible)`) via `L.withDom dom`
    constructively satisfies 3-argument `(L.withDom dom).Verified` with zero
    waivers. -/
theorem withDom_admits_genuinely_uninhabited_boundary {SemObs : Type}
    (L : Language SemObs) (dom : L.Query → Prop)
    (h_uninhab : ∀ q, ¬ dom q)
    (post : L.Query → L.Out → Prop) (prog : L.Prog) :
    (L.withDom dom).Verified dom post prog :=
  ⟨Or.inr h_uninhab,
   fun q hq => False.elim (h_uninhab q hq),
   fun q hq => False.elim (h_uninhab q hq)⟩

/-!
## 4. The Two-Sided Canary Squeeze & Standalone Human Review Theorem
-/

/-- **Canary Squeeze Lemma 1 (Strict Precondition Inhabitation):**
    If `L.VerifiedWithCanariesOn dom pre post goodProg (badProg :: rest)` holds
    and `∀ q, pre q → dom q` (which holds trivially when
    `dom := fun _ => True`), then `∃ q, pre q` holds constructively!
    Even if an author attempts to spoof `dom := fun _ => False` and
    `pre := fun _ => False`, the `Or.inr (∀ q, ¬ dom q)` disjunct is refuted
    because an empty `pre` would make `badProg` vacuously satisfy `VerifiedOn`,
    contradicting `RefutedOn dom pre post badProg`! -/
theorem verifiedWithCanariesOn_forces_inhabited_pre {SemObs : Type}
    {L : Language SemObs} {dom pre : L.Query → Prop}
    {post : L.Query → L.Out → Prop}
    {goodProg badProg : L.Prog} {rest : List L.Prog}
    (h_can : L.VerifiedWithCanariesOn dom pre post goodProg (badProg :: rest))
    (h_sub : ∀ q, pre q → dom q) :
    ∃ q, pre q := by
  cases h_can.1.1 with
  | inl hex => exact hex
  | inr h_no_dom =>
    have h_bad_ver : L.VerifiedOn dom pre post badProg :=
      ⟨Or.inr h_no_dom,
       fun q hpre => False.elim (h_no_dom q (h_sub q hpre)),
       fun q hpre => False.elim (h_no_dom q (h_sub q hpre))⟩
    exact False.elim (h_can.2.2.1 h_bad_ver)

/-- **Canary Squeeze Lemma 2 (Non-Trivial Postcondition):**
    If `L.VerifiedWithCanariesOn dom pre post goodProg (badProg :: rest)` holds
    and the negative canary `badProg` is productive on `pre`, then `post` cannot
    be trivially true on `pre` (`¬ (∀ q o, pre q → post q o)`). -/
theorem verifiedWithCanariesOn_forces_nontrivial_post {SemObs : Type}
    {L : Language SemObs} {dom pre : L.Query → Prop}
    {post : L.Query → L.Out → Prop}
    {goodProg badProg : L.Prog} {rest : List L.Prog}
    (h_can : L.VerifiedWithCanariesOn dom pre post goodProg (badProg :: rest))
    (h_bad_prod : L.ProductiveOn pre badProg) :
    ¬ (∀ q o, pre q → post q o) := by
  intro h_triv
  have h_bad_spec : L.sem badProg ≤ L.SpecOn pre post := by
    intro q hpre
    cases h_bad_prod q hpre with
    | intro hdef _ =>
      exact ⟨hdef, fun o _ => h_triv q o hpre⟩
  have h_bad_ver : L.VerifiedOn dom pre post badProg :=
    ⟨h_can.1.1, h_bad_prod, h_bad_spec⟩
  exact h_can.2.2.1 h_bad_ver

/-- **Canary Squeeze Lemma 3 (Refutation of `SemObs := Unit` Spine Erasure):**
    If `L.VerifiedSpineWithCanaries pre obsPost goodProg (badProg :: rest)`
    holds and `badProg` is productive on `pre`, then `SemObs` cannot be a
    subsingleton (`¬ (∀ x y : SemObs, x = y)`), and `L.obs` cannot be a
    constant projection (`¬ (∀ o₁ o₂ : L.Out, L.obs o₁ = L.obs o₂)`).
    This closes `EXPLOIT-2` / `GAP-5` inside pure `Prop` without requiring a
    human reviewer to inspect `L.obs`! -/
theorem verifiedSpineWithCanaries_refutes_constant_obs {SemObs : Type}
    {L : Language SemObs} {pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop}
    {goodProg badProg : L.Prog} {rest : List L.Prog}
    (h_can : L.VerifiedSpineWithCanaries pre obsPost goodProg (badProg :: rest))
    (h_bad_prod : L.ProductiveOn pre badProg) :
    ¬ (∀ o₁ o₂ : L.Out, L.obs o₁ = L.obs o₂) := by
  intro h_const_obs
  have h_bad_spec :
      L.sem badProg ≤ L.SpecOn pre (fun q o => obsPost q (L.obs o)) := by
    intro q hpre
    cases h_can.1.2.1 q hpre with
    | intro hdef_good hout_good =>
      cases hout_good with
      | intro o_good ho_good =>
        cases h_can.1.2.2 q hpre with
        | intro _ hpost_good =>
          have h_obs_good : obsPost q (L.obs o_good) :=
            hpost_good o_good ho_good
          cases h_bad_prod q hpre with
          | intro hdef_bad _ =>
            refine ⟨hdef_bad, ?_⟩
            intro o_bad _
            dsimp [Language.SpecOn]
            rw [h_const_obs o_bad o_good]
            exact h_obs_good
  have h_bad_ver :
      L.VerifiedOn L.dom pre (fun q o => obsPost q (L.obs o)) badProg :=
    ⟨h_can.1.1, h_bad_prod, h_bad_spec⟩
  exact h_can.2.2.1 h_bad_ver

/-- Corollary: `VerifiedSpineWithCanaries` with any productive `badProg`
    refutes `SemObs` being a subsingleton (such as `Unit`). -/
theorem verifiedSpineWithCanaries_refutes_subsingleton_semObs {SemObs : Type}
    {L : Language SemObs} {pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop}
    {goodProg badProg : L.Prog} {rest : List L.Prog}
    (h_can : L.VerifiedSpineWithCanaries pre obsPost goodProg (badProg :: rest))
    (h_bad_prod : L.ProductiveOn pre badProg) :
    ¬ (∀ x y : SemObs, x = y) := by
  intro h_sub
  exact verifiedSpineWithCanaries_refutes_constant_obs h_can h_bad_prod
    (fun o₁ o₂ => h_sub (L.obs o₁) (L.obs o₂))

/-- **Flagship Theorem (`standalone_human_review_soundness_and_nonvacuity`):**
    When a human reviewer checks a standalone `lake build` proof of
    `StrictUnitTheorem u` containing:
    - `Obligation.verifiedSpineWithCanaries id₁ L_src pre obsPost s`
      `(badProg :: rest)`
    - `Obligation.productiveCompiles id₂ L_src L_tgt c s t`
    - `EmittedArtifact`
      `{ path, contents := emitTarget t, expected := diskBytes }`
    with `∀ q₁, pre q₁ → L_src.dom q₁` and productive mutant `badProg`, the Lean
    kernel guarantees all seven end-to-end properties simultaneously:
    1. `u.waived = []` (zero waivers),
    2. `∃ q₁, pre q₁` (strictly inhabited precondition),
    3. `¬ (∀ q₁ o₁, pre q₁ → obsPost q₁ (L_src.obs o₁))` (non-trivial spec),
    4. `¬ (∀ o₁ o₂ : L_src.Out, L_src.obs o₁ = L_src.obs o₂)` (non-constant
       observable spine `L_src.obs`),
    5. `∀ q₁, pre q₁ → ∃ h₂ o₂, (L_tgt.sem t (c.encodeQuery q₁)).val h₂ o₂`
       (miracle-free target productivity on all encoded valid inputs),
    6. `L_tgt.sem t ≤ L_tgt.SpineSpecOn (fun q₂ => pre (c.decodeQuery q₂))`
       `(fun q₂ sObs => obsPost (c.decodeQuery q₂) sObs)`
       (direct spine specification transfer to the target program `t`), and
    7. `emitTarget t = diskBytes` (exact artifact byte binding). -/
theorem standalone_human_review_soundness_and_nonvacuity
    {Id SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (c : BehaviorCodec L_src L_tgt)
    (pre : L_src.Query → Prop)
    (obsPost : L_src.Query → SemObs → Prop)
    (s badProg : L_src.Prog) (rest : List L_src.Prog)
    (t : L_tgt.Prog)
    (emitTarget : L_tgt.Prog → String)
    (id₁ id₂ : Id) (path diskBytes : String)
    (policy : TrustPolicy Id) (waived : List Id)
    (h_dom : ∀ q₁, pre q₁ → L_src.dom q₁)
    (h_bad_prod : L_src.ProductiveOn pre badProg)
    (h_strict : StrictUnitTheorem {
      policy      := policy
      waived      := waived
      obligations := [
        Obligation.verifiedSpineWithCanaries
          id₁ L_src pre obsPost s (badProg :: rest),
        Obligation.productiveCompiles id₂ L_src L_tgt c s t
      ]
      artifacts   := [{
        path     := path
        contents := emitTarget t
        expected := diskBytes
      }]
    }) :
    waived = [] ∧
    (∃ q₁, pre q₁) ∧
    ¬ (∀ q₁ o₁, pre q₁ → obsPost q₁ (L_src.obs o₁)) ∧
    ¬ (∀ o₁ o₂ : L_src.Out, L_src.obs o₁ = L_src.obs o₂) ∧
    (∀ q₁, pre q₁ →
      ∃ h₂ : (L_tgt.sem t (c.encodeQuery q₁)).defined,
        ∃ o₂, (L_tgt.sem t (c.encodeQuery q₁)).val h₂ o₂) ∧
    (L_tgt.sem t ≤
      L_tgt.SpineSpecOn
        (fun q₂ => pre (c.decodeQuery q₂))
        (fun q₂ sObs => obsPost (c.decodeQuery q₂) sObs)) ∧
    emitTarget t = diskBytes := by
  have h_comp := strictUnitTheorem_complete h_strict
  have h_waived : waived = [] := h_comp.1
  have h_can :
      L_src.VerifiedSpineWithCanaries pre obsPost s (badProg :: rest) :=
    h_comp.2.2.2.1.1
  have h_pcomp : ProductiveCompiles L_src L_tgt c s t :=
    h_comp.2.2.2.1.2.1
  have h_art : emitTarget t = diskBytes :=
    h_comp.2.2.2.2.1
  have h_inhab : ∃ q₁, pre q₁ :=
    verifiedWithCanariesOn_forces_inhabited_pre h_can h_dom
  have h_nontriv : ¬ (∀ q₁ o₁, pre q₁ → obsPost q₁ (L_src.obs o₁)) :=
    verifiedWithCanariesOn_forces_nontrivial_post h_can h_bad_prod
  have h_nonconst_obs : ¬ (∀ o₁ o₂ : L_src.Out, L_src.obs o₁ = L_src.obs o₂) :=
    verifiedSpineWithCanaries_refutes_constant_obs h_can h_bad_prod
  have h_tgt_prod :
      ∀ q₁, pre q₁ →
        ∃ h₂ : (L_tgt.sem t (c.encodeQuery q₁)).defined,
          ∃ o₂, (L_tgt.sem t (c.encodeQuery q₁)).val h₂ o₂ :=
    fun q₁ hpre₁ => h_pcomp.2 q₁ (h_can.1.2.1 q₁ hpre₁)
  have h_tgt_spine :
      L_tgt.sem t ≤
        L_tgt.SpineSpecOn
          (fun q₂ => pre (c.decodeQuery q₂))
          (fun q₂ sObs => obsPost (c.decodeQuery q₂) sObs) :=
    compiles_transfers_spineSpecOn_directly h_can.1.2.2 h_pcomp.1
  exact ⟨h_waived, h_inhab, h_nontriv, h_nonconst_obs,
    h_tgt_prod, h_tgt_spine, h_art⟩

/-- Concrete instantiation of the Standalone Human Review workflow:
    - `goodProg = true` computes `q + 1`,
    - `badProg = false` is an off-by-one mutant computing `q`,
    - `emitDemoAsm` renders the target program to `"add eax, 1\nret"`, and
    - `StrictUnitTheorem` proves both obligations and binds `"inc.s"`. -/
abbrev StandaloneDemoLang : Language Nat :=
  Language.mkSimple Bool Nat Nat (fun isGood q =>
    Partial.pure (fun out => out = if isGood then q + 1 else q))

def emitDemoAsm (isGood : Bool) : String :=
  if isGood then "add eax, 1\nret" else "ret"

def demoStandaloneUnit : VerificationUnit String where
  obligations := [
    Obligation.verifiedSpineWithCanaries "spec_inc"
      StandaloneDemoLang (fun q => q < 100) (fun q out => out = q + 1)
      true [false],
    Obligation.productiveCompiles "compile_inc"
      StandaloneDemoLang StandaloneDemoLang
      (BehaviorCodec.id StandaloneDemoLang)
      true true
  ]
  artifacts := [{
    path     := "inc.s"
    contents := emitDemoAsm true
    expected := "add eax, 1\nret"
  }]

theorem demoStandaloneUnit_strict : StrictUnitTheorem demoStandaloneUnit := by
  refine ⟨⟨(by intro h; cases h), trivial, ?_, ?_, trivial⟩,
    rfl, ?_, ⟨rfl, trivial⟩⟩
  · refine Or.inr
      ⟨⟨Or.inl ⟨0, by decide⟩, ?_, ?_⟩, (by intro h; cases h), ?_, trivial⟩
    · intro q _
      exact ⟨trivial, q + 1, rfl⟩
    · intro q _
      exact ⟨trivial, fun _ ho => ho⟩
    · intro h_bad
      have h0_lt : (0 : Nat) < 100 := by decide
      cases h_bad.2.2 0 h0_lt with
      | intro _ hpost =>
        have h01 : (0 : Nat) = 0 + 1 := hpost 0 rfl
        cases h01
  · refine Or.inr ⟨Compiles.refl StandaloneDemoLang true, ?_⟩
    intro q hprod
    exact hprod
  · exact ⟨⟨by decide, trivial⟩, trivial, trivial⟩

end Challenger4

/-!
## 5. Zero-Tax Total & Partial `BB8.PassCompiler` Orthogonality Witnesses
-/

section PartialAndTotalPassCompilerOrthogonality


/-- Minimal deterministic language over `Nat` via `Language.mkSimple` (modeling
    `BB7.Language.ofDenotational` with zero `BB1`–`BB6` imports). -/
abbrev NatDenotLang : Language Nat :=
  Language.mkSimple Nat Nat Nat (fun prog q =>
    if prog < 100 then
      Partial.pure (fun out => out = q + prog)
    else
      Partial.ub)

/-- Total constant-folding pass (`PassCompiler.ofTotal`) with zero `Option` or
    PME tax. -/
def totalIdCompiler : PassCompiler NatDenotLang NatDenotLang :=
  PassCompiler.ofTotal (fun prog => prog) (BehaviorCodec.id NatDenotLang)

/-- Computable partial backend pass (`PassCompiler.ofOption`) that accepts
    programs with immediate `< 50` and rejects programs with immediate `≥ 50`
    at compile time (`none`). -/
def boundedImmCompiler : PassCompiler NatDenotLang NatDenotLang :=
  PassCompiler.ofOption
    (fun prog => if prog < 50 then some prog else none)
    (BehaviorCodec.id NatDenotLang)

/-- Composed two-stage pipeline (`Total` Stage 1 $\circ$ `Partial` Stage 2) via
    `PassCompiler.comp`. -/
def totalThenPartialPipeline : PassCompiler NatDenotLang NatDenotLang :=
  PassCompiler.comp totalIdCompiler boundedImmCompiler

/-- Definitional reduction witness: on an accepted program (`prog = 10`),
    `totalThenPartialPipeline.compileVal 10` reduces by `rfl` to `10` with zero
    explicit proof arguments (`⟨trivial, trivial⟩` is discharged
    automatically). -/
theorem totalThenPartial_compileVal_10_rfl :
    totalThenPartialPipeline.compileVal 10 = 10 :=
  rfl

theorem natProg10_verifiedOn :
    NatDenotLang.VerifiedInhabitedOn
      (fun _ => True)
      (fun q out => out = q + 10)
      10 := by
  refine ⟨Or.inl ⟨0, trivial⟩, ?_, ?_⟩
  · intro q _
    exact ⟨trivial, q + 10, rfl⟩
  · intro q _
    exact ⟨trivial, fun _ hout => hout⟩

/-- **Orthogonality Witness 1 (Zero-Tax Total `BiVerifiedOn`):**
    A total compiler lifted via `PassCompiler.ofTotal` satisfies two-sided
    `BiVerifiedOn` (`BiVerifiedTotalOn`) with zero `Option`, PME, or waiver
    overhead. -/
theorem totalIdCompiler_biVerifiedOn_10 :
    totalIdCompiler.BiVerifiedOn
      (fun _ => True)
      (fun _ => True)
      (fun q out => out = q + 10)
      10 := by
  refine ⟨⟨natProg10_verifiedOn, trivial, Compiles.refl NatDenotLang 10⟩, ?_⟩
  intro _ q _
  exact ⟨trivial, q + 10, rfl⟩

/-- **Orthogonality Witness 2 (Total $\circ$ Partial Pipeline `BiVerifiedOn`
    on Accepted Program `10`):** -/
theorem totalThenPartial_biVerifiedOn_10 :
    totalThenPartialPipeline.BiVerifiedOn
      (fun _ => True)
      (fun _ => True)
      (fun q out => out = q + 10)
      10 := by
  refine PassCompiler.BiVerifiedOn.comp totalIdCompiler_biVerifiedOn_10
    (fun _ => trivial) ?_
  intro _ _
  refine ⟨Compiles.refl NatDenotLang 10, ?_⟩
  intro q _
  exact ⟨trivial, q + 10, rfl⟩

/-- Target soundness for `totalThenPartialPipeline` on `10` with `h_def`
    discharged automatically by `h.defined`. -/
theorem totalThenPartial_target_sound_10 :
    NatDenotLang.sem (totalThenPartialPipeline.compileVal 10) ≤
      totalThenPartialPipeline.codec.toMorphism
        (NatDenotLang.SpecOn (fun _ => True) (fun q out => out = q + 10)) :=
  proof_gated_pipeline_sound
    totalThenPartialPipeline
    totalThenPartial_biVerifiedOn_10.1

/-- **Orthogonality Witness 3 (Clean Compile-Time Rejection on `prog = 60`):**
    Program `60` is safe at the source level (`60 < 100`), but rejected by
    `boundedImmCompiler` (`60 ≮ 50`). It satisfies Mode 2
    (`VerifiedIfCompiledOn`) with zero waivers, while refuting Mode 1
    (`VerifiedOn` / `VerifiedTotalOn`). -/
theorem totalThenPartial_rejected_60_verifiedIfCompiledOn_and_not_verifiedOn :
    totalThenPartialPipeline.VerifiedIfCompiledOn
      (fun _ => True)
      (fun _ => True)
      (fun q out => out = q + 60)
      60 ∧
    ¬ totalThenPartialPipeline.VerifiedOn
      (fun _ => True)
      (fun _ => True)
      (fun q out => out = q + 60)
      60 := by
  have h_not_def : ¬ (totalThenPartialPipeline.compile 60).defined := by
    intro ⟨_, h₂⟩
    exact h₂
  refine ⟨?_, ?_⟩
  · refine ⟨⟨Or.inl ⟨0, trivial⟩, ?_, ?_⟩, ?_⟩
    · intro q _
      exact ⟨trivial, q + 60, rfl⟩
    · intro q _
      exact ⟨trivial, fun _ hout => hout⟩
    · intro hdef
      exact False.elim (h_not_def hdef)
  · intro ⟨_, hdef, _⟩
    exact h_not_def hdef

/-- **Orthogonality Witness 4 (Mode 2 `VerifiedIfCompiledOn` Rejects Source UB
    Even When Rejected at Compile Time):**
    Program `150` has source UB (`150 ≮ 100`) and is also rejected by
    `totalThenPartialPipeline` (`150 ≮ 50`). Mode 2 (`VerifiedIfCompiledOn`)
    rejects `150` because source verification is unguarded! -/
theorem totalThenPartial_mode2_rejects_source_ub_150 :
    ¬ totalThenPartialPipeline.VerifiedIfCompiledOn
      (fun _ => True)
      (fun _ => True)
      (fun _ _ => True)
      150 := by
  intro hver
  cases hver.1.2.1 0 trivial with
  | intro hdef _ =>
    exact hdef

end PartialAndTotalPassCompilerOrthogonality

/-!
## 6. Zero-Tax `Language.Verified`, `Language.withDom`, `Obligation` Smart
   Constructors, and `StrictUnitTheorem` Orthogonality Witnesses
-/

section Pass2AuditInFrameworkOrthogonality


/-- Zero-tax constructor for `StrictUnitTheorem` on waiver-free verification
    units (`u.waived = []`): automatically discharges `u.obligations ≠ []`,
    `AllHold (u.waived.map u.policy.isAllowed)`, `u.waived = []`, `NoDupIds`,
    and `AllHold (u.artifacts.map EmittedArtifact.holds)`, requiring only the
    obligation proofs `h_obs`. -/
theorem StrictUnitTheorem.of_obligations {Id : Type} (u : VerificationUnit Id)
    (h_obs : AllHold (u.obligations.map (fun ob => ob.id ∈ u.waived ∨ ob.prop)))
    (h_nonempty : u.obligations ≠ [] := by decide)
    (h_policy : AllHold (u.waived.map u.policy.isAllowed) := by
      repeat (first | trivial | assumption | refine ⟨?_, ?_⟩ | decide))
    (h_waived : u.waived = [] := by rfl)
    (h_nodup : NoDupIds (u.obligations.map Obligation.id) := by
      repeat (first | trivial | assumption | refine ⟨?_, ?_⟩ | decide))
    (h_art : AllHold (u.artifacts.map EmittedArtifact.holds) := by
      repeat (first | trivial | assumption | refine ⟨?_, ?_⟩ | decide)) :
    StrictUnitTheorem u :=
  ⟨⟨h_nonempty, h_policy, h_obs⟩, h_waived, h_nodup, h_art⟩

/-- **Orthogonality Witness 6.1 (Zero Universe Lift):**
    Because `Obligation (Id : Type)` uses `private mk ::` rather than an
    existential `inductive Claim : Type 1` over `Language SemObs : Type 1`,
    both `Obligation Id` and `VerificationUnit Id` remain in `Type`
    (`Type 0`). -/
def obligationAndUnitStayInTypeZero (Id : Type) : Type :=
  Obligation Id × VerificationUnit Id

/-- Minimal deterministic language over `Nat` via `Language.mkSimple` (default
    `dom := fun _ => True`). -/
abbrev SimpleAddLang : Language Nat :=
  Language.mkSimple Nat Nat Nat (fun prog q =>
    if prog < 100 then
      Partial.pure (fun out => out = q + prog)
    else
      Partial.ub)

/-- **Orthogonality Witness 6.2
    (`Language.Verified = VerifiedInhabitedOn` by `rfl`):**
    When a language `L` uses the default `dom : Query → Prop := fun _ => True`
    (including `Language.mkSimple`, `SmallStepMachine.toLanguage`,
    `BB7.Language.ofDenotational`, and `BB7.Language.ofRelation`), 3-argument
    `L.Verified pre post prog` is judgmentally equal (`rfl`) to
    `L.VerifiedInhabitedOn pre post prog` and to
    `L.VerifiedOn (fun _ => True) pre post prog`. -/
theorem verified_eq_verifiedInhabitedOn_rfl
    (pre : Nat → Prop) (post : Nat → Nat → Prop) (prog : Nat) :
    SimpleAddLang.Verified pre post prog =
      SimpleAddLang.VerifiedInhabitedOn pre post prog :=
  rfl

/-- **Orthogonality Witness 6.3
    (`Language.VerifiedSpine = Verified` on `mkSimple` by `rfl`):**
    When `L` is constructed via `Language.mkSimple` (`obs := id`), 3-argument
    `L.VerifiedSpine pre post prog` is judgmentally equal (`rfl`) to
    `L.Verified pre post prog`. -/
theorem verifiedSpine_eq_verified_on_mkSimple_rfl
    (pre : Nat → Prop) (post : Nat → Nat → Prop) (prog : Nat) :
    SimpleAddLang.VerifiedSpine pre post prog =
      SimpleAddLang.Verified pre post prog :=
  rfl

/-- **Orthogonality Witness 6.4
    (`(L.withDom dom).Verified = L.VerifiedOn dom` by `rfl`):**
    Attaching an explicit domain `dom` to `L` via `L.withDom` makes
    `(L.withDom dom).Verified pre post prog` judgmentally equal (`rfl`) to
    `L.VerifiedOn dom pre post prog`. -/
theorem withDom_verified_eq_verifiedOn_rfl
    {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop) (prog : L.Prog) :
    (L.withDom dom).Verified pre post prog =
      L.VerifiedOn dom pre post prog :=
  rfl

/-- **Orthogonality Witness 6.5 (Definitional `rfl` Projections for `Obligation`
    Smart Constructors):**
    Every `@[vetted]` smart constructor on `Obligation` projects `.id` and
    `.prop` judgmentally by `rfl` with zero `Claim.toProp` match unfolding. -/
theorem obligation_smart_constructors_proj_rfl :
    (Obligation.verified "add_10" SimpleAddLang
      (fun _ => True) (fun q out => out = q + 10) 10).id = "add_10" ∧
    (Obligation.verified "add_10" SimpleAddLang
      (fun _ => True) (fun q out => out = q + 10) 10).prop =
      SimpleAddLang.Verified (fun _ => True) (fun q out => out = q + 10) 10 ∧
    (Obligation.refuted "ub_150" SimpleAddLang
      (fun _ => True) (fun q out => out = q + 10) 150).prop =
      SimpleAddLang.Refuted (fun _ => True) (fun q out => out = q + 10) 150 :=
  ⟨rfl, rfl, rfl⟩

theorem simpleAdd10_verified :
    SimpleAddLang.Verified (fun _ => True) (fun q out => out = q + 10) 10 := by
  refine ⟨Or.inl ⟨0, trivial⟩, ?_, ?_⟩
  · intro q _
    exact ⟨trivial, q + 10, rfl⟩
  · intro q _
    exact ⟨trivial, fun _ hout => hout⟩

theorem simpleAdd150_refuted :
    SimpleAddLang.Refuted (fun _ => True) (fun q out => out = q + 10) 150 := by
  intro hver
  cases hver.2.1 0 trivial with
  | intro hdef _ => exact hdef

theorem simpleAdd20_wrong_val_refuted :
    SimpleAddLang.Refuted (fun _ => True) (fun q out => out = q + 10) 20 := by
  intro hver
  cases hver.2.2 0 trivial with
  | intro _ hpost =>
    have h20 : 20 = 0 + 10 := hpost 20 rfl
    revert h20
    decide

/-- **Orthogonality Witness 6.6 (Two-Sided `VerifiedSpineWithCanaries`
    Squeeze):**
    Proves in a single 3-argument judgment that `prog = 10` satisfies the spine
    specification while `prog = 150` (UB) and `prog = 20` (wrong return value)
    are both refuted. -/
theorem simpleAdd10_verifiedSpineWithCanaries :
    SimpleAddLang.VerifiedSpineWithCanaries
      (fun _ => True)
      (fun q out => out = q + 10)
      10
      [150, 20] :=
  ⟨simpleAdd10_verified, by decide,
   simpleAdd150_refuted, simpleAdd20_wrong_val_refuted, trivial⟩

/-- Standalone `VerificationUnit` constructed purely with `Obligation` smart
    constructors (`verifiedSpineWithCanaries` and `refuted`) and zero
    waivers. -/
def standaloneOrthoUnit : VerificationUnit String where
  obligations := [
    Obligation.verifiedSpineWithCanaries "add_10_two_sided" SimpleAddLang
      (fun _ => True) (fun q out => out = q + 10) 10 [150, 20],
    Obligation.refuted "canary_ub_150" SimpleAddLang
      (fun _ => True) (fun q out => out = q + 10) 150
  ]

/-- **Orthogonality Witness 6.7 (One-Line `StrictUnitTheorem` via
    `StrictUnitTheorem.of_obligations`):**
    Discharges `obligations ≠ []`, `AllHold (waived.map policy.isAllowed)`,
    `waived = []`, `NoDupIds`, and
    `AllHold (artifacts.map EmittedArtifact.holds)` automatically by default
    tactics, requiring only the obligation proofs! -/
theorem standaloneOrthoUnit_strictUnitTheorem :
    StrictUnitTheorem standaloneOrthoUnit :=
  StrictUnitTheorem.of_obligations standaloneOrthoUnit
    ⟨Or.inr simpleAdd10_verifiedSpineWithCanaries,
     Or.inr simpleAdd150_refuted,
     trivial⟩

end Pass2AuditInFrameworkOrthogonality

end Anneal
