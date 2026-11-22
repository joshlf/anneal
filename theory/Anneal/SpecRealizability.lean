-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Trusted

/-!
# Specification Realizability, Postcondition Dichotomy, and Vacuity Analysis

This module provides:

1. **Frozen 5-Class Cross-Language Vacuity Taxonomy** (`VacuityClass`), shared between
   Lean static realizability analysis and the Rust dynamic contract checker.
2. **Part I — Pure Kernel Realizability, Dichotomy, Mutant-Kill & Observation-Fibre
   Calculus**:
   - Generic relational obligations (`PreconditionSatisfiable`, `ContractRealizable`,
     `UniversalContractRealizable`, `PostconditionDichotomy`,
     `PointwisePostconditionDichotomy`, `ContractDeterministicOn`,
     `ContractDeterministic`, `OutputInsensitive`, `DichotomyModuloObservation`,
     `MutantKilledBySpec`).
   - Core hierarchy, mutant-kill, vacuity-refutation, monotonicity, and product
     composition theorems (zero `MetaM` dependency, zero `sorry`, zero `native_decide`,
     axioms strictly in `{propext, Classical.choice, Quot.sound}`).
   - Specializations for `Trusted.VerificationResult` claims (`Claim`, `StatefulClaim`,
     `TotalClaim`, `ModularClaim`, `NonVacuousPre`, `NonVacuousStatefulPre`) and
     `MirCallContract` / `externalSpecCallContract`, including the three external-spec
     soundness traps and `MirCallContract.holdsOn` handler bridges.
3. **Part II — `MetaM` Structural + Bounded-Probe Vacuity Checker**:
   - Structurally terminating (fuel-bounded, zero `partial`/`unsafe`), heartbeat-capped
     (`cappedHeartbeats?`, never passing `0`), message-log-isolated `MetaM` analyzer
     (`checkEnsuresBindsOutput`, `checkDeclEnsuresBindsOutput`,
     `checkRequiresSatisfiable`, `assertEnsuresBindsOutput`, `assertEnsuresVacuous`).
-/

namespace Anneal.SpecRealizability

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Layout
open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.VerificationResult

/-! ## Frozen 5-Class Cross-Language Vacuity Taxonomy -/

/-- Frozen 5-class cross-language specification vacuity taxonomy shared across
    Lean static realizability checks and the Rust dynamic contract checker. -/
inductive VacuityClass : Type where
  | deadPrecondition
  | specViolation
  | trivialPostcondition
  | unboundReturnOutput
  | survivedAllMutants
  deriving DecidableEq, Repr, Inhabited

/-- Canonical wire and diagnostic name for each `VacuityClass`. -/
def VacuityClass.canonicalName : VacuityClass → String
  | .deadPrecondition => "DeadPrecondition"
  | .specViolation => "SpecViolation"
  | .trivialPostcondition => "TrivialPostcondition"
  | .unboundReturnOutput => "UnboundReturnOutput"
  | .survivedAllMutants => "SurvivedAllMutants"

/-- `VacuityClass.canonicalName` is injective across all 5 variants. -/
theorem VacuityClass.canonicalName_injective {a b : VacuityClass}
    (h : a.canonicalName = b.canonicalName) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [VacuityClass.canonicalName] at h)

/-! ## Part I — Pure Kernel Realizability, Dichotomy, Mutant-Kill & Observation-Fibre Calculus -/

section PureCalculus

universe u v w u₁ u₂ v₁ v₂

/-! ### 1. Generic Relational Obligations -/

/-- Precondition `pre` admits at least one valid input witness. -/
def PreconditionSatisfiable {X : Type u} (pre : X → Prop) : Prop :=
  ∃ x, pre x

/-- Contract `(pre, post)` admits at least one valid input and satisfying output. -/
def ContractRealizable {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ∃ x, pre x ∧ ∃ y, post x y

/-- Contract `(pre, post)` has a satisfiable precondition and every valid input
    admits at least one satisfying output. -/
def UniversalContractRealizable {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  PreconditionSatisfiable pre ∧ ∀ x, pre x → ∃ y, post x y

/-- Contract `(pre, post)` is nontrivial: some valid input admits both an accepted
    output `y_ok` and a rejected output `y_bad`. -/
def PostconditionDichotomy {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ∃ x, pre x ∧ (∃ y_ok, post x y_ok) ∧ (∃ y_bad, ¬ post x y_bad)

/-- Contract `(pre, post)` has a satisfiable precondition and every valid input
    admits both an accepted output and a rejected output. -/
def PointwisePostconditionDichotomy {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  PreconditionSatisfiable pre ∧
    ∀ x, pre x → (∃ y_ok, post x y_ok) ∧ (∃ y_bad, ¬ post x y_bad)

/-- Postcondition `post` uniquely determines observation `obs y` for every input
    satisfying `pre`. -/
def ContractDeterministicOn {X : Type u} {Y : Type v} {Z : Type w}
    (obs : Y → Z) (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ∀ x y₁ y₂, pre x → post x y₁ → post x y₂ → obs y₁ = obs y₂

/-- Postcondition `post` uniquely determines the output value `y` on every input
    satisfying `pre`. -/
def ContractDeterministic {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ContractDeterministicOn id pre post

/-- Postcondition `post` cannot distinguish any two outputs under `pre`. -/
def OutputInsensitive {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ∀ x, pre x → ∀ y₁ y₂, post x y₁ ↔ post x y₂

/-- Postcondition `post` achieves dichotomy within a single observation fibre of `obs`,
    ruling out vacuous dichotomy caused solely by differing `obs` boilerplate values. -/
def DichotomyModuloObservation {X : Type u} {Y : Type v} {Z : Type w}
    (obs : X → Y → Z) (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ∃ x, pre x ∧ ∃ y_ok y_bad,
    obs x y_ok = obs x y_bad ∧ post x y_ok ∧ ¬ post x y_bad

/-- Concrete mutant witness: on valid input `x`, `y_ok` satisfies `post`, while the
    distinct mutant output `y_bad ≠ y_ok` is rejected by `post`. -/
def MutantKilledBySpec {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) (x : X) (y_ok y_bad : Y) : Prop :=
  pre x ∧ y_bad ≠ y_ok ∧ post x y_ok ∧ ¬ post x y_bad

/-! ### 2. Core Hierarchy, Mutant-Kill, Vacuity-Refutation & Composition Theorems -/

theorem ContractRealizable.preconditionSatisfiable
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : ContractRealizable pre post) : PreconditionSatisfiable pre := by
  rcases h with ⟨x, hPre, _⟩
  exact ⟨x, hPre⟩

theorem UniversalContractRealizable.preconditionSatisfiable
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : UniversalContractRealizable pre post) : PreconditionSatisfiable pre :=
  h.1

theorem UniversalContractRealizable.contractRealizable
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : UniversalContractRealizable pre post) : ContractRealizable pre post := by
  rcases h with ⟨⟨x, hPre⟩, hAll⟩
  exact ⟨x, hPre, hAll x hPre⟩

theorem PostconditionDichotomy.contractRealizable
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : PostconditionDichotomy pre post) : ContractRealizable pre post := by
  rcases h with ⟨x, hPre, hOk, _⟩
  exact ⟨x, hPre, hOk⟩

theorem PostconditionDichotomy.preconditionSatisfiable
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : PostconditionDichotomy pre post) : PreconditionSatisfiable pre :=
  h.contractRealizable.preconditionSatisfiable

theorem PointwisePostconditionDichotomy.universalContractRealizable
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : PointwisePostconditionDichotomy pre post) :
    UniversalContractRealizable pre post :=
  ⟨h.1, fun x hPre => (h.2 x hPre).1⟩

theorem PointwisePostconditionDichotomy.postconditionDichotomy
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : PointwisePostconditionDichotomy pre post) :
    PostconditionDichotomy pre post := by
  rcases h with ⟨⟨x, hPre⟩, hAll⟩
  exact ⟨x, hPre, hAll x hPre⟩

theorem DichotomyModuloObservation.postconditionDichotomy
    {X : Type u} {Y : Type v} {Z : Type w}
    {obs : X → Y → Z} {pre : X → Prop} {post : X → Y → Prop}
    (h : DichotomyModuloObservation obs pre post) :
    PostconditionDichotomy pre post := by
  rcases h with ⟨x, hPre, y_ok, y_bad, _, hOk, hBad⟩
  exact ⟨x, hPre, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩

theorem postconditionDichotomy_iff_dichotomyModuloObservation_const
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop} :
    PostconditionDichotomy pre post ↔
      DichotomyModuloObservation (fun (_ : X) (_ : Y) => PUnit.unit) pre post := by
  constructor
  · rintro ⟨x, hPre, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩
    exact ⟨x, hPre, y_ok, y_bad, rfl, hOk, hBad⟩
  · exact DichotomyModuloObservation.postconditionDichotomy

/-- Postcondition dichotomy is equivalent to the existence of at least one killed mutant. -/
theorem postconditionDichotomy_iff_exists_killed_mutant
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop} :
    PostconditionDichotomy pre post ↔
      ∃ x y_ok y_bad, MutantKilledBySpec pre post x y_ok y_bad := by
  constructor
  · rintro ⟨x, hPre, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩
    refine ⟨x, y_ok, y_bad, hPre, ?_, hOk, hBad⟩
    intro hEq
    exact hBad (hEq ▸ hOk)
  · rintro ⟨x, y_ok, y_bad, hPre, _, hOk, hBad⟩
    exact ⟨x, hPre, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩

/-- Under `UniversalContractRealizable`, observational determinism holds iff the
    postcondition kills every mutant whose observation differs from an accepted output. -/
theorem contractDeterministicOn_iff_kills_every_obs_nonequivalent_mutant
    {X : Type u} {Y : Type v} {Z : Type w}
    {obs : Y → Z} {pre : X → Prop} {post : X → Y → Prop}
    (_hReal : UniversalContractRealizable pre post) :
    ContractDeterministicOn obs pre post ↔
      ∀ x y_ok y_bad,
        pre x → post x y_ok → obs y_bad ≠ obs y_ok → ¬ post x y_bad := by
  constructor
  · intro hDet x y_ok y_bad hPre hOk hNe hBad
    exact hNe (hDet x y_bad y_ok hPre hBad hOk)
  · intro hKill x y₁ y₂ hPre h1 h2
    exact Classical.byContradiction fun hNe =>
      hKill x y₁ y₂ hPre h1 (Ne.symm hNe) h2

/-- A universally realizable contract that is deterministic on an observation with no
    isolated values satisfies pointwise postcondition dichotomy. -/
theorem pointwisePostconditionDichotomy_of_deterministicOn
    {X : Type u} {Y : Type v} {Z : Type w}
    {obs : Y → Z} {pre : X → Prop} {post : X → Y → Prop}
    (hReal : UniversalContractRealizable pre post)
    (hDet : ContractDeterministicOn obs pre post)
    (hNontriv : ∀ y : Y, ∃ y' : Y, obs y' ≠ obs y) :
    PointwisePostconditionDichotomy pre post := by
  refine ⟨hReal.1, fun x hPre => ?_⟩
  rcases hReal.2 x hPre with ⟨y_ok, hOk⟩
  rcases hNontriv y_ok with ⟨y_bad, hNe⟩
  refine ⟨⟨y_ok, hOk⟩, ⟨y_bad, ?_⟩⟩
  intro hBad
  exact hNe (hDet x y_bad y_ok hPre hBad hOk)

/-- Functional specifications `post x y := y = f x` are always deterministic. -/
theorem contractDeterministic_of_function
    {X : Type u} {Y : Type v} (pre : X → Prop) (f : X → Y) :
    ContractDeterministic pre (fun x y => y = f x) := by
  intro x y₁ y₂ _ h1 h2
  exact h1.trans h2.symm

/-- Functional specifications `post x y := y = f x` satisfy dichotomy whenever `pre` is
    satisfiable and `Y` has at least two distinct elements. -/
theorem postconditionDichotomy_of_function
    {X : Type u} {Y : Type v} {pre : X → Prop} (f : X → Y)
    (hPre : PreconditionSatisfiable pre)
    (hTwo : ∃ y₁ y₂ : Y, y₁ ≠ y₂) :
    PostconditionDichotomy pre (fun x y => y = f x) := by
  rcases hPre with ⟨x, hx⟩
  rcases hTwo with ⟨y₁, y₂, hNe⟩
  refine ⟨x, hx, ⟨f x, rfl⟩, ?_⟩
  by_cases h1 : y₁ = f x
  · refine ⟨y₂, ?_⟩
    intro h2
    exact hNe (h1.trans h2.symm)
  · exact ⟨y₁, h1⟩

/-! ### 3. Vacuity Refutations -/

theorem not_contractRealizable_of_unsat_pre
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hUnsat : ¬ PreconditionSatisfiable pre) :
    ¬ ContractRealizable pre post :=
  fun hReal => hUnsat hReal.preconditionSatisfiable

theorem not_postconditionDichotomy_of_unsat_pre
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hUnsat : ¬ PreconditionSatisfiable pre) :
    ¬ PostconditionDichotomy pre post :=
  fun hDich => hUnsat hDich.preconditionSatisfiable

theorem not_postconditionDichotomy_of_trivial
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hTriv : ∀ x y, pre x → post x y) :
    ¬ PostconditionDichotomy pre post := by
  rintro ⟨x, hPre, _, ⟨y_bad, hNot⟩⟩
  exact hNot (hTriv x y_bad hPre)

theorem not_postconditionDichotomy_of_impossible
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hImp : ∀ x y, pre x → ¬ post x y) :
    ¬ PostconditionDichotomy pre post := by
  rintro ⟨x, hPre, ⟨y_ok, hOk⟩, _⟩
  exact hImp x y_ok hPre hOk

theorem not_postconditionDichotomy_of_outputInsensitive
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hInsens : OutputInsensitive pre post) :
    ¬ PostconditionDichotomy pre post := by
  rintro ⟨x, hPre, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩
  exact hBad ((hInsens x hPre y_ok y_bad).mp hOk)

theorem not_postconditionDichotomy_of_subsingleton
    {X : Type u} {Y : Type v} [Subsingleton Y]
    {pre : X → Prop} {post : X → Y → Prop} :
    ¬ PostconditionDichotomy pre post := by
  rintro ⟨x, _, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩
  exact hBad (Subsingleton.elim y_ok y_bad ▸ hOk)

theorem not_dichotomyModuloObservation_of_fibre_insensitive
    {X : Type u} {Y : Type v} {Z : Type w}
    {obs : X → Y → Z} {pre : X → Prop} {post : X → Y → Prop}
    (hInsens : ∀ x y₁ y₂, pre x → obs x y₁ = obs x y₂ → (post x y₁ ↔ post x y₂)) :
    ¬ DichotomyModuloObservation obs pre post := by
  rintro ⟨x, hPre, y_ok, y_bad, hObsEq, hOk, hBad⟩
  exact hBad ((hInsens x y_ok y_bad hPre hObsEq).mp hOk)

theorem not_postconditionDichotomy_of_post_true
    {X : Type u} {Y : Type v} (pre : X → Prop) :
    ¬ PostconditionDichotomy pre (fun (_ : X) (_ : Y) => True) :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => trivial)

theorem not_contractRealizable_of_post_false
    {X : Type u} {Y : Type v} (pre : X → Prop) :
    ¬ ContractRealizable pre (fun (_ : X) (_ : Y) => False) := by
  rintro ⟨_, _, _, hFalse⟩
  exact hFalse

/-! ### 4. Monotonicity, Weakening & Product Composition -/

theorem PreconditionSatisfiable.mono
    {X : Type u} {pre₁ pre₂ : X → Prop}
    (hImp : ∀ x, pre₁ x → pre₂ x)
    (h : PreconditionSatisfiable pre₁) :
    PreconditionSatisfiable pre₂ := by
  rcases h with ⟨x, h1⟩
  exact ⟨x, hImp x h1⟩

theorem ContractRealizable.mono
    {X : Type u} {Y : Type v} {pre₁ pre₂ : X → Prop} {post₁ post₂ : X → Y → Prop}
    (hPre : ∀ x, pre₁ x → pre₂ x)
    (hPost : ∀ x y, pre₁ x → post₁ x y → post₂ x y)
    (h : ContractRealizable pre₁ post₁) :
    ContractRealizable pre₂ post₂ := by
  rcases h with ⟨x, hx, y, hy⟩
  exact ⟨x, hPre x hx, y, hPost x y hx hy⟩

theorem ContractDeterministicOn.anti
    {X : Type u} {Y : Type v} {Z : Type w}
    {obs : Y → Z} {pre₁ pre₂ : X → Prop} {post₁ post₂ : X → Y → Prop}
    (hPre : ∀ x, pre₂ x → pre₁ x)
    (hPost : ∀ x y, pre₂ x → post₂ x y → post₁ x y)
    (hDet : ContractDeterministicOn obs pre₁ post₁) :
    ContractDeterministicOn obs pre₂ post₂ := by
  intro x y₁ y₂ hx h1 h2
  exact hDet x y₁ y₂ (hPre x hx) (hPost x y₁ hx h1) (hPost x y₂ hx h2)

theorem DichotomyModuloObservation.of_refining_obs
    {X : Type u} {Y : Type v} {Z₁ : Type w} {Z₂ : Type u₁}
    {obs₁ : X → Y → Z₁} {obs₂ : X → Y → Z₂}
    {pre : X → Prop} {post : X → Y → Prop}
    (hRef : ∀ x y₁ y₂, obs₁ x y₁ = obs₁ x y₂ → obs₂ x y₁ = obs₂ x y₂)
    (h : DichotomyModuloObservation obs₁ pre post) :
    DichotomyModuloObservation obs₂ pre post := by
  rcases h with ⟨x, hPre, y_ok, y_bad, hObsEq, hOk, hBad⟩
  exact ⟨x, hPre, y_ok, y_bad, hRef x y_ok y_bad hObsEq, hOk, hBad⟩

theorem preconditionSatisfiable_prod
    {X₁ : Type u₁} {X₂ : Type u₂} {pre₁ : X₁ → Prop} {pre₂ : X₂ → Prop}
    (h₁ : PreconditionSatisfiable pre₁) (h₂ : PreconditionSatisfiable pre₂) :
    PreconditionSatisfiable (fun p : X₁ × X₂ => pre₁ p.1 ∧ pre₂ p.2) := by
  rcases h₁ with ⟨x₁, hx₁⟩
  rcases h₂ with ⟨x₂, hx₂⟩
  exact ⟨(x₁, x₂), hx₁, hx₂⟩

theorem contractRealizable_prod
    {X₁ : Type u₁} {X₂ : Type u₂} {Y₁ : Type v₁} {Y₂ : Type v₂}
    {pre₁ : X₁ → Prop} {pre₂ : X₂ → Prop}
    {post₁ : X₁ → Y₁ → Prop} {post₂ : X₂ → Y₂ → Prop}
    (h₁ : ContractRealizable pre₁ post₁) (h₂ : ContractRealizable pre₂ post₂) :
    ContractRealizable
      (fun p : X₁ × X₂ => pre₁ p.1 ∧ pre₂ p.2)
      (fun (p : X₁ × X₂) (q : Y₁ × Y₂) => post₁ p.1 q.1 ∧ post₂ p.2 q.2) := by
  rcases h₁ with ⟨x₁, hx₁, y₁, hy₁⟩
  rcases h₂ with ⟨x₂, hx₂, y₂, hy₂⟩
  exact ⟨(x₁, x₂), ⟨hx₁, hx₂⟩, (y₁, y₂), ⟨hy₁, hy₂⟩⟩

theorem postconditionDichotomy_prod_left
    {X₁ : Type u₁} {X₂ : Type u₂} {Y₁ : Type v₁} {Y₂ : Type v₂}
    {pre₁ : X₁ → Prop} {pre₂ : X₂ → Prop}
    {post₁ : X₁ → Y₁ → Prop} {post₂ : X₂ → Y₂ → Prop}
    (h₁ : PostconditionDichotomy pre₁ post₁) (h₂ : ContractRealizable pre₂ post₂) :
    PostconditionDichotomy
      (fun p : X₁ × X₂ => pre₁ p.1 ∧ pre₂ p.2)
      (fun (p : X₁ × X₂) (q : Y₁ × Y₂) => post₁ p.1 q.1 ∧ post₂ p.2 q.2) := by
  rcases h₁ with ⟨x₁, hx₁, ⟨y₁_ok, hy₁_ok⟩, ⟨y₁_bad, hy₁_bad⟩⟩
  rcases h₂ with ⟨x₂, hx₂, y₂_ok, hy₂_ok⟩
  refine ⟨(x₁, x₂), ⟨hx₁, hx₂⟩, ⟨(y₁_ok, y₂_ok), hy₁_ok, hy₂_ok⟩, ⟨(y₁_bad, y₂_ok), ?_⟩⟩
  rintro ⟨hBad, _⟩
  exact hy₁_bad hBad

theorem postconditionDichotomy_prod_right
    {X₁ : Type u₁} {X₂ : Type u₂} {Y₁ : Type v₁} {Y₂ : Type v₂}
    {pre₁ : X₁ → Prop} {pre₂ : X₂ → Prop}
    {post₁ : X₁ → Y₁ → Prop} {post₂ : X₂ → Y₂ → Prop}
    (h₁ : ContractRealizable pre₁ post₁) (h₂ : PostconditionDichotomy pre₂ post₂) :
    PostconditionDichotomy
      (fun p : X₁ × X₂ => pre₁ p.1 ∧ pre₂ p.2)
      (fun (p : X₁ × X₂) (q : Y₁ × Y₂) => post₁ p.1 q.1 ∧ post₂ p.2 q.2) := by
  rcases h₁ with ⟨x₁, hx₁, y₁_ok, hy₁_ok⟩
  rcases h₂ with ⟨x₂, hx₂, ⟨y₂_ok, hy₂_ok⟩, ⟨y₂_bad, hy₂_bad⟩⟩
  refine ⟨(x₁, x₂), ⟨hx₁, hx₂⟩, ⟨(y₁_ok, y₂_ok), hy₁_ok, hy₂_ok⟩, ⟨(y₁_ok, y₂_bad), ?_⟩⟩
  rintro ⟨_, hBad⟩
  exact hy₂_bad hBad

theorem contractDeterministic_prod
    {X₁ : Type u₁} {X₂ : Type u₂} {Y₁ : Type v₁} {Y₂ : Type v₂}
    {pre₁ : X₁ → Prop} {pre₂ : X₂ → Prop}
    {post₁ : X₁ → Y₁ → Prop} {post₂ : X₂ → Y₂ → Prop}
    (h₁ : ContractDeterministic pre₁ post₁) (h₂ : ContractDeterministic pre₂ post₂) :
    ContractDeterministic
      (fun p : X₁ × X₂ => pre₁ p.1 ∧ pre₂ p.2)
      (fun (p : X₁ × X₂) (q : Y₁ × Y₂) => post₁ p.1 q.1 ∧ post₂ p.2 q.2) := by
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨y₁', y₂'⟩ ⟨hx₁, hx₂⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩
  have eq1 : y₁ = y₁' := h₁ x₁ y₁ y₁' hx₁ h1 h1'
  have eq2 : y₂ = y₂' := h₂ x₂ y₂ y₂' hx₂ h2 h2'
  cases eq1
  cases eq2
  rfl

/-! ### 5. Specializations for `Trusted.VerificationResult` Claims -/

theorem preconditionSatisfiable_iff_nonVacuousPre (pre : List Value → Prop) :
    PreconditionSatisfiable pre ↔ NonVacuousPre pre :=
  Iff.rfl

theorem preconditionSatisfiable_iff_nonVacuousStatefulPre
    (pre : List Value → Memory → Prop) :
    PreconditionSatisfiable (fun p : List Value × Memory => pre p.1 p.2) ↔
      NonVacuousStatefulPre pre := by
  constructor
  · rintro ⟨⟨args, mem⟩, h⟩
    exact ⟨args, mem, h⟩
  · rintro ⟨args, mem, h⟩
    exact ⟨(args, mem), h⟩

/-! #### Stateless `Claim` -/

def ClaimPreSatisfiable (c : Claim) : Prop :=
  PreconditionSatisfiable c.pre

def ClaimRealizable (c : Claim) : Prop :=
  ContractRealizable c.pre c.post

def ClaimUniversalRealizable (c : Claim) : Prop :=
  UniversalContractRealizable c.pre c.post

def ClaimDichotomy (c : Claim) : Prop :=
  PostconditionDichotomy c.pre c.post

def ClaimDeterministic (c : Claim) : Prop :=
  ContractDeterministic c.pre c.post

theorem claimPreSatisfiable_iff_nonVacuousPre (c : Claim) :
    ClaimPreSatisfiable c ↔ NonVacuousPre c.pre :=
  Iff.rfl

theorem ClaimDichotomy.toRealizable {c : Claim} (h : ClaimDichotomy c) :
    ClaimRealizable c :=
  PostconditionDichotomy.contractRealizable h

theorem ClaimRealizable.toPreSatisfiable {c : Claim} (h : ClaimRealizable c) :
    ClaimPreSatisfiable c :=
  ContractRealizable.preconditionSatisfiable h

/-! #### Stateful `StatefulClaim` -/

def StatefulClaimPreSatisfiable (c : StatefulClaim) : Prop :=
  PreconditionSatisfiable (fun p : List Value × Memory => c.pre p.1 p.2)

def StatefulClaimRealizable (c : StatefulClaim) : Prop :=
  ContractRealizable
    (fun p : List Value × Memory => c.pre p.1 p.2)
    (fun (p : List Value × Memory) (q : Value × Memory) => c.post p.1 p.2 q.1 q.2)

def StatefulClaimDichotomy (c : StatefulClaim) : Prop :=
  PostconditionDichotomy
    (fun p : List Value × Memory => c.pre p.1 p.2)
    (fun (p : List Value × Memory) (q : Value × Memory) => c.post p.1 p.2 q.1 q.2)

/-- Strict return-value dichotomy for a `StatefulClaim`: holds the post-memory `mem'`
    fixed so that a spec constraining only `mem'` while leaving `retVal` unconstrained
    cannot pass. -/
def StatefulClaimReturnDichotomy (c : StatefulClaim) : Prop :=
  ∃ args mem mem' v_ok v_bad,
    c.pre args mem ∧ c.post args mem v_ok mem' ∧ ¬ c.post args mem v_bad mem'

def StatefulClaimDeterministic (c : StatefulClaim) : Prop :=
  ContractDeterministic
    (fun p : List Value × Memory => c.pre p.1 p.2)
    (fun (p : List Value × Memory) (q : Value × Memory) => c.post p.1 p.2 q.1 q.2)

theorem statefulClaimPreSatisfiable_iff_nonVacuousStatefulPre (c : StatefulClaim) :
    StatefulClaimPreSatisfiable c ↔ NonVacuousStatefulPre c.pre :=
  preconditionSatisfiable_iff_nonVacuousStatefulPre c.pre

theorem statefulClaimReturnDichotomy_iff_moduloMemory (c : StatefulClaim) :
    StatefulClaimReturnDichotomy c ↔
      DichotomyModuloObservation
        (fun (_ : List Value × Memory) (q : Value × Memory) => q.2)
        (fun p : List Value × Memory => c.pre p.1 p.2)
        (fun (p : List Value × Memory) (q : Value × Memory) => c.post p.1 p.2 q.1 q.2) := by
  constructor
  · rintro ⟨args, mem, mem', v_ok, v_bad, hPre, hOk, hBad⟩
    exact ⟨(args, mem), hPre, (v_ok, mem'), (v_bad, mem'), rfl, hOk, hBad⟩
  · rintro ⟨⟨args, mem⟩, hPre, ⟨v_ok, m_ok⟩, ⟨v_bad, m_bad⟩, hMemEq, hOk, hBad⟩
    dsimp at hMemEq
    subst hMemEq
    exact ⟨args, mem, m_ok, v_ok, v_bad, hPre, hOk, hBad⟩

theorem StatefulClaimReturnDichotomy.toDichotomy {c : StatefulClaim}
    (h : StatefulClaimReturnDichotomy c) : StatefulClaimDichotomy c :=
  ((statefulClaimReturnDichotomy_iff_moduloMemory c).mp h).postconditionDichotomy

theorem StatefulClaimDichotomy.toRealizable {c : StatefulClaim}
    (h : StatefulClaimDichotomy c) : StatefulClaimRealizable c :=
  PostconditionDichotomy.contractRealizable h

theorem StatefulClaimRealizable.toPreSatisfiable {c : StatefulClaim}
    (h : StatefulClaimRealizable c) : StatefulClaimPreSatisfiable c :=
  ContractRealizable.preconditionSatisfiable h

/-! #### Total-Correctness `TotalClaim` -/

def TotalClaimPreSatisfiable (c : TotalClaim) : Prop :=
  PreconditionSatisfiable (fun p : List Value × Memory => c.pre p.1 p.2)

def TotalClaimRealizable (c : TotalClaim) : Prop :=
  ContractRealizable
    (fun p : List Value × Memory => c.pre p.1 p.2)
    (fun (p : List Value × Memory) (q : Value × Memory) => c.post p.1 p.2 q.1 q.2)

def TotalClaimDichotomy (c : TotalClaim) : Prop :=
  PostconditionDichotomy
    (fun p : List Value × Memory => c.pre p.1 p.2)
    (fun (p : List Value × Memory) (q : Value × Memory) => c.post p.1 p.2 q.1 q.2)

def TotalClaimReturnDichotomy (c : TotalClaim) : Prop :=
  ∃ args mem mem' v_ok v_bad,
    c.pre args mem ∧ c.post args mem v_ok mem' ∧ ¬ c.post args mem v_bad mem'

theorem totalClaimReturnDichotomy_iff_moduloMemory (c : TotalClaim) :
    TotalClaimReturnDichotomy c ↔
      DichotomyModuloObservation
        (fun (_ : List Value × Memory) (q : Value × Memory) => q.2)
        (fun p : List Value × Memory => c.pre p.1 p.2)
        (fun (p : List Value × Memory) (q : Value × Memory) => c.post p.1 p.2 q.1 q.2) := by
  constructor
  · rintro ⟨args, mem, mem', v_ok, v_bad, hPre, hOk, hBad⟩
    exact ⟨(args, mem), hPre, (v_ok, mem'), (v_bad, mem'), rfl, hOk, hBad⟩
  · rintro ⟨⟨args, mem⟩, hPre, ⟨v_ok, m_ok⟩, ⟨v_bad, m_bad⟩, hMemEq, hOk, hBad⟩
    dsimp at hMemEq
    subst hMemEq
    exact ⟨args, mem, m_ok, v_ok, v_bad, hPre, hOk, hBad⟩

theorem TotalClaimReturnDichotomy.toDichotomy {c : TotalClaim}
    (h : TotalClaimReturnDichotomy c) : TotalClaimDichotomy c :=
  ((totalClaimReturnDichotomy_iff_moduloMemory c).mp h).postconditionDichotomy

theorem TotalClaimDichotomy.toRealizable {c : TotalClaim}
    (h : TotalClaimDichotomy c) : TotalClaimRealizable c :=
  PostconditionDichotomy.contractRealizable h

theorem TotalClaimRealizable.toPreSatisfiable {c : TotalClaim}
    (h : TotalClaimRealizable c) : TotalClaimPreSatisfiable c :=
  ContractRealizable.preconditionSatisfiable h

/-- A verified `TotalClaim` that reaches any return from a valid `(args, mem)` state
    is constructively realizable. -/
theorem totalClaimRealizable_of_verified_reachesRet
    {c : TotalClaim}
    (hVer : TotalVerificationResult c)
    {args : List Value} {mem : Memory}
    {tr : List (Event MirEffect)} {out : MirOutcome}
    (hPre : c.pre args mem)
    (hRet : ReachesRet (mirStatefulTreeWithCallees c.body args mem c.callees) tr out) :
    TotalClaimRealizable c := by
  have hHold := hVer.proof args mem hPre
  rcases hHold.2.2.2 tr out hRet with ⟨retVal, mem', _, hPost⟩
  exact ⟨(args, mem), hPre, (retVal, mem'), hPost⟩

/-! #### Modular Rely-Guarantee `ModularClaim` -/

def ModularClaimPreSatisfiable (c : ModularClaim) : Prop :=
  PreconditionSatisfiable (fun p : List Value × Memory => c.pre p.1 p.2)

/-- Rely satisfiability: the assumed external-call environment `c.envAssumed` is
    inhabited by at least one `ExternalCallHandler`. -/
def ModularClaimEnvSatisfiable (c : ModularClaim) : Prop :=
  ∃ h : ExternalCallHandler, c.envAssumed h

def ModularClaimRealizable (c : ModularClaim) : Prop :=
  ContractRealizable
    (fun p : List Value × Memory => c.pre p.1 p.2)
    (fun (p : List Value × Memory) (q : Value × Memory) => c.post p.1 p.2 q.1 q.2)

def ModularClaimDichotomy (c : ModularClaim) : Prop :=
  PostconditionDichotomy
    (fun p : List Value × Memory => c.pre p.1 p.2)
    (fun (p : List Value × Memory) (q : Value × Memory) => c.post p.1 p.2 q.1 q.2)

def ModularClaimReturnDichotomy (c : ModularClaim) : Prop :=
  ∃ args mem mem' v_ok v_bad,
    c.pre args mem ∧ c.post args mem v_ok mem' ∧ ¬ c.post args mem v_bad mem'

theorem modularClaimReturnDichotomy_iff_moduloMemory (c : ModularClaim) :
    ModularClaimReturnDichotomy c ↔
      DichotomyModuloObservation
        (fun (_ : List Value × Memory) (q : Value × Memory) => q.2)
        (fun p : List Value × Memory => c.pre p.1 p.2)
        (fun (p : List Value × Memory) (q : Value × Memory) => c.post p.1 p.2 q.1 q.2) := by
  constructor
  · rintro ⟨args, mem, mem', v_ok, v_bad, hPre, hOk, hBad⟩
    exact ⟨(args, mem), hPre, (v_ok, mem'), (v_bad, mem'), rfl, hOk, hBad⟩
  · rintro ⟨⟨args, mem⟩, hPre, ⟨v_ok, m_ok⟩, ⟨v_bad, m_bad⟩, hMemEq, hOk, hBad⟩
    dsimp at hMemEq
    subst hMemEq
    exact ⟨args, mem, m_ok, v_ok, v_bad, hPre, hOk, hBad⟩

theorem ModularClaimReturnDichotomy.toDichotomy {c : ModularClaim}
    (h : ModularClaimReturnDichotomy c) : ModularClaimDichotomy c :=
  ((modularClaimReturnDichotomy_iff_moduloMemory c).mp h).postconditionDichotomy

theorem ModularClaimDichotomy.toRealizable {c : ModularClaim}
    (h : ModularClaimDichotomy c) : ModularClaimRealizable c :=
  PostconditionDichotomy.contractRealizable h

theorem ModularClaimRealizable.toPreSatisfiable {c : ModularClaim}
    (h : ModularClaimRealizable c) : ModularClaimPreSatisfiable c :=
  ContractRealizable.preconditionSatisfiable h

/-! ### 6. `MirCallContract`, `externalSpecCallContract` & the Three Soundness Traps -/

/-- `callFramePreserved` is reflexive on every `Memory`. -/
theorem callFramePreserved_refl (mem : Memory) : callFramePreserved mem mem :=
  ⟨rfl, rfl, rfl, rfl, .nil, rfl⟩

/-- Precondition satisfiability for an external call contract. -/
def MirCallContractPreSatisfiable (c : MirCallContract) : Prop :=
  PreconditionSatisfiable c.pre

/-- Normal-return realizability for `MirCallContract`: requires an accepted
    `.returned retVal memAfter` outcome rather than escaping via `.aborted`. -/
def MirCallContractRealizable (c : MirCallContract) : Prop :=
  ∃ req retVal memAfter, c.pre req ∧ c.post req (.returned retVal memAfter)

/-- Alias for `MirCallContractRealizable` emphasizing normal `.returned` outcomes. -/
abbrev MirCallContractNormalRealizable (c : MirCallContract) : Prop :=
  MirCallContractRealizable c

/-- Normal-return dichotomy for `MirCallContract`: some valid request admits both an
    accepted normal return and a rejected normal return (ruling out Trap 2 where
    `.panicked => False` fakes dichotomy against a trivial `.returned => True`). -/
def MirCallContractNormalDichotomy (c : MirCallContract) : Prop :=
  ∃ req v₁ m₁ v₂ m₂,
    c.pre req ∧
    c.post req (.returned v₁ m₁) ∧
    ¬ c.post req (.returned v₂ m₂)

/-- Strict return-value dichotomy for `MirCallContract` holding post-call memory `m`
    fixed across accepted and rejected return values. -/
def MirCallContractReturnValueDichotomy (c : MirCallContract) : Prop :=
  ∃ req m v_ok v_bad,
    c.pre req ∧
    c.post req (.returned v_ok m) ∧
    ¬ c.post req (.returned v_bad m)

theorem MirCallContractRealizable.toContractRealizable {c : MirCallContract}
    (h : MirCallContractRealizable c) : ContractRealizable c.pre c.post := by
  rcases h with ⟨req, retVal, memAfter, hPre, hPost⟩
  exact ⟨req, hPre, .returned retVal memAfter, hPost⟩

theorem MirCallContractRealizable.toPreSatisfiable {c : MirCallContract}
    (h : MirCallContractRealizable c) : MirCallContractPreSatisfiable c := by
  rcases h with ⟨req, _, _, hPre, _⟩
  exact ⟨req, hPre⟩

theorem MirCallContractNormalDichotomy.toRealizable {c : MirCallContract}
    (h : MirCallContractNormalDichotomy c) : MirCallContractRealizable c := by
  rcases h with ⟨req, v₁, m₁, _, _, hPre, hOk, _⟩
  exact ⟨req, v₁, m₁, hPre, hOk⟩

theorem MirCallContractNormalDichotomy.toPostconditionDichotomy {c : MirCallContract}
    (h : MirCallContractNormalDichotomy c) : PostconditionDichotomy c.pre c.post := by
  rcases h with ⟨req, v₁, m₁, v₂, m₂, hPre, hOk, hBad⟩
  exact ⟨req, hPre, ⟨.returned v₁ m₁, hOk⟩, ⟨.returned v₂ m₂, hBad⟩⟩

theorem MirCallContractReturnValueDichotomy.toNormalDichotomy {c : MirCallContract}
    (h : MirCallContractReturnValueDichotomy c) : MirCallContractNormalDichotomy c := by
  rcases h with ⟨req, m, v_ok, v_bad, hPre, hOk, hBad⟩
  exact ⟨req, v_ok, m, v_bad, m, hPre, hOk, hBad⟩

/-- **Soundness Trap 1**: Naive `ContractRealizable c.pre c.post` on any
    `externalSpecCallContract` collapses to `PreconditionSatisfiable c.pre`—even when
    `extraPost := fun _ _ => False`—because `c.post req .aborted` is unconditionally
    `True`. Use `MirCallContractRealizable` instead. -/
theorem externalSpecCallContract_naive_realizable_iff_preSatisfiable
    (targetDefPath : DefPath) (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop) (extraPost : List Value → Value → Prop) :
    ContractRealizable
        (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).pre
        (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).post ↔
      PreconditionSatisfiable
        (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).pre := by
  constructor
  · exact ContractRealizable.preconditionSatisfiable
  · rintro ⟨req, hPre⟩
    exact ⟨req, hPre, .aborted, trivial⟩

/-- Characterization of genuine normal-return realizability for
    `externalSpecCallContract`. -/
theorem externalSpecCallContract_realizable_iff
    (targetDefPath : DefPath) (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop) (extraPost : List Value → Value → Prop) :
    MirCallContractRealizable
        (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost) ↔
      ∃ req retVal memAfter,
        (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).pre req ∧
        callFramePreserved req.memory memAfter ∧
        retMatchesCalleeReturnTy sidecarBody retVal ∧
        extraPost req.args retVal := by
  constructor
  · rintro ⟨req, retVal, memAfter, hPre, hFrame, hRetTy, hExtra⟩
    exact ⟨req, retVal, memAfter, hPre, hFrame, hRetTy, hExtra⟩
  · rintro ⟨req, retVal, memAfter, hPre, hFrame, hRetTy, hExtra⟩
    exact ⟨req, retVal, memAfter, hPre, hFrame, hRetTy, hExtra⟩

/-- Helper witness constructor for `MirCallContractRealizable` on an
    `externalSpecCallContract`, reusing `req.memory` via `callFramePreserved_refl`. -/
theorem externalSpecCallContract_realizable_of_witness
    {targetDefPath : DefPath} {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop} {extraPost : List Value → Value → Prop}
    (req : MirCallReq) (retVal : Value)
    (hPre : (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).pre req)
    (hRetTy : retMatchesCalleeReturnTy sidecarBody retVal)
    (hExtra : extraPost req.args retVal) :
    MirCallContractRealizable
      (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost) :=
  ⟨req, retVal, req.memory, hPre, callFramePreserved_refl req.memory, hRetTy, hExtra⟩

/-- Unlike naive `ContractRealizable`, `MirCallContractRealizable` rejects an
    `externalSpecCallContract` whose user postcondition is `False`. -/
theorem not_mirCallContractRealizable_externalSpec_false_post
    (targetDefPath : DefPath) (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop) :
    ¬ MirCallContractRealizable
      (externalSpecCallContract targetDefPath sidecarBody extraPre (fun _ _ => False)) := by
  rintro ⟨_, _, _, _, _, _, hFalse⟩
  exact hFalse

/-- **Soundness Trap 2**: `MirCallContractNormalDichotomy` is strictly stronger than
    generic `PostconditionDichotomy c.pre c.post`: a nounwind contract with
    `.panicked _ => False` and `.returned _ _ => True` satisfies generic dichotomy
    across `.returned` vs. `.panicked` while accepting every normal return. -/
theorem normalDichotomy_strictly_stronger_than_dichotomy :
    (∀ c : MirCallContract,
      MirCallContractNormalDichotomy c → PostconditionDichotomy c.pre c.post) ∧
    ∃ c : MirCallContract,
      PostconditionDichotomy c.pre c.post ∧ ¬ MirCallContractNormalDichotomy c := by
  refine ⟨fun _ h => h.toPostconditionDichotomy, ?_⟩
  let c : MirCallContract := {
    pre := fun _ => True
    post := fun _ ans =>
      match ans with
      | .returned _ _ => True
      | .panicked _ => False
      | .aborted => True
  }
  refine ⟨c, ?_, ?_⟩
  · let req : MirCallReq := { defPath := "", args := .nil, memory := emptyMemory }
    exact ⟨req, trivial, ⟨.returned .unit emptyMemory, trivial⟩,
      ⟨.panicked emptyMemory, fun h => h⟩⟩
  · rintro ⟨_, _, _, _, _, _, _, hNot⟩
    exact hNot trivial

/-- **Soundness Trap 3** observation: projects a normal `(retVal, memAfter)` outcome of
    an `externalSpecCallContract` onto its auto-generated boilerplate atoms
    `(callFramePreserved, retMatchesCalleeReturnTy)`. -/
def externalSpecBoilerplateObs
    (sidecarBody : CapturedMir) (req : MirCallReq) :
    Value × Memory → Prop × Prop :=
  fun q =>
    (callFramePreserved req.memory q.2, retMatchesCalleeReturnTy sidecarBody q.1)

/-- Genuine postcondition dichotomy for an `externalSpecCallContract` modulo its
    auto-generated frame and return-type boilerplate. -/
def ExternalSpecEnsuresDichotomy
    (targetDefPath : DefPath)
    (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop := fun _ => True)
    (extraPost : List Value → Value → Prop := fun _ _ => True) : Prop :=
  let c := externalSpecCallContract targetDefPath sidecarBody extraPre extraPost
  DichotomyModuloObservation
    (externalSpecBoilerplateObs sidecarBody)
    c.pre
    (fun req q => c.post req (.returned q.1 q.2))

/-- **Soundness Trap 3 Theorem**: Normal-return `DichotomyModuloObservation` over
    `(callFramePreserved, retMatchesCalleeReturnTy)` holds for an
    `externalSpecCallContract` iff there exist a valid request `req`, a frame-preserving
    `memAfter`, and two return-type-valid values `v_ok, v_bad` separated by `extraPost`. -/
theorem externalSpecEnsuresDichotomy_iff_moduloObservation
    (targetDefPath : DefPath) (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop) (extraPost : List Value → Value → Prop) :
    ExternalSpecEnsuresDichotomy targetDefPath sidecarBody extraPre extraPost ↔
      ∃ req memAfter v_ok v_bad,
        (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).pre req ∧
        callFramePreserved req.memory memAfter ∧
        retMatchesCalleeReturnTy sidecarBody v_ok ∧
        retMatchesCalleeReturnTy sidecarBody v_bad ∧
        extraPost req.args v_ok ∧
        ¬ extraPost req.args v_bad := by
  constructor
  · rintro ⟨req, hPre, ⟨v_ok, m_ok⟩, ⟨v_bad, m_bad⟩, hObsEq, hOk, hBad⟩
    rcases hOk with ⟨hFrameOk, hTyOk, hExtraOk⟩
    have hFrameEq : callFramePreserved req.memory m_ok = callFramePreserved req.memory m_bad :=
      congrArg Prod.fst hObsEq
    have hTyEq : retMatchesCalleeReturnTy sidecarBody v_ok =
        retMatchesCalleeReturnTy sidecarBody v_bad :=
      congrArg Prod.snd hObsEq
    have hFrameBad : callFramePreserved req.memory m_bad := hFrameEq ▸ hFrameOk
    have hTyBad : retMatchesCalleeReturnTy sidecarBody v_bad := hTyEq ▸ hTyOk
    refine ⟨req, m_ok, v_ok, v_bad, hPre, hFrameOk, hTyOk, hTyBad, hExtraOk, ?_⟩
    intro hExtraBad
    exact hBad ⟨hFrameBad, hTyBad, hExtraBad⟩
  · rintro ⟨req, memAfter, v_ok, v_bad, hPre, hFrame, hTyOk, hTyBad, hExtraOk, hNotExtraBad⟩
    refine ⟨req, hPre, (v_ok, memAfter), (v_bad, memAfter), ?_, ?_, ?_⟩
    · exact congrArg (Prod.mk (callFramePreserved req.memory memAfter))
        (propext ⟨fun _ => hTyBad, fun _ => hTyOk⟩)
    · exact ⟨hFrame, hTyOk, hExtraOk⟩
    · rintro ⟨_, _, hExtraBad⟩
      exact hNotExtraBad hExtraBad

theorem externalSpecEnsuresDichotomy_to_returnValueDichotomy
    {targetDefPath : DefPath} {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop} {extraPost : List Value → Value → Prop}
    (h : ExternalSpecEnsuresDichotomy targetDefPath sidecarBody extraPre extraPost) :
    MirCallContractReturnValueDichotomy
      (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost) := by
  rcases (externalSpecEnsuresDichotomy_iff_moduloObservation
    targetDefPath sidecarBody extraPre extraPost).mp h with
    ⟨req, memAfter, v_ok, v_bad, hPre, hFrame, hTyOk, _, hExtraOk, hNotExtraBad⟩
  exact ⟨req, memAfter, v_ok, v_bad, hPre, ⟨hFrame, hTyOk, hExtraOk⟩,
    fun ⟨_, _, hBad⟩ => hNotExtraBad hBad⟩

theorem not_externalSpecEnsuresDichotomy_of_trivial_extraPost
    (targetDefPath : DefPath) (sidecarBody : CapturedMir)
    (extraPre : List Value → Prop) {extraPost : List Value → Value → Prop}
    (hTriv : ∀ args v, extraPost args v) :
    ¬ ExternalSpecEnsuresDichotomy targetDefPath sidecarBody extraPre extraPost := by
  intro h
  rcases (externalSpecEnsuresDichotomy_iff_moduloObservation
    targetDefPath sidecarBody extraPre extraPost).mp h with
    ⟨req, _, _, v_bad, _, _, _, _, _, hNotBad⟩
  exact hNotBad (hTriv req.args v_bad)

/-! #### `MirCallContract.holdsOn` Handler Bridges -/

/-- If `h` implements `c` (`c.holdsOn h`) and `h req` reaches a normal `.returned`
    answer on a valid `req`, then `c` is normally realizable. -/
theorem mirCallContractRealizable_of_holdsOn_reachesRet
    {c : MirCallContract} {h : ExternalCallHandler}
    (hHolds : c.holdsOn h)
    {req : MirCallReq} {tr : List (Event MirClosedEffect)}
    {retVal : Value} {memAfter : Memory}
    (hPre : c.pre req)
    (hRet : ReachesRet (h req) tr (.returned retVal memAfter)) :
    MirCallContractRealizable c := by
  have hPost := (hHolds req hPre).2 tr (.returned retVal memAfter) hRet
  exact ⟨req, retVal, memAfter, hPre, hPost⟩

/-- If `h` implements `c` and `h req` reaches any `MirCallAns` under `c.pre req`,
    then `ContractRealizable c.pre c.post` holds. -/
theorem contractRealizable_of_holdsOn_reachesRet
    {c : MirCallContract} {h : ExternalCallHandler}
    (hHolds : c.holdsOn h)
    {req : MirCallReq} {tr : List (Event MirClosedEffect)} {ans : MirCallAns}
    (hPre : c.pre req)
    (hRet : ReachesRet (h req) tr ans) :
    ContractRealizable c.pre c.post :=
  ⟨req, hPre, ans, (hHolds req hPre).2 tr ans hRet⟩

private theorem tauStar_ret_eq {E : Effect.{0}} {R : Type} {r : R} {u : ITree E R}
    (h : TauStar (ITree.ret (E := E) r) u) : u = ITree.ret r := by
  cases h with
  | refl => rfl
  | step hObs _ =>
    rw [ITree.observe_ret] at hObs
    cases hObs

private theorem reaches_ret_eq {E : Effect.{0}} {R : Type} [FaultEffect E]
    {r : R} {tr : List (Event E)} {u : ITree E R}
    (h : Reaches (ITree.ret (E := E) r) tr u) : tr = [] ∧ u = ITree.ret r := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | tau hObs _ =>
    rw [ITree.observe_ret] at hObs
    cases hObs
  | vis hObs _ _ _ =>
    rw [ITree.observe_ret] at hObs
    cases hObs

/-- A pure returning tree `ITree.ret r` is `TreeSafe`. -/
theorem treeSafe_ret {E : Effect.{0}} {R : Type} [FaultEffect E] (r : R) :
    TreeSafe (ITree.ret (E := E) r) := by
  intro tr u hReach hFault
  have hu : u = ITree.ret r := (reaches_ret_eq hReach).2
  subst hu
  rcases hFault with ⟨t', i, k, hTau, hObs, _⟩
  have ht' : t' = ITree.ret r := tauStar_ret_eq hTau
  subst ht'
  rw [ITree.observe_ret] at hObs
  cases hObs

/-- Any return value reached from `ITree.ret r` equals `r` along the empty trace. -/
theorem reachesRet_ret_inv {E : Effect.{0}} {R : Type} [FaultEffect E]
    {r r' : R} {tr : List (Event E)}
    (h : ReachesRet (ITree.ret (E := E) r) tr r') : tr = [] ∧ r' = r := by
  rcases h with ⟨u, hReach, hObs⟩
  rcases reaches_ret_eq hReach with ⟨hTr, hu⟩
  subst hu
  rw [ITree.observe_ret] at hObs
  cases hObs
  exact ⟨hTr, rfl⟩

/-- Every universally normally realizable `MirCallContract` admits an `ExternalCallHandler`
    that satisfies `c.holdsOn h` and returns normally on every valid request. -/
theorem exists_handler_holdsOn_of_universalNormalRealizable
    {c : MirCallContract}
    (hUniv : ∀ req, c.pre req → ∃ retVal memAfter, c.post req (.returned retVal memAfter)) :
    ∃ h : ExternalCallHandler,
      c.holdsOn h ∧
      ∀ req, c.pre req → ∃ retVal memAfter, ReachesRet (h req) [] (.returned retVal memAfter) := by
  classical
  let h : ExternalCallHandler := fun req =>
    if hPre : c.pre req then
      let v := Classical.choose (hUniv req hPre)
      let m := Classical.choose (Classical.choose_spec (hUniv req hPre))
      ITree.ret (.returned v m)
    else
      ITree.ret .aborted
  refine ⟨h, ?_, ?_⟩
  · intro req hPre
    have hEq : h req =
        ITree.ret (.returned
          (Classical.choose (hUniv req hPre))
          (Classical.choose (Classical.choose_spec (hUniv req hPre)))) := by
      dsimp [h]
      split
      · rfl
      · rename_i hNot
        exact False.elim (hNot hPre)
    rw [hEq]
    refine ⟨treeSafe_ret _, fun tr ans hRet => ?_⟩
    rcases reachesRet_ret_inv hRet with ⟨_, hAns⟩
    subst hAns
    exact Classical.choose_spec (Classical.choose_spec (hUniv req hPre))
  · intro req hPre
    have hEq : h req =
        ITree.ret (.returned
          (Classical.choose (hUniv req hPre))
          (Classical.choose (Classical.choose_spec (hUniv req hPre)))) := by
      dsimp [h]
      split
      · rfl
      · rename_i hNot
        exact False.elim (hNot hPre)
    rw [hEq]
    exact ⟨_, _, ITree.ret _, Reaches.refl _, ITree.observe_ret _⟩

end PureCalculus

/-! ## Part II — `MetaM` Structural + Bounded-Probe Vacuity Checker -/

section MetaChecker

open Lean Meta Elab

/-- Fine-grained diagnostic reason why an `ensures` clause failed realizability or
    output-binding checks. -/
inductive EnsuresVacuityReason : Type where
  | requiresUnsatisfiable
  | unrealizableUnderRequires
  | trivialConstantTrue
  | reflexiveEquality
  | tautologicalDisjunction
  | tautologicalImplication
  | tautologicalByProver
  | unusedOutputBinder
  | discardedLetBinding
  | subsingletonOutputType
  | boilerplateOnlyMasking
  | vacuousUnderRequires
  deriving DecidableEq, Repr, Inhabited

/-- Map each fine-grained `EnsuresVacuityReason` to its frozen cross-language
    `VacuityClass`. -/
def EnsuresVacuityReason.toVacuityClass : EnsuresVacuityReason → VacuityClass
  | .requiresUnsatisfiable => .deadPrecondition
  | .unrealizableUnderRequires => .specViolation
  | .trivialConstantTrue => .trivialPostcondition
  | .reflexiveEquality => .trivialPostcondition
  | .tautologicalDisjunction => .trivialPostcondition
  | .tautologicalImplication => .trivialPostcondition
  | .tautologicalByProver => .trivialPostcondition
  | .unusedOutputBinder => .unboundReturnOutput
  | .discardedLetBinding => .unboundReturnOutput
  | .subsingletonOutputType => .unboundReturnOutput
  | .boilerplateOnlyMasking => .unboundReturnOutput
  | .vacuousUnderRequires => .survivedAllMutants

/-- Configuration options for `checkEnsuresBindsOutput` and
    `checkDeclEnsuresBindsOutput`. `stepHeartbeats` and `totalHeartbeats` are
    specified in `maxHeartbeats` option units (1 unit = 1000 internal heartbeats). -/
structure EnsuresCheckConfig : Type where
  useRequires : Bool := true
  userEnsuresOnly : Bool := true
  strictReturnValue : Bool := false
  stepHeartbeats : Nat := 50000
  totalHeartbeats : Nat := 250000
  deriving Repr, Inhabited

/-- Result of checking whether an `ensures` specification genuinely constrains its
    return output without vacuity. -/
structure EnsuresCheckResult : Type where
  bindsOutput : Bool
  reason? : Option EnsuresVacuityReason := none
  vacuityClass? : Option VacuityClass := none
  notes : List String := []
  deriving Repr, Inhabited

/-- Construct a passing `EnsuresCheckResult`. -/
def EnsuresCheckResult.ok (notes : List String := []) : EnsuresCheckResult :=
  { bindsOutput := true, reason? := none, vacuityClass? := none, notes }

/-- Construct a vacuity-flagged `EnsuresCheckResult` with consistent `vacuityClass?`. -/
def EnsuresCheckResult.vacuous (reason : EnsuresVacuityReason)
    (notes : List String := []) : EnsuresCheckResult :=
  { bindsOutput := false
    reason? := some reason
    vacuityClass? := some reason.toVacuityClass
    notes }

/-- Result of checking whether a `requires` precondition is satisfiable. -/
structure RequiresCheckResult : Type where
  satisfiable? : Option Bool
  reason : String
  deriving Repr, Inhabited

/-! ### Soundness & Anti-DoS Heartbeat / Prover Safeguards -/

/-- Compute a strictly positive internal heartbeat cap (`≥ 1000`) from a remaining
    internal heartbeat budget and a per-step cap in `maxHeartbeats` option units.
    Never returns `0`, because Lean 4 interprets `maxHeartbeats = 0` as unlimited.
    Returns `none` once `remainingInternal == 0`. -/
def cappedHeartbeats? (remainingInternal : Nat) (stepUnits : Nat) : Option Nat :=
  if remainingInternal == 0 then
    none
  else
    let stepInternal := max 1000 (stepUnits * 1000)
    some (max 1000 (min remainingInternal stepInternal))

/-- Run a `MetaM` computation under a strictly positive heartbeat cap, also respecting
    any tighter outer `Core.Context.maxHeartbeats`. Catches heartbeat timeouts and
    exceptions cleanly without leaking errors. -/
def withBoundedHeartbeats {α : Type} (capInternal : Nat) (x : MetaM α) :
    MetaM (Option α) := do
  let safeCap := max 1000 capInternal
  let now ← IO.getNumHeartbeats
  let origCtx ← readThe Core.Context
  let effCap : Nat :=
    if origCtx.maxHeartbeats == 0 then
      safeCap
    else
      let used := now - origCtx.initHeartbeats
      let parentRem :=
        if used < origCtx.maxHeartbeats then origCtx.maxHeartbeats - used else 1000
      max 1000 (min safeCap parentRem)
  try
    let res ← withTheReader Core.Context
      (fun ctx => { ctx with initHeartbeats := now, maxHeartbeats := effCap })
      x
    return some res
  catch _ =>
    return none

/-- Mutable internal-heartbeat budget tracker across bounded prover probes. -/
structure ProbeBudget : Type where
  startHeartbeats : Nat
  totalInternal : Nat
  stepUnits : Nat

def ProbeBudget.init (cfg : EnsuresCheckConfig) : BaseIO ProbeBudget := do
  let now ← IO.getNumHeartbeats
  let totalInternal := max 1000 (cfg.totalHeartbeats * 1000)
  return { startHeartbeats := now, totalInternal, stepUnits := cfg.stepHeartbeats }

def ProbeBudget.nextCap? (b : ProbeBudget) : BaseIO (Option Nat) := do
  let now ← IO.getNumHeartbeats
  let used := now - b.startHeartbeats
  let remaining := if used < b.totalInternal then b.totalInternal - used else 0
  return cappedHeartbeats? remaining b.stepUnits

/-- Introduce leading universal binders and unfold outer `Not` (`P → False`) arrows
    so negated conjunctions/existentials enter the local context for `destructHypsAux`. -/
private def introsUnfoldingNot : Nat → MVarId → MetaM MVarId
  | 0, mvarId => return mvarId
  | fuel + 1, mvarId => do
    let (_, mvarId) ← mvarId.intros
    let tgt := (← instantiateMVars (← mvarId.getType)).consumeMData
    if tgt.isAppOfArity ``Not 1 then
      let (_, mvarId') ← mvarId.intro1
      introsUnfoldingNot fuel mvarId'
    else
      return mvarId

/-- Destruct `Exists`, `And`, and `False` hypotheses in the local context of `mvarId`
    with explicit fuel (zero `partial`) and a `tried` guard so dependent hypotheses
    that reject `cases` never cause failures or loops. -/
private def destructHypsAux : Nat → Array FVarId → MVarId → MetaM (Option MVarId)
  | 0, _, mvarId => return some mvarId
  | fuel + 1, tried, mvarId => do
    mvarId.withContext do
      let lctx ← getLCtx
      let mut target? : Option (FVarId × Nat) := none
      for decl in lctx do
        if decl.isImplementationDetail || tried.contains decl.fvarId then continue
        let ty ← instantiateMVars decl.type
        let tyWhnf ← whnf ty
        if tyWhnf.isConstOf ``False then
          target? := some (decl.fvarId, 0)
          break
        else if tyWhnf.isAppOfArity ``And 2 then
          target? := some (decl.fvarId, 1)
          break
        else if tyWhnf.isAppOfArity ``Exists 2 then
          target? := some (decl.fvarId, 2)
          break
      match target? with
      | none => return some mvarId
      | some (fvarId, kind) =>
        try
          let subgoals ← mvarId.cases fvarId
          if kind == 0 then
            return none
          match subgoals.toList with
          | [] => return none
          | [sg] => destructHypsAux fuel tried sg.mvarId
          | _ => return some mvarId
        catch _ =>
          destructHypsAux fuel (tried.push fvarId) mvarId

/-- Run a single tactic syntax snippet against `goalTy` inside a fresh isolated
    metavariable, restoring `Core.State.messages`, verifying zero errors, zero `sorry`,
    zero unassigned metavariables, and full `Meta.check` kernel typechecking. -/
private def tryTacticSnippet
    (goalTy : Expr) (stepCapInternal : Nat) (tac : TSyntax `tactic) : MetaM Bool := do
  let savedMsgs := (← getThe Core.State).messages
  let result ← withoutModifyingState do
    modifyThe Core.State fun s => { s with messages := {} }
    let attempt? ← withBoundedHeartbeats stepCapInternal do
      let goalTy ← instantiateMVars goalTy
      if !(← isProp goalTy) then
        return false
      let mvar ← mkFreshExprSyntheticOpaqueMVar goalTy
      let mvarId ← introsUnfoldingNot 8 mvar.mvarId!
      let next? ← destructHypsAux 24 #[] mvarId
      let remaining ← match next? with
        | none => pure []
        | some mid =>
          Term.TermElabM.run' <| Tactic.run mid <| Tactic.evalTactic tac
      if !remaining.isEmpty then
        return false
      let proof ← instantiateMVars mvar
      let hasErrs := (← getThe Core.State).messages.hasErrors
      if hasErrs || proof.hasSorry || proof.hasExprMVar then
        return false
      Meta.check proof
      let proofTy ← inferType proof
      if !(← isDefEq proofTy goalTy) then
        return false
      return true
    return attempt?.getD false
  modifyThe Core.State fun s => { s with messages := savedMsgs }
  return result

/-- Sound, heartbeat-bounded, message-log-isolated prover for closed or local-context
    propositions `goalTy`. Tries fast deterministic tactics (`trivial`/`rfl`/
    `assumption`/`contradiction`/`decide`, `omega`, `simp_all`, `grind`) and accepts
    a proof only after `Meta.check` confirms zero `sorry`, zero mvars, and zero errors. -/
def tryProve (goalTy : Expr) (stepCapInternal : Nat := 50000000) : MetaM Bool := do
  let goalTy ← instantiateMVars goalTy
  if !(← isProp goalTy) then
    return false
  let tac1 ← `(tactic| first | trivial | rfl | assumption | contradiction | decide | omega)
  if ← tryTacticSnippet goalTy stepCapInternal tac1 then
    return true
  let tac2 ← `(tactic| (try simp_all) <;> first | trivial | rfl | assumption | contradiction | decide | omega)
  if ← tryTacticSnippet goalTy stepCapInternal tac2 then
    return true
  let tac3 ← `(tactic| grind)
  if ← tryTacticSnippet goalTy stepCapInternal tac3 then
    return true
  return false

/-! ### Structural Reduction, Subsingleton/Empty Type & Tautology Helpers -/

/-- Fuel-bounded zeta + beta reduction that eliminates unused `let` bindings and
    immediately applied lambdas without unfolding user or `Trusted` definitions. -/
def zetaBetaReduce : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, e =>
    match e with
    | .mdata _ b => zetaBetaReduce fuel b
    | .letE _ _ v b _ =>
      let v' := zetaBetaReduce fuel v
      zetaBetaReduce fuel (b.instantiate1 v')
    | .app f a =>
      let f' := zetaBetaReduce fuel f
      let a' := zetaBetaReduce fuel a
      match f' with
      | .lam _ _ body _ => zetaBetaReduce fuel (body.instantiate1 a')
      | _ => .app f' a'
    | .lam n t b bi =>
      .lam n (zetaBetaReduce fuel t) (zetaBetaReduce fuel b) bi
    | .forallE n t b bi =>
      .forallE n (zetaBetaReduce fuel t) (zetaBetaReduce fuel b) bi
    | .proj s i struct =>
      .proj s i (zetaBetaReduce fuel struct)
    | other => other

/-- Reduce trivial structure projections (`Meta.reduceProj?`) alongside `zetaBetaReduce`. -/
def zetaBetaProjReduce : Nat → Expr → MetaM Expr
  | 0, e => return zetaBetaReduce 64 e
  | fuel + 1, e => do
    let e := zetaBetaReduce 64 e
    match e with
    | .proj s i struct =>
      let struct' ← zetaBetaProjReduce fuel struct
      let e' := Expr.proj s i struct'
      match ← Meta.reduceProj? e' with
      | some r => zetaBetaProjReduce fuel r
      | none => return e'
    | .app f a =>
      let f' ← zetaBetaProjReduce fuel f
      let a' ← zetaBetaProjReduce fuel a
      match f' with
      | .lam _ _ body _ => zetaBetaProjReduce fuel (body.instantiate1 a')
      | _ => return .app f' a'
    | .lam n t b bi =>
      return .lam n (← zetaBetaProjReduce fuel t) (← zetaBetaProjReduce fuel b) bi
    | .forallE n t b bi =>
      return .forallE n (← zetaBetaProjReduce fuel t) (← zetaBetaProjReduce fuel b) bi
    | other => return other

/-- Check whether `e` is or reduces to natural number literal `target` (handling both
    raw nat literals, `OfNat.ofNat`, `Nat.zero`, and `Nat.succ`). -/
private def exprIsNatLit (e : Expr) (target : Nat) : MetaM Bool := do
  if let some n ← Meta.getNatValue? e then
    return n == target
  let e' ← whnf e
  if let some n ← Meta.getNatValue? e' then
    return n == target
  if target == 0 && e'.isConstOf ``Nat.zero then
    return true
  if target == 1 && e'.isAppOfArity ``Nat.succ 1 then
    let arg ← whnf e'.appArg!
    if arg.isConstOf ``Nat.zero then return true
    if let some n ← Meta.getNatValue? arg then return n == 0
  return false

/-- Fuel-bounded conservative detector for provably empty types (`Empty`, `PEmpty`,
    `False`, `Fin 0`, empty inductives, products with an empty component, or inductives
    every constructor of which requires an empty argument). Uses a `visited` cycle guard
    so recursive inhabited inductives (`Nat`, `List`, `Value`) are never false-flagged. -/
private def isEmptyTypeAux : Nat → NameSet → Expr → MetaM Bool
  | 0, _, _ => return false
  | fuel + 1, visited, ty => do
    let ty ← whnf ty
    let fn := ty.getAppFn
    let args := ty.getAppArgs
    match fn with
    | .const name lvls =>
      if name == ``Empty || name == ``PEmpty || name == ``False then
        return true
      if name == ``Fin && args.size == 1 then
        return ← exprIsNatLit args[0]! 0
      if (name == ``Prod || name == ``PProd || name == ``And) && args.size == 2 then
        if ← isEmptyTypeAux fuel visited args[0]! then return true
        return ← isEmptyTypeAux fuel visited args[1]!
      if (name == ``Sum || name == ``PSum) && args.size == 2 then
        if !(← isEmptyTypeAux fuel visited args[0]!) then return false
        return ← isEmptyTypeAux fuel visited args[1]!
      if visited.contains name then
        return false
      let env ← getEnv
      match env.find? name with
      | some (.inductInfo indVal) =>
        if indVal.ctors.isEmpty then
          return true
        -- Skip indexed families other than `Fin` handled above so we stay sound.
        if indVal.numIndices > 0 || args.size < indVal.numParams then
          return false
        let visited' := visited.insert name
        let params := args.extract 0 indVal.numParams
        for ctorName in indVal.ctors do
          let some (.ctorInfo ctorVal) := env.find? ctorName | return false
          if ctorVal.levelParams.length != lvls.length then return false
          let ctorTy := ctorVal.type.instantiateLevelParams ctorVal.levelParams lvls
          let ctorInst ← instantiateForall ctorTy params
          let ctorEmpty ← forallTelescope ctorInst fun ctorArgs _ => do
            for a in ctorArgs do
              let aTy ← inferType a
              if ← isEmptyTypeAux fuel visited' aTy then
                return true
            return false
          if !ctorEmpty then
            return false
        return true
      | _ => return false
    | _ => return false

/-- Conservative detector for subsingleton or empty output types (`Unit`, `PUnit`, `True`,
    `Empty`, `PEmpty`, `False`, `Fin 0`, `Fin 1`, `Option Empty`, `Option (Fin 0)`,
    `List Empty`, `Prop`s, products of subsingletons, or types with a synthesized
    `Subsingleton` instance). Never false-flags inhabited multi-valued types. -/
def isSubsingletonOrEmptyType : Nat → Expr → MetaM Bool
  | 0, _ => return false
  | fuel + 1, ty => do
    let ty ← whnf ty
    if ← isProp ty then
      return true
    if ← isEmptyTypeAux (fuel + 1) {} ty then
      return true
    let fn := ty.getAppFn
    let args := ty.getAppArgs
    if let .const name _ := fn then
      if name == ``Unit || name == ``PUnit || name == ``True then
        return true
      if name == ``Fin && args.size == 1 then
        if ← exprIsNatLit args[0]! 0 then return true
        if ← exprIsNatLit args[0]! 1 then return true
      if name == ``Option && args.size == 1 then
        if ← isEmptyTypeAux (fuel + 1) {} args[0]! then return true
      if name == ``List && args.size == 1 then
        if ← isEmptyTypeAux (fuel + 1) {} args[0]! then return true
      if (name == ``Prod || name == ``PProd) && args.size == 2 then
        let s0 ← isSubsingletonOrEmptyType fuel args[0]!
        let s1 ← isSubsingletonOrEmptyType fuel args[1]!
        if s0 && s1 then return true
      if name == ``Subtype && args.size == 2 then
        if ← isSubsingletonOrEmptyType fuel args[0]! then return true
    -- Fall back to Lean's `Subsingleton` typeclass synthesis (sound by construction).
    try
      let u ← getLevel ty
      match u with
      | .succ u' =>
        let subInst? ← synthInstance? (mkApp (mkConst ``Subsingleton [u']) ty)
        return subInst?.isSome
      | _ => return false
    catch _ =>
      return false

/-- Strip `Not` if `e` is `Not inner`. -/
private def unwrapNot? (e : Expr) : Option Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``Not 1 then
    some e.appArg!
  else
    none

/-- Fast syntactic tautology recognizer for `Prop` expressions (`True`, `r = r`,
    `¬ (r ≠ r)`, `r ≤ r`, `P ↔ P`, `P → P`, `A → B → A`, `r = r ∨ P`, `P ∨ ¬ P`). -/
def detectSyntacticTautology : Nat → List Expr → Expr → Option EnsuresVacuityReason
  | 0, _, _ => none
  | fuel + 1, hyps, e =>
    let e := e.consumeMData
    if e.isConstOf ``True then
      some .trivialConstantTrue
    else if hyps.any (fun h => h == e) then
      some .tautologicalImplication
    else if e.isAppOfArity ``Eq 3 then
      let args := e.getAppArgs
      if args[1]! == args[2]! then some .reflexiveEquality else none
    else if e.isAppOfArity ``LE.le 4 then
      let args := e.getAppArgs
      if args[2]! == args[3]! then some .reflexiveEquality else none
    else if e.isAppOfArity ``Iff 2 then
      let args := e.getAppArgs
      if args[0]! == args[1]! then some .tautologicalImplication else none
    else if e.isAppOfArity ``Not 1 then
      let inner := e.appArg!.consumeMData
      if inner.isConstOf ``False then
        some .trivialConstantTrue
      else if inner.isAppOfArity ``Ne 3 then
        let args := inner.getAppArgs
        if args[1]! == args[2]! then some .reflexiveEquality else none
      else if inner.isAppOfArity ``Not 1 then
        match detectSyntacticTautology fuel hyps inner.appArg! with
        | some r => some r
        | none => none
      else
        none
    else if e.isAppOfArity ``Or 2 then
      let lhs := e.appFn!.appArg!.consumeMData
      let rhs := e.appArg!.consumeMData
      if (detectSyntacticTautology fuel hyps lhs).isSome ||
         (detectSyntacticTautology fuel hyps rhs).isSome then
        some .tautologicalDisjunction
      else if unwrapNot? lhs == some rhs || unwrapNot? rhs == some lhs then
        some .tautologicalDisjunction
      else
        none
    else if e.isAppOfArity ``And 2 then
      let lhs := e.appFn!.appArg!
      let rhs := e.appArg!
      match detectSyntacticTautology fuel hyps lhs, detectSyntacticTautology fuel hyps rhs with
      | some r1, some _ => some r1
      | _, _ => none
    else
      match e with
      | .forallE _ dom body _ =>
        if !body.hasLooseBVars then
          let dom := dom.consumeMData
          let body := body.consumeMData
          if dom.isConstOf ``False then
            some .tautologicalImplication
          else if dom == body then
            some .tautologicalImplication
          else if (detectSyntacticTautology fuel (dom :: hyps) body).isSome then
            some .tautologicalImplication
          else
            none
        else
          none
      | _ => none

/-! ### `MirCallAns` Boilerplate-Atom Cofactoring (`k ≤ 8`) -/

/-- Whether `e` is an auto-generated external-spec boilerplate atom
    (`callFramePreserved` or `retMatchesCalleeReturnTy`). -/
private def isBoilerplateAtom (e : Expr) : Bool :=
  let fn := e.consumeMData.getAppFn
  match fn with
  | .const name _ =>
    name == ``Trusted.VerificationResult.callFramePreserved ||
    name == ``Trusted.VerificationResult.retMatchesCalleeReturnTy
  | _ => false

/-- Collect distinct boilerplate atoms occurring under propositional connectives,
    stopping once `limit` atoms have been gathered (bounded by `fuel`). -/
private def collectBoilerplateAtoms :
    Nat → Nat → Expr → Array Expr → Array Expr × Bool
  | 0, _, _, acc => (acc, false)
  | fuel + 1, limit, e, acc =>
    let e := e.consumeMData
    if isBoilerplateAtom e then
      if acc.any (fun a => a == e) then
        (acc, false)
      else if acc.size < limit then
        (acc.push e, false)
      else
        (acc, true)
    else if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2 then
      let (acc1, ov1) := collectBoilerplateAtoms fuel limit e.appFn!.appArg! acc
      let (acc2, ov2) := collectBoilerplateAtoms fuel limit e.appArg! acc1
      (acc2, ov1 || ov2)
    else if e.isAppOfArity ``Not 1 then
      collectBoilerplateAtoms fuel limit e.appArg! acc
    else if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
      let args := e.getAppArgs
      let (acc1, ov1) := collectBoilerplateAtoms fuel limit args[1]! acc
      let (acc2, ov2) := collectBoilerplateAtoms fuel limit args[3]! acc1
      let (acc3, ov3) := collectBoilerplateAtoms fuel limit args[4]! acc2
      (acc3, ov1 || ov2 || ov3)
    else
      match e with
      | .forallE _ dom body _ =>
        if !body.hasLooseBVars then
          let (acc1, ov1) := collectBoilerplateAtoms fuel limit dom acc
          let (acc2, ov2) := collectBoilerplateAtoms fuel limit body acc1
          (acc2, ov1 || ov2)
        else
          (acc, false)
      | .lam _ _ body _ =>
        collectBoilerplateAtoms fuel limit body acc
      | _ => (acc, false)

/-- Lookup the truth assignment (`true` / `false`) for `e` in `atoms` under bitmask `mask`. -/
private def lookupAtomMask? (atoms : Array Expr) (mask : Nat) (e : Expr) : Option Bool := Id.run do
  for i in [:atoms.size] do
    if atoms[i]! == e then
      return some (((mask >>> i) &&& 1) == 1)
  return none

private def mkBoolProp (b : Bool) : Expr :=
  if b then mkConst ``True else mkConst ``False

/-- Shannon cofactor `e` with respect to `atoms` under truth-assignment bitmask `mask`,
    simplifying propositional connectives and `ite`/`dite` conditions while keeping the
    resulting `Prop` expression well-typed. -/
private def cofactorBoilerplate : Nat → Array Expr → Nat → Expr → Expr
  | 0, _, _, e => e
  | fuel + 1, atoms, mask, e =>
    let e := e.consumeMData
    match lookupAtomMask? atoms mask e with
    | some b => mkBoolProp b
    | none =>
      if e.isAppOfArity ``And 2 then
        let p := cofactorBoilerplate fuel atoms mask e.appFn!.appArg!
        let q := cofactorBoilerplate fuel atoms mask e.appArg!
        if p.isConstOf ``False || q.isConstOf ``False then mkConst ``False
        else if p.isConstOf ``True then q
        else if q.isConstOf ``True then p
        else mkApp2 (mkConst ``And) p q
      else if e.isAppOfArity ``Or 2 then
        let p := cofactorBoilerplate fuel atoms mask e.appFn!.appArg!
        let q := cofactorBoilerplate fuel atoms mask e.appArg!
        if p.isConstOf ``True || q.isConstOf ``True then mkConst ``True
        else if p.isConstOf ``False then q
        else if q.isConstOf ``False then p
        else mkApp2 (mkConst ``Or) p q
      else if e.isAppOfArity ``Not 1 then
        let p := cofactorBoilerplate fuel atoms mask e.appArg!
        if p.isConstOf ``True then mkConst ``False
        else if p.isConstOf ``False then mkConst ``True
        else mkApp (mkConst ``Not) p
      else if e.isAppOfArity ``Iff 2 then
        let p := cofactorBoilerplate fuel atoms mask e.appFn!.appArg!
        let q := cofactorBoilerplate fuel atoms mask e.appArg!
        if p.isConstOf ``True then q
        else if q.isConstOf ``True then p
        else if p.isConstOf ``False then
          if q.isConstOf ``False then mkConst ``True else mkApp (mkConst ``Not) q
        else if q.isConstOf ``False then mkApp (mkConst ``Not) p
        else mkApp2 (mkConst ``Iff) p q
      else if e.isAppOfArity ``ite 5 then
        let args := e.getAppArgs
        let cond' := cofactorBoilerplate fuel atoms mask args[1]!
        if cond'.isConstOf ``True then
          cofactorBoilerplate fuel atoms mask args[3]!
        else if cond'.isConstOf ``False then
          cofactorBoilerplate fuel atoms mask args[4]!
        else
          let t' := cofactorBoilerplate fuel atoms mask args[3]!
          let f' := cofactorBoilerplate fuel atoms mask args[4]!
          mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, t', f']
      else if e.isAppOfArity ``dite 5 then
        let args := e.getAppArgs
        let cond' := cofactorBoilerplate fuel atoms mask args[1]!
        if cond'.isConstOf ``True then
          match args[3]! with
          | .lam _ _ tb _ =>
            if !tb.hasLooseBVar 0 then cofactorBoilerplate fuel atoms mask tb else e
          | _ => e
        else if cond'.isConstOf ``False then
          match args[4]! with
          | .lam _ _ fb _ =>
            if !fb.hasLooseBVar 0 then cofactorBoilerplate fuel atoms mask fb else e
          | _ => e
        else
          e
      else
        match e with
        | .forallE n dom body bi =>
          if !body.hasLooseBVars then
            let d' := cofactorBoilerplate fuel atoms mask dom
            let b' := cofactorBoilerplate fuel atoms mask body
            if d'.isConstOf ``False || b'.isConstOf ``True then mkConst ``True
            else if d'.isConstOf ``True then b'
            else .forallE n d' b' bi
          else
            e
        | _ => e

/-- Unfold a user-defined head predicate (excluding `Init`/`Std`/`Trusted` primitives)
    to expose constant or trivial `extraPost` definitions after boilerplate cofactoring. -/
private def unfoldUserHead : Nat → Expr → MetaM Expr
  | 0, e => return zetaBetaReduce 64 e
  | fuel + 1, e => do
    let e := zetaBetaReduce 64 e
    match e.getAppFn with
    | .const name _ =>
      let s := name.toString
      if s.startsWith "Init." || s.startsWith "Std." || s.startsWith "Trusted." ||
         name == ``True || name == ``False || name == ``And || name == ``Or ||
         name == ``Not || name == ``Eq || name == ``Ne || name == ``Iff ||
         name == ``Exists || name == ``LE.le || name == ``LT.lt then
        return e
      match ← unfoldDefinition? e with
      | some e' =>
        if e' != e then unfoldUserHead fuel e' else return e
      | none => return e
    | _ => return e

/-! ### Top-Level Lambda / Projection Normalization & Input/Output Splitting -/

/-- Expose leading lambda binders of `ensuresExpr` without destroying internal `let`
    bindings (so `discardedLetBinding` remains distinguishable from `unusedOutputBinder`). -/
private def exposeHeadLambda : Nat → Expr → MetaM Expr
  | 0, e => return e.consumeMData
  | fuel + 1, e => do
    let e := e.consumeMData
    if e.isLambda then
      return e
    match e with
    | .proj .. =>
      match ← reduceProj? e with
      | some e' => exposeHeadLambda fuel e'
      | none =>
        let e' ← whnfCore e
        if e' != e then exposeHeadLambda fuel e' else return e
    | _ =>
      let fn := e.getAppFn
      if let .const name _ := fn then
        if name == ``Eq || name == ``Ne || name == ``And || name == ``Or ||
           name == ``Not || name == ``Iff || name == ``True || name == ``False then
          return e
      match ← unfoldDefinition? e with
      | some e' =>
        if e' != e then exposeHeadLambda fuel e' else return e
      | none =>
        let e' ← whnfCore e
        if e' != e then exposeHeadLambda fuel e' else return e

/-- Safely apply `requiresExpr` to `preInputs` checking each argument's type via
    `isDefEq` and verifying the resulting expression is a `Prop`. -/
private def applyRequiresSafe (requiresExpr : Expr) (preInputs : Array Expr) :
    MetaM (Option Expr) := do
  let mut cur := requiresExpr
  for arg in preInputs do
    let ty ← whnf (← inferType cur)
    match ty with
    | .forallE _ dom _ _ =>
      let argTy ← inferType arg
      if ← isDefEq argTy dom then
        cur := (mkApp cur arg).headBeta
      else
        return none
    | _ => return none
  if ← isProp cur then
    return some cur
  else
    return none

/-- Fuel-bounded reduction of a `MirCallAns` postcondition applied to
    `MirCallAns.returned retVal memAfter` that resolves `MirCallContract.post`,
    `externalSpecCallContract`, and `match ans` WITHOUT unfolding `ite`/`dite` or the
    boilerplate predicates `callFramePreserved` / `retMatchesCalleeReturnTy`. -/
private def reduceMirCallAnsReturnedAux : Nat → Expr → MetaM Expr
  | 0, e => return e.consumeMData.headBeta
  | fuel + 1, e => do
    let e := e.consumeMData.headBeta
    if isBoilerplateAtom e ||
       e.isConstOf ``True || e.isConstOf ``False ||
       e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 ||
       e.isAppOfArity ``Not 1 || e.isAppOfArity ``Iff 2 ||
       e.isAppOfArity ``Eq 3 || e.isAppOfArity ``Ne 3 ||
       e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
      return e
    match ← reduceMatcher? e with
    | .reduced val => return ← reduceMirCallAnsReturnedAux fuel val
    | _ => pure ()
    if let .proj .. := e then
      if let some val ← reduceProj? e then
        return ← reduceMirCallAnsReturnedAux fuel val
    let eCore ← whnfCore e
    if eCore != e then
      return ← reduceMirCallAnsReturnedAux fuel eCore
    match ← unfoldDefinition? e with
    | some e' =>
      if e' != e then reduceMirCallAnsReturnedAux fuel e' else return e
    | none => return e

private def reduceMirCallAnsReturned (postExpr req retVal memAfter : Expr) :
    MetaM Expr := do
  let ans := mkApp2 (mkConst ``Trusted.Rustc.V2026_06_01.MirSemantics.MirCallAns.returned) retVal memAfter
  let applied := mkApp2 postExpr req ans
  reduceMirCallAnsReturnedAux 24 applied

/-- Core analyzer operating once `preInputs`, `fixedVars`, `outVars`, `rawBody`,
    `isMirCallAns`, and `requiresExpr?` have been isolated inside the local context. -/
private def analyzeNormalizedSpec
    (preInputs fixedVars outVars : Array Expr)
    (rawBody : Expr)
    (isMirCallAns : Bool)
    (requiresExpr? : Option Expr)
    (cfg : EnsuresCheckConfig) : MetaM EnsuresCheckResult := do
  let budget ← ProbeBudget.init cfg
  let outFVarIds : Array FVarId := outVars.map Expr.fvarId!
  let allFixed := preInputs ++ fixedVars
  let allVars := allFixed ++ outVars

  -- Phase 0: Check whether `requires` is provably unsatisfiable (`DeadPrecondition`).
  let preProp? ←
    if cfg.useRequires then
      match requiresExpr? with
      | some reqExpr => applyRequiresSafe reqExpr preInputs
      | none => pure none
    else
      pure none

  let preNorm? ←
    match preProp? with
    | some preProp => pure (some (← unfoldUserHead 8 (zetaBetaReduce 64 preProp)))
    | none => pure none

  if let some preNorm := preNorm? then
    if preNorm.isConstOf ``False then
      return .vacuous .requiresUnsatisfiable ["requires is syntactically False"]
    if let some cap ← budget.nextCap? then
      let unsatPreGoal ← mkForallFVars preInputs (mkApp (mkConst ``Not) preNorm)
      if ← tryProve unsatPreGoal cap then
        return .vacuous .requiresUnsatisfiable
          ["requires proved unsatisfiable for all inputs"]

  -- Phase 1: Subsingleton or empty output type (`UnboundReturnOutput`).
  if !outVars.isEmpty then
    let mut allSubsingleton := true
    for ov in outVars do
      let ovTy ← inferType ov
      if !(← isSubsingletonOrEmptyType 16 ovTy) then
        allSubsingleton := false
        break
    if allSubsingleton then
      return .vacuous .subsingletonOutputType
        ["all inspected output types are subsingleton or empty"]

  -- Phase 2: Bare `True` / `False`, discarded `let`/beta bindings, unused output binder.
  let rawClean := rawBody.consumeMData
  if rawClean.isConstOf ``True then
    return .vacuous .trivialConstantTrue ["ensures is syntactically True"]
  if rawClean.isConstOf ``False then
    return .vacuous .unrealizableUnderRequires ["ensures is syntactically False"]

  let freeBefore := rawClean.hasAnyFVar (fun fv => outFVarIds.contains fv)
  let reducedBody ← zetaBetaProjReduce 32 rawClean
  let freeAfter := reducedBody.hasAnyFVar (fun fv => outFVarIds.contains fv)

  if freeBefore && !freeAfter then
    return .vacuous .discardedLetBinding
      ["output variable occurs only in a discarded let/beta binding"]

  if !freeAfter then
    -- Check syntactic tautologies (e.g. `x < 10 → x < 10`) vs unused input-only formulas.
    if reducedBody.isConstOf ``True then
      return .vacuous .trivialConstantTrue ["ensures reduces to True"]
    if reducedBody.isConstOf ``False then
      return .vacuous .unrealizableUnderRequires ["ensures reduces to False"]
    return .vacuous .unusedOutputBinder
      ["output variable does not occur free in ensures body"]

  -- Phase 3: `MirCallAns` boilerplate-atom cofactoring (`k ≤ 8`).
  let mut notes : List String := []
  if isMirCallAns && cfg.userEnsuresOnly then
    let (atoms, overflow) := collectBoilerplateAtoms 64 8 reducedBody #[]
    if overflow then
      notes := notes ++ ["skipped boilerplate cofactoring: >8 boilerplate atoms"]
    else if !atoms.isEmpty then
      let numMasks := 1 <<< atoms.size
      let mut anyNonFalse := false
      let mut anyGenuineOutputConstraint := false
      let mut firstTautReason? : Option EnsuresVacuityReason := none
      for mask in [:numMasks] do
        let rawRes := cofactorBoilerplate 64 atoms mask reducedBody
        let res ← unfoldUserHead 8 rawRes
        if res.isConstOf ``False then
          continue
        anyNonFalse := true
        -- Check whether this non-False fibre still constrains an output variable.
        let fibreBindsOut := res.hasAnyFVar (fun fv => outFVarIds.contains fv)
        if !fibreBindsOut then
          continue
        -- Output occurs in `res`; verify `res` is not syntactically tautological.
        match detectSyntacticTautology 32 [] res with
        | some r =>
          if firstTautReason?.isNone then firstTautReason? := some r
        | none =>
          -- Check bounded prover tautology / impossibility on this fibre.
          let mut fibreTrivial := false
          if let some cap ← budget.nextCap? then
            let fibreTautGoal ← mkForallFVars allVars res
            if ← tryProve fibreTautGoal cap then
              fibreTrivial := true
              if firstTautReason?.isNone then
                firstTautReason? := some .tautologicalByProver
          if !fibreTrivial then
            anyGenuineOutputConstraint := true
      if !anyNonFalse then
        return .vacuous .unrealizableUnderRequires
          (notes ++ ["all boilerplate fibres simplify to False"])
      if !anyGenuineOutputConstraint then
        match firstTautReason? with
        | some r =>
          return .vacuous r
            (notes ++ ["residual user ensures across boilerplate fibres is tautological"])
        | none =>
          return .vacuous .boilerplateOnlyMasking
            (notes ++ ["normal-return postcondition constrains only boilerplate atoms"])

  -- Phase 4: Syntactic tautology & global prover checks (without `requires`).
  if let some tautReason := detectSyntacticTautology 32 [] reducedBody then
    return .vacuous tautReason (notes ++ ["detected syntactic tautology"])

  if let some cap ← budget.nextCap? then
    let globalTautGoal ← mkForallFVars allVars reducedBody
    if ← tryProve globalTautGoal cap then
      return .vacuous .tautologicalByProver
        (notes ++ ["ensures proved universally valid independent of requires"])

  if let some cap ← budget.nextCap? then
    let globalUnsatGoal ← mkForallFVars allVars (mkApp (mkConst ``Not) reducedBody)
    if ← tryProve globalUnsatGoal cap then
      return .vacuous .unrealizableUnderRequires
        (notes ++ ["ensures proved unsatisfiable for all inputs and outputs"])

  -- Phase 5: `requires`-aware semantic realizability and vacuity checks.
  if let some preNorm := preNorm? then
    let resUnderPre ← withLocalDeclD `h_pre preNorm fun hPre => do
      let scopedVars := preInputs ++ #[hPre] ++ fixedVars ++ outVars
      if let some cap ← budget.nextCap? then
        let unsatGoal ← mkForallFVars scopedVars (mkApp (mkConst ``Not) reducedBody)
        if ← tryProve unsatGoal cap then
          return some (EnsuresCheckResult.vacuous .unrealizableUnderRequires
            (notes ++ ["ensures proved unsatisfiable under requires"]))
      if let some cap ← budget.nextCap? then
        let tautGoal ← mkForallFVars scopedVars reducedBody
        if ← tryProve tautGoal cap then
          return some (EnsuresCheckResult.vacuous .vacuousUnderRequires
            (notes ++ ["ensures proved vacuously true for all outputs under requires"]))
      return none
    if let some r := resUnderPre then
      return r

  return .ok notes

/-- Check whether `ensuresExpr` (optionally paired with `requiresExpr?`) genuinely
    constrains its return output without falling into any of the 5 `VacuityClass`
    failure modes. Supports:
    - Stateless `(inputs..., ret)` specs,
    - Stateful `(args, mem, ret, mem')` specs (with `cfg.strictReturnValue` holding
      `mem'` fixed to catch return-ignoring stateful postconditions), and
    - External call `(req, ans : MirCallAns)` specs (projecting onto `.returned` and
      cofactoring `callFramePreserved` / `retMatchesCalleeReturnTy` boilerplate). -/
def checkEnsuresBindsOutput
    (ensuresExpr : Expr)
    (requiresExpr? : Option Expr := none)
    (cfg : EnsuresCheckConfig := {}) : MetaM EnsuresCheckResult := do
  let ensuresExposed ← exposeHeadLambda 16 ensuresExpr
  let ensuresTy ← inferType ensuresExposed
  forallTelescopeReducing ensuresTy fun allArgs retSort => do
    if !(← isDefEq retSort (mkSort Level.zero)) then
      return .vacuous .unusedOutputBinder ["ensures expression does not return Prop"]
    let n := allArgs.size
    if n == 0 then
      let body := ensuresExposed.consumeMData
      if body.isConstOf ``True then
        return .vacuous .trivialConstantTrue ["0-ary ensures is True"]
      else if body.isConstOf ``False then
        return .vacuous .unrealizableUnderRequires ["0-ary ensures is False"]
      else
        return .vacuous .unusedOutputBinder ["0-ary ensures has no output binder"]

    let lastArg := allArgs[n - 1]!
    let lastTy ← whnf (← inferType lastArg)

    -- Shape 1: `(req, ans : MirCallAns)` external call contract.
    if n == 2 && lastTy.isConstOf ``MirCallAns then
      let req := allArgs[0]!
      withLocalDeclD `retVal (mkConst ``Value) fun retVal =>
        withLocalDeclD `memAfter (mkConst ``Memory) fun memAfter => do
          let normalBody ← reduceMirCallAnsReturned ensuresExposed req retVal memAfter
          let (fixedVars, outVars) :=
            if cfg.strictReturnValue then (#[memAfter], #[retVal])
            else (#[], #[retVal, memAfter])
          analyzeNormalizedSpec #[req] fixedVars outVars normalBody true requiresExpr? cfg
    else
      -- Apply `ensuresExposed` to `allArgs` and perform ONLY head beta reduction so
      -- internal `let _ := ret; ...` bindings are preserved for Phase 2 detection.
      let rawBody := (mkAppN ensuresExposed allArgs).headBeta
      -- Shape 2: Stateful `(args, mem, ret, mem')` where last binder is `Memory`.
      let isStateful4 ← do
        if n >= 4 && lastTy.isConstOf ``Memory then
          let prevTy ← whnf (← inferType allArgs[n - 2]!)
          pure (!prevTy.isConstOf ``Memory)
        else
          pure false
      if isStateful4 then
        let preInputs := allArgs.extract 0 (n - 2)
        let retVar := allArgs[n - 2]!
        let memVar := allArgs[n - 1]!
        let (fixedVars, outVars) :=
          if cfg.strictReturnValue then (#[memVar], #[retVar])
          else (#[], #[retVar, memVar])
        analyzeNormalizedSpec preInputs fixedVars outVars rawBody false requiresExpr? cfg
      else
        -- Shape 3: General `(inputs..., ret)`.
        let preInputs := allArgs.extract 0 (n - 1)
        let outVars := #[lastArg]
        analyzeNormalizedSpec preInputs #[] outVars rawBody false requiresExpr? cfg

/-- Check a named declaration (`Claim`, `StatefulClaim`, `TotalClaim`, `ModularClaim`,
    `MirCallContract`, or standalone `ensures` predicate) for vacuity. -/
def checkDeclEnsuresBindsOutput
    (declName : Name) (cfg : EnsuresCheckConfig := {}) : MetaM EnsuresCheckResult := do
  let env ← getEnv
  let some info := env.find? declName
    | throwError "checkDeclEnsuresBindsOutput: unknown declaration `{declName}`"
  let declExpr := mkConst declName (info.levelParams.map Level.param)
  let ty ← whnf info.type
  if ty.isConstOf ``Claim then
    let preExpr := mkApp (mkConst ``Claim.pre) declExpr
    let postExpr := mkApp (mkConst ``Claim.post) declExpr
    checkEnsuresBindsOutput postExpr (if cfg.useRequires then some preExpr else none) cfg
  else if ty.isConstOf ``StatefulClaim then
    let preExpr := mkApp (mkConst ``StatefulClaim.pre) declExpr
    let postExpr := mkApp (mkConst ``StatefulClaim.post) declExpr
    checkEnsuresBindsOutput postExpr (if cfg.useRequires then some preExpr else none) cfg
  else if ty.isConstOf ``TotalClaim then
    let preExpr := mkApp (mkConst ``TotalClaim.pre) declExpr
    let postExpr := mkApp (mkConst ``TotalClaim.post) declExpr
    checkEnsuresBindsOutput postExpr (if cfg.useRequires then some preExpr else none) cfg
  else if ty.isConstOf ``ModularClaim then
    let preExpr := mkApp (mkConst ``ModularClaim.pre) declExpr
    let postExpr := mkApp (mkConst ``ModularClaim.post) declExpr
    checkEnsuresBindsOutput postExpr (if cfg.useRequires then some preExpr else none) cfg
  else if ty.isConstOf ``MirCallContract then
    let preExpr := mkApp (mkConst ``MirCallContract.pre) declExpr
    let postExpr := mkApp (mkConst ``MirCallContract.post) declExpr
    checkEnsuresBindsOutput postExpr (if cfg.useRequires then some preExpr else none) cfg
  else
    checkEnsuresBindsOutput declExpr none cfg

/-- Build nested `Exists` proposition `∃ x₀ ... x_{k-1}, body` over `fvars`. -/
private def mkNestedExists (fvars : Array Expr) (body : Expr) : MetaM Expr := do
  let mut cur := body
  for i in [:fvars.size] do
    let idx := fvars.size - 1 - i
    let fv := fvars[idx]!
    let lam ← mkLambdaFVars #[fv] cur
    cur ← mkAppM ``Exists #[lam]
  return cur

/-- Synthesize a lightweight concrete witness candidate for an input type when
    checking satisfiability of a `requires` predicate. -/
private def defaultWitnessForType? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnf ty
  if ty.isConstOf ``Nat then
    return some (mkNatLit 0)
  if ty.isConstOf ``Bool then
    return some (mkConst ``Bool.false)
  if ty.isConstOf ``Memory then
    return some (mkConst ``Trusted.Rustc.V2026_06_01.MirSemantics.emptyMemory)
  if ty.isConstOf ``Value then
    return some (mkConst ``Trusted.Rustc.V2026_06_01.MirSemantics.Value.unit)
  if ty.isAppOfArity ``List 1 then
    let elemTy := ty.appArg!
    let u ← getLevel elemTy
    match u with
    | .succ u' => return some (mkApp (mkConst ``List.nil [u']) elemTy)
    | _ => pure ()
  try
    let u ← getLevel ty
    match u with
    | .succ u' =>
      if let some inh ← synthInstance? (mkApp (mkConst ``Inhabited [u']) ty) then
        return some (mkApp2 (mkConst ``Inhabited.default [u']) ty inh)
    | _ => pure ()
  catch _ => pure ()
  return none

/-- Check whether `requiresExpr` is satisfiable, returning `some false` when refuted
    for all inputs, `some true` when a witness or `True` over inhabited inputs is
    confirmed, or `none` when undecided within bounded heartbeats. -/
def checkRequiresSatisfiable (requiresExpr : Expr)
    (cfg : EnsuresCheckConfig := {}) : MetaM RequiresCheckResult := do
  let budget ← ProbeBudget.init cfg
  let reqExposed ← exposeHeadLambda 16 requiresExpr
  let reqTy ← inferType reqExposed
  forallTelescopeReducing reqTy fun inputs _ => do
    let rawBody := (mkAppN reqExposed inputs).headBeta
    let normBody ← unfoldUserHead 8 (zetaBetaReduce 64 rawBody)
    if normBody.isConstOf ``False then
      return { satisfiable? := some false, reason := "precondition is syntactically False" }
    if let some cap ← budget.nextCap? then
      let unsatGoal ← mkForallFVars inputs (mkApp (mkConst ``Not) rawBody)
      if ← tryProve unsatGoal cap then
        return {
          satisfiable? := some false
          reason := "precondition proved unsatisfiable for all inputs"
        }
    if normBody.isConstOf ``True then
      let mut allInhabited := true
      for inp in inputs do
        let inpTy ← inferType inp
        let u ← getLevel inpTy
        match u with
        | .succ u' =>
          let inh? ← synthInstance? (mkApp (mkConst ``Nonempty [u']) inpTy)
          if inh?.isNone then
            let def? ← synthInstance? (mkApp (mkConst ``Inhabited [u']) inpTy)
            if def?.isNone then
              allInhabited := false
              break
        | _ => pure ()
      if allInhabited then
        return {
          satisfiable? := some true
          reason := "precondition is True over inhabited input types"
        }
    -- Try instantiating inputs with canonical default witnesses (e.g. `0`, `[]`, `emptyMemory`).
    let mut witnesses : Array Expr := #[]
    let mut allWitnessed := true
    for inp in inputs do
      let inpTy ← inferType inp
      match ← defaultWitnessForType? inpTy with
      | some w => witnesses := witnesses.push w
      | none =>
        allWitnessed := false
        break
    if allWitnessed then
      if let some cap ← budget.nextCap? then
        let instGoal := (mkAppN reqExposed witnesses).headBeta
        if ← tryProve instGoal cap then
          return {
            satisfiable? := some true
            reason := "precondition proved satisfiable via canonical witness"
          }
    if let some cap ← budget.nextCap? then
      let satGoal ← mkNestedExists inputs rawBody
      if ← tryProve satGoal cap then
        return {
          satisfiable? := some true
          reason := "precondition proved satisfiable"
        }
    return {
      satisfiable? := none
      reason := "precondition satisfiability undecided within bounded budget"
    }

/-- Assert inside `MetaM` that `ensuresExpr` (optionally with `requiresExpr?`) binds its
    return output and passes all vacuity checks. -/
def assertEnsuresBindsOutput
    (ensuresExpr : Expr)
    (requiresExpr? : Option Expr := none)
    (cfg : EnsuresCheckConfig := {}) : MetaM Unit := do
  let res ← checkEnsuresBindsOutput ensuresExpr requiresExpr? cfg
  unless res.bindsOutput do
    throwError "assertEnsuresBindsOutput failed: flagged vacuous \
      (reason := {repr res.reason?}, class := {repr res.vacuityClass?}, notes := {res.notes})"

/-- Assert inside `MetaM` that `ensuresExpr` (optionally with `requiresExpr?`) is flagged
    vacuous (`bindsOutput == false`) and, if `expectedClass?` is provided, matches that
    exact `VacuityClass`. -/
def assertEnsuresVacuous
    (ensuresExpr : Expr)
    (requiresExpr? : Option Expr := none)
    (expectedClass? : Option VacuityClass := none)
    (cfg : EnsuresCheckConfig := {}) : MetaM Unit := do
  let res ← checkEnsuresBindsOutput ensuresExpr requiresExpr? cfg
  if res.bindsOutput then
    throwError "assertEnsuresVacuous failed: expected vacuous spec \
      (expectedClass := {repr expectedClass?}), but checker accepted it (notes := {res.notes})"
  if let some expected := expectedClass? then
    unless res.vacuityClass? == some expected do
      throwError "assertEnsuresVacuous failed: expected VacuityClass \
        {expected.canonicalName}, got {repr res.vacuityClass?} \
        (reason := {repr res.reason?}, notes := {res.notes})"

/-- Declaration-level convenience wrapper around `assertEnsuresBindsOutput`. -/
def assertDeclEnsuresBindsOutput
    (declName : Name) (cfg : EnsuresCheckConfig := {}) : MetaM Unit := do
  let res ← checkDeclEnsuresBindsOutput declName cfg
  unless res.bindsOutput do
    throwError "assertDeclEnsuresBindsOutput failed on `{declName}`: flagged vacuous \
      (reason := {repr res.reason?}, class := {repr res.vacuityClass?}, notes := {res.notes})"

/-- Declaration-level convenience wrapper around `assertEnsuresVacuous`. -/
def assertDeclEnsuresVacuous
    (declName : Name)
    (expectedClass? : Option VacuityClass := none)
    (cfg : EnsuresCheckConfig := {}) : MetaM Unit := do
  let res ← checkDeclEnsuresBindsOutput declName cfg
  if res.bindsOutput then
    throwError "assertDeclEnsuresVacuous failed on `{declName}`: expected vacuous spec \
      (expectedClass := {repr expectedClass?}), but checker accepted it (notes := {res.notes})"
  if let some expected := expectedClass? then
    unless res.vacuityClass? == some expected do
      throwError "assertDeclEnsuresVacuous failed on `{declName}`: expected VacuityClass \
        {expected.canonicalName}, got {repr res.vacuityClass?} \
        (reason := {repr res.reason?}, notes := {res.notes})"

end MetaChecker

end Anneal.SpecRealizability
