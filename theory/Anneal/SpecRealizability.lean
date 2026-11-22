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
   - Every vacuity verdict that is not purely syntactic rests on a `Meta.check`ed
     proof: of validity, of unsatisfiability, or of output-insensitivity
     (`∀ x y y', post x y → post x y'`, i.e. `ForwardOutputInsensitive`, which refutes
     `PostconditionDichotomy`). A probe that fails or exhausts its heartbeat budget
     (a runtime exception, contained by `withBoundedHeartbeats`) never flags a
     specification, so the checker has no false positives by construction; missed
     detections are bounded by the strength of the prover.
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

/-- One-directional form of `OutputInsensitive`: under `pre`, accepting one output
    forces accepting every other output. This is the exact shape discharged by the
    `MetaM` output-insensitivity probe (`∀ x y y', post x y → post x y'`). -/
def ForwardOutputInsensitive {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ∀ x, pre x → ∀ y₁ y₂, post x y₁ → post x y₂

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

/-- Observational determinism holds iff the postcondition kills every mutant whose
    observation differs from an accepted output. -/
theorem contractDeterministicOn_iff_kills_every_obs_nonequivalent_mutant
    {X : Type u} {Y : Type v} {Z : Type w}
    {obs : Y → Z} {pre : X → Prop} {post : X → Y → Prop} :
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

theorem outputInsensitive_iff_forwardOutputInsensitive
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop} :
    OutputInsensitive pre post ↔ ForwardOutputInsensitive pre post := by
  constructor
  · intro h x hPre y₁ y₂ h1
    exact (h x hPre y₁ y₂).mp h1
  · intro h x hPre y₁ y₂
    exact ⟨h x hPre y₁ y₂, h x hPre y₂ y₁⟩

/-- Kernel justification of the `MetaM` output-insensitivity probe: a contract whose
    postcondition is forward output-insensitive under `pre` can never satisfy
    `PostconditionDichotomy`, so flagging it is never a false positive. -/
theorem not_postconditionDichotomy_of_forwardOutputInsensitive
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hInsens : ForwardOutputInsensitive pre post) :
    ¬ PostconditionDichotomy pre post := by
  rintro ⟨x, hPre, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩
  exact hBad (hInsens x hPre y_ok y_bad hOk)

/-- A tautological-under-`pre` postcondition is forward output-insensitive. -/
theorem forwardOutputInsensitive_of_trivial
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hTriv : ∀ x y, pre x → post x y) :
    ForwardOutputInsensitive pre post :=
  fun x hPre _ y₂ _ => hTriv x y₂ hPre

/-- An unrealizable-under-`pre` postcondition is forward output-insensitive. -/
theorem forwardOutputInsensitive_of_impossible
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hImp : ∀ x y, pre x → ¬ post x y) :
    ForwardOutputInsensitive pre post :=
  fun x hPre y₁ _ h1 => absurd h1 (hImp x y₁ hPre)

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

/-- One-directional form of `not_dichotomyModuloObservation_of_fibre_insensitive`,
    matching the per-fibre output-insensitivity goal discharged by the `MetaM` checker:
    a postcondition that cannot tell apart two outputs sharing an observation has no
    dichotomy modulo that observation. -/
theorem not_dichotomyModuloObservation_of_fibre_forwardInsensitive
    {X : Type u} {Y : Type v} {Z : Type w}
    {obs : X → Y → Z} {pre : X → Prop} {post : X → Y → Prop}
    (hInsens : ∀ x y₁ y₂, pre x → obs x y₁ = obs x y₂ → post x y₁ → post x y₂) :
    ¬ DichotomyModuloObservation obs pre post := by
  rintro ⟨x, hPre, y_ok, y_bad, hObsEq, hOk, hBad⟩
  exact hBad (hInsens x y_ok y_bad hPre hObsEq hOk)

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

/-- Disjunctive preconditions satisfy `PostconditionDichotomy` iff at least one
    branch satisfies dichotomy: a multi-branch contract that genuinely binds its
    output on one valid branch is not vacuous merely because another branch is weaker. -/
theorem postconditionDichotomy_or_pre_iff
    {X : Type u} {Y : Type v} {pre₁ pre₂ : X → Prop} {post : X → Y → Prop} :
    PostconditionDichotomy (fun x => pre₁ x ∨ pre₂ x) post ↔
      PostconditionDichotomy pre₁ post ∨ PostconditionDichotomy pre₂ post := by
  constructor
  · rintro ⟨x, hPre, hOk, hBad⟩
    rcases hPre with h1 | h2
    · exact Or.inl ⟨x, h1, hOk, hBad⟩
    · exact Or.inr ⟨x, h2, hOk, hBad⟩
  · intro hOr
    rcases hOr with ⟨x, h1, hOk, hBad⟩ | ⟨x, h2, hOk, hBad⟩
    · exact ⟨x, Or.inl h1, hOk, hBad⟩
    · exact ⟨x, Or.inr h2, hOk, hBad⟩

/-- A disjunctive precondition refutes `PostconditionDichotomy` iff every branch
    fails dichotomy (for example, one branch is unsatisfiable and the other makes
    `post` output-insensitive). -/
theorem not_postconditionDichotomy_or_pre_iff
    {X : Type u} {Y : Type v} {pre₁ pre₂ : X → Prop} {post : X → Y → Prop} :
    ¬ PostconditionDichotomy (fun x => pre₁ x ∨ pre₂ x) post ↔
      ¬ PostconditionDichotomy pre₁ post ∧ ¬ PostconditionDichotomy pre₂ post := by
  constructor
  · intro hNot
    exact ⟨fun h1 => hNot (Iff.mpr (postconditionDichotomy_or_pre_iff (pre₁ := pre₁) (pre₂ := pre₂)) (Or.inl h1)),
      fun h2 => hNot (Iff.mpr (postconditionDichotomy_or_pre_iff (pre₁ := pre₁) (pre₂ := pre₂)) (Or.inr h2))⟩
  · rintro ⟨hNot1, hNot2⟩ hOr
    rcases Iff.mp (postconditionDichotomy_or_pre_iff (pre₁ := pre₁) (pre₂ := pre₂)) hOr with h1 | h2
    · exact hNot1 h1
    · exact hNot2 h2

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

/-- Kernel justification of `strictReturnValue`: a `StatefulClaim` whose postcondition
    cannot tell two return values apart once `(args, mem, mem')` are fixed has no strict
    return-value dichotomy, however tightly it constrains `mem'` (for example
    `retVal = retVal ∧ mem' = mem`). -/
theorem not_statefulClaimReturnDichotomy_of_returnInsensitive {c : StatefulClaim}
    (hInsens : ∀ args mem mem' v₁ v₂,
      c.pre args mem → c.post args mem v₁ mem' → c.post args mem v₂ mem') :
    ¬ StatefulClaimReturnDichotomy c := by
  rintro ⟨args, mem, mem', v_ok, v_bad, hPre, hOk, hBad⟩
  exact hBad (hInsens args mem mem' v_ok v_bad hPre hOk)

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

/-- A `MirCallContract` whose normal-return postcondition cannot tell two return values
    apart once `(req, memAfter)` are fixed has no strict return-value dichotomy. -/
theorem not_mirCallContractReturnValueDichotomy_of_returnInsensitive {c : MirCallContract}
    (hInsens : ∀ req m v₁ v₂,
      c.pre req → c.post req (.returned v₁ m) → c.post req (.returned v₂ m)) :
    ¬ MirCallContractReturnValueDichotomy c := by
  rintro ⟨req, m, v_ok, v_bad, hPre, hOk, hBad⟩
  exact hBad (hInsens req m v_ok v_bad hPre hOk)

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
  | outputInsensitive
  | vacuousUnderRequires
  | outputInsensitiveUnderRequires
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
  | .outputInsensitive => .unboundReturnOutput
  | .vacuousUnderRequires => .survivedAllMutants
  | .outputInsensitiveUnderRequires => .survivedAllMutants

/-- Configuration options for `checkEnsuresBindsOutput` and
    `checkDeclEnsuresBindsOutput`. `stepHeartbeats` and `totalHeartbeats` are
    specified in `maxHeartbeats` option units (1 unit = 1000 internal heartbeats).
    `totalHeartbeats` is additionally clamped to three quarters of what the enclosing
    `maxHeartbeats` context has left (`clampProbeBudget`).

    With `strictReturnValue := true`, a stateful `(args, mem, ret, mem')` or external
    call postcondition must distinguish return values with the post-memory held
    fixed: constraining only `mem'`, or mentioning `ret` without constraining it
    (`ret = ret ∧ mem' = mem`), is reported as `UnboundReturnOutput`. -/
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
    any tighter outer `Core.Context.maxHeartbeats`. Returns `none` when the computation
    throws, including when it exhausts the heartbeat cap or the recursion depth.

    Heartbeat and recursion-depth exhaustion are *runtime* exceptions, which the
    ordinary `try ... catch` of `CoreM`-based monads deliberately re-throws; they are
    intercepted here with `tryCatchRuntimeEx` so an over-budget probe is reported as
    undecided instead of aborting the whole checker. Interrupt exceptions still
    propagate. -/
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
  tryCatchRuntimeEx
    (do
      let res ← withTheReader Core.Context
        (fun ctx => { ctx with initHeartbeats := now, maxHeartbeats := effCap })
        x
      return some res)
    (fun _ => return none)

/-- Mutable internal-heartbeat budget tracker across bounded prover probes. -/
structure ProbeBudget : Type where
  startHeartbeats : Nat
  totalInternal : Nat
  stepUnits : Nat

/-- Clamp a requested total probe budget (internal heartbeats) against what the
    enclosing `maxHeartbeats` context has left (`none` when that context is unlimited).

    At most three quarters of the remaining outer budget is ever claimed, so the
    probes run dry and the checker returns a verdict before the enclosing command's
    own heartbeat limit is reached; otherwise a default `totalHeartbeats` larger than
    the ambient `maxHeartbeats` would turn a hard specification into an outer timeout.
    The result is never below `1000` and never `0`. -/
def clampProbeBudget (requestedInternal : Nat) (outerRemaining? : Option Nat) : Nat :=
  let requested := max 1000 requestedInternal
  match outerRemaining? with
  | none => requested
  | some outerRemaining => max 1000 (min requested (outerRemaining / 4 * 3))

def ProbeBudget.init (cfg : EnsuresCheckConfig) : CoreM ProbeBudget := do
  let now ← IO.getNumHeartbeats
  let ctx ← read
  let outerRemaining? : Option Nat :=
    if ctx.maxHeartbeats == 0 then
      none
    else
      some (ctx.maxHeartbeats - (now - ctx.initHeartbeats))
  let totalInternal := clampProbeBudget (cfg.totalHeartbeats * 1000) outerRemaining?
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

/-- Destruct `False`, `And`, `Exists`, and (up to `maxGoals` total leaves) `Or`
    hypotheses in the local contexts of `pending` with explicit fuel (zero `partial`)
    and per-goal `tried` guards so dependent hypotheses that reject `cases` never
    cause failures or loops. Non-branching hypotheses (`False`, `And`, `Exists`) are
    always prioritized ahead of branching `Or` splits so disjunctive preconditions
    like `(∃ n, P n) ∨ (∃ n, Q n)` open cleanly on every branch. -/
private def destructHypsMulti
    (maxGoals : Nat) : Nat → List (MVarId × Array FVarId) → List MVarId → MetaM (List MVarId)
  | 0, pending, done => return done ++ pending.map Prod.fst
  | _, [], done => return done
  | fuel + 1, (mvarId, tried) :: rest, done => do
    let canSplitOr : Bool := Nat.ble (done.length + rest.length + 2) maxGoals
    let (target?, tried') ← mvarId.withContext do
      let lctx ← getLCtx
      let mut nonBranch? : Option (FVarId × Nat) := none
      let mut orCand? : Option FVarId := none
      let mut nextTried := tried
      for decl in lctx do
        if decl.isImplementationDetail || nextTried.contains decl.fvarId then continue
        let ty ← instantiateMVars decl.type
        let tyWhnf ← whnf ty
        if tyWhnf.isConstOf ``False then
          nonBranch? := some (decl.fvarId, 0)
          break
        else if tyWhnf.isAppOfArity ``And 2 then
          nonBranch? := some (decl.fvarId, 1)
          break
        else if tyWhnf.isAppOfArity ``Exists 2 then
          nonBranch? := some (decl.fvarId, 2)
          break
        else if tyWhnf.isAppOfArity ``Or 2 then
          if canSplitOr && orCand?.isNone then
            orCand? := some decl.fvarId
        else
          nextTried := nextTried.push decl.fvarId
      match nonBranch? with
      | some nb => return (some nb, nextTried)
      | none => return (orCand?.map (fun fv => (fv, 3)), nextTried)
    match target? with
    | none => destructHypsMulti maxGoals fuel rest (mvarId :: done)
    | some (fvarId, kind) =>
      try
        let subgoals ← mvarId.cases fvarId
        if kind == 0 then
          destructHypsMulti maxGoals fuel rest done
        else
          let nextGoals := subgoals.toList.map (fun sg => (sg.mvarId, tried'))
          destructHypsMulti maxGoals fuel (nextGoals ++ rest) done
      catch _ =>
        destructHypsMulti maxGoals fuel ((mvarId, tried'.push fvarId) :: rest) done

/-- Outcome of a single bounded tactic probe. -/
private inductive ProbeOutcome : Type where
  | proved
  | undecided
  | cutOff
  deriving DecidableEq

/-- Run a single tactic syntax snippet against `goalTy` inside a fresh isolated
    metavariable, restoring `Core.State.messages`, verifying zero errors, zero `sorry`,
    zero unassigned metavariables, and full `Meta.check` kernel typechecking.

    The goal itself is typechecked first: a goal assembled by substitution (for
    example, an output-insensitivity goal over a dependent output type) is never
    handed to a tactic unless it is type-correct, so an ill-typed goal can never be
    reported as proved. Returns `.cutOff` when the heartbeat or recursion-depth cap
    aborts the probe. -/
private def tryTacticSnippetOutcome
    (goalTy : Expr) (stepCapInternal : Nat) (tac : TSyntax `tactic) : MetaM ProbeOutcome := do
  let savedMsgs := (← getThe Core.State).messages
  let result ← withoutModifyingState do
    modifyThe Core.State fun s => { s with messages := {} }
    let attempt? ← withBoundedHeartbeats stepCapInternal do
      let goalTy ← instantiateMVars goalTy
      if !(← isTypeCorrect goalTy) then
        return false
      if !(← isProp goalTy) then
        return false
      let mvar ← mkFreshExprSyntheticOpaqueMVar goalTy
      let mvarId ← introsUnfoldingNot 8 mvar.mvarId!
      let goals ← destructHypsMulti 8 128 [(mvarId, #[])] []
      let mut allClosed := true
      for mid in goals do
        let rem ← Term.TermElabM.run' <| Tactic.run mid <| Tactic.evalTactic tac
        if !rem.isEmpty then
          allClosed := false
          break
      if !allClosed then
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
    match attempt? with
    | some true => return .proved
    | some false => return .undecided
    | none => return .cutOff
  modifyThe Core.State fun s => { s with messages := savedMsgs }
  return result

private def tryTacticSnippet
    (goalTy : Expr) (stepCapInternal : Nat) (tac : TSyntax `tactic) : MetaM Bool := do
  return (← tryTacticSnippetOutcome goalTy stepCapInternal tac) == .proved

/-- The fixed, ordered battery of tactic snippets tried by the bounded prover: fast
    deterministic closers, then `simp_all`-normalized closers, then `grind`. -/
private def proverSnippets : MetaM (Array (TSyntax `tactic)) := do
  let tac1 ← `(tactic| first | trivial | rfl | assumption | contradiction | decide | omega)
  let tac2 ← `(tactic| (try simp_all) <;> first | trivial | rfl | assumption | contradiction | decide | omega)
  let tac3 ← `(tactic| grind)
  return #[tac1, tac2, tac3]

/-- Sound, heartbeat-bounded, message-log-isolated prover for closed or local-context
    propositions `goalTy`. Tries fast deterministic tactics (`trivial`/`rfl`/
    `assumption`/`contradiction`/`decide`, `omega`, `simp_all`, `grind`) and accepts
    a proof only after `Meta.check` confirms zero `sorry`, zero mvars, and zero errors. -/
def tryProve (goalTy : Expr) (stepCapInternal : Nat := 50000000) : MetaM Bool := do
  let goalTy ← instantiateMVars goalTy
  for tac in (← proverSnippets) do
    if ← tryTacticSnippet goalTy stepCapInternal tac then
      return true
  return false

/-! ### Closed-Arithmetic Goal Normalization -/

/-- Exclusive upper bound on the numerals `foldClosedArith` introduces. A closed term
    evaluating to a larger value stays symbolic, so no oversized literal enters a goal. -/
private def closedNatFoldBound : Nat := 2 ^ 512

/-- Internal-heartbeat cap for one `foldClosedArith` pass. Evaluating the closed
    constants of a realistic specification (`scalarModulus 8`, a sidecar's `argCount`)
    needs a few thousand heartbeats. An expensive closed term abandons only its own
    subterm evaluation (under `closedNatSubtermHeartbeats`) instead of aborting the
    whole pass or draining the probe budget. -/
private def closedNatFoldHeartbeats : Nat := 2000000

/-- Per-subterm internal-heartbeat cap inside `evalClosedNatLit?`. Isolating each
    closed `Nat` evaluation ensures one costly or recursion-deep closed term (such as
    `Fin (deepIndex 5000)` in a binder type) stays symbolic without preventing other
    closed constants (`scalarModulus 4`, `sidecar.argCount`) in the same goal from
    folding. -/
private def closedNatSubtermHeartbeats : Nat := 250000

/-- Conservative syntactic pre-check that avoids calling `whnf` on closed `Nat`
    exponentiations, shifts, or scalar moduli whose literal operand would already
    produce a value at or above `closedNatFoldBound` (`2 ^ 512`), preventing
    oversized bignum allocation before heartbeats are checked. -/
private def isOversizedNatOp? (e : Expr) : MetaM Bool := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let .const name _ := fn | return false
  if name == ``HPow.hPow && args.size == 6 then
    if let some exp ← Meta.getNatValue? args[5]! then
      if Nat.ble 512 exp then
        if let some base ← Meta.getNatValue? args[4]! then
          return Nat.ble 2 base
        return true
  else if name == ``Nat.pow && args.size == 2 then
    if let some exp ← Meta.getNatValue? args[1]! then
      if Nat.ble 512 exp then
        if let some base ← Meta.getNatValue? args[0]! then
          return Nat.ble 2 base
        return true
  else if name == ``HShiftLeft.hShiftLeft && args.size == 6 then
    if let some shift ← Meta.getNatValue? args[5]! then
      if Nat.ble 512 shift then
        if let some base ← Meta.getNatValue? args[4]! then
          return Nat.ble 1 base
        return true
  else if name == ``Nat.shiftLeft && args.size == 2 then
    if let some shift ← Meta.getNatValue? args[1]! then
      if Nat.ble 512 shift then
        if let some base ← Meta.getNatValue? args[0]! then
          return Nat.ble 1 base
        return true
  else if name == ``scalarModulus && args.size == 1 then
    if let some bytes ← Meta.getNatValue? args[0]! then
      return Nat.ble 64 bytes
  else if name == ``scalarPow2 && args.size == 1 then
    if let some bits ← Meta.getNatValue? args[0]! then
      return Nat.ble 512 bits
  return false

/-- Evaluate `e` to a numeral when it is a closed `Nat`-typed term: one with no free,
    meta, or loose bound variable, so its value depends on no input or output.

    Returns `some e` unchanged when `e` already is a numeral, `some lit` when `whnf`
    evaluates `e` to a value below `closedNatFoldBound` within `subtermCap` internal
    heartbeats, and `none` otherwise (including on heartbeat or recursion-depth cutoff).
    `whnf` only produces definitionally equal terms, so `lit` is definitionally equal
    to `e`. -/
private def evalClosedNatLit? (subtermCap : Nat) (e : Expr) : MetaM (Option Expr) := do
  if e.hasFVar || e.hasExprMVar || e.hasLooseBVars then
    return none
  if (← Meta.getNatValue? e).isSome then
    return some e
  if ← isOversizedNatOp? e then
    return none
  let eval? ← withBoundedHeartbeats subtermCap do
    let rawTy ← inferType e
    match rawTy with
    | .forallE .. | .sort .. => return none
    | _ => pure ()
    let ty ← if rawTy.isConstOf ``Nat then pure rawTy else whnf rawTy
    if !ty.isConstOf ``Nat then
      return none
    let v ← whnf e
    if let some n ← Meta.getNatValue? v then
      if n < closedNatFoldBound then
        return some (mkNatLit n)
      return none
    if v.isConstOf ``Nat.zero then
      return some (mkNatLit 0)
    return none
  match eval? with
  | some res => return res
  | none => return none

/-- Fuel-bounded normalizer applied to a goal before it reaches the bounded prover.

    * Every maximal closed `Nat`-typed subterm is replaced by the numeral it evaluates
      to (`evalClosedNatLit?`). `omega`, `simp`, and `grind` treat a closed application
      such as `scalarModulus 4` or `sidecar.argCount` as an opaque atom, so without
      this step `scalarModulus 4 ≤ 0 → ret = x` (vacuously true) and
      `ret % scalarModulus 4 < scalarModulus 4` (true of every `ret`) are accepted as
      binding postconditions. Each subterm evaluation is isolated under a per-subterm
      heartbeat/recursion cap so one costly subterm cannot prevent other closed
      constants in the same goal from folding.
    * `Trusted.Sequence.length` is replaced by `List.length`, its definition, so the
      standard list-length lemmas apply to the argument-count conjunct
      `Trusted.Sequence.length req.args = sidecar.argCount` of an external-spec
      `requires`.

    Both rewrites replace a subterm by a definitionally equal one of the same type, so
    the result is definitionally equal to the input and a proof of the normalized goal
    proves the original. Subterms nested deeper than `fuel` are left untouched. -/
private def foldClosedArith (passEnd : Nat) : Nat → Expr → MetaM Expr
  | 0, e => return e
  | fuel + 1, e => do
    let now ← IO.getNumHeartbeats
    if now >= passEnd then
      return e
    let subCap := min (passEnd - now) closedNatSubtermHeartbeats
    match e with
    | .mdata d b =>
      return .mdata d (← foldClosedArith passEnd fuel b)
    | .lam n t b bi =>
      return .lam n (← foldClosedArith passEnd fuel t) (← foldClosedArith passEnd fuel b) bi
    | .forallE n t b bi =>
      return .forallE n (← foldClosedArith passEnd fuel t) (← foldClosedArith passEnd fuel b) bi
    | .letE n t v b nd =>
      return .letE n (← foldClosedArith passEnd fuel t) (← foldClosedArith passEnd fuel v)
        (← foldClosedArith passEnd fuel b) nd
    | .proj s i b =>
      if let some lit ← evalClosedNatLit? subCap e then
        return lit
      return .proj s i (← foldClosedArith passEnd fuel b)
    | .const name us =>
      if name == ``Trusted.Sequence.length then
        return .const ``List.length us
      if let some lit ← evalClosedNatLit? subCap e then
        return lit
      return e
    | .app .. =>
      if let some lit ← evalClosedNatLit? subCap e then
        return lit
      let fn ← foldClosedArith passEnd fuel e.getAppFn
      let mut args : Array Expr := #[]
      for a in e.getAppArgs do
        args := args.push (← foldClosedArith passEnd fuel a)
      return mkAppN fn args
    | _ => return e

/-- Normalize `goalTy` with `foldClosedArith` under a small heartbeat cap drawn from
    `budget`. Returns `goalTy` unchanged when the budget is exhausted or the pass is
    cut off (heartbeats or recursion depth), so a costly closed term never aborts or
    starves a probe. -/
private def normalizeGoalArith (budget : ProbeBudget) (goalTy : Expr) : MetaM Expr := do
  let some cap ← budget.nextCap? | return goalTy
  let passCap := min cap closedNatFoldHeartbeats
  let now ← IO.getNumHeartbeats
  let passEnd := now + passCap
  let folded? ← withBoundedHeartbeats passCap
    (foldClosedArith passEnd 96 goalTy)
  return folded?.getD goalTy

/-- Budget-aware variant of `tryProve`: re-derives a strictly positive heartbeat cap
    from `budget` before every tactic snippet, and reports the goal as undecided as
    soon as the total budget is exhausted. A single probe can therefore overshoot the
    total budget by at most one per-snippet cap.

    The goal is first normalized by `normalizeGoalArith`, so closed arithmetic
    constants reach the tactics as numerals. The normalized goal is definitionally
    equal to `goalTy`, so every verdict still rests on a `Meta.check`ed proof of a
    statement equivalent to the one requested. When `cutOffRef?` is provided, it is
    set to `true` if any snippet hits a heartbeat/recursion cap or budget exhaustion. -/
private def tryProveWithin (budget : ProbeBudget) (goalTy : Expr)
    (cutOffRef? : Option (IO.Ref Bool) := none) : MetaM Bool := do
  let goalTy ← normalizeGoalArith budget (← instantiateMVars goalTy)
  for tac in (← proverSnippets) do
    match ← budget.nextCap? with
    | none =>
      if let some ref := cutOffRef? then
        ref.set true
      return false
    | some cap =>
      match ← tryTacticSnippetOutcome goalTy cap tac with
      | .proved => return true
      | .undecided => pure ()
      | .cutOff =>
        if let some ref := cutOffRef? then
          ref.set true
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

/-- Reduce structure projections (both raw `Expr.proj` and non-class projection
    function applications such as `Prod.snd (a, b)` or custom structure field
    getters applied to a constructor) alongside `zetaBetaReduce`, opening binders
    with `withLocalDecl` so `Meta.reduceProj?` never sees loose bound variables. -/
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
      | _ =>
        let e' := Expr.app f' a'
        if let .const fnName _ := e'.getAppFn then
          if let some projInfo := (← getEnv).getProjectionFnInfo? fnName then
            if !projInfo.fromClass then
              let args := e'.getAppArgs
              if hStruct : projInfo.numParams < args.size then
                let structVal := args[projInfo.numParams].consumeMData
                if structVal.getAppFn.isConstOf projInfo.ctorName then
                  let ctorArgs := structVal.getAppArgs
                  let fieldIdx := projInfo.numParams + projInfo.i
                  if hField : fieldIdx < ctorArgs.size then
                    let restArgs := args.extract (projInfo.numParams + 1) args.size
                    let reduced := mkAppN ctorArgs[fieldIdx] restArgs
                    return ← zetaBetaProjReduce fuel reduced
        return e'
    | .lam n t b bi =>
      let t' ← zetaBetaProjReduce fuel t
      withLocalDecl n bi t' fun fv => do
        let b' ← zetaBetaProjReduce fuel (b.instantiate1 fv)
        return .lam n t' (b'.abstract #[fv]) bi
    | .forallE n t b bi =>
      let t' ← zetaBetaProjReduce fuel t
      withLocalDecl n bi t' fun fv => do
        let b' ← zetaBetaProjReduce fuel (b.instantiate1 fv)
        return .forallE n t' (b'.abstract #[fv]) bi
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
    every constructor of which requires an argument of empty type).

    Recursive occurrences are resolved coinductively: `visiting` holds the exact types
    whose emptiness is currently being established, and re-encountering one of them
    counts as empty. Inhabitation of an inductive type is a least fixed point (some
    constructor must have all arguments inhabited, bottoming out at a constructor with
    no recursive argument), so emptiness is the complementary greatest fixed point.
    This catches uninhabited recursive inductives such as
    `inductive Bad | mk : Bad → Bad`, while `Nat`, `List α`, `Value`, and rose trees
    are never flagged because each has a constructor all of whose argument types are
    refuted as empty without appeal to the cycle rule.

    `visiting` is keyed by the full (weak-head-normal) type rather than by the type
    constructor name, so a nested instance such as `Box (Box Nat)` is not mistaken
    for a recursive occurrence of `Box Nat`. Function-typed arguments, indexed
    families other than `Fin`, and anything not understood yield `false`. -/
private def isEmptyTypeAux : Nat → List Expr → Expr → MetaM Bool
  | 0, _, _ => return false
  | fuel + 1, visiting, ty => do
    let ty ← instantiateMVars (← whnf ty)
    let fn := ty.getAppFn
    let args := ty.getAppArgs
    match fn with
    | .const name lvls =>
      if name == ``Empty || name == ``PEmpty || name == ``False then
        return true
      if name == ``Fin && args.size == 1 then
        return ← exprIsNatLit args[0]! 0
      if (name == ``Prod || name == ``PProd || name == ``And) && args.size == 2 then
        if ← isEmptyTypeAux fuel visiting args[0]! then return true
        return ← isEmptyTypeAux fuel visiting args[1]!
      if (name == ``Sum || name == ``PSum) && args.size == 2 then
        if !(← isEmptyTypeAux fuel visiting args[0]!) then return false
        return ← isEmptyTypeAux fuel visiting args[1]!
      if visiting.any (fun t => t == ty) then
        return true
      let env ← getEnv
      match env.find? name with
      | some (.inductInfo indVal) =>
        if indVal.ctors.isEmpty then
          return true
        -- Skip indexed families other than `Fin` handled above so we stay sound.
        if indVal.numIndices > 0 || args.size < indVal.numParams then
          return false
        let visiting' := ty :: visiting
        let params := args.extract 0 indVal.numParams
        for ctorName in indVal.ctors do
          let some (.ctorInfo ctorVal) := env.find? ctorName | return false
          if ctorVal.levelParams.length != lvls.length then return false
          let ctorTy := ctorVal.type.instantiateLevelParams ctorVal.levelParams lvls
          let ctorInst ← instantiateForall ctorTy params
          let ctorEmpty ← forallTelescope ctorInst fun ctorArgs _ => do
            for a in ctorArgs do
              let aTy ← inferType a
              if ← isEmptyTypeAux fuel visiting' aTy then
                return true
            return false
          if !ctorEmpty then
            return false
        return true
      | _ => return false
    | _ => return false

/-- Synthesize an instance of the `Sort`-polymorphic class `cls` (`Inhabited`,
    `Nonempty`, or `Subsingleton`, each declared over `α : Sort u`) at `ty`.

    The class must be instantiated at the sort level `u` of `ty` itself (`ty : Sort u`),
    not at its predecessor: for `ty : Type` that is `u = 1`, and `Subsingleton.{0} ty`
    would be ill-typed and never synthesize. Returns `none` on any failure. -/
private def synthSortClassInstance? (cls : Name) (ty : Expr) : MetaM (Option Expr) := do
  try
    let u ← getLevel ty
    synthInstance? (mkApp (mkConst cls [u]) ty)
  catch _ =>
    return none

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
    if ← isEmptyTypeAux (fuel + 1) [] ty then
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
        if ← isEmptyTypeAux (fuel + 1) [] args[0]! then return true
      if name == ``List && args.size == 1 then
        if ← isEmptyTypeAux (fuel + 1) [] args[0]! then return true
      if (name == ``Prod || name == ``PProd) && args.size == 2 then
        let s0 ← isSubsingletonOrEmptyType fuel args[0]!
        let s1 ← isSubsingletonOrEmptyType fuel args[1]!
        if s0 && s1 then return true
      if name == ``Subtype && args.size == 2 then
        if ← isSubsingletonOrEmptyType fuel args[0]! then return true
    -- Fall back to Lean's `Subsingleton` typeclass synthesis (sound by construction).
    return (← synthSortClassInstance? ``Subsingleton ty).isSome

/-- Strip `Not` if `e` is `Not inner`. -/
private def unwrapNot? (e : Expr) : Option Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``Not 1 then
    some e.appArg!
  else
    none

/-- Fast syntactic tautology recognizer for `Prop` expressions (`True`, `r = r`,
    `¬ (r ≠ r)`, `P ↔ P`, `P → P`, `A → B → A`, `r = r ∨ P`, `P ∨ ¬ P`).

    Every recognized shape is valid in all models. In particular `r ≤ r` is *not*
    recognized syntactically: `LE.le` is an arbitrary user-supplied relation, and
    reflexivity fails for lawless instances (IEEE `Float`, where `NaN ≤ NaN` is false,
    or any strict or partial user-defined `LE`), for which `r ≤ r` is a genuine
    constraint on `r`. Reflexive inequalities over lawful orders are still caught by
    the bounded prover, which must actually prove them. -/
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
    else if e.isAppOfArity ``Iff 2 then
      let args := e.getAppArgs
      let lhs := args[0]!.consumeMData
      let rhs := args[1]!.consumeMData
      if lhs == rhs then
        some .tautologicalImplication
      else if (detectSyntacticTautology fuel hyps lhs).isSome &&
              (detectSyntacticTautology fuel hyps rhs).isSome then
        some .tautologicalImplication
      else if lhs.isAppOfArity ``Eq 3 && rhs.isAppOfArity ``Eq 3 then
        let la := lhs.getAppArgs
        let ra := rhs.getAppArgs
        if la[1]!.consumeMData == ra[2]!.consumeMData &&
           la[2]!.consumeMData == ra[1]!.consumeMData then
          some .tautologicalImplication
        else
          none
      else
        none
    else if e.isAppOfArity ``ite 5 then
      let args := e.getAppArgs
      let cond := args[1]!.consumeMData
      let tBranch := args[3]!
      let fBranch := args[4]!
      if (detectSyntacticTautology fuel (cond :: hyps) tBranch).isSome &&
         (detectSyntacticTautology fuel (mkApp (mkConst ``Not) cond :: hyps) fBranch).isSome then
        some .tautologicalImplication
      else
        none
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

/-- Collect distinct closed (zero loose bvar) boilerplate atoms occurring under
    propositional connectives, `ite`/`dite`, `.lam`, and `.letE`, stopping once `limit`
    atoms have been gathered (bounded by `fuel`). -/
private def collectBoilerplateAtoms :
    Nat → Nat → Expr → Array Expr → Array Expr × Bool
  | 0, _, _, acc => (acc, false)
  | fuel + 1, limit, e, acc =>
    let e := e.consumeMData
    if isBoilerplateAtom e then
      if e.hasLooseBVars then
        (acc, false)
      else if acc.any (fun a => a == e) then
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
      | .letE _ _ val body _ =>
        collectBoilerplateAtoms fuel limit (body.instantiate1 val) acc
      | _ => (acc, false)

/-- Lookup the truth assignment (`true` / `false`) for `e` in `atoms` under bitmask `mask`. -/
private def lookupAtomMask? (atoms : Array Expr) (mask : Nat) (e : Expr) : Option Bool := Id.run do
  for i in [:atoms.size] do
    if atoms[i]! == e then
      return some (((mask >>> i) &&& 1) == 1)
  return none

private def mkBoolProp (b : Bool) : Expr :=
  if b then mkConst ``True else mkConst ``False

/-- Eliminate a `Prop`-valued `if cond' then t' else f'` into propositionally
    equivalent connectives without needing a fresh `Decidable cond'` instance.
    Caller guarantees `cond'`, `t'`, and `f'` are `Prop` expressions with no loose
    bound variables so constructing non-dependent arrows cannot capture any `bvar`. -/
private def simplifyPropIte (cond' t' f' : Expr) : Expr :=
  let mkNonDepArrow (p q : Expr) : Expr := .forallE Name.anonymous p q .default
  let negCond := mkApp (mkConst ``Not) cond'
  if t' == f' then t'
  else if t'.isConstOf ``True && f'.isConstOf ``False then cond'
  else if t'.isConstOf ``False && f'.isConstOf ``True then negCond
  else if t'.isConstOf ``True then mkNonDepArrow negCond f'
  else if f'.isConstOf ``True then mkNonDepArrow cond' t'
  else if t'.isConstOf ``False then mkApp2 (mkConst ``And) negCond f'
  else if f'.isConstOf ``False then mkApp2 (mkConst ``And) cond' t'
  else mkApp2 (mkConst ``And) (mkNonDepArrow cond' t') (mkNonDepArrow negCond f')

/-- Shannon cofactor `e` with respect to `atoms` under truth-assignment bitmask `mask`,
    simplifying propositional connectives, `ite`/`dite` conditions and branches, `.lam`
    bodies, and `.letE` bindings while keeping the resulting `Prop` well-typed. -/
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
        if p == q then mkConst ``True
        else if p.isConstOf ``True then q
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
          let isPropRes := args[0]!.consumeMData == mkSort Level.zero
          if t' == f' then
            t'
          else if isPropRes && cond' != args[1]! &&
              !cond'.hasLooseBVars && !t'.hasLooseBVars && !f'.hasLooseBVars then
            simplifyPropIte cond' t' f'
          else
            mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, t', f']
      else if e.isAppOfArity ``dite 5 then
        let args := e.getAppArgs
        let cond' := cofactorBoilerplate fuel atoms mask args[1]!
        let tLam := args[3]!.consumeMData
        let fLam := args[4]!.consumeMData
        if cond'.isConstOf ``True then
          match tLam with
          | .lam n dom tb bi =>
            let tb' := cofactorBoilerplate fuel atoms mask tb
            if !tb'.hasLooseBVars then tb'
            else
              let fLam' := match fLam with
                | .lam fn fdom fb fbi => .lam fn fdom (cofactorBoilerplate fuel atoms mask fb) fbi
                | other => other
              mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, .lam n dom tb' bi, fLam']
          | _ => e
        else if cond'.isConstOf ``False then
          match fLam with
          | .lam n dom fb bi =>
            let fb' := cofactorBoilerplate fuel atoms mask fb
            if !fb'.hasLooseBVars then fb'
            else
              let tLam' := match tLam with
                | .lam tn tdom tb tbi => .lam tn tdom (cofactorBoilerplate fuel atoms mask tb) tbi
                | other => other
              mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, tLam', .lam n dom fb' bi]
          | _ => e
        else
          match tLam, fLam with
          | .lam tn tdom tb tbi, .lam fn fdom fb fbi =>
            let tb' := cofactorBoilerplate fuel atoms mask tb
            let fb' := cofactorBoilerplate fuel atoms mask fb
            let isPropRes := args[0]!.consumeMData == mkSort Level.zero
            if !tb'.hasLooseBVars && !fb'.hasLooseBVars then
              if tb' == fb' then
                tb'
              else if isPropRes && cond' != args[1]! && !cond'.hasLooseBVars then
                simplifyPropIte cond' tb' fb'
              else
                mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!,
                  .lam tn tdom tb' tbi, .lam fn fdom fb' fbi]
            else
              mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!,
                .lam tn tdom tb' tbi, .lam fn fdom fb' fbi]
          | _, _ => e
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
        | .lam n dom body bi =>
          .lam n dom (cofactorBoilerplate fuel atoms mask body) bi
        | .letE _ _ val body _ =>
          cofactorBoilerplate fuel atoms mask (body.instantiate1 val)
        | _ => e

/-- Fast sound recognizer for boilerplate atoms whose truth value is fixed
    independently of variables (for example `callFramePreserved m m`, which holds
    for every `m` by `callFramePreserved_refl`). -/
private def atomFixedTruth? (e : Expr) : Option Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``Trusted.VerificationResult.callFramePreserved 2 then
    let args := e.getAppArgs
    if args[0]!.consumeMData == args[1]!.consumeMData then
      some true
    else
      none
  else
    none

/-- Build the propositional conjunction characterizing a boilerplate fibre
    (`atom_i` for bit `1`, `¬ atom_i` for bit `0`). -/
private def mkFibreAssumption (atoms : Array Expr) (mask : Nat) : Expr := Id.run do
  let mut acc? : Option Expr := none
  for i in [:atoms.size] do
    let b := ((mask >>> i) &&& 1) == 1
    let lit := if b then atoms[i]! else mkApp (mkConst ``Not) atoms[i]!
    acc? := match acc? with
      | none => some lit
      | some prev => some (mkApp2 (mkConst ``And) prev lit)
  return acc?.getD (mkConst ``True)

/-- Root component of a hierarchical `Name` (e.g. `Init` for `Init.Prelude`). -/
private def nameRoot : Name → Name
  | .str .anonymous s => .str .anonymous s
  | .str p _ => nameRoot p
  | .num p _ => nameRoot p
  | .anonymous => .anonymous

/-- Whether `name` is a core/standard/trusted primitive, matcher, or projection
    that user-predicate unfolding must leave intact. -/
private def isProtectedConst (env : Environment) (name : Name) : Bool :=
  if name == ``True || name == ``False || name == ``And || name == ``Or ||
     name == ``Not || name == ``Eq || name == ``Ne || name == ``Iff ||
     name == ``Exists || name == ``LE.le || name == ``LT.lt ||
     name == ``GE.ge || name == ``GT.gt || name == ``ite || name == ``dite ||
     name == ``Trusted.VerificationResult.callFramePreserved ||
     name == ``Trusted.VerificationResult.retMatchesCalleeReturnTy ||
     env.isProjectionFn name || isMatcherCore env name then
    true
  else
    match env.getModuleIdxFor? name with
    | some idx =>
      let mods := env.allImportedModuleNames
      if h : idx.toNat < mods.size then
        let root := nameRoot mods[idx.toNat]
        root == `Init || root == `Std || root == `Lean || root == `Trusted
      else
        false
    | none => false

/-- Unfold a user-defined head predicate (excluding `Init`/`Std`/`Lean`/`Trusted`
    primitives, stuck matchers, and projections) to expose hidden definitions in
    `requires` and `ensures` clauses.

    A matcher applied to constructor discriminants is iota-reduced to its selected
    alternative. Without this step a `match ans with ...` nested under a connective,
    or hidden behind a helper predicate, stays opaque once `ans` has been
    instantiated to `MirCallAns.returned retVal memAfter`, and the boilerplate atoms
    inside its alternatives escape cofactoring. A matcher stuck on a variable is left
    intact. Every step is a definitional unfolding or iota reduction, so the result
    is definitionally equal to the input. -/
private def unfoldUserHead : Nat → Expr → MetaM Expr
  | 0, e => return zetaBetaReduce 64 e
  | fuel + 1, e => do
    let e := zetaBetaReduce 64 e
    match ← reduceMatcher? e with
    | .reduced val => return ← unfoldUserHead fuel val
    | _ => pure ()
    match e.getAppFn with
    | .const name _ =>
      let env ← getEnv
      if isProtectedConst env name then
        return e
      match ← unfoldDefinition? e with
      | some e' =>
        if e' != e then unfoldUserHead fuel e' else return e
      | none => return e
    | _ => return e

/-- Unfold user-defined head predicates recursively through propositional connectives
    (`And`, `Or`, `Iff`, `Not`, non-dependent `→`, and `ite`/`dite` conditions and
    branches), preserving auto-generated boilerplate atoms. Each step is a definitional
    unfolding or zeta/beta/projection/iota reduction, so the result is definitionally
    equal to the input. -/
private def unfoldUserConnectives : Nat → Expr → MetaM Expr
  | 0, e => return e
  | fuel + 1, e => do
    let e := e.consumeMData
    if isBoilerplateAtom e then
      return e
    let e1 ← unfoldUserHead 6 e
    let e ← if e1 != e then unfoldUserHead 4 (← zetaBetaProjReduce 8 e1) else pure e1
    if isBoilerplateAtom e then
      return e
    if e.isAppOfArity ``And 2 then
      let lhs ← unfoldUserConnectives fuel e.appFn!.appArg!
      let rhs ← unfoldUserConnectives fuel e.appArg!
      return mkApp2 (mkConst ``And) lhs rhs
    else if e.isAppOfArity ``Or 2 then
      let lhs ← unfoldUserConnectives fuel e.appFn!.appArg!
      let rhs ← unfoldUserConnectives fuel e.appArg!
      return mkApp2 (mkConst ``Or) lhs rhs
    else if e.isAppOfArity ``Iff 2 then
      let lhs ← unfoldUserConnectives fuel e.appFn!.appArg!
      let rhs ← unfoldUserConnectives fuel e.appArg!
      return mkApp2 (mkConst ``Iff) lhs rhs
    else if e.isAppOfArity ``Not 1 then
      let inner ← unfoldUserConnectives fuel e.appArg!
      return mkApp (mkConst ``Not) inner
    else if e.isAppOfArity ``ite 5 then
      let args := e.getAppArgs
      let cond' ← unfoldUserConnectives fuel args[1]!
      let t' ← unfoldUserConnectives fuel args[3]!
      let f' ← unfoldUserConnectives fuel args[4]!
      if cond' != args[1]! then
        let withCond := mkAppN e.getAppFn #[args[0]!, cond', args[2]!, t', f']
        if ← isTypeCorrect withCond then
          return withCond
      return mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, t', f']
    else if e.isAppOfArity ``dite 5 then
      let args := e.getAppArgs
      let cond' ← unfoldUserConnectives fuel args[1]!
      let t' ← match args[3]!.consumeMData with
        | .lam n dom body bi =>
          withLocalDecl n bi dom fun fv => do
            let body' ← unfoldUserConnectives fuel (body.instantiate1 fv)
            return .lam n dom (body'.abstract #[fv]) bi
        | other => pure other
      let f' ← match args[4]!.consumeMData with
        | .lam n dom body bi =>
          withLocalDecl n bi dom fun fv => do
            let body' ← unfoldUserConnectives fuel (body.instantiate1 fv)
            return .lam n dom (body'.abstract #[fv]) bi
        | other => pure other
      if cond' != args[1]! then
        let withCond := mkAppN e.getAppFn #[args[0]!, cond', args[2]!, t', f']
        if ← isTypeCorrect withCond then
          return withCond
      return mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, t', f']
    else
      match e with
      | .forallE n dom body bi =>
        if !body.hasLooseBVars then
          let dom' ← unfoldUserConnectives fuel dom
          let body' ← unfoldUserConnectives fuel body
          return .forallE n dom' body' bi
        else
          return e
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

/-! ### Output-Insensitivity Goals -/

/-- Run `k` with a fresh copy of every output variable in `outVars` in scope. The type
    of each copy is the type of the original with all earlier output variables replaced
    by their copies, so mutually dependent output types stay well-typed. -/
private def withOutputCopies {α : Type} [Inhabited α]
    (outVars : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
  let mut infos : Array (Name × (Array Expr → MetaM Expr)) := #[]
  for i in [:outVars.size] do
    let ovTy ← inferType outVars[i]!
    infos := infos.push
      (Name.mkSimple s!"out{i}'",
        fun copies => pure (ovTy.replaceFVars (outVars.extract 0 copies.size) copies))
  withLocalDeclsD infos k

/-- Build the output-insensitivity goal `∀ binders outs', (extraHyp →) body → body[outs := outs']`,
    where `binders` must bind every free variable of `body` (including `outVars`
    themselves). Proving it establishes `ForwardOutputInsensitive`, which refutes
    `PostconditionDichotomy` (`not_postconditionDichotomy_of_forwardOutputInsensitive`).

    Returns `none` when there is no output variable or when the substituted goal fails
    `Meta.check` (for instance because another binder's type depends on an output
    variable), so an ill-typed substitution is never handed to the prover. -/
private def mkOutputInsensitivityGoal?
    (binders outVars : Array Expr) (body : Expr)
    (extraHyp? : Option Expr := none) : MetaM (Option Expr) := do
  if outVars.isEmpty then
    return none
  withOutputCopies outVars fun copies => do
    let body' := body.replaceFVars outVars copies
    let core ← mkArrow body body'
    let inner ← match extraHyp? with
      | some hyp => mkArrow hyp core
      | none => pure core
    let goal ← mkForallFVars (binders ++ copies) inner
    if ← isTypeCorrect goal then
      return some goal
    else
      return none

/-- Build the per-fibre output-insensitivity goal
    `∀ binders outs', cfpReflTy → fibreAssump → fibreAssump[outs := outs'] → body → body[outs := outs']`,
    matching `not_dichotomyModuloObservation_of_fibre_forwardInsensitive`. -/
private def mkFibreInsensitivityGoal?
    (binders outVars : Array Expr) (cfpReflTy fibreAssump body : Expr) :
    MetaM (Option Expr) := do
  if outVars.isEmpty then
    return none
  withOutputCopies outVars fun copies => do
    let fa' := fibreAssump.replaceFVars outVars copies
    let body' := body.replaceFVars outVars copies
    let inner ← mkArrow cfpReflTy
      (← mkArrow fibreAssump (← mkArrow fa' (← mkArrow body body')))
    let goal ← mkForallFVars (binders ++ copies) inner
    if ← isTypeCorrect goal then
      return some goal
    else
      return none

/-- How one boilerplate fibre of a `MirCallAns` postcondition treats the outputs. -/
private inductive FibreKind : Type where
  /-- The residual is `False` or provably unsatisfiable on this fibre: it accepts nothing. -/
  | contradictory
  /-- The residual is tautological. -/
  | tautological (reason : EnsuresVacuityReason)
  /-- The residual accepts something but does not distinguish outputs. -/
  | insensitive
  /-- The residual fails to distinguish outputs only under `requires`. -/
  | insensitiveUnderRequires
  /-- The residual genuinely constrains an output. -/
  | genuine

/-- Core analyzer operating once `preInputs`, `fixedVars`, `outVars`, `rawBody`,
    `isMirCallAns`, and `requiresExpr?` have been isolated inside the local context.

    A specification is accepted only if no phase can show it vacuous:

    * Phase 0 refutes `requires` (`DeadPrecondition`).
    * Phase 1 rejects subsingleton or empty output types (`UnboundReturnOutput`).
    * Phase 2 handles bodies that do not mention an output after reduction.
    * Phase 3 cofactors `MirCallAns` bodies over their boilerplate atoms while keeping
      each fibre's atom assumptions in scope, pruning impossible fibres so an
      unreachable branch can never supply a "genuine" constraint.
    * Phase 4 tries to prove the body valid, unsatisfiable, or output-insensitive
      without `requires`.
    * Phase 5 repeats those probes under `requires`.

    Every prover probe is sound: a specification is flagged only on a `Meta.check`ed
    proof, never on a failed proof attempt. -/
private def analyzeNormalizedSpec
    (preInputs fixedVars outVars : Array Expr)
    (rawBody : Expr)
    (isMirCallAns : Bool)
    (requiresExpr? : Option Expr)
    (cfg : EnsuresCheckConfig) : MetaM EnsuresCheckResult := do
  let budget ← ProbeBudget.init cfg
  let probeCutOffRef ← IO.mkRef false
  let cutOffOpt : Option (IO.Ref Bool) := some probeCutOffRef
  let outFVarIds : Array FVarId := outVars.map Expr.fvarId!
  let allVars := preInputs ++ fixedVars ++ outVars
  let mentionsOutput (e : Expr) : Bool := e.hasAnyFVar (fun fv => outFVarIds.contains fv)
  let negate (e : Expr) : Expr := mkApp (mkConst ``Not) e
  let cfpReflTy? : Option Expr ←
    if isMirCallAns then
      some <$> inferType (mkConst ``callFramePreserved_refl)
    else
      pure none
  let withCfpRefl (goal : Expr) : MetaM Expr :=
    match cfpReflTy? with
    | some ty => mkArrow ty goal
    | none => pure goal

  -- `∀ allVars, (cfpRefl →) goal`.
  let proveClosed (goal : Expr) : MetaM Bool := do
    tryProveWithin budget (← mkForallFVars allVars (← withCfpRefl goal)) cutOffOpt
  -- `∀ preInputs (h_pre : requires) fixedVars outVars, (cfpRefl →) goal`.
  let proveUnderRequires (preNorm goal : Expr) : MetaM Bool :=
    withLocalDeclD `h_pre preNorm fun hPre => do
      tryProveWithin budget
        (← mkForallFVars (preInputs ++ #[hPre] ++ fixedVars ++ outVars) (← withCfpRefl goal))
        cutOffOpt
  -- `∀ allVars outs', (cfpRefl →) body → body[outs := outs']`.
  let proveInsensitive (body : Expr) : MetaM Bool := do
    match ← mkOutputInsensitivityGoal? allVars outVars body cfpReflTy? with
    | some goal => tryProveWithin budget goal cutOffOpt
    | none => return false
  -- The same goal with `h_pre : requires` in scope.
  let proveInsensitiveUnderRequires (preNorm body : Expr) : MetaM Bool :=
    withLocalDeclD `h_pre preNorm fun hPre => do
      let scopedVars := preInputs ++ #[hPre] ++ fixedVars ++ outVars
      match ← mkOutputInsensitivityGoal? scopedVars outVars body cfpReflTy? with
      | some goal => tryProveWithin budget goal cutOffOpt
      | none => return false

  -- Phase 0: Check whether `requires` is provably unsatisfiable (`DeadPrecondition`).
  -- The `requires` expression is exposed down to its defining lambda and user
  -- predicates under connectives are unfolded, so later `requires`-aware probes see
  -- usable hypotheses rather than an opaque `c.pre req` projection.
  let preProp? ←
    if cfg.useRequires then
      match requiresExpr? with
      | some reqExpr => applyRequiresSafe (← exposeHeadLambda 16 reqExpr) preInputs
      | none => pure none
    else
      pure none

  let preNorm? ←
    match preProp? with
    | some preProp =>
      pure (some (← unfoldUserConnectives 16 (← zetaBetaProjReduce 32 preProp)))
    | none => pure none

  if let some preNorm := preNorm? then
    if preNorm.isConstOf ``False then
      return .vacuous .requiresUnsatisfiable ["requires is syntactically False"]
    if ← tryProveWithin budget (← mkForallFVars preInputs (negate preNorm)) cutOffOpt then
      return .vacuous .requiresUnsatisfiable
        ["requires proved unsatisfiable for all inputs"]

  -- Drop a syntactically `True` precondition after Phase 0 so later phases do not
  -- repeat identical prover probes with a redundant `h_pre : True` hypothesis.
  let preNorm? : Option Expr :=
    match preNorm? with
    | some p => if p.isConstOf ``True then none else some p
    | none => none

  let mut notes : List String := []
  let mut budgetExhaustedNoteAdded := false

  -- Phase 1: Subsingleton or empty output type (`UnboundReturnOutput`).
  -- Deciding emptiness can evaluate a type index (`Fin n`) and run instance synthesis,
  -- so every output type is inspected under a heartbeat cap bounded by `budget`. An
  -- inspection that runs out of heartbeats or recursion depth (both runtime exceptions)
  -- records a conservative degradation note instead of aborting the whole check. The
  -- cap retains a fixed structural floor so trivial types still resolve under starved
  -- probe configurations.
  if !outVars.isEmpty then
    let typeCap := max 1000000 (min budget.totalInternal (cfg.stepHeartbeats * 1000))
    let mut allSubsingleton := true
    for ov in outVars do
      let ovTy ← inferType ov
      let isSub? ← withBoundedHeartbeats typeCap (isSubsingletonOrEmptyType 16 ovTy)
      match isSub? with
      | some true => pure ()
      | some false =>
        allSubsingleton := false
        break
      | none =>
        notes := notes ++
          ["output-type subsingleton/emptiness check exceeded heartbeat/recursion cap; skipped conservatively"]
        allSubsingleton := false
        break
    if allSubsingleton then
      return .vacuous .subsingletonOutputType
        (notes ++ ["all inspected output types are subsingleton or empty"])

  -- Phase 2: Bare `True` / `False`, discarded `let`/beta/projection bindings, unused output binder.
  let rawClean := rawBody.consumeMData
  if rawClean.isConstOf ``True then
    return .vacuous .trivialConstantTrue ["ensures is syntactically True"]
  if rawClean.isConstOf ``False then
    return .vacuous .unrealizableUnderRequires ["ensures is syntactically False"]

  let freeBefore := mentionsOutput rawClean
  let reducedBody ← zetaBetaProjReduce 32 rawClean
  let freeAfter := mentionsOutput reducedBody

  if reducedBody.isConstOf ``False then
    return .vacuous .unrealizableUnderRequires ["ensures reduces to False"]

  if freeBefore && !freeAfter then
    let normDiscarded ← unfoldUserConnectives 8 reducedBody
    if normDiscarded.isConstOf ``False then
      return .vacuous .unrealizableUnderRequires
        ["ensures reduces to False after discarding output"]
    if ← proveClosed (negate normDiscarded) then
      return .vacuous .unrealizableUnderRequires
        ["ensures with discarded output proved unsatisfiable"]
    if let some preNorm := preNorm? then
      if ← proveUnderRequires preNorm (negate normDiscarded) then
        return .vacuous .unrealizableUnderRequires
          ["ensures with discarded output proved unsatisfiable under requires"]
    return .vacuous .discardedLetBinding
      ["output variable occurs only in a discarded let/beta/projection binding"]

  let classifyInputOnly (body : Expr) (fallbackReason : EnsuresVacuityReason)
      (fallbackNote : String) : MetaM EnsuresCheckResult := do
    if body.isConstOf ``True then
      return .vacuous .trivialConstantTrue ["ensures reduces to True"]
    if body.isConstOf ``False then
      return .vacuous .unrealizableUnderRequires ["ensures reduces to False"]
    if let some tautReason := detectSyntacticTautology 32 [] body then
      return .vacuous tautReason ["input-only ensures is syntactically tautological"]
    if ← proveClosed body then
      return .vacuous .tautologicalByProver ["input-only ensures proved universally valid"]
    if ← proveClosed (negate body) then
      return .vacuous .unrealizableUnderRequires ["input-only ensures proved unsatisfiable"]
    if let some preNorm := preNorm? then
      if ← proveUnderRequires preNorm (negate body) then
        return .vacuous .unrealizableUnderRequires
          ["input-only ensures proved unsatisfiable under requires"]
    return .vacuous fallbackReason [fallbackNote]

  if !freeAfter then
    let normInputOnly ← unfoldUserConnectives 8 reducedBody
    return ← classifyInputOnly normInputOnly .unusedOutputBinder
      "output variable does not occur free in ensures body"

  -- Unfold user helper predicates nested under connectives (preserving boilerplate
  -- atoms, core/trusted primitives, matchers, and projections).
  let workBody ← unfoldUserConnectives 8 reducedBody
  if !mentionsOutput workBody then
    return ← classifyInputOnly workBody .outputInsensitive
      "output variable drops out once user helper predicates are unfolded"

  -- Phase 3: `MirCallAns` boilerplate-atom cofactoring (`k ≤ 8`).
  if isMirCallAns && cfg.userEnsuresOnly then
    let (atoms, overflow) := collectBoilerplateAtoms 64 8 workBody #[]
    if overflow then
      notes := notes ++ ["skipped boilerplate cofactoring: >8 boilerplate atoms"]
    else if !atoms.isEmpty then
      let cfpReflTy ← inferType (mkConst ``callFramePreserved_refl)
      let proveFibreContra (fibreAssump res : Expr) : MetaM Bool := do
        let body ←
          if res.isConstOf ``True then pure (negate fibreAssump)
          else mkArrow fibreAssump (negate res)
        tryProveWithin budget (← mkForallFVars allVars (← mkArrow cfpReflTy body)) cutOffOpt
      let proveFibreContraUnderRequires (preNorm fibreAssump res : Expr) : MetaM Bool :=
        withLocalDeclD `h_pre preNorm fun hPre => do
          let scopedVars := preInputs ++ #[hPre] ++ fixedVars ++ outVars
          let body ←
            if res.isConstOf ``True then pure (negate fibreAssump)
            else mkArrow fibreAssump (negate res)
          tryProveWithin budget (← mkForallFVars scopedVars (← mkArrow cfpReflTy body)) cutOffOpt
      let proveFibreInsensitive (fibreAssump res : Expr) : MetaM Bool := do
        match ← mkFibreInsensitivityGoal? allVars outVars cfpReflTy fibreAssump res with
        | some goal => tryProveWithin budget goal cutOffOpt
        | none => return false
      let proveFibreInsensitiveUnderRequires (preNorm fibreAssump res : Expr) : MetaM Bool :=
        withLocalDeclD `h_pre preNorm fun hPre => do
          let scopedVars := preInputs ++ #[hPre] ++ fixedVars ++ outVars
          match ← mkFibreInsensitivityGoal? scopedVars outVars cfpReflTy fibreAssump res with
          | some goal => tryProveWithin budget goal cutOffOpt
          | none => return false

      -- Classify the residual user postcondition of one boilerplate fibre, keeping
      -- the fibre's atom assignment in scope so impossible branches are pruned.
      let classifyFibre (fibreAssump res : Expr) : MetaM FibreKind := do
        if res.isConstOf ``False then
          return .contradictory
        if res.isConstOf ``True then
          if ← proveFibreContra fibreAssump res then
            return .contradictory
          if let some preNorm := preNorm? then
            if ← proveFibreContraUnderRequires preNorm fibreAssump res then
              return .contradictory
          return .insensitive
        if !mentionsOutput res then
          if ← proveFibreContra fibreAssump res then
            return .contradictory
          if let some preNorm := preNorm? then
            if ← proveFibreContraUnderRequires preNorm fibreAssump res then
              return .contradictory
          if let some tautReason := detectSyntacticTautology 32 [] res then
            return .tautological tautReason
          if ← proveClosed res then
            return .tautological .tautologicalByProver
          return .insensitive
        if let some tautReason := detectSyntacticTautology 32 [] res then
          if ← proveFibreContra fibreAssump (mkConst ``True) then
            return .contradictory
          if let some preNorm := preNorm? then
            if ← proveFibreContraUnderRequires preNorm fibreAssump (mkConst ``True) then
              return .contradictory
          return .tautological tautReason
        if ← proveFibreInsensitive fibreAssump res then
          if ← proveFibreContra fibreAssump res then
            return .contradictory
          if let some preNorm := preNorm? then
            if ← proveFibreContraUnderRequires preNorm fibreAssump res then
              return .contradictory
          if ← proveClosed res then
            return .tautological .tautologicalByProver
          return .insensitive
        if let some preNorm := preNorm? then
          if ← proveFibreInsensitiveUnderRequires preNorm fibreAssump res then
            if ← proveFibreContraUnderRequires preNorm fibreAssump res then
              return .contradictory
            return .insensitiveUnderRequires
        return .genuine

      let numMasks := 1 <<< atoms.size
      let mut feasibleMasks : Nat := 0
      let mut fibreGenuine := false
      let mut liveFibres : Nat := 0
      let mut allLiveTrue := true
      let mut anyInsensitive := false
      let mut firstTautReason? : Option EnsuresVacuityReason := none
      for mask in [:numMasks] do
        let mut maskFeasible := true
        for i in [:atoms.size] do
          if let some fixedVal := atomFixedTruth? atoms[i]! then
            if (((mask >>> i) &&& 1) == 1) != fixedVal then
              maskFeasible := false
              break
        if !maskFeasible then
          continue
        let remCap? ← budget.nextCap?
        if remCap?.isNone then
          notes := notes ++
            ["probe heartbeat budget exhausted during boilerplate cofactoring; remaining fibres degraded conservatively"]
          budgetExhaustedNoteAdded := true
          fibreGenuine := true
          break
        let remCap := remCap?.getD 1000
        feasibleMasks := feasibleMasks + 1
        let fibreAssump := mkFibreAssumption atoms mask
        let rawRes := cofactorBoilerplate 64 atoms mask workBody
        let res? ← withBoundedHeartbeats remCap (unfoldUserConnectives 8 rawRes)
        let res := res?.getD rawRes
        match ← classifyFibre fibreAssump res with
        | .contradictory => pure ()
        | .tautological tautReason =>
          liveFibres := liveFibres + 1
          allLiveTrue := false
          if firstTautReason?.isNone then firstTautReason? := some tautReason
        | .insensitive =>
          liveFibres := liveFibres + 1
          anyInsensitive := true
          if !res.isConstOf ``True then allLiveTrue := false
        | .insensitiveUnderRequires =>
          liveFibres := liveFibres + 1
          allLiveTrue := false
        | .genuine =>
          fibreGenuine := true
        -- One genuine fibre settles Phase 3; skip the remaining fibres.
        if fibreGenuine then break
      if !fibreGenuine then
        if liveFibres == 0 then
          return .vacuous .unrealizableUnderRequires
            (notes ++ ["every boilerplate fibre is contradictory"])
        if let some tautReason := firstTautReason? then
          return .vacuous tautReason
            (notes ++ ["residual user ensures across boilerplate fibres is tautological"])
        if allLiveTrue && liveFibres == feasibleMasks then
          return .vacuous .trivialConstantTrue
            (notes ++ ["ensures is a propositional tautology over boilerplate atoms"])
        if liveFibres == feasibleMasks then
          if ← proveClosed workBody then
            return .vacuous .tautologicalByProver
              (notes ++ ["ensures proved universally valid across all boilerplate fibres"])
        if anyInsensitive then
          return .vacuous .boilerplateOnlyMasking
            (notes ++ ["normal-return postcondition constrains only boilerplate atoms"])
        return .vacuous .outputInsensitiveUnderRequires
          (notes ++ ["residual user ensures is output-insensitive under requires in every fibre"])

  -- Phase 4: Syntactic tautology & global prover checks (without `requires`).
  if let some tautReason := detectSyntacticTautology 32 [] workBody then
    return .vacuous tautReason (notes ++ ["detected syntactic tautology"])

  if ← proveClosed workBody then
    return .vacuous .tautologicalByProver
      (notes ++ ["ensures proved universally valid independent of requires"])

  if ← proveClosed (negate workBody) then
    return .vacuous .unrealizableUnderRequires
      (notes ++ ["ensures proved unsatisfiable for all inputs and outputs"])

  -- Always run the sound global output-insensitivity check: an unresolved or
  -- unreachable boilerplate fibre in Phase 3 does not refute global insensitivity.
  -- Check `requires`-relative unsatisfiability before returning `outputInsensitive` so
  -- unrealizable specs (`ret = ret ∧ ¬ pre`) are classified as `SpecViolation`.
  if ← proveInsensitive workBody then
    if let some preNorm := preNorm? then
      if ← proveUnderRequires preNorm (negate workBody) then
        return .vacuous .unrealizableUnderRequires
          (notes ++ ["ensures proved unsatisfiable under requires"])
    return .vacuous .outputInsensitive
      (notes ++ ["ensures proved independent of the output"])

  -- Phase 5: `requires`-aware semantic realizability and vacuity checks.
  if let some preNorm := preNorm? then
    if ← proveUnderRequires preNorm (negate workBody) then
      return .vacuous .unrealizableUnderRequires
        (notes ++ ["ensures proved unsatisfiable under requires"])
    if ← proveUnderRequires preNorm workBody then
      return .vacuous .vacuousUnderRequires
        (notes ++ ["ensures proved vacuously true for all outputs under requires"])
    if ← proveInsensitiveUnderRequires preNorm workBody then
      return .vacuous .outputInsensitiveUnderRequires
        (notes ++ ["ensures proved independent of the output under requires"])

  let probeCutOff ← probeCutOffRef.get
  let budgetExhausted := (← budget.nextCap?).isNone
  if !budgetExhaustedNoteAdded && budgetExhausted then
    notes := notes ++
      ["probe heartbeat budget exhausted; remaining semantic vacuity checks degraded conservatively"]
  else if !budgetExhaustedNoteAdded && probeCutOff then
    notes := notes ++
      ["one or more semantic vacuity probes exceeded their heartbeat/recursion cap; degraded conservatively"]

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
      -- Shape 2: Stateful `(inputs..., mem : Memory, ret, mem' : Memory)`.
      -- Requiring `allArgs[n - 3]` to also have type `Memory` avoids misclassifying
      -- ordinary stateless 4-argument functions returning `Memory` as stateful specs.
      let isStateful4 ← do
        if n >= 4 && lastTy.isConstOf ``Memory then
          let preMemTy ← whnf (← inferType allArgs[n - 3]!)
          let prevTy ← whnf (← inferType allArgs[n - 2]!)
          pure (preMemTy.isConstOf ``Memory && !prevTy.isConstOf ``Memory)
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
    `MirCallContract`, or standalone `ensures` predicate) for vacuity. For the five
    contract structures, `pre` is passed as `requires` whenever `cfg.useRequires`.

    A parameterized contract such as `def boundedClaim (bound : Nat) : Claim` is
    analyzed with its own parameters opened as local hypotheses. Every probe is then
    proved for arbitrary parameter values, so such a contract is flagged only when it
    is vacuous at every instantiation, instead of being misread as an `ensures`
    predicate that does not return `Prop`. -/
def checkDeclEnsuresBindsOutput
    (declName : Name) (cfg : EnsuresCheckConfig := {}) : MetaM EnsuresCheckResult := do
  let env ← getEnv
  let some info := env.find? declName
    | throwError "checkDeclEnsuresBindsOutput: unknown declaration `{declName}`"
  let declConst := mkConst declName (info.levelParams.map Level.param)
  let contractResult? : Option EnsuresCheckResult ←
    forallTelescopeReducing info.type fun (params : Array Expr) (resTy : Expr) => do
      let declExpr := mkAppN declConst params
      let ty ← whnf resTy
      let projNames? : Option (Name × Name) :=
        if ty.isConstOf ``Claim then
          some (``Claim.pre, ``Claim.post)
        else if ty.isConstOf ``StatefulClaim then
          some (``StatefulClaim.pre, ``StatefulClaim.post)
        else if ty.isConstOf ``TotalClaim then
          some (``TotalClaim.pre, ``TotalClaim.post)
        else if ty.isConstOf ``ModularClaim then
          some (``ModularClaim.pre, ``ModularClaim.post)
        else if ty.isConstOf ``MirCallContract then
          some (``MirCallContract.pre, ``MirCallContract.post)
        else
          none
      match projNames? with
      | some (preName, postName) =>
        let preExpr := mkApp (mkConst preName) declExpr
        let postExpr := mkApp (mkConst postName) declExpr
        let res ← checkEnsuresBindsOutput postExpr
          (if cfg.useRequires then some preExpr else none) cfg
        return some res
      | none => return none
  match contractResult? with
  | some res => return res
  | none =>
    -- Standalone `ensures` predicate: analyzed outside the parameter telescope so its
    -- own binders are split into inputs and outputs by `checkEnsuresBindsOutput`.
    checkEnsuresBindsOutput declConst none cfg

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
  if let some inh ← synthSortClassInstance? ``Inhabited ty then
    try
      let u ← getLevel ty
      return some (mkApp2 (mkConst ``Inhabited.default [u]) ty inh)
    catch _ => pure ()
  return none

/-- Check whether `requiresExpr` is satisfiable, returning `some false` when refuted
    for all inputs, `some true` when a witness or `True` over inhabited inputs is
    confirmed, or `none` when undecided within bounded heartbeats. -/
def checkRequiresSatisfiable (requiresExpr : Expr)
    (cfg : EnsuresCheckConfig := {}) : MetaM RequiresCheckResult := do
  let budget ← ProbeBudget.init cfg
  let typeCap := max 1000000 (min budget.totalInternal (cfg.stepHeartbeats * 1000))
  let reqExposed ← exposeHeadLambda 16 requiresExpr
  let reqTy ← inferType reqExposed
  forallTelescopeReducing reqTy fun inputs retSort => do
    if !(← isDefEq retSort (mkSort Level.zero)) then
      return {
        satisfiable? := none
        reason := "precondition expression does not return Prop"
      }
    let rawBody := (mkAppN reqExposed inputs).headBeta
    let normBody ← unfoldUserConnectives 16 (← zetaBetaProjReduce 32 rawBody)
    if normBody.isConstOf ``False then
      return { satisfiable? := some false, reason := "precondition is syntactically False" }
    let unsatGoal ← mkForallFVars inputs (mkApp (mkConst ``Not) normBody)
    if ← tryProveWithin budget unsatGoal then
      return {
        satisfiable? := some false
        reason := "precondition proved unsatisfiable for all inputs"
      }
    if normBody.isConstOf ``True then
      -- `True` is satisfiable exactly when every input type is inhabited. A
      -- proposition-typed input (a hypothesis binder) counts only if an instance
      -- witnesses it; it is never assumed inhabited. Instance synthesis is bounded
      -- so costly type indices (e.g. `Fin (deepIndex 5000)`) degrade cleanly.
      let mut allInhabited := true
      for inp in inputs do
        let inpTy ← inferType inp
        let nonEmpty? ← withBoundedHeartbeats typeCap (synthSortClassInstance? ``Nonempty inpTy)
        let hasNonEmpty : Bool := match nonEmpty? with
          | some (some _) => true
          | _ => false
        if !hasNonEmpty then
          let inh? ← withBoundedHeartbeats typeCap (synthSortClassInstance? ``Inhabited inpTy)
          let hasInh : Bool := match inh? with
            | some (some _) => true
            | _ => false
          if !hasInh then
            allInhabited := false
            break
      if allInhabited then
        return {
          satisfiable? := some true
          reason := "precondition is True over inhabited input types"
        }
    -- Try instantiating inputs with canonical default witnesses (e.g. `0`, `[]`, `emptyMemory`).
    -- The type of a dependent input is instantiated with the witnesses already chosen
    -- for the inputs it depends on, so the instantiated precondition stays well-typed
    -- (and `tryProveWithin` re-checks type-correctness before attempting a proof).
    let mut witnesses : Array Expr := #[]
    let mut allWitnessed := true
    for inp in inputs do
      let inpTy := (← inferType inp).replaceFVars (inputs.extract 0 witnesses.size) witnesses
      let w? ← withBoundedHeartbeats typeCap (defaultWitnessForType? inpTy)
      match w? with
      | some (some w) => witnesses := witnesses.push w
      | _ =>
        allWitnessed := false
        break
    if allWitnessed then
      let instRaw := (mkAppN reqExposed witnesses).headBeta
      let instGoal ← unfoldUserConnectives 16 (← zetaBetaProjReduce 32 instRaw)
      if ← tryProveWithin budget instGoal then
        return {
          satisfiable? := some true
          reason := "precondition proved satisfiable via canonical witness"
        }
    let satGoal ← mkNestedExists inputs normBody
    if ← tryProveWithin budget satGoal then
      return {
        satisfiable? := some true
        reason := "precondition proved satisfiable"
      }
    if (← budget.nextCap?).isNone then
      return {
        satisfiable? := none
        reason := "precondition satisfiability undecided: probe heartbeat budget exhausted"
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
