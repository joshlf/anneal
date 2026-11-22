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
# Contract realizability, postcondition dichotomy, and `ensures`-binding checks

**Prototype.** A kernel-checked proof of `pre → post` says nothing about whether
the *contract* is meaningful. *Verified but Vacuous* (arXiv:2611.05590)
catalogues contracts that verify while constraining nothing. This module
gives the five classes it motivates a semantic definition and a syntactic
detector:

1. an unsatisfiable `requires` (`requires(false)`, `requires(x < 10 && x > 20)`),
2. a constant-true `ensures` (`ensures(true)`),
3. a reflexive `ensures` (`ensures(ret == ret)`, `let y := ret; y = y`),
4. an input-only `ensures` (`ensures(x == x)`, `ensures(x < 100)`), and
5. an outcome-blind or return-blind `MirCallContract`, whose postcondition
   accepts every answer, or every *normal return* while still separating a
   return from an unwind.

It has two parts.

* **Part I (kernel).** A realizability and dichotomy calculus over arbitrary
  `Input` and `Output` types (`PreconditionSatisfiable`, `ContractRealizable`,
  `UniversalContractRealizable`, `PostconditionDichotomy`,
  `PointwisePostconditionDichotomy`, `ContractDeterministic`,
  `ContractDeterministicOn`), specialised to the trusted `MirCallContract`,
  `Claim`, and `StatefulClaim` gates. The central notion is
  `PostconditionDichotomy`: some admissible input has one accepted and one
  rejected output. Its negation is exactly `OutputInsensitive`
  (`not_postconditionDichotomy_iff_outputInsensitive`), so each of the classes
  2–5 refutes it, and it is equivalent to the existence of a killed output
  mutant (`postconditionDichotomy_iff_exists_killed_mutant`). Its relativised
  form `DichotomyModuloObservation` asks for the two outputs to agree on a
  given observation (the frame and return-type boilerplate of an external
  spec), which is what "the user `ensures` clause binds the output" means.

* **Part II (`MetaM`).** `checkEnsuresBindsOutput` inspects the `Expr` of a
  postcondition, normalises it by logical equivalences and definitional
  reductions only, and reports whether any designated output binder survives
  outside a tautology. Because every rewrite preserves the truth value of the
  postcondition, a postcondition it flags is `OutputInsensitive` in the
  designated outputs; the converse is not claimed (the check is a syntactic
  under-approximation of vacuity, strengthened by a bounded proof search).

Nothing here is part of the trusted computing base: the definitions are
obligations a specification author may be asked to discharge *before* a proof
is attempted, and the checker is advisory.
-/

namespace Anneal.SpecRealizabilityPrototype

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

universe u v w

/-! ## Part I.1 — Polymorphic realizability and anti-vacuity predicates -/

section Generic

variable {Input : Type u} {Output : Type v}

/-- Some input satisfies `pre`: the contract is not vacuous by `requires`. -/
def PreconditionSatisfiable (pre : Input → Prop) : Prop :=
  ∃ inp, pre inp

/-- Some admissible input has an accepted output. -/
def ContractRealizable
    (pre : Input → Prop) (post : Input → Output → Prop) : Prop :=
  ∃ inp out, pre inp ∧ post inp out

/--
`pre` is satisfiable and *every* admissible input has an accepted output: the
contract is implementable by a total (possibly non-computable) function.
-/
def UniversalContractRealizable
    (pre : Input → Prop) (post : Input → Output → Prop) : Prop :=
  PreconditionSatisfiable pre ∧ ∀ inp, pre inp → ∃ out, post inp out

/--
Some admissible input has an accepted output `out_ok` and a rejected output
`out_bad`: the postcondition separates two candidate results on one input.
-/
def PostconditionDichotomy
    (pre : Input → Prop) (post : Input → Output → Prop) : Prop :=
  ∃ inp out_ok out_bad, pre inp ∧ post inp out_ok ∧ ¬ post inp out_bad

/--
`pre` is satisfiable and *every* admissible input has both an accepted and a
rejected output.
-/
def PointwisePostconditionDichotomy
    (pre : Input → Prop) (post : Input → Output → Prop) : Prop :=
  PreconditionSatisfiable pre ∧
    ∀ inp, pre inp →
      (∃ out_ok, post inp out_ok) ∧ (∃ out_bad, ¬ post inp out_bad)

/-- Every admissible input has at most one accepted output. -/
def ContractDeterministic
    (pre : Input → Prop) (post : Input → Output → Prop) : Prop :=
  ∀ inp out₁ out₂, pre inp → post inp out₁ → post inp out₂ → out₁ = out₂

/--
Every admissible input determines the observation `proj out` of its accepted
outputs. This is the usable notion when `Output` pairs a returned `Value` with
a heap `Memory` the contract deliberately leaves loose.
-/
def ContractDeterministicOn {Val : Type w} (proj : Output → Val)
    (pre : Input → Prop) (post : Input → Output → Prop) : Prop :=
  ∀ inp out₁ out₂, pre inp → post inp out₁ → post inp out₂ →
    proj out₁ = proj out₂

/--
On every admissible input the postcondition cannot tell two outputs apart.
This is the semantic content of "the `ensures` clause does not bind the
output", and the exact negation of `PostconditionDichotomy`.
-/
def OutputInsensitive
    (pre : Input → Prop) (post : Input → Output → Prop) : Prop :=
  ∀ inp out₁ out₂, pre inp → post inp out₁ → post inp out₂

/--
Data-carrying dichotomy witness: an admissible input together with an accepted
and a rejected output.
-/
structure StrongContractWitness
    (pre : Input → Prop) (post : Input → Output → Prop) where
  /-- The admissible input. -/
  inp : Input
  /-- An output the postcondition accepts on `inp`. -/
  outOk : Output
  /-- An output the postcondition rejects on `inp`. -/
  outBad : Output
  pre_inp : pre inp
  post_ok : post inp outOk
  post_bad : ¬ post inp outBad

/--
Proof-level certificate bundling the three anti-vacuity levels a contract is
expected to meet.
-/
structure DichotomyCertificate
    (pre : Input → Prop) (post : Input → Output → Prop) : Prop where
  preSatisfiable : PreconditionSatisfiable pre
  realizable : ContractRealizable pre post
  dichotomy : PostconditionDichotomy pre post

/--
Certificate for a contract that is implementable on every admissible input,
separates outputs on every admissible input, and pins the observation `proj`.
-/
structure PointwiseDichotomyCertificate {Val : Type w} (proj : Output → Val)
    (pre : Input → Prop) (post : Input → Output → Prop) : Prop where
  universal : UniversalContractRealizable pre post
  pointwise : PointwisePostconditionDichotomy pre post
  deterministicOn : ContractDeterministicOn proj pre post

/-! ### Hierarchy -/

variable {pre : Input → Prop} {post : Input → Output → Prop}

theorem StrongContractWitness.toPostconditionDichotomy
    (wit : StrongContractWitness pre post) : PostconditionDichotomy pre post :=
  ⟨wit.inp, wit.outOk, wit.outBad, wit.pre_inp, wit.post_ok, wit.post_bad⟩

theorem postconditionDichotomy_iff_nonempty_witness :
    PostconditionDichotomy pre post ↔
      Nonempty (StrongContractWitness pre post) :=
  ⟨fun ⟨inp, ok, bad, hp, hok, hbad⟩ => ⟨⟨inp, ok, bad, hp, hok, hbad⟩⟩,
    fun ⟨wit⟩ => wit.toPostconditionDichotomy⟩

theorem ContractRealizable.toPreconditionSatisfiable
    (h : ContractRealizable pre post) : PreconditionSatisfiable pre :=
  let ⟨inp, _, hp, _⟩ := h
  ⟨inp, hp⟩

theorem PostconditionDichotomy.toContractRealizable
    (h : PostconditionDichotomy pre post) : ContractRealizable pre post :=
  let ⟨inp, ok, _, hp, hok, _⟩ := h
  ⟨inp, ok, hp, hok⟩

theorem PostconditionDichotomy.toPreconditionSatisfiable
    (h : PostconditionDichotomy pre post) : PreconditionSatisfiable pre :=
  h.toContractRealizable.toPreconditionSatisfiable

theorem UniversalContractRealizable.toContractRealizable
    (h : UniversalContractRealizable pre post) : ContractRealizable pre post :=
  let ⟨⟨inp, hp⟩, hall⟩ := h
  let ⟨out, hout⟩ := hall inp hp
  ⟨inp, out, hp, hout⟩

theorem PointwisePostconditionDichotomy.toUniversalContractRealizable
    (h : PointwisePostconditionDichotomy pre post) :
    UniversalContractRealizable pre post :=
  ⟨h.1, fun inp hp => (h.2 inp hp).1⟩

theorem PointwisePostconditionDichotomy.toPostconditionDichotomy
    (h : PointwisePostconditionDichotomy pre post) :
    PostconditionDichotomy pre post :=
  let ⟨⟨inp, hp⟩, hall⟩ := h
  let ⟨⟨ok, hok⟩, ⟨bad, hbad⟩⟩ := hall inp hp
  ⟨inp, ok, bad, hp, hok, hbad⟩

theorem DichotomyCertificate.ofDichotomy
    (h : PostconditionDichotomy pre post) : DichotomyCertificate pre post :=
  ⟨h.toPreconditionSatisfiable, h.toContractRealizable, h⟩

theorem DichotomyCertificate.ofWitness
    (wit : StrongContractWitness pre post) : DichotomyCertificate pre post :=
  .ofDichotomy wit.toPostconditionDichotomy

theorem PointwiseDichotomyCertificate.toDichotomyCertificate
    {Val : Type w} {proj : Output → Val}
    (h : PointwiseDichotomyCertificate proj pre post) :
    DichotomyCertificate pre post :=
  .ofDichotomy h.pointwise.toPostconditionDichotomy

theorem ContractDeterministic.toDeterministicOn {Val : Type w}
    (proj : Output → Val) (h : ContractDeterministic pre post) :
    ContractDeterministicOn proj pre post :=
  fun inp out₁ out₂ hp h₁ h₂ => congrArg proj (h inp out₁ out₂ hp h₁ h₂)

theorem contractDeterministic_iff_deterministicOn_id :
    ContractDeterministic pre post ↔ ContractDeterministicOn id pre post :=
  Iff.rfl

/--
A realizable contract that pins the observation `proj` separates outputs as
soon as some output is observably different from the realizing one. No
classical reasoning is needed: the differing output is itself rejected.
-/
theorem postconditionDichotomy_of_realizable_and_deterministicOn
    {Val : Type w} {proj : Output → Val}
    (h_det : ContractDeterministicOn proj pre post)
    (h_wit : ∃ inp out_ok, pre inp ∧ post inp out_ok ∧
      ∃ out_bad, proj out_bad ≠ proj out_ok) :
    PostconditionDichotomy pre post :=
  let ⟨inp, ok, hp, hok, bad, hne⟩ := h_wit
  ⟨inp, ok, bad, hp, hok, fun hbad => hne (h_det inp bad ok hp hbad hok)⟩

/--
Variant of `postconditionDichotomy_of_realizable_and_deterministicOn` for an
observation that is nowhere constant: every output has an observably different
one.
-/
theorem postconditionDichotomy_of_realizable_and_deterministicOn_of_forall
    {Val : Type w} {proj : Output → Val}
    (h_real : ContractRealizable pre post)
    (h_det : ContractDeterministicOn proj pre post)
    (h_two : ∀ out_ok, ∃ out_bad, proj out_bad ≠ proj out_ok) :
    PostconditionDichotomy pre post :=
  let ⟨inp, ok, hp, hok⟩ := h_real
  postconditionDichotomy_of_realizable_and_deterministicOn h_det
    ⟨inp, ok, hp, hok, h_two ok⟩

/--
Variant for an observation with two distinct values: one of the two outputs
realising them is rejected (classically, whichever is not the accepted one).
-/
theorem postconditionDichotomy_of_realizable_and_deterministicOn_of_two
    {Val : Type w} {proj : Output → Val}
    (h_real : ContractRealizable pre post)
    (h_det : ContractDeterministicOn proj pre post)
    (h_two : ∃ y₁ y₂ : Output, proj y₁ ≠ proj y₂) :
    PostconditionDichotomy pre post := by
  obtain ⟨inp, ok, hp, hok⟩ := h_real
  obtain ⟨y₁, y₂, hne⟩ := h_two
  refine postconditionDichotomy_of_realizable_and_deterministicOn h_det
    ⟨inp, ok, hp, hok, ?_⟩
  by_cases h₁ : proj y₁ = proj ok
  · exact ⟨y₂, fun h₂ => hne (h₁.trans h₂.symm)⟩
  · exact ⟨y₁, h₁⟩

/--
A realizable, deterministic contract over an output type with two distinct
elements separates outputs: determinism forbids accepting both.
-/
theorem postconditionDichotomy_of_realizable_and_deterministic
    (h_real : ContractRealizable pre post)
    (h_det : ContractDeterministic pre post)
    (h_two : ∃ y₁ y₂ : Output, y₁ ≠ y₂) :
    PostconditionDichotomy pre post :=
  postconditionDichotomy_of_realizable_and_deterministicOn_of_two
    (proj := id) h_real h_det h_two

/--
A contract that is implementable on every admissible input and pins an
observation that is nowhere constant separates outputs on *every* admissible
input.
-/
theorem pointwiseDichotomy_of_universal_and_deterministicOn
    {Val : Type w} {proj : Output → Val}
    (h_univ : UniversalContractRealizable pre post)
    (h_det : ContractDeterministicOn proj pre post)
    (h_two : ∀ out_ok, ∃ out_bad, proj out_bad ≠ proj out_ok) :
    PointwisePostconditionDichotomy pre post :=
  ⟨h_univ.1, fun inp hp =>
    let ⟨ok, hok⟩ := h_univ.2 inp hp
    let ⟨bad, hne⟩ := h_two ok
    ⟨⟨ok, hok⟩, ⟨bad, fun hbad => hne (h_det inp bad ok hp hbad hok)⟩⟩⟩

/-! ### Impossibility: each vacuity class refutes the matching predicate -/

/-- Class 1: an unsatisfiable `requires`. -/
theorem not_preconditionSatisfiable_of_unsat
    (h : ∀ inp, ¬ pre inp) : ¬ PreconditionSatisfiable pre :=
  fun ⟨inp, hp⟩ => h inp hp

theorem not_realizable_of_unsat_pre
    (h : ¬ PreconditionSatisfiable pre) : ¬ ContractRealizable pre post :=
  fun hr => h hr.toPreconditionSatisfiable

theorem not_universalRealizable_of_unsat_pre
    (h : ¬ PreconditionSatisfiable pre) :
    ¬ UniversalContractRealizable pre post :=
  fun hr => h hr.1

theorem not_dichotomy_of_unsat_pre
    (h : ¬ PreconditionSatisfiable pre) : ¬ PostconditionDichotomy pre post :=
  fun hd => h hd.toPreconditionSatisfiable

/--
The exact semantic characterisation of a non-binding `ensures`: dichotomy
fails precisely when the postcondition is output-insensitive on `pre`.
-/
theorem not_postconditionDichotomy_iff_outputInsensitive :
    ¬ PostconditionDichotomy pre post ↔ OutputInsensitive pre post := by
  constructor
  · intro h inp out₁ out₂ hp h₁
    apply Classical.byContradiction
    intro h₂
    exact h ⟨inp, out₁, out₂, hp, h₁, h₂⟩
  · rintro h ⟨inp, ok, bad, hp, hok, hbad⟩
    exact hbad (h inp ok bad hp hok)

theorem postconditionDichotomy_iff_not_outputInsensitive :
    PostconditionDichotomy pre post ↔ ¬ OutputInsensitive pre post := by
  constructor
  · exact fun hd hi => not_postconditionDichotomy_iff_outputInsensitive.mpr hi hd
  · intro h
    apply Classical.byContradiction
    exact fun hd => h (not_postconditionDichotomy_iff_outputInsensitive.mp hd)

/-- Class 4 (general form): the postcondition ignores the output. -/
theorem not_dichotomy_of_input_only
    (h : ∀ inp out₁ out₂, pre inp → (post inp out₁ ↔ post inp out₂)) :
    ¬ PostconditionDichotomy pre post :=
  not_postconditionDichotomy_iff_outputInsensitive.mpr
    fun inp out₁ out₂ hp h₁ => (h inp out₁ out₂ hp).mp h₁

/-- Class 4: the postcondition is a predicate `p` of the input alone. -/
theorem not_dichotomy_of_input_predicate (p : Input → Prop)
    (h : ∀ inp out, pre inp → (post inp out ↔ p inp)) :
    ¬ PostconditionDichotomy pre post :=
  not_dichotomy_of_input_only fun inp out₁ out₂ hp =>
    (h inp out₁ hp).trans (h inp out₂ hp).symm

/-- Class 2: the postcondition holds of every output of an admissible input. -/
theorem not_dichotomy_of_universal_post
    (h : ∀ inp out, pre inp → post inp out) :
    ¬ PostconditionDichotomy pre post :=
  fun ⟨inp, _, bad, hp, _, hbad⟩ => hbad (h inp bad hp)

/-- Class 2: `ensures(true)`, the canonical universally true postcondition. -/
theorem not_dichotomy_of_const_true
    (h : ∀ inp out, pre inp → post inp out) :
    ¬ PostconditionDichotomy pre post :=
  not_dichotomy_of_universal_post h

/-- Class 2: the literal constant `True` postcondition never separates outputs. -/
theorem not_dichotomy_of_const_true_literal :
    ¬ PostconditionDichotomy pre (fun (_ : Input) (_ : Output) => (True : Prop)) :=
  not_dichotomy_of_universal_post fun _ _ _ => trivial

/-- Class 2, stated as an equivalence with `True`. -/
theorem not_dichotomy_of_iff_true
    (h : ∀ inp out, pre inp → (post inp out ↔ True)) :
    ¬ PostconditionDichotomy pre post :=
  not_dichotomy_of_universal_post fun inp out hp => (h inp out hp).mpr trivial

/--
Class 3: the postcondition is a reflexive equation `f inp out = f inp out`,
which mentions the output while holding of all of them.
-/
theorem not_dichotomy_of_refl_tautology {α : Sort w} (f : Input → Output → α)
    (h : ∀ inp out, pre inp → (post inp out ↔ f inp out = f inp out)) :
    ¬ PostconditionDichotomy pre post :=
  not_dichotomy_of_universal_post fun inp out hp => (h inp out hp).mpr rfl

/-- A postcondition no output satisfies is not realizable, hence not separating. -/
theorem not_dichotomy_of_unsat_post
    (h : ∀ inp out, pre inp → ¬ post inp out) :
    ¬ PostconditionDichotomy pre post :=
  fun ⟨inp, ok, _, hp, hok, _⟩ => h inp ok hp hok

/--
No contract (deterministic or not) over a subsingleton output type can separate
outputs: dichotomy requires two distinct candidates.
-/
theorem not_dichotomy_of_subsingleton_output
    (h : ∀ out₁ out₂ : Output, out₁ = out₂) :
    ¬ PostconditionDichotomy pre post :=
  fun ⟨_, ok, bad, _, hok, hbad⟩ => hbad (h ok bad ▸ hok)

theorem not_dichotomy_of_subsingleton [Subsingleton Output] :
    ¬ PostconditionDichotomy pre post :=
  not_dichotomy_of_subsingleton_output Subsingleton.elim

/--
`UniversalContractRealizable` is strictly stronger than `ContractRealizable`:
a contract can have one realizable input while failing on another admissible
input.
-/
theorem universalRealizable_strictly_stronger_than_realizable :
    (∀ (pre : Input → Prop) (post : Input → Output → Prop),
      UniversalContractRealizable pre post → ContractRealizable pre post) ∧
      ∃ (pre : Bool → Prop) (post : Bool → Bool → Prop),
        ContractRealizable pre post ∧ ¬ UniversalContractRealizable pre post :=
  ⟨fun _ _ h => h.toContractRealizable,
    fun _ => True, fun b _ => b = true,
    ⟨true, true, trivial, rfl⟩,
    fun ⟨_, hall⟩ =>
      let ⟨_, hbad⟩ := hall false trivial
      Bool.false_ne_true hbad⟩

/--
`PointwisePostconditionDichotomy` is strictly stronger than
`PostconditionDichotomy`: a postcondition may constrain the output on one input
while accepting every output on another.
-/
theorem pointwiseDichotomy_strictly_stronger_than_dichotomy :
    (∀ (pre : Input → Prop) (post : Input → Output → Prop),
      PointwisePostconditionDichotomy pre post →
        PostconditionDichotomy pre post) ∧
      ∃ (pre : Bool → Prop) (post : Bool → Bool → Prop),
        PostconditionDichotomy pre post ∧
          ¬ PointwisePostconditionDichotomy pre post :=
  ⟨fun _ _ h => h.toPostconditionDichotomy,
    fun _ => True, fun inp out => inp = true → out = true,
    ⟨true, true, false, trivial, fun _ => rfl,
      fun h => Bool.false_ne_true (h rfl)⟩,
    fun ⟨_, hall⟩ =>
      let ⟨_, ⟨_bad, hbad⟩⟩ := hall false trivial
      hbad fun h => absurd h Bool.false_ne_true⟩

/-! ### Refinement, strengthening, and subsumption -/

/--
Strengthening the postcondition preserves dichotomy at any input where the
stronger contract is still realizable and the weaker one already rejects an
output. The hypothesis `pre inp₀` is not used: rejection by `post` is
transported along `h_strengthen`, which only needs `pre' inp₀`; see
`dichotomy_of_strengthening_at` for the statement without it.
-/
theorem dichotomy_preserved_under_strengthening_of_nonvacuous_refinement
    {pre' : Input → Prop} {post' : Input → Output → Prop}
    (h_strengthen : ∀ inp out, pre' inp → post' inp out → post inp out)
    (h_wit : ∃ inp₀, pre' inp₀ ∧ pre inp₀ ∧
      (∃ out_ok, post' inp₀ out_ok) ∧ (∃ out_bad, ¬ post inp₀ out_bad)) :
    PostconditionDichotomy pre' post' :=
  let ⟨inp₀, hp', _, ⟨ok, hok⟩, ⟨bad, hbad⟩⟩ := h_wit
  ⟨inp₀, ok, bad, hp', hok, fun h => hbad (h_strengthen inp₀ bad hp' h)⟩

/-- Sharp form of the strengthening theorem, without the unused `pre inp₀`. -/
theorem dichotomy_of_strengthening_at
    {pre' : Input → Prop} {post' : Input → Output → Prop}
    (h_strengthen : ∀ inp out, pre' inp → post' inp out → post inp out)
    (inp₀ : Input) (h_pre' : pre' inp₀)
    (h_ok : ∃ out_ok, post' inp₀ out_ok)
    (h_bad : ∃ out_bad, ¬ post inp₀ out_bad) :
    PostconditionDichotomy pre' post' :=
  let ⟨ok, hok⟩ := h_ok
  let ⟨bad, hbad⟩ := h_bad
  ⟨inp₀, ok, bad, h_pre', hok, fun h => hbad (h_strengthen inp₀ bad h_pre' h)⟩

/--
Strengthening alone does not preserve dichotomy: the non-vacuity hypothesis of
`dichotomy_preserved_under_strengthening_of_nonvacuous_refinement` is needed,
because strengthening to an unsatisfiable postcondition destroys realizability.
-/
theorem exists_strengthening_losing_dichotomy :
    ∃ (pre : Unit → Prop) (post post' : Unit → Bool → Prop),
      PostconditionDichotomy pre post ∧
      (∀ inp out, pre inp → post' inp out → post inp out) ∧
      ¬ PostconditionDichotomy pre post' :=
  ⟨fun _ => True, fun _ b => b = true, fun _ _ => False,
    ⟨(), true, false, trivial, rfl, Bool.false_ne_true⟩,
    fun _ _ _ h => h.elim,
    fun ⟨_, _, _, _, hok, _⟩ => hok⟩

/-- Weakening does not preserve dichotomy either: `ensures(true)` is weakest. -/
theorem exists_weakening_losing_dichotomy :
    ∃ (pre : Unit → Prop) (post post' : Unit → Bool → Prop),
      PostconditionDichotomy pre post ∧
      (∀ inp out, pre inp → post inp out → post' inp out) ∧
      ¬ PostconditionDichotomy pre post' :=
  ⟨fun _ => True, fun _ b => b = true, fun _ _ => True,
    ⟨(), true, false, trivial, rfl, Bool.false_ne_true⟩,
    fun _ _ _ _ => trivial,
    fun ⟨_, _, _, _, _, hbad⟩ => hbad trivial⟩

/--
Contract subsumption in the shape of `MirCallContract.Subsumes`: every input
the *sub* contract admits is admitted by the *super* contract, and every output
the super contract accepts there is accepted by the sub contract. The super
contract is therefore the more demanding callee specification (weaker
`requires`, stronger `ensures`).
-/
def ContractSubsumes
    (preSub : Input → Prop) (postSub : Input → Output → Prop)
    (preSuper : Input → Prop) (postSuper : Input → Output → Prop) : Prop :=
  ∀ inp, preSub inp → preSuper inp ∧ ∀ out, postSuper inp out → postSub inp out

section Subsumption

variable {preSub preSuper : Input → Prop}
  {postSub postSuper : Input → Output → Prop}

/-- Precondition satisfiability ascends from `cSub` to `cSuper`. -/
theorem ContractSubsumes.preSatisfiable_super_of_sub
    (h : ContractSubsumes preSub postSub preSuper postSuper)
    (h_pre : PreconditionSatisfiable preSub) :
    PreconditionSatisfiable preSuper :=
  let ⟨inp, hp⟩ := h_pre
  ⟨inp, (h inp hp).1⟩

/--
Acceptance flows from super to sub: a super-accepted output on a sub-admissible
input realises *both* contracts.
-/
theorem ContractSubsumes.realizable_of_super_on_sub
    (h : ContractSubsumes preSub postSub preSuper postSuper)
    (h_wit : ∃ inp out, preSub inp ∧ postSuper inp out) :
    ContractRealizable preSub postSub ∧
      ContractRealizable preSuper postSuper :=
  let ⟨inp, out, hp, hq⟩ := h_wit
  ⟨⟨inp, out, hp, (h inp hp).2 out hq⟩, ⟨inp, out, (h inp hp).1, hq⟩⟩

/-- Rejection flows from sub to super on sub-admissible inputs. -/
theorem ContractSubsumes.not_post_super_of_not_post_sub
    (h : ContractSubsumes preSub postSub preSuper postSuper)
    {inp : Input} {out : Output} (h_pre : preSub inp)
    (h_bad : ¬ postSub inp out) : ¬ postSuper inp out :=
  fun hq => h_bad ((h inp h_pre).2 out hq)

/--
Dichotomy transfer under subsumption. If, on one sub-admissible input, the
super contract accepts `out_ok` and the sub contract rejects `out_bad`, then
*both* contracts separate outputs there: acceptance is pulled down to the sub
contract and rejection is pushed up to the super contract.
-/
theorem ContractSubsumes.dichotomy_of_super_ok_sub_bad
    (h : ContractSubsumes preSub postSub preSuper postSuper)
    (h_wit : ∃ inp out_ok out_bad,
      preSub inp ∧ postSuper inp out_ok ∧ ¬ postSub inp out_bad) :
    PostconditionDichotomy preSub postSub ∧
      PostconditionDichotomy preSuper postSuper :=
  let ⟨inp, ok, bad, hp, hok, hbad⟩ := h_wit
  ⟨⟨inp, ok, bad, hp, (h inp hp).2 ok hok, hbad⟩,
    ⟨inp, ok, bad, (h inp hp).1, hok,
      h.not_post_super_of_not_post_sub hp hbad⟩⟩

/--
If the super contract accepts every output on the sub domain, the sub contract
(whose postcondition is weaker there) cannot separate outputs. In general
neither contract's dichotomy implies the other's
(`exists_subsumes_dichotomy_super_not_sub`,
`exists_subsumes_dichotomy_sub_not_super`).
-/
theorem ContractSubsumes.not_dichotomy_sub_of_universal_super_on_sub
    (h : ContractSubsumes preSub postSub preSuper postSuper)
    (h_total : ∀ inp out, preSub inp → postSuper inp out) :
    ¬ PostconditionDichotomy preSub postSub :=
  not_dichotomy_of_universal_post fun inp out hp =>
    (h inp hp).2 out (h_total inp out hp)

end Subsumption

/-- Dichotomy of the super contract does not descend to the sub contract. -/
theorem exists_subsumes_dichotomy_super_not_sub :
    ∃ (preSub preSuper : Unit → Prop) (postSub postSuper : Unit → Bool → Prop),
      ContractSubsumes preSub postSub preSuper postSuper ∧
      PostconditionDichotomy preSuper postSuper ∧
      ¬ PostconditionDichotomy preSub postSub :=
  ⟨fun _ => True, fun _ => True, fun _ _ => True, fun _ b => b = true,
    fun _ _ => ⟨trivial, fun _ _ => trivial⟩,
    ⟨(), true, false, trivial, rfl, Bool.false_ne_true⟩,
    fun ⟨_, _, _, _, _, hbad⟩ => hbad trivial⟩

/-- Dichotomy of the sub contract does not ascend to the super contract. -/
theorem exists_subsumes_dichotomy_sub_not_super :
    ∃ (preSub preSuper : Unit → Prop) (postSub postSuper : Unit → Bool → Prop),
      ContractSubsumes preSub postSub preSuper postSuper ∧
      PostconditionDichotomy preSub postSub ∧
      ¬ PostconditionDichotomy preSuper postSuper :=
  ⟨fun _ => True, fun _ => True, fun _ b => b = true, fun _ _ => False,
    fun _ _ => ⟨trivial, fun _ h => h.elim⟩,
    ⟨(), true, false, trivial, rfl, Bool.false_ne_true⟩,
    fun ⟨_, _, _, _, hok, _⟩ => hok⟩

/-! ### Vacuity is relative to the precondition -/

/-- A postcondition no output satisfies on admissible inputs is not realizable. -/
theorem not_realizable_of_unsat_post
    (h : ∀ inp out, pre inp → ¬ post inp out) :
    ¬ ContractRealizable pre post :=
  fun ⟨inp, out, hp, hq⟩ => h inp out hp hq

/-- Output-insensitivity is inherited by every stronger precondition. -/
theorem OutputInsensitive.of_pre_imp {pre' : Input → Prop}
    (h_imp : ∀ inp, pre' inp → pre inp) (h : OutputInsensitive pre post) :
    OutputInsensitive pre' post :=
  fun inp out₁ out₂ hp h₁ => h inp out₁ out₂ (h_imp inp hp) h₁

/-- Dichotomy survives weakening the precondition. -/
theorem PostconditionDichotomy.of_pre_imp {pre' : Input → Prop}
    (h_imp : ∀ inp, pre inp → pre' inp) (h : PostconditionDichotomy pre post) :
    PostconditionDichotomy pre' post :=
  let ⟨inp, ok, bad, hp, hok, hbad⟩ := h
  ⟨inp, ok, bad, h_imp inp hp, hok, hbad⟩

/--
Whether an `ensures` clause binds the output cannot be judged from the clause
alone: a postcondition that separates outputs with no precondition may fail to
separate any on the inputs a satisfiable precondition admits. Here
`requires(x = false) ensures(x = true → ret = true)`: the guard of the
`ensures` contradicts the `requires`.
-/
theorem exists_dichotomy_lost_under_requires :
    ∃ (pre : Bool → Prop) (post : Bool → Bool → Prop),
      PostconditionDichotomy (fun _ => True) post ∧
      PreconditionSatisfiable pre ∧
      ContractRealizable pre post ∧
      ¬ PostconditionDichotomy pre post :=
  ⟨fun x => x = false, fun x ret => x = true → ret = true,
    ⟨true, true, false, trivial, fun _ => rfl,
      fun h => Bool.false_ne_true (h rfl)⟩,
    ⟨false, rfl⟩,
    ⟨false, false, rfl, fun h => absurd h Bool.false_ne_true⟩,
    not_dichotomy_of_universal_post fun _ _ hx h =>
      absurd (hx.symm.trans h) Bool.false_ne_true⟩

/-! ### Sequential composition -/

section Sequential

variable {Mid : Type w}

/--
Precondition of the sequential composite of two contracts through an
intermediate value: the first contract admits the input, and every
intermediate value it accepts is admitted by the second.
-/
def seqPre (pre₁ : Input → Prop) (post₁ : Input → Mid → Prop)
    (pre₂ : Mid → Prop) : Input → Prop :=
  fun inp => pre₁ inp ∧ ∀ mid, post₁ inp mid → pre₂ mid

/--
Postcondition of the sequential composite: some intermediate value accepted by
the first contract leads to the output under the second.
-/
def seqPost (post₁ : Input → Mid → Prop) (post₂ : Mid → Output → Prop) :
    Input → Output → Prop :=
  fun inp out => ∃ mid, post₁ inp mid ∧ post₂ mid out

variable {pre₁ : Input → Prop} {post₁ : Input → Mid → Prop}
  {pre₂ : Mid → Prop} {post₂ : Mid → Output → Prop}

/--
Vacuity is contagious downstream: if the second contract does not bind its
output, neither does any composite that ends with it, whatever the first
contract says.
-/
theorem not_dichotomy_seq_of_second_outputInsensitive
    (h : OutputInsensitive pre₂ post₂) :
    ¬ PostconditionDichotomy (seqPre pre₁ post₁ pre₂) (seqPost post₁ post₂) :=
  not_postconditionDichotomy_iff_outputInsensitive.mpr
    fun _ out₁ out₂ ⟨_, hmid⟩ ⟨mid, h₁, h₂⟩ =>
      ⟨mid, h₁, h mid out₁ out₂ (hmid mid h₁) h₂⟩

/-- An unrealizable first contract makes every composite unrealizable. -/
theorem not_realizable_seq_of_first_unrealizable
    (h : ¬ ContractRealizable pre₁ post₁) :
    ¬ ContractRealizable (seqPre pre₁ post₁ pre₂) (seqPost post₁ post₂) :=
  fun ⟨inp, _, ⟨hp, _⟩, mid, h₁, _⟩ => h ⟨inp, mid, hp, h₁⟩

/--
Dichotomy is transported through a *deterministic* first contract: if the
intermediate value is pinned and the second contract separates two outputs on
it, the composite separates them on the original input.
-/
theorem dichotomy_seq_of_deterministic_first
    (h_det : ContractDeterministic pre₁ post₁)
    (h_wit : ∃ inp mid out_ok out_bad,
      seqPre pre₁ post₁ pre₂ inp ∧ post₁ inp mid ∧
        post₂ mid out_ok ∧ ¬ post₂ mid out_bad) :
    PostconditionDichotomy (seqPre pre₁ post₁ pre₂) (seqPost post₁ post₂) :=
  let ⟨inp, mid, ok, bad, hp, h₁, hok, hbad⟩ := h_wit
  ⟨inp, ok, bad, hp, ⟨mid, h₁, hok⟩, fun ⟨mid', h₁', hbad'⟩ =>
    hbad (h_det inp mid' mid hp.1 h₁' h₁ ▸ hbad')⟩

/--
Determinism of the first contract cannot be dropped: a first contract that
accepts every intermediate value erases the dichotomy of the second.
-/
theorem exists_seq_losing_dichotomy :
    ∃ (pre₁ : Unit → Prop) (post₁ : Unit → Bool → Prop) (pre₂ : Bool → Prop)
      (post₂ : Bool → Bool → Prop),
      PostconditionDichotomy pre₂ post₂ ∧
      ContractRealizable (seqPre pre₁ post₁ pre₂) (seqPost post₁ post₂) ∧
      ¬ PostconditionDichotomy (seqPre pre₁ post₁ pre₂) (seqPost post₁ post₂) :=
  ⟨fun _ => True, fun _ _ => True, fun _ => True, fun mid out => out = mid,
    ⟨true, true, false, trivial, rfl, Bool.false_ne_true⟩,
    ⟨(), true, ⟨trivial, fun _ _ => trivial⟩, true, trivial, rfl⟩,
    not_dichotomy_of_universal_post fun _ out _ => ⟨out, trivial, rfl⟩⟩

/-- If the second contract is unrealizable, so is every composite ending with it. -/
theorem not_realizable_seq_of_second_unrealizable
    (h : ¬ ContractRealizable pre₂ post₂) :
    ¬ ContractRealizable (seqPre pre₁ post₁ pre₂) (seqPost post₁ post₂) :=
  fun ⟨_, out, ⟨_, hmid⟩, mid, h₁, h₂⟩ => h ⟨mid, out, hmid mid h₁, h₂⟩

/-- Sequential composition of two deterministic contracts is deterministic. -/
theorem contractDeterministic_seq
    (h₁ : ContractDeterministic pre₁ post₁)
    (h₂ : ContractDeterministic pre₂ post₂) :
    ContractDeterministic (seqPre pre₁ post₁ pre₂) (seqPost post₁ post₂) := by
  rintro inp out₁ out₂ ⟨hp₁, hmid⟩ ⟨m₁, hm₁, ho₁⟩ ⟨m₂, hm₂, ho₂⟩
  have hm : m₁ = m₂ := h₁ inp m₁ m₂ hp₁ hm₁ hm₂
  subst hm
  exact h₂ m₁ out₁ out₂ (hmid m₁ hm₁) ho₁ ho₂

/-- Universal realizability composes whenever the composite precondition holds. -/
theorem universalRealizable_seq
    (h_pre : PreconditionSatisfiable (seqPre pre₁ post₁ pre₂))
    (h₁ : UniversalContractRealizable pre₁ post₁)
    (h₂ : UniversalContractRealizable pre₂ post₂) :
    UniversalContractRealizable (seqPre pre₁ post₁ pre₂) (seqPost post₁ post₂) :=
  ⟨h_pre, fun inp ⟨hp₁, hmid⟩ =>
    let ⟨mid, hm⟩ := h₁.2 inp hp₁
    let ⟨out, ho⟩ := h₂.2 mid (hmid mid hm)
    ⟨out, mid, hm, ho⟩⟩

/--
Pointwise dichotomy composes through a deterministic first stage whenever the
composite precondition is satisfiable.
-/
theorem pointwiseDichotomy_seq_of_deterministic_first
    (h_pre : PreconditionSatisfiable (seqPre pre₁ post₁ pre₂))
    (h_u₁ : UniversalContractRealizable pre₁ post₁)
    (h_det₁ : ContractDeterministic pre₁ post₁)
    (h_pt₂ : PointwisePostconditionDichotomy pre₂ post₂) :
    PointwisePostconditionDichotomy (seqPre pre₁ post₁ pre₂) (seqPost post₁ post₂) :=
  ⟨h_pre, fun inp ⟨hp₁, hmid⟩ =>
    let ⟨mid, hm⟩ := h_u₁.2 inp hp₁
    let ⟨⟨ok, hok⟩, ⟨bad, hbad⟩⟩ := h_pt₂.2 mid (hmid mid hm)
    ⟨⟨ok, mid, hm, hok⟩,
      ⟨bad, fun ⟨mid', hm', hbad'⟩ =>
        hbad (h_det₁ inp mid' mid hp₁ hm' hm ▸ hbad')⟩⟩⟩

end Sequential

/-! ### Dichotomy beyond a boilerplate predicate (semantic cofactoring) -/

/--
`post` genuinely separates outputs *beyond* a side/boilerplate predicate `bp`:
some admissible input has an accepted output `out_ok` and a rejected output
`out_bad` that agree on `bp` (`bp inp out_ok ↔ bp inp out_bad`). This is the
exact semantic property tested by cofactoring `bp` over `{True, False}` in
`userEnsuresOnly` mode.
-/
def DichotomyBeyondPredicate
    (bp : Input → Output → Prop)
    (pre : Input → Prop) (post : Input → Output → Prop) : Prop :=
  ∃ inp out_ok out_bad,
    pre inp ∧ (bp inp out_ok ↔ bp inp out_bad) ∧
      post inp out_ok ∧ ¬ post inp out_bad

theorem DichotomyBeyondPredicate.toPostconditionDichotomy
    {bp : Input → Output → Prop}
    (h : DichotomyBeyondPredicate bp pre post) :
    PostconditionDichotomy pre post :=
  let ⟨inp, ok, bad, hp, _, hok, hbad⟩ := h
  ⟨inp, ok, bad, hp, hok, hbad⟩

/--
Exact cofactor decomposition: `post` separates two outputs agreeing on `bp` if
and only if either the `bp = True` cofactor or the `bp = False` cofactor
separates two outputs.
-/
theorem dichotomyBeyondPredicate_iff_cofactors
    (bp : Input → Output → Prop) :
    DichotomyBeyondPredicate bp pre post ↔
      (∃ inp out_ok out_bad,
        pre inp ∧ bp inp out_ok ∧ bp inp out_bad ∧
          post inp out_ok ∧ ¬ post inp out_bad) ∨
      (∃ inp out_ok out_bad,
        pre inp ∧ ¬ bp inp out_ok ∧ ¬ bp inp out_bad ∧
          post inp out_ok ∧ ¬ post inp out_bad) := by
  constructor
  · rintro ⟨inp, ok, bad, hp, hiff, hok, hbad⟩
    rcases Classical.em (bp inp ok) with hbp | hnbp
    · exact .inl ⟨inp, ok, bad, hp, hbp, hiff.mp hbp, hok, hbad⟩
    · exact .inr ⟨inp, ok, bad, hp, hnbp, fun h => hnbp (hiff.mpr h), hok, hbad⟩
  · rintro (⟨inp, ok, bad, hp, hb1, hb2, hok, hbad⟩ |
      ⟨inp, ok, bad, hp, hnb1, hnb2, hok, hbad⟩)
    · exact ⟨inp, ok, bad, hp, ⟨fun _ => hb2, fun _ => hb1⟩, hok, hbad⟩
    · exact ⟨inp, ok, bad, hp, ⟨fun h => absurd h hnb1, fun h => absurd h hnb2⟩,
        hok, hbad⟩

/--
A postcondition determined solely by the input and the truth value of `bp`
(including `bp ∨ False`, `¬¬ bp`, `bp ↔ True`, `¬ bp → False`, or any Boolean
combination of boilerplate alone) has no dichotomy beyond `bp`.
-/
theorem not_dichotomyBeyondPredicate_of_boilerplate_only
    {bp : Input → Output → Prop}
    (h : ∀ inp out₁ out₂, pre inp →
      (bp inp out₁ ↔ bp inp out₂) → (post inp out₁ ↔ post inp out₂)) :
    ¬ DichotomyBeyondPredicate bp pre post :=
  fun ⟨inp, ok, bad, hp, hiff, hok, hbad⟩ =>
    hbad ((h inp ok bad hp hiff).mp hok)

/-! ### Dichotomy modulo an observation (several boilerplate predicates) -/

/--
`post` separates two outputs that the observation `obs` cannot tell apart: some
admissible input has an accepted `out_ok` and a rejected `out_bad` with
`obs inp out_ok = obs inp out_bad`.

`DichotomyBeyondPredicate bp` is the instance `obs := bp`
(`dichotomyBeyondPredicate_iff_moduloObservation`). With several boilerplate
predicates the observation that matters is the *tuple* of their truth values:
the two candidates have to agree on **each** predicate. Agreeing on their
conjunction is strictly coarser (`exists_dichotomyBeyond_conj_not_moduloPair`):
a postcondition that merely repeats one of two boilerplate predicates separates
two outputs on which the conjunction is false both times. The tuple is what
the checker fixes in `userEnsuresOnly` mode, one cofactor per truth assignment
(`not_dichotomyModuloObservation_of_cofactors_insensitive`).
-/
def DichotomyModuloObservation {Obs : Type w}
    (obs : Input → Output → Obs)
    (pre : Input → Prop) (post : Input → Output → Prop) : Prop :=
  ∃ inp out_ok out_bad,
    pre inp ∧ obs inp out_ok = obs inp out_bad ∧
      post inp out_ok ∧ ¬ post inp out_bad

theorem DichotomyModuloObservation.toPostconditionDichotomy
    {Obs : Type w} {obs : Input → Output → Obs}
    (h : DichotomyModuloObservation obs pre post) :
    PostconditionDichotomy pre post :=
  let ⟨inp, ok, bad, hp, _, hok, hbad⟩ := h
  ⟨inp, ok, bad, hp, hok, hbad⟩

/-- A single predicate is the observation of its truth value. -/
theorem dichotomyBeyondPredicate_iff_moduloObservation
    (bp : Input → Output → Prop) :
    DichotomyBeyondPredicate bp pre post ↔
      DichotomyModuloObservation bp pre post :=
  ⟨fun ⟨inp, ok, bad, hp, hiff, hok, hbad⟩ =>
      ⟨inp, ok, bad, hp, propext hiff, hok, hbad⟩,
    fun ⟨inp, ok, bad, hp, heq, hok, hbad⟩ =>
      ⟨inp, ok, bad, hp, heq ▸ Iff.rfl, hok, hbad⟩⟩

/--
Fibre decomposition, the `n`-ary form of `dichotomyBeyondPredicate_iff_cofactors`:
`post` separates two outputs with the same observation iff, for some observed
value `b`, it separates two outputs both observed as `b`.
-/
theorem dichotomyModuloObservation_iff_fibres
    {Obs : Type w} (obs : Input → Output → Obs) :
    DichotomyModuloObservation obs pre post ↔
      ∃ b inp out_ok out_bad,
        pre inp ∧ obs inp out_ok = b ∧ obs inp out_bad = b ∧
          post inp out_ok ∧ ¬ post inp out_bad :=
  ⟨fun ⟨inp, ok, bad, hp, heq, hok, hbad⟩ =>
      ⟨obs inp ok, inp, ok, bad, hp, rfl, heq.symm, hok, hbad⟩,
    fun ⟨_, inp, ok, bad, hp, h₁, h₂, hok, hbad⟩ =>
      ⟨inp, ok, bad, hp, h₁.trans h₂.symm, hok, hbad⟩⟩

/--
The exact negation: no dichotomy modulo `obs` iff, on admissible inputs, the
verdict of `post` is a function of the observation.
-/
theorem not_dichotomyModuloObservation_iff
    {Obs : Type w} (obs : Input → Output → Obs) :
    ¬ DichotomyModuloObservation obs pre post ↔
      ∀ inp out₁ out₂, pre inp → obs inp out₁ = obs inp out₂ →
        post inp out₁ → post inp out₂ :=
  ⟨fun h inp out₁ out₂ hp heq h₁ =>
      Classical.byContradiction fun h₂ => h ⟨inp, out₁, out₂, hp, heq, h₁, h₂⟩,
    fun h ⟨inp, ok, bad, hp, heq, hok, hbad⟩ => hbad (h inp ok bad hp heq hok)⟩

/--
A postcondition that is, on admissible inputs, any function `f` of the input
and the observation (any Boolean combination of the boilerplate predicates)
has no dichotomy modulo that observation.
-/
theorem not_dichotomyModuloObservation_of_factors
    {Obs : Type w} {obs : Input → Output → Obs} (f : Input → Obs → Prop)
    (h : ∀ inp out, pre inp → (post inp out ↔ f inp (obs inp out))) :
    ¬ DichotomyModuloObservation obs pre post :=
  fun ⟨inp, ok, bad, hp, heq, hok, hbad⟩ =>
    hbad ((h inp bad hp).mpr (heq ▸ (h inp ok hp).mp hok))

/--
Soundness of cofactoring over any number of boilerplate predicates. Let `cof b`
be `post` with the observation fixed to `b` (so `post` and `cof b` agree on
every output observed as `b`). If every cofactor is output-insensitive, `post`
has no dichotomy modulo `obs`: this is the verdict `boilerplateOnly`.
-/
theorem not_dichotomyModuloObservation_of_cofactors_insensitive
    {Obs : Type w} {obs : Input → Output → Obs}
    (cof : Obs → Input → Output → Prop)
    (h_cof : ∀ inp out, pre inp → (post inp out ↔ cof (obs inp out) inp out))
    (h_ins : ∀ b, OutputInsensitive pre (cof b)) :
    ¬ DichotomyModuloObservation obs pre post :=
  fun ⟨inp, ok, bad, hp, heq, hok, hbad⟩ =>
    hbad ((h_cof inp bad hp).mpr
      (heq ▸ h_ins (obs inp ok) inp ok bad hp ((h_cof inp ok hp).mp hok)))

/--
Completeness of cofactoring: a dichotomy modulo `obs` is a dichotomy of the
cofactor at the common observation, witnessed on that fibre. A cofactor that
separates two outputs *of its own fibre* therefore cannot be dismissed; a
checker that samples only some of the `2 ^ k` assignments can miss exactly
this witness.
-/
theorem DichotomyModuloObservation.exists_cofactor_dichotomy
    {Obs : Type w} {obs : Input → Output → Obs}
    (cof : Obs → Input → Output → Prop)
    (h_cof : ∀ inp out, pre inp → (post inp out ↔ cof (obs inp out) inp out))
    (h : DichotomyModuloObservation obs pre post) :
    ∃ b inp out_ok out_bad, pre inp ∧ obs inp out_ok = b ∧ obs inp out_bad = b ∧
      cof b inp out_ok ∧ ¬ cof b inp out_bad :=
  let ⟨inp, ok, bad, hp, heq, hok, hbad⟩ := h
  ⟨obs inp ok, inp, ok, bad, hp, rfl, heq.symm, (h_cof inp ok hp).mp hok,
    fun hc => hbad ((h_cof inp bad hp).mpr (heq ▸ hc))⟩

/--
Coarsening: when `obs'` is determined by `obs`, two outputs that `obs` cannot
tell apart are not told apart by `obs'` either, so a dichotomy modulo the finer
`obs` is a dichotomy modulo the coarser `obs'`. Equivalently, observing *more*
boilerplate can only remove dichotomies.
-/
theorem DichotomyModuloObservation.of_coarser
    {Obs : Type w} {Obs' : Type _} {obs : Input → Output → Obs}
    {obs' : Input → Output → Obs'}
    (h_obs : ∀ inp out₁ out₂, obs inp out₁ = obs inp out₂ →
      obs' inp out₁ = obs' inp out₂)
    (h : DichotomyModuloObservation obs pre post) :
    DichotomyModuloObservation obs' pre post :=
  let ⟨inp, ok, bad, hp, heq, hok, hbad⟩ := h
  ⟨inp, ok, bad, hp, h_obs inp ok bad heq, hok, hbad⟩

/-- A constant observation sees nothing: the notion is plain dichotomy. -/
theorem dichotomyModuloObservation_const_iff {Obs : Type w} (b : Obs) :
    DichotomyModuloObservation (fun (_ : Input) (_ : Output) => b) pre post ↔
      PostconditionDichotomy pre post :=
  ⟨fun h => h.toPostconditionDichotomy,
    fun ⟨inp, ok, bad, hp, hok, hbad⟩ => ⟨inp, ok, bad, hp, rfl, hok, hbad⟩⟩

/--
An observation that determines the output leaves nothing to bind: whatever the
postcondition says, it is a function of what is already observed.
-/
theorem not_dichotomyModuloObservation_of_injective
    {Obs : Type w} {obs : Input → Output → Obs}
    (h_inj : ∀ inp out₁ out₂, obs inp out₁ = obs inp out₂ → out₁ = out₂) :
    ¬ DichotomyModuloObservation obs pre post :=
  fun ⟨inp, ok, bad, _, heq, hok, hbad⟩ => hbad (h_inj inp ok bad heq ▸ hok)

/--
Agreement on each of two predicates implies agreement on their conjunction, so
a dichotomy modulo the pair is a dichotomy beyond the conjunction.
-/
theorem DichotomyModuloObservation.pair_toBeyondConj
    {bp₁ bp₂ : Input → Output → Prop}
    (h : DichotomyModuloObservation
      (fun inp out => (bp₁ inp out, bp₂ inp out)) pre post) :
    DichotomyBeyondPredicate (fun inp out => bp₁ inp out ∧ bp₂ inp out)
      pre post :=
  let ⟨inp, ok, bad, hp, heq, hok, hbad⟩ := h
  have h₁ : bp₁ inp ok = bp₁ inp bad := congrArg Prod.fst heq
  have h₂ : bp₂ inp ok = bp₂ inp bad := congrArg Prod.snd heq
  have hiff : (bp₁ inp ok ∧ bp₂ inp ok) ↔ (bp₁ inp bad ∧ bp₂ inp bad) := by
    rw [h₁, h₂]
  ⟨inp, ok, bad, hp, hiff, hok, hbad⟩

/--
The converse fails: over `Bool × Bool` with `bp₁ o := o.1 = true` and
`bp₂ o := o.2 = true`, the postcondition `bp₁` (pure boilerplate) separates
`(true, false)` from `(false, false)`, on which the conjunction is false both
times; yet it never separates two outputs agreeing on `bp₁` and on `bp₂`. A
checker judging boilerplate by the conjunction alone would report that this
postcondition binds its output beyond boilerplate.
-/
theorem exists_dichotomyBeyond_conj_not_moduloPair :
    ∃ (bp₁ bp₂ post : Unit → Bool × Bool → Prop),
      DichotomyBeyondPredicate (fun inp out => bp₁ inp out ∧ bp₂ inp out)
        (fun _ => True) post ∧
      ¬ DichotomyModuloObservation (fun inp out => (bp₁ inp out, bp₂ inp out))
        (fun _ => True) post :=
  ⟨fun _ o => o.1 = true, fun _ o => o.2 = true, fun _ o => o.1 = true,
    ⟨(), (true, false), (false, false), trivial,
      ⟨fun h => absurd h.2 Bool.false_ne_true,
        fun h => absurd h.1 Bool.false_ne_true⟩,
      rfl, Bool.false_ne_true⟩,
    fun ⟨_, ok, bad, _, heq, hok, hbad⟩ =>
      have h₁ : (ok.1 = true) = (bad.1 = true) := congrArg Prod.fst heq
      hbad (h₁.mp hok)⟩

/-! ### Mutation-testing bridge -/

/--
An output mutant: a transformation of the output an implementation produced on
a given input (off-by-one, constant replacement, identity, ...).
-/
def OutputMutant (Input : Type u) (Output : Type v) : Type (max u v) :=
  Input → Output → Output

/--
The contract kills `mutant` on the valid execution `(inp, out)`: `out` is
accepted on the admissible `inp`, and the mutated output is rejected.
-/
def KillsMutantAt (pre : Input → Prop) (post : Input → Output → Prop)
    (mutant : OutputMutant Input Output) (inp : Input) (out : Output) : Prop :=
  pre inp ∧ post inp out ∧ ¬ post inp (mutant inp out)

/-- The contract kills `mutant` on some valid execution. -/
def MutantKilledBySpec (pre : Input → Prop) (post : Input → Output → Prop)
    (mutant : OutputMutant Input Output) : Prop :=
  ∃ inp out, KillsMutantAt pre post mutant inp out

theorem MutantKilledBySpec.toPostconditionDichotomy
    {mutant : OutputMutant Input Output}
    (h : MutantKilledBySpec pre post mutant) : PostconditionDichotomy pre post :=
  let ⟨inp, out, hp, hok, hbad⟩ := h
  ⟨inp, out, mutant inp out, hp, hok, hbad⟩

/--
Dichotomy is exactly mutation adequacy at its weakest: the contract kills at
least one output mutant on at least one valid execution.
-/
theorem postconditionDichotomy_iff_exists_killed_mutant :
    PostconditionDichotomy pre post ↔
      ∃ mutant : OutputMutant Input Output, MutantKilledBySpec pre post mutant :=
  ⟨fun ⟨inp, ok, bad, hp, hok, hbad⟩ =>
      ⟨fun _ _ => bad, inp, ok, hp, hok, hbad⟩,
    fun ⟨_, h⟩ => h.toPostconditionDichotomy⟩

/--
Relational form: a valid execution `(inp, out_ok)` and a mutant output
`out_bad` on the same input that the postcondition rejects.
-/
theorem postconditionDichotomy_iff_exists_killed_output :
    PostconditionDichotomy pre post ↔
      ∃ inp out_ok, (pre inp ∧ post inp out_ok) ∧
        ∃ out_bad, ¬ post inp out_bad :=
  ⟨fun ⟨inp, ok, bad, hp, hok, hbad⟩ => ⟨inp, ok, ⟨hp, hok⟩, bad, hbad⟩,
    fun ⟨inp, ok, ⟨hp, hok⟩, bad, hbad⟩ => ⟨inp, ok, bad, hp, hok, hbad⟩⟩

/-- A vacuous contract kills no mutant at all. -/
theorem not_mutantKilledBySpec_of_not_dichotomy
    (h : ¬ PostconditionDichotomy pre post)
    (mutant : OutputMutant Input Output) :
    ¬ MutantKilledBySpec pre post mutant :=
  fun hk => h hk.toPostconditionDichotomy

/-- An equivalent mutant (one that reproduces the output) is never killed. -/
theorem not_killsMutantAt_of_equivalent
    {mutant : OutputMutant Input Output} {inp : Input} {out : Output}
    (h : mutant inp out = out) : ¬ KillsMutantAt pre post mutant inp out :=
  fun ⟨_, hok, hbad⟩ => hbad (by rw [h]; exact hok)

theorem not_mutantKilledBySpec_id :
    ¬ MutantKilledBySpec pre post (fun _ out => out) :=
  fun ⟨_, _, hk⟩ => not_killsMutantAt_of_equivalent rfl hk

/--
A contract that pins the observation `proj` kills every mutant that changes
that observation on a valid execution.
-/
theorem killsMutantAt_of_deterministicOn {Val : Type w} {proj : Output → Val}
    (h_det : ContractDeterministicOn proj pre post)
    {mutant : OutputMutant Input Output} {inp : Input} {out : Output}
    (h_pre : pre inp) (h_post : post inp out)
    (h_ne : proj (mutant inp out) ≠ proj out) :
    KillsMutantAt pre post mutant inp out :=
  ⟨h_pre, h_post, fun h => h_ne (h_det inp _ out h_pre h h_post)⟩

theorem killsMutantAt_of_deterministic
    (h_det : ContractDeterministic pre post)
    {mutant : OutputMutant Input Output} {inp : Input} {out : Output}
    (h_pre : pre inp) (h_post : post inp out)
    (h_ne : mutant inp out ≠ out) :
    KillsMutantAt pre post mutant inp out :=
  killsMutantAt_of_deterministicOn (proj := id) h_det h_pre h_post h_ne

/--
Full mutation adequacy is determinism: a contract kills every non-equivalent
mutant on every valid execution exactly when it is deterministic.
-/
theorem contractDeterministic_iff_kills_every_nonequivalent_mutant :
    ContractDeterministic pre post ↔
      ∀ (mutant : OutputMutant Input Output) inp out,
        pre inp → post inp out → mutant inp out ≠ out →
          KillsMutantAt pre post mutant inp out := by
  constructor
  · exact fun h _ _ _ hp hq hne => killsMutantAt_of_deterministic h hp hq hne
  · intro h inp out₁ out₂ hp h₁ h₂
    apply Classical.byContradiction
    intro hne
    exact (h (fun _ _ => out₂) inp out₁ hp h₁ (fun h' => hne h'.symm)).2.2 h₂

/--
Observational mutation adequacy: a contract kills every mutant that alters
`proj out` on a valid execution if and only if it is deterministic on `proj`.
-/
theorem contractDeterministicOn_iff_kills_every_obs_nonequivalent_mutant
    {Val : Type w} (proj : Output → Val) :
    ContractDeterministicOn proj pre post ↔
      ∀ (mutant : OutputMutant Input Output) inp out,
        pre inp → post inp out → proj (mutant inp out) ≠ proj out →
          KillsMutantAt pre post mutant inp out := by
  constructor
  · exact fun h _ _ _ hp hq hne => killsMutantAt_of_deterministicOn h hp hq hne
  · intro h inp out₁ out₂ hp h₁ h₂
    apply Classical.byContradiction
    intro hne
    exact (h (fun _ _ => out₂) inp out₁ hp h₁ (fun h' => hne h'.symm)).2.2 h₂

end Generic

/-! ## Part I.2 — Anneal MIR specialisations -/

section Mir

/-- Ergonomic alias for the response to a `MirCallReq`. -/
abbrev MirCallResp : Type := MirCallAns

/-- A call request on no arguments in the empty memory, used as a witness. -/
def witnessReq : MirCallReq :=
  { defPath := "", args := .nil, memory := emptyMemory }

/-! ### `MirCallContract` -/

/--
The normal-return slice of a call postcondition, as a relation between the
request and the returned `(retVal, memAfter)` pair.
-/
def mirCallNormalPost (c : MirCallContract) :
    MirCallReq → Value × Memory → Prop :=
  fun req out => c.post req (.returned out.1 out.2)

def MirCallContractPreSatisfiable (c : MirCallContract) : Prop :=
  PreconditionSatisfiable c.pre

/-- Some admissible request has an accepted answer of *any* outcome. -/
def MirCallContractRealizable (c : MirCallContract) : Prop :=
  ContractRealizable c.pre c.post

/-- Some admissible request has an accepted *normal return*. -/
def MirCallContractNormalRealizable (c : MirCallContract) : Prop :=
  ∃ req retVal memAfter, c.pre req ∧ c.post req (.returned retVal memAfter)

/-- Some admissible request has an accepted and a rejected answer. -/
def MirCallContractDichotomy (c : MirCallContract) : Prop :=
  PostconditionDichotomy c.pre c.post

/--
Some admissible request has an accepted and a rejected *normal return*. Unlike
`MirCallContractDichotomy`, the rejected answer may not be an unwind or an
abort, so separating outcomes does not count as binding the return.
-/
def MirCallContractNormalDichotomy (c : MirCallContract) : Prop :=
  ∃ req v_ok m_ok v_bad m_bad,
    c.pre req ∧ c.post req (.returned v_ok m_ok) ∧
      ¬ c.post req (.returned v_bad m_bad)

/--
Some admissible request has an accepted and a rejected normal return *into the
same memory*: the contract separates two returned values, not merely two
post-call heaps. This is the level at which frame conditions stop counting.
-/
def MirCallContractReturnValueDichotomy (c : MirCallContract) : Prop :=
  ∃ req v_ok v_bad memAfter,
    c.pre req ∧ c.post req (.returned v_ok memAfter) ∧
      ¬ c.post req (.returned v_bad memAfter)

variable {c : MirCallContract}

theorem mirCallContractNormalRealizable_iff :
    MirCallContractNormalRealizable c ↔
      ContractRealizable c.pre (mirCallNormalPost c) :=
  ⟨fun ⟨req, v, m, hp, hq⟩ => ⟨req, (v, m), hp, hq⟩,
    fun ⟨req, out, hp, hq⟩ => ⟨req, out.1, out.2, hp, hq⟩⟩

theorem mirCallContractNormalDichotomy_iff :
    MirCallContractNormalDichotomy c ↔
      PostconditionDichotomy c.pre (mirCallNormalPost c) :=
  ⟨fun ⟨req, v, m, v', m', hp, hok, hbad⟩ =>
      ⟨req, (v, m), (v', m'), hp, hok, hbad⟩,
    fun ⟨req, ok, bad, hp, hok, hbad⟩ =>
      ⟨req, ok.1, ok.2, bad.1, bad.2, hp, hok, hbad⟩⟩

theorem MirCallContractRealizable.toPreSatisfiable
    (h : MirCallContractRealizable c) : MirCallContractPreSatisfiable c :=
  ContractRealizable.toPreconditionSatisfiable h

theorem MirCallContractDichotomy.toRealizable
    (h : MirCallContractDichotomy c) : MirCallContractRealizable c :=
  PostconditionDichotomy.toContractRealizable h

theorem MirCallContractNormalRealizable.toRealizable
    (h : MirCallContractNormalRealizable c) : MirCallContractRealizable c :=
  let ⟨req, v, m, hp, hq⟩ := h
  ⟨req, .returned v m, hp, hq⟩

theorem MirCallContractNormalDichotomy.toDichotomy
    (h : MirCallContractNormalDichotomy c) : MirCallContractDichotomy c :=
  let ⟨req, v, m, v', m', hp, hok, hbad⟩ := h
  ⟨req, .returned v m, .returned v' m', hp, hok, hbad⟩

theorem MirCallContractNormalDichotomy.toNormalRealizable
    (h : MirCallContractNormalDichotomy c) :
    MirCallContractNormalRealizable c :=
  let ⟨req, v, m, _, _, hp, hok, _⟩ := h
  ⟨req, v, m, hp, hok⟩

theorem MirCallContractReturnValueDichotomy.toNormalDichotomy
    (h : MirCallContractReturnValueDichotomy c) :
    MirCallContractNormalDichotomy c :=
  let ⟨req, v, v', m, hp, hok, hbad⟩ := h
  ⟨req, v, m, v', m, hp, hok, hbad⟩

/-- The returned value of an answer, when the answer is a normal return. -/
def mirCallRetVal? : MirCallAns → Option Value
  | .returned retVal _ => some retVal
  | .panicked _ => none
  | .aborted => none

/-- `Value` has no universal element: every value differs from some other. -/
theorem exists_value_ne (v : Value) : ∃ v' : Value, v' ≠ v := by
  by_cases h_unit : v = Value.unit
  · exact ⟨Value.uninit, fun h => nomatch h.trans h_unit⟩
  · exact ⟨Value.unit, fun h => h_unit h.symm⟩

/--
Determinism of the returned value over all answers gives determinism of the
first component of the normal-return slice.
-/
theorem returnDeterministic_of_deterministicOn_retVal
    (h : ContractDeterministicOn mirCallRetVal? c.pre c.post) :
    ContractDeterministicOn Prod.fst c.pre (mirCallNormalPost c) :=
  fun req _ _ hp h₁ h₂ => Option.some.inj (h req _ _ hp h₁ h₂)

/--
A contract with an accepted return that pins the returned value separates two
returned values in one post-call memory: the value that is not the pinned one
is rejected there.
-/
theorem mirCallContractReturnValueDichotomy_of_return_deterministic
    (h_real : MirCallContractNormalRealizable c)
    (h_det : ContractDeterministicOn Prod.fst c.pre (mirCallNormalPost c)) :
    MirCallContractReturnValueDichotomy c :=
  let ⟨req, v, m, hp, hq⟩ := h_real
  let ⟨v_bad, h_ne⟩ := exists_value_ne v
  ⟨req, v, v_bad, m, hp, hq,
    fun hq' => h_ne (h_det req (v_bad, m) (v, m) hp hq' hq)⟩

/-!
#### Why normal realizability is strictly stronger than realizability

`ContractRealizable c.pre c.post` quantifies over every `MirCallAns`. A contract
that permits `.aborted` on every admissible request (as
`externalSpecCallContract` does: its `.aborted` arm is `True`) is therefore
realizable as soon as its precondition is satisfiable, whatever its `ensures`
clause says, including `ensures(false)`. `MirCallContractNormalRealizable`
demands a `.returned` witness and is not fooled.
-/

/-- An abort-permitting contract is realizable as soon as `pre` is satisfiable. -/
theorem mirCallContractRealizable_of_abort_permitted
    (h_pre : MirCallContractPreSatisfiable c)
    (h_abort : ∀ req, c.pre req → c.post req .aborted) :
    MirCallContractRealizable c :=
  let ⟨req, hp⟩ := h_pre
  ⟨req, .aborted, hp, h_abort req hp⟩

/--
For an abort-permitting contract, raw realizability carries no information
beyond satisfiability of the precondition.
-/
theorem mirCallContractRealizable_iff_preSatisfiable_of_abort_permitted
    (h_abort : ∀ req, c.pre req → c.post req .aborted) :
    MirCallContractRealizable c ↔ MirCallContractPreSatisfiable c :=
  ⟨MirCallContractRealizable.toPreSatisfiable,
    fun h => mirCallContractRealizable_of_abort_permitted h h_abort⟩

theorem not_mirCallContractNormalRealizable_of_no_normal_return
    (h : ∀ req v m, c.pre req → ¬ c.post req (.returned v m)) :
    ¬ MirCallContractNormalRealizable c :=
  fun ⟨req, v, m, hp, hq⟩ => h req v m hp hq

/-- A contract satisfied only by aborting: realizable, never by a return. -/
def abortOnlyContract : MirCallContract where
  pre _ := True
  post _ ans :=
    match ans with
    | .returned _ _ => False
    | .panicked _ => False
    | .aborted => True

theorem abortOnlyContract_realizable :
    MirCallContractRealizable abortOnlyContract :=
  ⟨witnessReq, .aborted, trivial, trivial⟩

theorem abortOnlyContract_not_normalRealizable :
    ¬ MirCallContractNormalRealizable abortOnlyContract :=
  fun ⟨_, _, _, _, hq⟩ => hq

/-- Normal realizability implies realizability, and the converse fails. -/
theorem normalRealizable_strictly_stronger_than_realizable :
    (∀ c, MirCallContractNormalRealizable c → MirCallContractRealizable c) ∧
      ∃ c, MirCallContractRealizable c ∧ ¬ MirCallContractNormalRealizable c :=
  ⟨fun _ h => h.toRealizable,
    abortOnlyContract, abortOnlyContract_realizable,
    abortOnlyContract_not_normalRealizable⟩

/-! #### Vacuity refutations -/

/-- Class 5a: the postcondition cannot tell any two answers apart. -/
theorem not_mirCallContractDichotomy_of_outcome_blind
    (h : ∀ req ans₁ ans₂, c.pre req → (c.post req ans₁ ↔ c.post req ans₂)) :
    ¬ MirCallContractDichotomy c :=
  not_dichotomy_of_input_only h

/--
Class 5b: the postcondition cannot tell any two *normal returns* apart. It may
still reject `.panicked`, which is why `MirCallContractDichotomy` is too weak.
-/
theorem not_mirCallContractNormalDichotomy_of_return_blind
    (h : ∀ req v₁ m₁ v₂ m₂, c.pre req →
      (c.post req (.returned v₁ m₁) ↔ c.post req (.returned v₂ m₂))) :
    ¬ MirCallContractNormalDichotomy c :=
  fun ⟨req, v, m, v', m', hp, hok, hbad⟩ => hbad ((h req v m v' m' hp).mp hok)

/-- The postcondition cannot tell two returned values apart in a fixed memory. -/
theorem not_mirCallContractReturnValueDichotomy_of_value_blind
    (h : ∀ req v₁ v₂ m, c.pre req →
      (c.post req (.returned v₁ m) ↔ c.post req (.returned v₂ m))) :
    ¬ MirCallContractReturnValueDichotomy c :=
  fun ⟨req, v, v', m, hp, hok, hbad⟩ => hbad ((h req v v' m hp).mp hok)

theorem not_mirCallContractNormalDichotomy_of_not_normalRealizable
    (h : ¬ MirCallContractNormalRealizable c) :
    ¬ MirCallContractNormalDichotomy c :=
  fun hd => h hd.toNormalRealizable

/--
A nounwind contract satisfies the *naive* dichotomy as soon as it has one
accepted return: the forbidden `.panicked` answer is the rejected output.
Dichotomy over all of `MirCallAns` therefore says nothing about whether the
return is bound.
-/
theorem mirCallContractDichotomy_of_normalRealizable_of_panic_forbidden
    (h_real : MirCallContractNormalRealizable c)
    (h_nounwind : ∀ req m, c.pre req → ¬ c.post req (.panicked m)) :
    MirCallContractDichotomy c :=
  let ⟨req, v, m, hp, hq⟩ := h_real
  ⟨req, .returned v m, .panicked m, hp, hq, h_nounwind req m hp⟩

/--
The return-blind nounwind contract: every normal return is accepted, unwinding
is forbidden, aborting is permitted.
-/
def returnBlindNounwindContract : MirCallContract where
  pre _ := True
  post _ ans :=
    match ans with
    | .returned _ _ => True
    | .panicked _ => False
    | .aborted => True

theorem returnBlindNounwindContract_dichotomy :
    MirCallContractDichotomy returnBlindNounwindContract :=
  ⟨witnessReq, .aborted, .panicked emptyMemory, trivial, trivial, id⟩

theorem returnBlindNounwindContract_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy returnBlindNounwindContract :=
  not_mirCallContractNormalDichotomy_of_return_blind
    fun _ _ _ _ _ _ => Iff.rfl

/-- Normal dichotomy implies dichotomy, and the converse fails. -/
theorem normalDichotomy_strictly_stronger_than_dichotomy :
    (∀ c, MirCallContractNormalDichotomy c → MirCallContractDichotomy c) ∧
      ∃ c, MirCallContractDichotomy c ∧ ¬ MirCallContractNormalDichotomy c :=
  ⟨fun _ h => h.toDichotomy,
    returnBlindNounwindContract, returnBlindNounwindContract_dichotomy,
    returnBlindNounwindContract_not_normalDichotomy⟩

/--
Return-value dichotomy is dichotomy of the normal-return slice *modulo the
returned memory*: the accepted and the rejected return share `memAfter`. Any
observation that is a function of the memory alone (every frame predicate) is
coarser, so a return-value dichotomy survives it
(`DichotomyModuloObservation.of_coarser`).
-/
theorem mirCallContractReturnValueDichotomy_iff_moduloMemory :
    MirCallContractReturnValueDichotomy c ↔
      DichotomyModuloObservation
        (fun (_ : MirCallReq) (out : Value × Memory) => out.2)
        c.pre (mirCallNormalPost c) := by
  constructor
  · rintro ⟨req, ok, bad, m, hp, hok, hbad⟩
    exact ⟨req, (ok, m), (bad, m), hp, rfl, hok, hbad⟩
  · rintro ⟨req, ⟨ok, m₁⟩, ⟨bad, m₂⟩, hp, heq, hok, hbad⟩
    have heq : m₁ = m₂ := heq
    subst heq
    exact ⟨req, ok, bad, m₁, hp, hok, hbad⟩

/--
A frame-only call contract: normal returns must preserve the call frame, but
every returned `Value` is blindly accepted.
-/
def frameOnlyMirCallContract : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned _ memAfter => callFramePreserved req.memory memAfter
    | .panicked _ => False
    | .aborted => True

/--
Return-value dichotomy is strictly stronger than normal dichotomy: the
frame-only contract separates post-call memories yet never separates two
returned values in the same memory.
-/
theorem returnValueDichotomy_strictly_stronger_than_normalDichotomy :
    (∀ c, MirCallContractReturnValueDichotomy c →
      MirCallContractNormalDichotomy c) ∧
      ∃ c, MirCallContractNormalDichotomy c ∧
        ¬ MirCallContractReturnValueDichotomy c :=
  ⟨fun _ h => h.toNormalDichotomy,
    frameOnlyMirCallContract,
    ⟨witnessReq, .unit, emptyMemory, .unit,
      { emptyMemory with activeProtectors := [0] }, trivial,
      ⟨rfl, rfl, rfl, rfl, .nil, rfl⟩,
      fun h => List.cons_ne_self 0 _ h.2.2.2.1⟩,
    not_mirCallContractReturnValueDichotomy_of_value_blind
      fun _ _ _ _ _ => Iff.rfl⟩

/--
*Verified but vacuous* for `MirCallContract.holdsOn`: an unsatisfiable call
precondition is satisfied by *every* `ExternalCallHandler`, including one that
immediately triggers undefined behavior (`ITree.fail .ub`).
-/
theorem mirCallContract_holdsOn_of_not_preSatisfiable
    (h : ¬ MirCallContractPreSatisfiable c) (handler : ExternalCallHandler) :
    c.holdsOn handler :=
  fun req h_pre => absurd ⟨req, h_pre⟩ h

/--
When `.aborted` is unconditionally allowed on admissible requests (as in
`externalSpecCallContract`), the trivial always-aborting handler satisfies
`c.holdsOn` regardless of `c`'s normal-return postcondition.
-/
theorem mirCallContract_holdsOn_abort_of_abort_permitted
    (h_abort : ∀ req, c.pre req → c.post req .aborted) :
    c.holdsOn (fun _ => .ret .aborted) := by
  intro req h_pre
  have h_reaches :
      ∀ tr u,
        Trusted.ITree.Reaches
          (Trusted.ITree.ITree.ret (E := MirClosedEffect) MirCallAns.aborted)
          tr u →
        u = Trusted.ITree.ITree.ret (E := MirClosedEffect) MirCallAns.aborted := by
    intro tr u hr
    cases hr with
    | refl => rfl
    | tau hobs _ => simp [Trusted.ITree.ITree.observe_ret] at hobs
    | vis hobs _ _ _ => simp [Trusted.ITree.ITree.observe_ret] at hobs
  refine ⟨?_, ?_⟩
  · intro tr u hr hf
    rw [h_reaches tr u hr] at hf
    rcases hf with ⟨t', i, k, htau, hobs, _⟩
    cases htau with
    | refl => simp [Trusted.ITree.ITree.observe_ret] at hobs
    | step hstep _ => simp [Trusted.ITree.ITree.observe_ret] at hstep
  · intro tr ans ⟨u, hr, hobs⟩
    rw [h_reaches tr u hr, Trusted.ITree.ITree.observe_ret] at hobs
    cases hobs
    exact h_abort req h_pre

/--
A handler that satisfies the contract and returns normally on an admissible
request witnesses normal realizability.
-/
theorem mirCallContractNormalRealizable_of_holdsOn_of_returns
    {handler : ExternalCallHandler} (h_holds : c.holdsOn handler)
    {req : MirCallReq} (h_pre : c.pre req)
    {tr : List (Trusted.Effect.Event MirClosedEffect)} {retVal : Value}
    {memAfter : Memory}
    (h_ret : Trusted.ITree.ReachesRet (handler req) tr
      (MirCallAns.returned retVal memAfter)) :
    MirCallContractNormalRealizable c :=
  ⟨req, retVal, memAfter, h_pre, (h_holds req h_pre).2 tr _ h_ret⟩

/--
Why normal realizability matters to a *caller*: under a contract no normal
return realises, no handler that satisfies it ever returns on an admissible
request. Every proof obligation after the call is then discharged vacuously.
-/
theorem not_reachesRet_returned_of_holdsOn_of_not_normalRealizable
    (h : ¬ MirCallContractNormalRealizable c)
    {handler : ExternalCallHandler} (h_holds : c.holdsOn handler)
    {req : MirCallReq} (h_pre : c.pre req)
    (tr : List (Trusted.Effect.Event MirClosedEffect)) (retVal : Value)
    (memAfter : Memory) :
    ¬ Trusted.ITree.ReachesRet (handler req) tr
      (MirCallAns.returned retVal memAfter) :=
  fun h_ret =>
    h (mirCallContractNormalRealizable_of_holdsOn_of_returns h_holds h_pre h_ret)

/-! #### `externalSpecCallContract`: boilerplate versus the user `ensures` -/

section ExternalSpec

variable (targetDefPath : DefPath) (sidecarBody : CapturedMir)
  (extraPre : List Value → Prop) (extraPost : List Value → Value → Prop)

theorem externalSpecCallContract_post_returned_iff
    (req : MirCallReq) (retVal : Value) (memAfter : Memory) :
    (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).post
        req (.returned retVal memAfter) ↔
      callFramePreserved req.memory memAfter ∧
        retMatchesCalleeReturnTy sidecarBody retVal ∧
          extraPost req.args retVal :=
  Iff.rfl

/-- The `requires` clause is a conjunct of the generated precondition. -/
theorem externalSpecCallContract_extraPre_of_pre {req : MirCallReq}
    (h : (externalSpecCallContract targetDefPath sidecarBody extraPre
      extraPost).pre req) : extraPre req.args :=
  h.2.2.2

/--
Raw realizability of an external spec is satisfiability of its precondition:
the `.aborted` arm is `True`, so the `ensures` clause is never consulted.
-/
theorem externalSpecCallContract_realizable_iff_preSatisfiable :
    MirCallContractRealizable
        (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost) ↔
      MirCallContractPreSatisfiable
        (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost) :=
  mirCallContractRealizable_iff_preSatisfiable_of_abort_permitted
    fun _ _ => trivial

/-- An unsatisfiable `ensures` is caught by normal realizability. -/
theorem not_externalSpecCallContract_normalRealizable_of_unsat_ensures
    (h : ∀ args v, extraPre args → ¬ extraPost args v) :
    ¬ MirCallContractNormalRealizable
        (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost) :=
  fun ⟨req, v, _, hp, hq⟩ => h req.args v hp.2.2.2 hq.2.2

theorem callFramePreserved_refl (mem : Memory) : callFramePreserved mem mem :=
  ⟨rfl, rfl, rfl, rfl, .nil, rfl⟩

/--
The frame conjunct alone separates normal returns: any accepted return is
rejected once the returned memory carries a different protector stack. So
`MirCallContractNormalDichotomy` holds of *every* normal-realizable external
spec, including one whose `ensures` clause is `True`; binding of the returned
value has to be asked for separately (`ExternalSpecEnsuresDichotomy`).
-/
theorem externalSpecCallContract_normalDichotomy_of_normalRealizable
    (h : MirCallContractNormalRealizable
      (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost)) :
    MirCallContractNormalDichotomy
      (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost) :=
  let ⟨req, v, m, hp, hq⟩ := h
  ⟨req, v, m, v,
    { m with activeProtectors := 0 :: req.memory.activeProtectors }, hp, hq,
    fun hbad => List.cons_ne_self 0 _ hbad.1.2.2.2.1⟩

/--
The user `ensures` clause of an external spec separates two *well-typed*
returned values on an admissible request. Frame and return-type boilerplate
cannot witness this: both candidates satisfy `retMatchesCalleeReturnTy`, and
no memory is mentioned.
-/
def ExternalSpecEnsuresDichotomy : Prop :=
  ∃ req v_ok v_bad,
    (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).pre
        req ∧
      retMatchesCalleeReturnTy sidecarBody v_ok ∧ extraPost req.args v_ok ∧
      retMatchesCalleeReturnTy sidecarBody v_bad ∧ ¬ extraPost req.args v_bad

theorem ExternalSpecEnsuresDichotomy.toReturnValueDichotomy
    {targetDefPath : DefPath} {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop} {extraPost : List Value → Value → Prop}
    (h : ExternalSpecEnsuresDichotomy targetDefPath sidecarBody extraPre
      extraPost) :
    MirCallContractReturnValueDichotomy
      (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost) :=
  let ⟨req, ok, bad, hp, hty, hok, _, hbad⟩ := h
  ⟨req, ok, bad, req.memory, hp, ⟨callFramePreserved_refl _, hty, hok⟩,
    fun hq => hbad hq.2.2⟩

/-- A return-blind `ensures` clause never separates well-typed returns. -/
theorem not_externalSpecEnsuresDichotomy_of_return_blind
    (h : ∀ args v₁ v₂, extraPre args →
      (extraPost args v₁ ↔ extraPost args v₂)) :
    ¬ ExternalSpecEnsuresDichotomy targetDefPath sidecarBody extraPre
      extraPost :=
  fun ⟨req, ok, bad, hp, _, hok, _, hbad⟩ =>
    hbad ((h req.args ok bad hp.2.2.2).mp hok)

/-- The default `ensures` clause (`fun _ _ => True`) binds nothing. -/
theorem not_externalSpecEnsuresDichotomy_default :
    ¬ ExternalSpecEnsuresDichotomy targetDefPath sidecarBody extraPre
      (fun _ _ => True) :=
  not_externalSpecEnsuresDichotomy_of_return_blind targetDefPath sidecarBody
    extraPre _ fun _ _ _ _ => Iff.rfl

/--
`ExternalSpecEnsuresDichotomy` is equivalent to `DichotomyBeyondPredicate` on
the normal-return slice relative to the combined frame-and-return-type
boilerplate predicate.
-/
theorem externalSpecEnsuresDichotomy_iff_dichotomyBeyond_boilerplate :
    ExternalSpecEnsuresDichotomy targetDefPath sidecarBody extraPre extraPost ↔
      DichotomyBeyondPredicate
        (fun req (out : Value × Memory) =>
          callFramePreserved req.memory out.2 ∧
            retMatchesCalleeReturnTy sidecarBody out.1)
        (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).pre
        (mirCallNormalPost
          (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost)) := by
  constructor
  · rintro ⟨req, ok, bad, hp, htyOk, hok, htyBad, hbad⟩
    refine ⟨req, (ok, req.memory), (bad, req.memory), hp, ?_,
      ⟨callFramePreserved_refl _, htyOk, hok⟩, fun h => hbad h.2.2⟩
    exact ⟨fun _ => ⟨callFramePreserved_refl _, htyBad⟩,
      fun _ => ⟨callFramePreserved_refl _, htyOk⟩⟩
  · rintro ⟨req, ⟨ok, mok⟩, ⟨bad, mbad⟩, hp, hiff, ⟨hfOk, htyOk, hok⟩, hbad⟩
    have ⟨_, htyBad⟩ := hiff.mp ⟨hfOk, htyOk⟩
    exact ⟨req, ok, bad, hp, htyOk, hok, htyBad,
      fun hpost => hbad ⟨(hiff.mp ⟨hfOk, htyOk⟩).1, htyBad, hpost⟩⟩

/--
What the frame and return-type boilerplate of an external spec observes of a
normal return: the truth values of `callFramePreserved req.memory memAfter` and
of `retMatchesCalleeReturnTy sidecarBody retVal`, *separately*.
-/
def externalSpecBoilerplateObs (req : MirCallReq) (out : Value × Memory) :
    Prop × Prop :=
  (callFramePreserved req.memory out.2,
    retMatchesCalleeReturnTy sidecarBody out.1)

/--
`ExternalSpecEnsuresDichotomy` is dichotomy of the normal-return slice modulo
the pair observation. For the external spec itself this coincides with the
conjunction form above (an accepted return satisfies both predicates); for an
arbitrary postcondition only the pair form is the right notion
(`frameOnlyMirCallContract_dichotomyBeyond_conj_of_illTyped`).
-/
theorem externalSpecEnsuresDichotomy_iff_moduloObservation :
    ExternalSpecEnsuresDichotomy targetDefPath sidecarBody extraPre extraPost ↔
      DichotomyModuloObservation (externalSpecBoilerplateObs sidecarBody)
        (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).pre
        (mirCallNormalPost
          (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost)) := by
  constructor
  · rintro ⟨req, ok, bad, hp, htyOk, hok, htyBad, hbad⟩
    refine ⟨req, (ok, req.memory), (bad, req.memory), hp, ?_,
      ⟨callFramePreserved_refl _, htyOk, hok⟩, fun h => hbad h.2.2⟩
    exact congrArg (Prod.mk _) (propext ⟨fun _ => htyBad, fun _ => htyOk⟩)
  · rintro ⟨req, ⟨ok, mok⟩, ⟨bad, mbad⟩, hp, heq, ⟨hfOk, htyOk, hok⟩, hbad⟩
    have hf : callFramePreserved req.memory mok =
        callFramePreserved req.memory mbad := congrArg Prod.fst heq
    have hty : retMatchesCalleeReturnTy sidecarBody ok =
        retMatchesCalleeReturnTy sidecarBody bad := congrArg Prod.snd heq
    exact ⟨req, ok, bad, hp, htyOk, hok, hty ▸ htyOk,
      fun hpost => hbad ⟨hf ▸ hfOk, hty ▸ htyOk, hpost⟩⟩

/--
The frame-only contract binds nothing beyond boilerplate, whatever the sidecar
body: its normal-return verdict is the first component of the observation.
-/
theorem frameOnlyMirCallContract_not_dichotomyModuloBoilerplate :
    ¬ DichotomyModuloObservation (externalSpecBoilerplateObs sidecarBody)
      frameOnlyMirCallContract.pre
      (mirCallNormalPost frameOnlyMirCallContract) :=
  not_dichotomyModuloObservation_of_factors (fun _ b => b.1)
    fun _ _ _ => Iff.rfl

/--
Relative to the *conjunction* of frame and return type, the same frame-only
contract would count as binding as soon as one value is ill-typed: with that
value returned, the conjunction is false whether or not the frame is preserved,
while the contract accepts one memory and rejects the other. This is why the
checker cofactors over the boilerplate atoms individually.
-/
theorem frameOnlyMirCallContract_dichotomyBeyond_conj_of_illTyped
    (h : ∃ v, ¬ retMatchesCalleeReturnTy sidecarBody v) :
    DichotomyBeyondPredicate
      (fun req (out : Value × Memory) =>
        callFramePreserved req.memory out.2 ∧
          retMatchesCalleeReturnTy sidecarBody out.1)
      frameOnlyMirCallContract.pre
      (mirCallNormalPost frameOnlyMirCallContract) :=
  let ⟨v, hv⟩ := h
  ⟨witnessReq, (v, emptyMemory),
    (v, { emptyMemory with activeProtectors := [0] }), trivial,
    ⟨fun hc => absurd hc.2 hv, fun hc => absurd hc.2 hv⟩,
    callFramePreserved_refl _,
    fun hbad => List.cons_ne_self 0 _ hbad.2.2.2.1⟩

end ExternalSpec

/-! #### Subsumption (`MirCallContract.Subsumes`) -/

/--
`cSub` is subsumed by `cSuper`, stated over the generic `ContractSubsumes`. It
unfolds to the body of `MirCallContract.Subsumes` (`mirCallContractSubsumes_iff`),
which is restated here so this module needs only the trusted foundation.
-/
def MirCallContractSubsumes (cSub cSuper : MirCallContract) : Prop :=
  ContractSubsumes cSub.pre cSub.post cSuper.pre cSuper.post

theorem mirCallContractSubsumes_iff (cSub cSuper : MirCallContract) :
    MirCallContractSubsumes cSub cSuper ↔
      ∀ req : MirCallReq, cSub.pre req →
        cSuper.pre req ∧
          ∀ ans : MirCallAns, cSuper.post req ans → cSub.post req ans :=
  Iff.rfl

theorem MirCallContractSubsumes.refl (c : MirCallContract) :
    MirCallContractSubsumes c c :=
  fun _ hp => ⟨hp, fun _ hq => hq⟩

theorem MirCallContractSubsumes.trans {c₁ c₂ c₃ : MirCallContract}
    (h₁₂ : MirCallContractSubsumes c₁ c₂)
    (h₂₃ : MirCallContractSubsumes c₂ c₃) : MirCallContractSubsumes c₁ c₃ :=
  fun req hp₁ =>
    let ⟨hp₂, hq₁₂⟩ := h₁₂ req hp₁
    let ⟨hp₃, hq₂₃⟩ := h₂₃ req hp₂
    ⟨hp₃, fun ans hq₃ => hq₁₂ ans (hq₂₃ ans hq₃)⟩

section MirSubsumption

variable {cSub cSuper : MirCallContract}

/--
Realizability transfers *downwards and upwards at once* from a single witness:
a normal return the super contract accepts on a sub-admissible request is a
normal-return witness for both contracts.
-/
theorem MirCallContractSubsumes.normalRealizable_of_super_on_sub
    (h : MirCallContractSubsumes cSub cSuper)
    (h_wit : ∃ req v m, cSub.pre req ∧ cSuper.post req (.returned v m)) :
    MirCallContractNormalRealizable cSub ∧
      MirCallContractNormalRealizable cSuper :=
  let ⟨req, v, m, hp, hq⟩ := h_wit
  ⟨⟨req, v, m, hp, (h req hp).2 _ hq⟩, ⟨req, v, m, (h req hp).1, hq⟩⟩

/--
The direction of transfer under `MirCallContract.Subsumes`. *Acceptance* flows
from `cSuper` to `cSub` and *rejection* flows from `cSub` to `cSuper`, both on
`cSub.pre`. So when `cSuper` has a normal-return witness on a `cSub`-admissible
request and `cSub` rejects some return on that request, both contracts have a
normal dichotomy there.
-/
theorem MirCallContractSubsumes.normalDichotomy_of_super_ok_sub_bad
    (h : MirCallContractSubsumes cSub cSuper)
    (h_wit : ∃ req v_ok m_ok v_bad m_bad,
      cSub.pre req ∧ cSuper.post req (.returned v_ok m_ok) ∧
        ¬ cSub.post req (.returned v_bad m_bad)) :
    MirCallContractNormalDichotomy cSub ∧
      MirCallContractNormalDichotomy cSuper :=
  let ⟨req, v, m, v', m', hp, hok, hbad⟩ := h_wit
  ⟨⟨req, v, m, v', m', hp, (h req hp).2 _ hok, hbad⟩,
    ⟨req, v, m, v', m', (h req hp).1, hok,
      fun hq => hbad ((h req hp).2 _ hq)⟩⟩

/-- The all-answers form of the same transfer. -/
theorem MirCallContractSubsumes.dichotomy_of_super_ok_sub_bad
    (h : MirCallContractSubsumes cSub cSuper)
    (h_wit : ∃ req ans_ok ans_bad,
      cSub.pre req ∧ cSuper.post req ans_ok ∧ ¬ cSub.post req ans_bad) :
    MirCallContractDichotomy cSub ∧ MirCallContractDichotomy cSuper :=
  ContractSubsumes.dichotomy_of_super_ok_sub_bad h h_wit

/-- Return-value dichotomy transfer in a single post-call memory. -/
theorem MirCallContractSubsumes.returnValueDichotomy_of_super_ok_sub_bad
    (h : MirCallContractSubsumes cSub cSuper)
    (h_wit : ∃ req v_ok v_bad memAfter,
      cSub.pre req ∧ cSuper.post req (.returned v_ok memAfter) ∧
        ¬ cSub.post req (.returned v_bad memAfter)) :
    MirCallContractReturnValueDichotomy cSub ∧
      MirCallContractReturnValueDichotomy cSuper :=
  let ⟨req, v, v', m, hp, hok, hbad⟩ := h_wit
  ⟨⟨req, v, v', m, hp, (h req hp).2 _ hok, hbad⟩,
    ⟨req, v, v', m, (h req hp).1, hok,
      fun hq => hbad ((h req hp).2 _ hq)⟩⟩

end MirSubsumption

/--
The transfer is not symmetric (1): a normal dichotomy of `cSuper` does not
descend to `cSub`, because `cSub` may accept everything.
-/
theorem exists_mirSubsumes_normalDichotomy_super_not_sub :
    ∃ cSub cSuper, MirCallContractSubsumes cSub cSuper ∧
      MirCallContractNormalDichotomy cSuper ∧
      ¬ MirCallContractNormalDichotomy cSub :=
  ⟨{}, { post := fun _ ans =>
            match ans with
            | .returned v _ => v = Value.unit
            | .panicked _ => True
            | .aborted => True },
    fun _ _ => ⟨trivial, fun _ _ => trivial⟩,
    ⟨witnessReq, .unit, emptyMemory, .uninit, emptyMemory, trivial, rfl,
      nofun⟩,
    fun ⟨_, _, _, _, _, _, _, hbad⟩ => hbad trivial⟩

/--
The transfer is not symmetric (2): normal realizability of `cSub` does not
ascend to `cSuper`, because `cSuper` may accept nothing.
-/
theorem exists_mirSubsumes_normalRealizable_sub_not_super :
    ∃ cSub cSuper, MirCallContractSubsumes cSub cSuper ∧
      MirCallContractNormalRealizable cSub ∧
      ¬ MirCallContractNormalRealizable cSuper :=
  ⟨{}, { post := fun _ _ => False },
    fun _ _ => ⟨trivial, fun _ h => h.elim⟩,
    ⟨witnessReq, .unit, emptyMemory, trivial, trivial⟩,
    fun ⟨_, _, _, _, hq⟩ => hq⟩

/-! ### `Claim` -/

def ClaimPreSatisfiable (c : Claim) : Prop :=
  PreconditionSatisfiable c.pre

def ClaimRealizable (c : Claim) : Prop :=
  ContractRealizable c.pre c.post

def ClaimDichotomy (c : Claim) : Prop :=
  PostconditionDichotomy c.pre c.post

def ClaimDeterministic (c : Claim) : Prop :=
  ContractDeterministic c.pre c.post

section ClaimTheorems

variable {c : Claim}

theorem ClaimRealizable.toPreSatisfiable
    (h : ClaimRealizable c) : ClaimPreSatisfiable c :=
  ContractRealizable.toPreconditionSatisfiable h

theorem ClaimDichotomy.toRealizable
    (h : ClaimDichotomy c) : ClaimRealizable c :=
  PostconditionDichotomy.toContractRealizable h

theorem not_claimDichotomy_of_return_blind
    (h : ∀ args r₁ r₂, c.pre args → (c.post args r₁ ↔ c.post args r₂)) :
    ¬ ClaimDichotomy c :=
  not_dichotomy_of_input_only h

/-- `Value` has two distinct inhabitants, so determinism forces dichotomy. -/
theorem claimDichotomy_of_realizable_and_deterministic
    (h_real : ClaimRealizable c) (h_det : ClaimDeterministic c) :
    ClaimDichotomy c :=
  postconditionDichotomy_of_realizable_and_deterministic h_real h_det
    ⟨Value.unit, Value.uninit, nofun⟩

/--
*Verified but vacuous*, in the trusted gate itself: a `Claim` whose
precondition is unsatisfiable holds of **every** body, because the Smyth
refinement is only checked where the specification is defined.
-/
theorem claim_holds_of_not_preSatisfiable
    (h : ¬ ClaimPreSatisfiable c) : c.holds :=
  fun args h_def => absurd ⟨args, h_def⟩ h

/-- `ClaimPreSatisfiable` coincides with `Trusted.VerificationResult.NonVacuousPre`. -/
theorem claimPreSatisfiable_iff_nonVacuousPre :
    ClaimPreSatisfiable c ↔ NonVacuousPre c.pre :=
  Iff.rfl

theorem verificationResult_of_not_preSatisfiable
    (h : ¬ ClaimPreSatisfiable c) : VerificationResult c :=
  ⟨claim_holds_of_not_preSatisfiable h⟩

end ClaimTheorems

/-! ### `StatefulClaim` -/

/-- The precondition of a `StatefulClaim` over the paired input `(args, mem)`. -/
def statefulClaimPre (c : StatefulClaim) : List Value × Memory → Prop :=
  fun inp => c.pre inp.1 inp.2

/--
The postcondition of a `StatefulClaim` as a relation between the paired input
`(args, mem)` and the paired output `(retVal, mem')`.
-/
def statefulClaimPost (c : StatefulClaim) :
    List Value × Memory → Value × Memory → Prop :=
  fun inp out => c.post inp.1 inp.2 out.1 out.2

def StatefulClaimPreSatisfiable (c : StatefulClaim) : Prop :=
  ∃ args mem, c.pre args mem

def StatefulClaimRealizable (c : StatefulClaim) : Prop :=
  ∃ args mem retVal mem', c.pre args mem ∧ c.post args mem retVal mem'

/-- Some admissible state has an accepted and a rejected `(retVal, mem')`. -/
def StatefulClaimDichotomy (c : StatefulClaim) : Prop :=
  ∃ args mem ret_ok mem_ok ret_bad mem_bad,
    c.pre args mem ∧ c.post args mem ret_ok mem_ok ∧
      ¬ c.post args mem ret_bad mem_bad

/--
Some admissible state has an accepted and a rejected *returned value* for the
same post-memory. A frame-only postcondition has `StatefulClaimDichotomy` but
not this.
-/
def StatefulClaimReturnDichotomy (c : StatefulClaim) : Prop :=
  ∃ args mem ret_ok ret_bad mem',
    c.pre args mem ∧ c.post args mem ret_ok mem' ∧
      ¬ c.post args mem ret_bad mem'

section StatefulClaimTheorems

variable {c : StatefulClaim}

theorem statefulClaimPreSatisfiable_iff :
    StatefulClaimPreSatisfiable c ↔
      PreconditionSatisfiable (statefulClaimPre c) :=
  ⟨fun ⟨args, mem, hp⟩ => ⟨(args, mem), hp⟩,
    fun ⟨inp, hp⟩ => ⟨inp.1, inp.2, hp⟩⟩

theorem statefulClaimRealizable_iff :
    StatefulClaimRealizable c ↔
      ContractRealizable (statefulClaimPre c) (statefulClaimPost c) :=
  ⟨fun ⟨args, mem, r, m', hp, hq⟩ => ⟨(args, mem), (r, m'), hp, hq⟩,
    fun ⟨inp, out, hp, hq⟩ => ⟨inp.1, inp.2, out.1, out.2, hp, hq⟩⟩

theorem statefulClaimDichotomy_iff :
    StatefulClaimDichotomy c ↔
      PostconditionDichotomy (statefulClaimPre c) (statefulClaimPost c) :=
  ⟨fun ⟨args, mem, r, m, r', m', hp, hok, hbad⟩ =>
      ⟨(args, mem), (r, m), (r', m'), hp, hok, hbad⟩,
    fun ⟨inp, ok, bad, hp, hok, hbad⟩ =>
      ⟨inp.1, inp.2, ok.1, ok.2, bad.1, bad.2, hp, hok, hbad⟩⟩

theorem StatefulClaimRealizable.toPreSatisfiable
    (h : StatefulClaimRealizable c) : StatefulClaimPreSatisfiable c :=
  let ⟨args, mem, _, _, hp, _⟩ := h
  ⟨args, mem, hp⟩

theorem StatefulClaimDichotomy.toRealizable
    (h : StatefulClaimDichotomy c) : StatefulClaimRealizable c :=
  let ⟨args, mem, r, m, _, _, hp, hok, _⟩ := h
  ⟨args, mem, r, m, hp, hok⟩

theorem StatefulClaimReturnDichotomy.toDichotomy
    (h : StatefulClaimReturnDichotomy c) : StatefulClaimDichotomy c :=
  let ⟨args, mem, r, r', m', hp, hok, hbad⟩ := h
  ⟨args, mem, r, m', r', m', hp, hok, hbad⟩

theorem not_statefulClaimDichotomy_of_output_blind
    (h : ∀ args mem r₁ m₁ r₂ m₂, c.pre args mem →
      (c.post args mem r₁ m₁ ↔ c.post args mem r₂ m₂)) :
    ¬ StatefulClaimDichotomy c :=
  fun ⟨args, mem, r, m, r', m', hp, hok, hbad⟩ =>
    hbad ((h args mem r m r' m' hp).mp hok)

/--
The postcondition ignores the returned value (it may still constrain the
post-memory): the claim has no return dichotomy.
-/
theorem not_statefulClaimReturnDichotomy_of_return_blind
    (h : ∀ args mem r₁ r₂ mem', c.pre args mem →
      (c.post args mem r₁ mem' ↔ c.post args mem r₂ mem')) :
    ¬ StatefulClaimReturnDichotomy c :=
  fun ⟨args, mem, r, r', m', hp, hok, hbad⟩ =>
    hbad ((h args mem r r' m' hp).mp hok)

/--
A realizable stateful claim that pins the returned value has a return
dichotomy: `Value` has two distinct inhabitants, and the one that is not the
pinned return is rejected in the same post-memory.
-/
theorem statefulClaimReturnDichotomy_of_realizable_and_return_deterministic
    (h_real : StatefulClaimRealizable c)
    (h_det : ContractDeterministicOn Prod.fst
      (statefulClaimPre c) (statefulClaimPost c)) :
    StatefulClaimReturnDichotomy c :=
  let ⟨args, mem, r, m', hp, hq⟩ := h_real
  let ⟨r_bad, h_ne⟩ := exists_value_ne r
  ⟨args, mem, r, r_bad, m', hp, hq,
    fun hq' => h_ne (h_det (args, mem) (r_bad, m') (r, m') hp hq' hq)⟩

/--
*Verified but vacuous* for the stateful gate: an unsatisfiable precondition
makes the claim hold of every body.
-/
theorem statefulClaim_holds_of_not_preSatisfiable
    (h : ¬ StatefulClaimPreSatisfiable c) : c.holds :=
  fun args mem h_def => absurd ⟨args, mem, h_def⟩ h

/--
`StatefulClaimPreSatisfiable` coincides with
`Trusted.VerificationResult.NonVacuousStatefulPre`.
-/
theorem statefulClaimPreSatisfiable_iff_nonVacuousStatefulPre :
    StatefulClaimPreSatisfiable c ↔ NonVacuousStatefulPre c.pre :=
  Iff.rfl

theorem statefulVerificationResult_of_not_preSatisfiable
    (h : ¬ StatefulClaimPreSatisfiable c) : StatefulVerificationResult c :=
  ⟨statefulClaim_holds_of_not_preSatisfiable h⟩

end StatefulClaimTheorems

/-- A stateful claim whose postcondition is the frame condition `mem' = mem`. -/
def frameOnlyStatefulClaim (body : CapturedMir) : StatefulClaim where
  body := body
  pre _ _ := True
  post _ mem _ mem' := mem' = mem

/-- The frame-only claim separates post-memories ... -/
theorem frameOnlyStatefulClaim_dichotomy (body : CapturedMir) :
    StatefulClaimDichotomy (frameOnlyStatefulClaim body) :=
  ⟨.nil, emptyMemory, .unit, emptyMemory, .unit,
    { emptyMemory with nextTag := 2 }, trivial, rfl,
    fun h => absurd (congrArg Memory.nextTag h) (by decide)⟩

/-- ... but never two returned values: `retVal` is unconstrained. -/
theorem frameOnlyStatefulClaim_not_returnDichotomy (body : CapturedMir) :
    ¬ StatefulClaimReturnDichotomy (frameOnlyStatefulClaim body) :=
  not_statefulClaimReturnDichotomy_of_return_blind fun _ _ _ _ _ _ => Iff.rfl

/--
`StatefulClaimReturnDichotomy` is strictly stronger than
`StatefulClaimDichotomy`: the frame-only claim witnesses the gap for any body.
-/
theorem statefulClaimReturnDichotomy_strictly_stronger_than_dichotomy
    (body : CapturedMir) :
    (∀ c, StatefulClaimReturnDichotomy c → StatefulClaimDichotomy c) ∧
      ∃ c : StatefulClaim, c.body = body ∧
        StatefulClaimDichotomy c ∧ ¬ StatefulClaimReturnDichotomy c :=
  ⟨fun _ h => h.toDichotomy,
    frameOnlyStatefulClaim body, rfl,
    frameOnlyStatefulClaim_dichotomy body,
    frameOnlyStatefulClaim_not_returnDichotomy body⟩

/--
*Verified but vacuous* for the total-correctness gate: an unsatisfiable
precondition certifies `TotalVerificationResult` for every body.
-/
theorem totalClaim_holds_of_not_preSatisfiable {c : TotalClaim}
    (h : ¬ NonVacuousStatefulPre c.pre) : c.holds :=
  fun args mem hp => absurd ⟨args, mem, hp⟩ h

theorem totalVerificationResult_of_not_preSatisfiable {c : TotalClaim}
    (h : ¬ NonVacuousStatefulPre c.pre) : TotalVerificationResult c :=
  ⟨totalClaim_holds_of_not_preSatisfiable h⟩

/--
*Verified but vacuous* for the modular gate: an unsatisfiable precondition
certifies `ModularVerificationResult` for every body and rely predicate.
-/
theorem modularClaim_holds_of_not_preSatisfiable {c : ModularClaim}
    (h : ¬ NonVacuousStatefulPre c.pre) : c.holds :=
  fun _ _ args mem hp => absurd ⟨args, mem, hp⟩ h

theorem modularVerificationResult_of_not_preSatisfiable {c : ModularClaim}
    (h : ¬ NonVacuousStatefulPre c.pre) : ModularVerificationResult c :=
  ⟨modularClaim_holds_of_not_preSatisfiable h⟩

end Mir

/-! ## Part II — `MetaM` `ensures`-binding and vacuity checker

`checkEnsuresBindsOutput` decides, syntactically, whether a postcondition
constrains its designated output binders.

**Method.** The postcondition is applied to fresh variables and rewritten to a
*residual* by steps that each preserve its truth value:

* definitional reductions (`mdata`, beta, zeta, eta, iota on constructors,
  structure projections including projection functions applied to unfolded
  structure instances, and pushing non-dependent projections into `ite`/`cond`/
  `dite`/non-dependent `match` branches) and head unfolding, under a fuel bound,
  of definitions in proposition position and of Boolean-valued definitions
  compared with a literal. Smart unfolding leaves a recursive definition alone
  unless its recursion can progress, instances and irreducible definitions are
  never unfolded, and data terms are not delta-unfolded during syntactic
  normalisation, with one exception: a term that mentions an output and is
  equated with a constructor is evaluated to weak head normal form, so that a
  helper applied to `.returned v m` exposes its result (structured data, such
  as a list of `Value`s, is evaluated on either side of an equation). A `match`
  that scrutinises an output and does not collapse alternative by alternative
  is also judged through its case tree, where a constructor discriminant
  selects a subtree even if another discriminant, or a nested pattern, is
  stuck, and by a depth-bounded case split on what it is stuck on
  (`splitStuckMatch`). A structure of an opaque type (`CapturedMir` by default) is never
  unfolded to reach a field, so captured MIR bodies stay untouched;
* propositional identities (`True ∧ P`, `P ∨ True`, `False → P`, `P → True`,
  `P → P`, `P ↔ P`, `P ∨ ¬P`, `P ∧ ¬P`, double negation, canonical ordering of
  conjunctions/disjunctions/`Iff`, `if`/`dite` as a conjunction of implications,
  collapse of a `match` — including curried applications — whose alternatives
  all reduce to one pattern-independent term under their exact `altNumParams`
  pattern binders) plus an exact bounded truth-table pass (`propSimplify`, up
  to 10 atoms) that detects classical tautologies/contradictions and eliminates
  propositionally irrelevant atoms (De Morgan, contraposition, Peirce's law,
  absorption, dead-branch implications, exhaustive case splits), and kernel-
  typechecked rewriting of a conclusion or remaining disjuncts by equational
  premises (`v = t → C[v]` as `v = t → C[t]`, and `¬(v = t) ∨ C[v]` as
  `¬(v = t) ∨ C[t]`, exposing both `ret = x → f ret = f x` and
  `ret ≠ x ∨ f ret = f x` without ever producing ill-typed dependent terms);
* reflexivity of `Eq` (compared up to orientation and subsingleton types),
  `HEq`, `Iff`, of `≤`/`≥` (and irreflexivity of `<`/`>`) only where the law is
  provable for the instance at hand, of `BEq.beq` only under a `ReflBEq`/
  `LawfulBEq` instance, and of `Nat.ble`/`Nat.beq`/`decide`; numerals are
  compared by value at `Nat` only;
* injectivity and disjointness of constructors, quantifier domain
  normalisation, currying of `Prod`/`PProd`/`Subtype` existentials, and the
  one-point rules `∃ y, y = t ∧ P y ↔ P t` and `∀ y, y = t → P y ↔ P t` for
  `y` not in `t`.

An output is *bound* when its type is not a subsingleton (by instance, by
proof, or structurally: at most one constructor can build a value, as for
`Option Empty`, `List Empty`, and structures over such types), it still occurs
in the residual, a bounded, `sorry`-free proof search (`rfl`, `omega`,
`simp +arith`, `decide`, `infer_instance`, `subst_vars`, `grind`, top-level
`Iff` splitting, existential witness search — over `Nat` including `v / 2` and
`List` including `[]`/`List.replicate` for a leading `∃`, behind a `∀`/`→`
prefix, and by Herbrand expansion of `Nat` existentials nested in positive
positions —, nested subformula probing, and single-step unfolding of small
non-recursive output helpers) can neither discharge the subformulas mentioning
it nor prove the residual insensitive to it, and a case split on its
constructors (for an inductive output with two to eight of them, skipping those
that need a value of an empty type) does not reduce the postcondition to one
proposition free of it. All rewrites are equivalences, so a postcondition
reported as not binding an output is semantically insensitive to that output;
a postcondition reported as binding may still be vacuous in a way the search
does not see (for example behind an `opaque` or `irreducible` definition, a
fact needing induction or nonlinear arithmetic, or an existential whose
witness is not among the candidates).

**Relative to the precondition.** `PostconditionDichotomy pre post` ranges over
admissible inputs, and an `ensures` clause that binds its output in general
may bind nothing on them (`requires(x < 10) ensures(x >= 10 ==> ret == 5)`,
`exists_dichotomy_lost_under_requires`). When the precondition is known (the
`pre` field of a `Claim`, `StatefulClaim`, or `MirCallContract`, or an explicit
`preExpr?`), it is first checked for unsatisfiability via the shared
`refuteUnderExists` and empty-domain check (keeping `checkRequiresSatisfiable`
and `checkEnsuresBindsOutput` consistent), and what the passes above leave
bound is then re-examined under it: its existentials are opened, its equations
rewrite the residual with typechecked substitution, constructor case splitting
is re-run on the rewritten residual, and its remaining facts are premises of
the proof search. The verdicts `requiresUnsatisfiable`, `vacuousUnderRequires`,
and `unrealizableUnderRequires` are the ones that needed it;
`useRequires := false` judges the postcondition alone.

**User `ensures` mode.** The one deliberate projection is `userEnsuresOnly`
(and the `bindsBeyondBoilerplate` field), which asks whether the clause still
separates two outputs once the frame and return-type boilerplate of an external
spec is fixed. With one boilerplate predicate this is
`DichotomyBeyondPredicate` (`dichotomyBeyondPredicate_iff_cofactors`); in
general it is `DichotomyModuloObservation` for the observation "truth value of
each boilerplate atom occurring in the postcondition"
(`externalSpecEnsuresDichotomy_iff_moduloObservation`). The atoms are judged
*individually*: agreement on their conjunction is strictly coarser and would
let pure boilerplate through (`exists_dichotomyBeyond_conj_not_moduloPair`,
`frameOnlyMirCallContract_dichotomyBeyond_conj_of_illTyped`). Rather than
replacing boilerplate predicates independently by syntactic polarity (which
collapses `frame → ret = 1`, `if frame then ret = 1 else ret = 2`, and
`¬(frame ∧ ret ≠ 1)` to `True`, while missing `frame ↔ retTy`), the checker
normalises with boilerplate kept opaque and then evaluates the cofactors over
**all** truth assignments `{True, False}^k` to the distinct closed boilerplate
atoms occurring in the residual (with a zero-cost fast path whenever no
boilerplate constant was encountered). An output is bound beyond boilerplate
iff some cofactor constrains it
(`not_dichotomyModuloObservation_of_cofactors_insensitive`). The assignments
are never sampled, since the one cofactor carrying a dichotomy can be any of
them; past eight atoms, or when a cofactor cannot be judged, the verdict is the
conservative *binds*. By convention every closed application of a boilerplate
predicate is an observation, including one at other arguments than the
contract's own (`callFramePreserved emptyMemory memAfter`): a clause built
from such atoms alone is reported `boilerplateOnly`.

**`MirCallAns`.** When the single output binder has type `MirCallAns`, the
postcondition is instantiated at `.returned retVal memAfter`, `.panicked
memAfter`, and `.aborted` with fresh variables, so that every `match`,
`casesOn`, helper predicate, and equation on the answer reduces. The verdict is
taken on the `.returned` instance alone: rejecting `.panicked` does not bind a
return.
-/

section Checker

open Lean Meta

/-- Why a postcondition was judged not to bind its output. -/
inductive EnsuresVacuityReason where
  /-- The postcondition is `True` up to definitional and connective reduction. -/
  | constTrue
  /-- The postcondition reduces to `False`: no output is accepted. -/
  | unsatisfiable
  /-- Every occurrence of the output sits inside a tautology (`r = r`, ...). -/
  | reflexiveTautology
  /-- The postcondition constrains (or repeats) only non-output binders. -/
  | inputOnly
  /--
  The output occurs in the residual, but proof search discharged the conjuncts
  mentioning it or proved the residual insensitive to it (`0 ≤ r`, `r - r = 0`).
  -/
  | semanticallyInsensitive
  /-- `MirCallAns`: all three outcomes reduce to one output-free proposition. -/
  | outcomeBlind
  /-- `MirCallAns`: the `.returned` instance ignores `retVal` and `memAfter`. -/
  | returnBlind
  /-- `MirCallAns`: the `.returned` instance reduces to `False`. -/
  | normalReturnUnsatisfiable
  /-- Strict mode: an output is bound, but not the returned value. -/
  | returnValueUnconstrained
  /--
  User-`ensures` mode: outputs are bound only by frame or return-type
  boilerplate (`callFramePreserved`, `retMatchesCalleeReturnTy`).
  -/
  | boilerplateOnly
  /--
  The precondition of the contract was refuted: no input is admissible, so
  `PostconditionDichotomy pre post` fails whatever the postcondition says.
  -/
  | requiresUnsatisfiable
  /--
  The postcondition constrains an output in general, but not on the inputs the
  precondition admits (`requires(x < 10) ensures(x >= 10 ==> ret == 5)`).
  -/
  | vacuousUnderRequires
  /--
  On every input the precondition admits, the postcondition rejects every
  output: the contract is not realizable.
  -/
  | unrealizableUnderRequires
  deriving DecidableEq, Repr, Inhabited

instance : ToString EnsuresVacuityReason where
  toString
    | .constTrue => "constTrue"
    | .unsatisfiable => "unsatisfiable"
    | .reflexiveTautology => "reflexiveTautology"
    | .inputOnly => "inputOnly"
    | .semanticallyInsensitive => "semanticallyInsensitive"
    | .outcomeBlind => "outcomeBlind"
    | .returnBlind => "returnBlind"
    | .normalReturnUnsatisfiable => "normalReturnUnsatisfiable"
    | .returnValueUnconstrained => "returnValueUnconstrained"
    | .boilerplateOnly => "boilerplateOnly"
    | .requiresUnsatisfiable => "requiresUnsatisfiable"
    | .vacuousUnderRequires => "vacuousUnderRequires"
    | .unrealizableUnderRequires => "unrealizableUnderRequires"

/-- Options of `checkEnsuresBindsOutput`. -/
structure EnsuresCheckConfig where
  /-- Head-unfolding fuel for definitions in proposition position. -/
  maxUnfolds : Nat := 128
  /-- Bound on normalisation steps; past it terms are left as they are. -/
  maxSteps : Nat := 50000
  /--
  Require the returned value itself to be bound: binder `2` of a
  `StatefulClaim` postcondition, `retVal` of a `.returned` answer, and every
  designated output otherwise.
  -/
  strictReturnValue : Bool := false
  /--
  Judge only the user `ensures` clause: conjuncts headed by a `boilerplate`
  constant are discarded before binding is assessed.
  -/
  userEnsuresOnly : Bool := false
  /-- Frame and return-type predicates every external spec carries. -/
  boilerplate : Array Name :=
    #[``callFramePreserved, ``retMatchesCalleeReturnTy]
  /-- Structure types never unfolded to reach a field. -/
  opaqueStructTypes : Array Name := #[``CapturedMir]
  /-- Run the bounded proof search on what the syntactic pass leaves. -/
  semanticProbe : Bool := true
  /--
  Judge binding relative to the precondition when one is known (a `Claim`,
  `StatefulClaim`, `MirCallContract`, or an explicit `preExpr?`): the proof
  search may then use the precondition as a hypothesis, which is what
  `PostconditionDichotomy pre post` quantifies over.
  -/
  useRequires : Bool := true
  /-- Heartbeat budget (in thousands) of each proof-search attempt. -/
  probeHeartbeats : Nat := 4000
  /-- Largest residual (in `Expr` nodes) handed to the proof search. -/
  probeMaxSize : Nat := 400

/-- Result of `checkEnsuresBindsOutput`. -/
structure EnsuresCheckReport where
  /-- What was analysed: `function`, `Claim`, `StatefulClaim`, `MirCallContract`. -/
  kind : String
  /-- Number of postcondition binders. -/
  arity : Nat
  /-- Indices of the binders designated as outputs. -/
  outputIdxs : Array Nat
  /-- Designated outputs the postcondition genuinely constrains. -/
  boundOutputIdxs : Array Nat
  /-- `none` when the postcondition binds its output. -/
  reason? : Option EnsuresVacuityReason
  /--
  Whether an output is still bound once frame and return-type boilerplate is
  discarded, that is, by the user `ensures` clause itself.
  -/
  bindsBeyondBoilerplate : Bool
  /-- The normalised postcondition (for `MirCallAns`, its `.returned` instance). -/
  residual : String
  /-- Further findings: per-outcome residuals, exhausted budgets. -/
  notes : Array String
  deriving Repr, Inhabited

/-- Whether the postcondition was found to bind its output. -/
def EnsuresCheckReport.bindsOutput (r : EnsuresCheckReport) : Bool :=
  r.reason?.isNone

/-- Whether the postcondition was flagged as vacuous in its output. -/
def EnsuresCheckReport.isVacuous (r : EnsuresCheckReport) : Bool :=
  r.reason?.isSome

def EnsuresCheckReport.describe (r : EnsuresCheckReport) : String :=
  let verdict :=
    match r.reason? with
    | none => "binds output"
    | some reason => s!"VACUOUS ({reason})"
  let notes := r.notes.foldl (fun acc n => acc ++ "\n  note: " ++ n) ""
  s!"{verdict}: {r.kind} of arity {r.arity}, outputs {r.outputIdxs}, bound \
    {r.boundOutputIdxs}, binds beyond boilerplate: {r.bindsBeyondBoilerplate}\n  \
    residual: {r.residual}{notes}"

namespace EnsuresCheck

/-- Read-only context of the normaliser. -/
structure Context where
  cfg : EnsuresCheckConfig
  /-- The free variables standing for the designated outputs. -/
  outputs : Array FVarId
  /--
  User-`ensures` mode: boilerplate predicates are kept as opaque atoms while
  normalising, and then eliminated by cofactoring (`analyzeUserBeyondBoilerplate`).
  -/
  stripBoilerplate : Bool
  /-- Remaining depth of case splits on what a stuck `match` scrutinises. -/
  splitFuel : Nat := 2

/-- What the normaliser discarded on the way to the residual. -/
structure State where
  unfolds : Nat := 0
  steps : Nat := 0
  /-- A tautology (or absorbed subformula) mentioning an output was discarded. -/
  droppedOutputTaut : Bool := false
  /-- A tautology (or absorbed subformula) without outputs was discarded. -/
  droppedInputTaut : Bool := false
  /-- A boilerplate predicate was eliminated via cofactoring. -/
  droppedBoilerplate : Bool := false
  /-- A boilerplate constant was encountered while normalising. -/
  sawBoilerplate : Bool := false
  /-- The proof search discharged a conjunct mentioning an output. -/
  semanticStrip : Bool := false
  /-- The fuel or step budget ran out; the residual is under-normalised. -/
  budgetExhausted : Bool := false

abbrev CheckM := ReaderT Context (StateRefT State MetaM)

/-- Run `x`, falling back to `dflt` on any exception, runtime ones included. -/
def safely {α : Type} (x : MetaM α) (dflt : α) : MetaM α :=
  tryCatchRuntimeEx x fun _ => pure dflt

def isTrueConst (e : Expr) : Bool := e.isConstOf ``True

def isFalseConst (e : Expr) : Bool := e.isConstOf ``False

def mentionsOutput (e : Expr) : CheckM Bool := do
  let outs := (← read).outputs
  return e.hasAnyFVar outs.contains

/-- Record that the subformula `e` was discarded by an equivalence. -/
def noteDropped (e : Expr) : CheckM Unit := do
  if isTrueConst e || isFalseConst e then
    return
  if ← mentionsOutput e then
    modify fun s => { s with droppedOutputTaut := true }
  else
    modify fun s => { s with droppedInputTaut := true }

/-- Spend one normalisation step; `false` once the budget is gone. -/
def tick : CheckM Bool := do
  let s ← get
  if s.steps ≥ (← read).cfg.maxSteps then
    set { s with budgetExhausted := true }
    return false
  set { s with steps := s.steps + 1 }
  return true

/-- Number of `Expr` nodes of `e`, counted up to `limit`. -/
partial def sizeUpTo (limit : Nat) (e : Expr) (acc : Nat := 0) : Nat :=
  if acc ≥ limit then
    acc
  else
    match e with
    | .app f a => sizeUpTo limit a (sizeUpTo limit f (acc + 1))
    | .lam _ d b _ | .forallE _ d b _ =>
      sizeUpTo limit b (sizeUpTo limit d (acc + 1))
    | .letE _ t v b _ =>
      sizeUpTo limit b (sizeUpTo limit v (sizeUpTo limit t (acc + 1)))
    | .mdata _ b | .proj _ _ b => sizeUpTo limit b (acc + 1)
    | _ => acc + 1

partial def conjuncts (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match e.getAppFnArgs with
  | (``And, #[a, b]) => conjuncts b (conjuncts a acc)
  | _ => acc.push e

partial def disjuncts (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match e.getAppFnArgs with
  | (``Or, #[a, b]) => disjuncts b (disjuncts a acc)
  | _ => acc.push e

/-- Right-nested application of the binary connective `op`; `unit` when empty. -/
def mkConnectiveN (op unit : Name) (es : Array Expr) : Expr :=
  if es.isEmpty then
    mkConst unit
  else
    es.pop.foldr (fun a acc => mkApp2 (mkConst op) a acc) es.back!

def mkAndN (es : Array Expr) : Expr := mkConnectiveN ``And ``True es

def mkOrN (es : Array Expr) : Expr := mkConnectiveN ``Or ``False es

def isNegationOf (a b : Expr) : Bool :=
  match a.getAppFnArgs with
  | (``Not, #[a']) => a' == b
  | _ => false

def complementary (a b : Expr) : Bool :=
  isNegationOf a b || isNegationOf b a

def mkNotS (a : Expr) : CheckM Expr := do
  if isTrueConst a then
    return mkConst ``False
  if isFalseConst a then
    return mkConst ``True
  match a.getAppFnArgs with
  | (``Not, #[b]) => return b
  | _ => return mkNot a

def mkAndS (a b : Expr) : CheckM Expr := do
  if isFalseConst a then
    noteDropped b
    return a
  if isFalseConst b then
    noteDropped a
    return b
  if isTrueConst a then
    return b
  if isTrueConst b then
    return a
  let mut acc : Array Expr := #[]
  for c in conjuncts b (conjuncts a) do
    if acc.contains c then
      continue
    if acc.any (complementary c) then
      noteDropped a
      noteDropped b
      return mkConst ``False
    acc := acc.push c
  return mkAndN (acc.qsort Expr.lt)

def mkOrS (a b : Expr) : CheckM Expr := do
  if isTrueConst a then
    noteDropped b
    return a
  if isTrueConst b then
    noteDropped a
    return b
  if isFalseConst a then
    return b
  if isFalseConst b then
    return a
  let mut acc : Array Expr := #[]
  for d in disjuncts b (disjuncts a) do
    if acc.contains d then
      continue
    if acc.any (complementary d) then
      noteDropped a
      noteDropped b
      return mkConst ``True
    acc := acc.push d
  return mkOrN (acc.qsort Expr.lt)

def mkImpS (a b : Expr) : CheckM Expr := do
  if isFalseConst a then
    noteDropped b
    return mkConst ``True
  if isTrueConst b then
    noteDropped a
    return b
  if isTrueConst a then
    return b
  if isFalseConst b then
    return ← mkNotS a
  -- `A₁ ∧ … ∧ Aₙ → B₁ ∧ … ∧ Bₘ` with every `Bⱼ` among the `Aᵢ`.
  let hyps := conjuncts a
  if a == b || (conjuncts b).all hyps.contains then
    noteDropped a
    noteDropped b
    return mkConst ``True
  return mkForall `h .default a b

def mkIffS (a b : Expr) : CheckM Expr := do
  -- Equal up to the order (and repetition) of conjuncts, or of disjuncts.
  let sameSet (xs ys : Array Expr) : Bool :=
    xs.all ys.contains && ys.all xs.contains
  if a == b || sameSet (conjuncts a) (conjuncts b) ||
      sameSet (disjuncts a) (disjuncts b) then
    noteDropped a
    return mkConst ``True
  if isTrueConst a then
    return b
  if isTrueConst b then
    return a
  if isFalseConst a then
    return ← mkNotS b
  if isFalseConst b then
    return ← mkNotS a
  if complementary a b then
    noteDropped a
    return mkConst ``False
  if b.lt a then
    return mkApp2 (mkConst ``Iff) b a
  return mkApp2 (mkConst ``Iff) a b

/--
Run a single heartbeat-bounded tactic against `goal`, isolating and restoring
both the elaboration state and the message log, and verifying that the produced
proof term contains neither `sorry` nor unassigned metavariables.
-/
def runTacticClosed (goal : Expr) (heartbeats : Nat) (tac : TSyntax `tactic) :
    MetaM Bool := do
  let saved ← saveState
  let savedMsgs ← Core.getMessageLog
  Core.resetMessageLog
  let r ← tryCatchRuntimeEx
    (do
      let mvar ← mkFreshExprMVar goal
      let (goals, _) ← withCurrHeartbeats <|
        withTheReader Core.Context
          (fun c => { c with maxHeartbeats := heartbeats * 1000 }) <|
          Lean.Elab.runTactic mvar.mvarId! tac
      let hasErrs := (← Core.getMessageLog).hasErrors
      if !goals.isEmpty || hasErrs then
        return false
      let proof ← instantiateMVars mvar
      return !proof.hasSorry && !proof.hasExprMVar)
    (fun _ => pure false)
  Core.setMessageLog savedMsgs
  saved.restore
  return r

/-- Fast heartbeat-bounded tactic portfolio (excludes `grind`). -/
def tryProveFast (goal : Expr) (heartbeats : Nat) : MetaM Bool := do
  let tac ← `(tactic|
    first
      | rfl
      | (intros; omega)
      | (simp +arith; done)
      | decide
      | infer_instance
      | (intros; subst_vars; rfl))
  runTacticClosed goal heartbeats tac

/-- Deep fallback (`grind`: congruence closure, case splits, ring arithmetic). -/
def tryProveGrind (goal : Expr) (heartbeats : Nat) : MetaM Bool := do
  let tac ← `(tactic| grind)
  runTacticClosed goal heartbeats tac

/--
Try to close a single `goal` with a short, heartbeat-bounded tactic portfolio,
falling back to `grind` when `deep := true`.
-/
def tryProveSingle (goal : Expr) (heartbeats : Nat) (deep : Bool := false) :
    MetaM Bool := do
  if ← tryProveFast goal heartbeats then
    return true
  if deep then
    tryProveGrind goal heartbeats
  else
    return false

/--
`goal` under the hypothesis `hyp`, with the leading existentials and
conjunctions of `hyp` opened into universally quantified variables and separate
premises: `(∃ w, A w ∧ B w) → G` becomes `∀ w, A w → B w → G`. The two are
equivalent, and the opened form is the one `omega` and `grind` can use.
-/
partial def underHyp (hyp goal : Expr) : MetaM Expr := do
  match hyp.getAppFnArgs with
  | (``True, #[]) => return goal
  | (``And, #[a, b]) => underHyp a (← underHyp b goal)
  | (``Exists, #[α, p]) =>
    let name := if let .lam n .. := p then n else `w
    withLocalDeclD name α fun w => do
      mkForallFVars #[w] (← underHyp (p.beta #[w]) goal)
  | _ => return mkForall `h .default hyp goal

/--
Open the hypotheses `pending`: leading existentials become fresh variables
`ws` and conjunctions are split, leaving a list of atomic `facts` over `ws`.
The continuation runs with the variables in scope.
-/
partial def openHyps {α : Type} (pending : List Expr) (ws facts : Array Expr)
    (k : Array Expr → Array Expr → MetaM α) : MetaM α :=
  match pending with
  | [] => k ws facts
  | h :: rest =>
    match h.getAppFnArgs with
    | (``True, #[]) => openHyps rest ws facts k
    | (``And, #[a, b]) => openHyps (a :: b :: rest) ws facts k
    | (``Exists, #[ty, p]) =>
      let name := if let .lam n .. := p then n else `w
      withLocalDeclD name ty fun w =>
        openHyps (p.beta #[w] :: rest) (ws.push w) facts k
    | _ => openHyps rest ws (facts.push h) k

/--
An equation usable as a rewrite rule `lhs ↦ rhs`: one side is a variable, or a
term that is not a constructor application while the other side is one, and
the replaced side does not occur in its replacement.
-/
def rewriteRule? (fact : Expr) : MetaM (Option (Expr × Expr)) := do
  let (``Eq, #[_, l, r]) := fact.getAppFnArgs | return none
  let occursIn (pat e : Expr) : Bool := (e.find? (· == pat)).isSome
  let isCtor (e : Expr) : MetaM Bool :=
    safely (do return (← constructorApp? e).isSome) false
  if l.isFVar && !occursIn l r then
    return some (l, r)
  if r.isFVar && !occursIn r l then
    return some (r, l)
  let lc ← isCtor l
  let rc ← isCtor r
  if rc && !lc && !occursIn l r then
    return some (l, r)
  if lc && !rc && !occursIn r l then
    return some (r, l)
  return none

/--
Try to close `goal`: run the fast portfolio on `goal` (and, for a top-level
`Iff`, on both directions in `MetaM` so `intros; omega` can close equivalences
directly), then fall back to a single `grind` call on `goal` when `deep := true`.
-/
def tryProveCore (goal : Expr) (heartbeats : Nat) (deep : Bool := false) :
    MetaM Bool := do
  if ← tryProveFast goal heartbeats then
    return true
  match goal.getAppFnArgs with
  | (``Iff, #[a, b]) =>
    let fwd := mkForall `h .default a b
    let bwd := mkForall `h .default b a
    if (← tryProveFast fwd heartbeats) && (← tryProveFast bwd heartbeats) then
      return true
    if deep then
      tryProveGrind goal heartbeats
    else
      return false
  | _ =>
    if deep then
      tryProveGrind goal heartbeats
    else
      return false

/--
Collect free variables occurring in `e` whose type is definitionally equal to `α`.
-/
def matchingFVars (e α : Expr) : MetaM (Array Expr) := do
  let st := Lean.collectFVars {} e
  let mut out : Array Expr := #[]
  for fv in st.fvarIds do
    let fvar := mkFVar fv
    let ty ← safely (inferType fvar) (mkConst ``Empty)
    if ← safely (withNewMCtxDepth <| withReducible <| isDefEq ty α) false then
      out := out.push fvar
  return out

/--
Candidate `Nat` witnesses built from the `Nat` variables occurring in `e`: `0`,
each variable `v`, `v + 1`, `v - 1`, `v / 2`, the sum of all and its successor,
and for two variables their truncated differences (and predecessors).
-/
def natWitnessCandidates (e : Expr) : MetaM (Array Expr) := do
  let fvars ← matchingFVars e (mkConst ``Nat)
  let mut cands : Array Expr := #[mkNatLit 0]
  for v in fvars do
    cands := cands.push v
    cands := cands.push (mkNatAdd v (mkNatLit 1))
    cands := cands.push (mkNatSub v (mkNatLit 1))
    if let some half ← safely (do
        return some (← mkAppM ``HDiv.hDiv #[v, mkNatLit 2])) none then
      cands := cands.push half
  if fvars.size ≥ 2 then
    let sum := fvars.foldl (fun acc v => mkNatAdd acc v) (mkNatLit 0)
    cands := cands.push sum
    cands := cands.push (mkNatAdd sum (mkNatLit 1))
  if fvars.size == 2 then
    for (v, w) in #[(fvars[0]!, fvars[1]!), (fvars[1]!, fvars[0]!)] do
      cands := cands.push (mkNatSub v w)
      cands := cands.push (mkNatSub (mkNatSub v w) (mkNatLit 1))
  return cands

/--
Herbrand strengthening. Each existential `∃ y : Nat, P y` in a *positive*
position of `e` (under `∧`, `∨`, a universal binder, or the conclusion of an
implication) is replaced by the finite disjunction `P w₁ ∨ … ∨ P wₙ` over
candidate witnesses. Positive positions are monotone, so the result implies
`e`: proving it proves `e`, and nothing is concluded when it is not proved.
Hypotheses, negations, and equivalences are left untouched.
-/
partial def herbrandNat (e : Expr) (fuel : Nat := 2) : MetaM Expr := do
  match e.getAppFnArgs with
  | (``And, #[a, b]) =>
    return mkApp2 (mkConst ``And) (← herbrandNat a fuel) (← herbrandNat b fuel)
  | (``Or, #[a, b]) =>
    return mkApp2 (mkConst ``Or) (← herbrandNat a fuel) (← herbrandNat b fuel)
  | (``Exists, #[α, p]) =>
    if fuel == 0 || !(← safely (whnfR α) α).isConstOf ``Nat then
      return e
    let cands := (← natWitnessCandidates p).extract 0 (if fuel ≥ 2 then 16 else 3)
    let mut out? : Option Expr := none
    for w in cands do
      let inst ← herbrandNat (p.beta #[w]) (fuel - 1)
      out? := some <|
        match out? with
        | none => inst
        | some acc => mkApp2 (mkConst ``Or) acc inst
    return out?.getD e
  | _ =>
    if e.isForall then
      forallBoundedTelescope e (some 1) fun xs body => do
        mkForallFVars xs (← herbrandNat body fuel)
    else
      return e

/--
`tryProveCore`, augmented with a sound witness search for existentials:

* a leading `∃ y : α, P y` (`Nat`: `0`, local variables, `v + 1`, `v / 2`, and
  sum plus one; `List β`: `[]`, local variables, and `List.replicate v default`
  when `Inhabited β` synthesizes; otherwise local variables);
* a `∀`/`→` prefix in front of an existential (`∀ a, ∃ b, a + r ≤ b`): the
  binders are introduced and the search continues on the conclusion;
* existentials over `Nat` nested under `∧`/`∨`/`→`/`∀` (`r = 0 ∨ ∃ y, r = y + 1`,
  `(∃ k, r = 2 * k) ∨ ∃ k, r = 2 * k + 1`): `herbrandNat`.

Every instance is proved by `tryProveCore` and kernel-checked, and each of the
goals attempted implies the original one, so this cannot introduce false
positives.
-/
partial def tryProve (goal : Expr) (heartbeats : Nat) (deep : Bool := false)
    (exFuel : Nat := 1) : MetaM Bool := do
  if ← tryProveCore goal heartbeats deep then
    return true
  if let (``Exists, #[α, p]) := goal.getAppFnArgs then
    let αn ← safely (whnfR α) α
    let fvars ← matchingFVars p αn
    let mut cands : Array Expr := #[]
    if αn.isConstOf ``Nat then
      cands := cands.push (mkNatLit 0)
      for v in fvars do
        cands := cands.push v
        cands := cands.push (mkNatAdd v (mkNatLit 1))
        if let some half ← safely (do
            return some (← mkAppM ``HDiv.hDiv #[v, mkNatLit 2])) none then
          cands := cands.push half
      if fvars.size ≥ 2 then
        let sum := fvars.foldl (fun acc v => mkNatAdd acc v) (mkNatLit 0)
        cands := cands.push (mkNatAdd sum (mkNatLit 1))
    else if let (``List, #[β]) := αn.getAppFnArgs then
      if let some nilE ← safely (do return some (← mkAppOptM ``List.nil #[some β])) none then
        cands := cands.push nilE
      cands := cands ++ fvars
      if let some dflt ← safely (do
          let u ← getLevel β
          let inst ← synthInstance (mkApp (mkConst ``Inhabited [u]) β)
          return some (mkApp2 (mkConst ``Inhabited.default [u]) β inst)) none then
        let natFVars ← matchingFVars p (mkConst ``Nat)
        for v in natFVars do
          if let some repE ← safely (do
              return some (← mkAppM ``List.replicate #[v, dflt])) none then
            cands := cands.push repE
    else
      cands := fvars
    let cap := if exFuel > 0 then 12 else 4
    let mut tried := 0
    for w in cands do
      if tried ≥ cap then
        break
      tried := tried + 1
      let inst := p.beta #[w]
      let ok ←
        if inst.isAppOf ``Exists && exFuel > 0 then
          tryProve inst heartbeats false (exFuel - 1)
        else
          tryProveCore inst heartbeats false
      if ok then
        return true
  else if goal.isForall then
    let found ← safely (forallTelescope goal fun _ body => do
      if body.isAppOf ``Exists then
        tryProve body heartbeats false exFuel
      else
        return false) false
    if found then
      return true
  -- Existentials over `Nat` anywhere in a positive position.
  let natExists (sub : Expr) : Bool :=
    match sub.getAppFnArgs with
    | (``Exists, #[α, _]) => α.isConstOf ``Nat
    | _ => false
  if exFuel > 0 && (goal.find? natExists).isSome then
    let strengthened ← safely (herbrandNat goal) goal
    if strengthened != goal && sizeUpTo 4001 strengthened ≤ 4000 then
      if ← safely (do check strengthened; return true) false then
        return ← tryProveCore strengthened heartbeats false
  return false

/-- Syntactic equality up to alpha and eta, or reducible definitional equality. -/
def sameExpr (a b : Expr) : CheckM Bool := do
  if a == b || a.eta == b.eta then
    return true
  safely (withNewMCtxDepth <| withReducible <| isDefEq a b) false

/-- Whether `α` is provably inhabited by instance resolution. -/
def typeNonempty (α : Expr) : CheckM Bool :=
  safely (do
    let u ← getLevel α
    return (← synthInstance? (mkApp (mkConst ``Nonempty [u]) α)).isSome) false

/--
Types with at least two distinct inhabitants whatever their arguments. `List`
and `Option` are deliberately absent: `List Empty` and `Option Empty` have
exactly one inhabitant (`knownTwoInhabitants`).
-/
def isKnownNonSubsingleton (α : Expr) : Bool :=
  match α.getAppFn with
  | .const n _ =>
    #[``Nat, ``Int, ``Bool, ``String, ``Char, ``Value,
      ``Memory, ``MirCallAns, ``MirCallReq].contains n
  | _ => false

/-- Types inhabited whatever their arguments (`[]`, `none`, `()`). -/
def isKnownNonempty (α : Expr) : Bool :=
  isKnownNonSubsingleton α ||
    match α.getAppFn with
    | .const n _ => #[``List, ``Option, ``Unit, ``PUnit].contains n
    | _ => false

/--
Whether `α` is known to have two distinct inhabitants: a base type of
`isKnownNonSubsingleton`, or `List β` / `Option β` over an element type that is
known to be inhabited (`[]` against `[b]`, `none` against `some b`).
-/
def knownTwoInhabitants (α : Expr) : MetaM Bool := do
  if isKnownNonSubsingleton α then
    return true
  match α.getAppFnArgs with
  | (``List, #[β]) | (``Option, #[β]) =>
    let βn ← safely (whnfR β) β
    if isKnownNonempty βn then
      return true
    safely (do
      let u ← getLevel βn
      return (← synthInstance? (mkApp (mkConst ``Nonempty [u]) βn)).isSome) false
  | _ => return false

/-- Whether `ty` reduces to an inductive type without constructors. -/
def isEmptyInductive (ty : Expr) : MetaM Bool :=
  safely (do
    let ty ← whnf ty
    let .const n _ := ty.getAppFn | return false
    let some (.inductInfo ind) := (← getEnv).find? n | return false
    return ind.ctors.isEmpty) false

/--
Whether the constructor application `ctor` (parameters supplied) has a field of
a constructorless type (`Empty`, `PEmpty`, `False`, ...), together with its
number of fields. Such a constructor builds no value: `some : Empty → Option
Empty`, `List.cons : Empty → List Empty → List Empty`.
-/
def ctorFieldInfo (ctor : Expr) : MetaM (Bool × Nat) :=
  safely (do
    forallTelescopeReducing (← inferType ctor) fun fields _ => do
      let dead ← fields.anyM fun f => do isEmptyInductive (← inferType f)
      return (dead, fields.size)) (false, 1)

/--
Structural subsingleton test: at most one constructor of the inductive type
`α` can build a value, and each of its fields ranges over a proposition or a
type that passes the same test (to depth `fuel`). This covers `Option Empty`,
`List Empty`, `Empty`, `Unit`, a one-constant enumeration, and structures over
such types.
-/
partial def inductiveAtMostOne (α : Expr) (fuel : Nat := 3) : MetaM Bool :=
  safely (do
    if ← isProp α then
      return true
    let ty ← whnf α
    let .const n lvls := ty.getAppFn | return false
    let some (.inductInfo ind) := (← getEnv).find? n | return false
    if ind.numIndices != 0 then
      return false
    let mut live := 0
    for c in ind.ctors do
      let ctor := mkAppN (mkConst c lvls) ty.getAppArgs
      -- `none`: builds no value; `some ok`: builds one, `ok` iff at most one.
      let verdict? ← forallTelescopeReducing (← inferType ctor) fun fields _ => do
        for f in fields do
          if ← isEmptyInductive (← inferType f) then
            return none
        for f in fields do
          if fuel == 0 then
            return some false
          unless ← inductiveAtMostOne (← inferType f) (fuel - 1) do
            return some false
        return some true
      match verdict? with
      | none => pure ()
      | some false => return false
      | some true => live := live + 1
    return live ≤ 1) false

/--
Whether `α` has at most one inhabitant (`Subsingleton α`, proof irrelevance, or
— when `semanticProbe` is enabled — a direct proof of `∀ a b : α, a = b`).
-/
def typeSubsingleton (α : Expr) (semanticProbe : Bool) (heartbeats : Nat) :
    MetaM Bool := do
  if ← safely (isProp α) false then
    return true
  if ← knownTwoInhabitants α then
    return false
  if ← inductiveAtMostOne α then
    return true
  let hasInst ← safely (do
    let u ← getLevel α
    return (← synthInstance? (mkApp (mkConst ``Subsingleton [u]) α)).isSome) false
  if hasInst then
    return true
  if semanticProbe then
    return ← safely (do
      withLocalDeclD `a α fun a =>
      withLocalDeclD `b α fun b => do
        tryProveCore (← mkEq a b) heartbeats) false
  return false

/-- Whether `ty` is provably empty (`∀ x : ty, False`). -/
def isEmptyDomain (ty : Expr) (heartbeats : Nat) : MetaM Bool := do
  let tyn ← safely (whnfR ty) ty
  if isKnownNonempty tyn then
    return false
  if ← safely (do
      let u ← getLevel tyn
      return (← synthInstance? (mkApp (mkConst ``Nonempty [u]) tyn)).isSome) false then
    return false
  let notInhab := mkForall `x .default tyn (mkConst ``False)
  let tac ← `(tactic|
    first | (intro x; cases x) | (intros; omega) | (simp +arith; done))
  runTacticClosed notInhab heartbeats tac

/--
Whether `e` is a bare equation or disequation `o = t`, `t = o`, `¬(o = t)`, or
`¬(t = o)` for a designated output `o` of a known multi-inhabitant type with
`o` not free in `t`. Such a formula can never be universally true, universally
false, or output-insensitive on any satisfiable precondition.
-/
def isBareOutputEq (outputs : Array Expr) (e : Expr) : MetaM Bool := do
  let core :=
    match e.getAppFnArgs with
    | (``Not, #[inner]) => inner
    | _ => e
  let (``Eq, #[α, l, r]) := core.getAppFnArgs | return false
  let isOut (x : Expr) : Bool := x.isFVar && outputs.any (· == x)
  let matched :=
    (isOut l && !r.containsFVar l.fvarId!) ||
    (isOut r && !l.containsFVar r.fvarId!)
  if !matched then
    return false
  let αn ← safely (whnfR α) α
  knownTwoInhabitants αn

/--
Marks a position that is not a positive conjunctive one. Boilerplate is kept
opaque everywhere during `stripBoilerplate := true` normalisation and eliminated
afterwards by exact cofactoring (`analyzeUserBeyondBoilerplate`).
-/
def withoutBoilerplate {α : Type} (x : CheckM α) : CheckM α :=
  x

/-- Pure constant folding of `True`/`False` under propositional connectives. -/
partial def evalBoolConsts (e : Expr) : Expr :=
  match e.getAppFnArgs with
  | (``Not, #[a]) =>
    let a := evalBoolConsts a
    if isTrueConst a then mkConst ``False
    else if isFalseConst a then mkConst ``True
    else mkNot a
  | (``And, #[a, b]) =>
    let a := evalBoolConsts a
    let b := evalBoolConsts b
    if isFalseConst a || isFalseConst b then mkConst ``False
    else if isTrueConst a then b
    else if isTrueConst b then a
    else mkApp2 (mkConst ``And) a b
  | (``Or, #[a, b]) =>
    let a := evalBoolConsts a
    let b := evalBoolConsts b
    if isTrueConst a || isTrueConst b then mkConst ``True
    else if isFalseConst a then b
    else if isFalseConst b then a
    else mkApp2 (mkConst ``Or) a b
  | (``Iff, #[a, b]) =>
    let a := evalBoolConsts a
    let b := evalBoolConsts b
    if isTrueConst a then b
    else if isTrueConst b then a
    else if isFalseConst a then evalBoolConsts (mkNot b)
    else if isFalseConst b then evalBoolConsts (mkNot a)
    else mkApp2 (mkConst ``Iff) a b
  | _ =>
    match e with
    | .forallE n d b bi =>
      if !b.hasLooseBVars then
        let d := evalBoolConsts d
        let b := evalBoolConsts b
        if isFalseConst d || isTrueConst b then mkConst ``True
        else if isTrueConst d then b
        else if isFalseConst b then evalBoolConsts (mkNot d)
        else .forallE n d b bi
      else e
    | _ => e

/--
Collect distinct full applications headed by a constant in `boilerplate`,
without descending into partial applications of those heads.
-/
partial def collectBoilerplateAtoms (boilerplate : Array Name)
    (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match e.getAppFn with
  | .const fn _ =>
    if boilerplate.contains fn then
      if acc.contains e then acc else acc.push e
    else
      e.getAppArgs.foldl (fun a arg => collectBoilerplateAtoms boilerplate arg a) acc
  | fn =>
    match e with
    | .app .. =>
      let acc := collectBoilerplateAtoms boilerplate fn acc
      e.getAppArgs.foldl (fun a arg => collectBoilerplateAtoms boilerplate arg a) acc
    | .lam _ d b _ | .forallE _ d b _ =>
      collectBoilerplateAtoms boilerplate b (collectBoilerplateAtoms boilerplate d acc)
    | .letE _ t v b _ =>
      collectBoilerplateAtoms boilerplate b
        (collectBoilerplateAtoms boilerplate v (collectBoilerplateAtoms boilerplate t acc))
    | .mdata _ b | .proj _ _ b => collectBoilerplateAtoms boilerplate b acc
    | _ => acc

/--
Instantiate the boilerplate `atoms` in `e` according to the bitmask `mask`
(`1 ↦ True`, `0 ↦ False`), collapsing `Decidable.decide`, `ite`, and `dite`
when their conditions become constant so `Decidable` instances never become
ill-typed, and kernel-checking non-connective argument replacements.
-/
partial def replaceBoilerplateAtoms (atoms : Array Expr) (mask : Nat)
    (e : Expr) : MetaM Expr := do
  if let some i := atoms.idxOf? e then
    let bit := ((mask >>> i) &&& 1) == 1
    let isBool ← safely (do
      if e.hasLooseBVars then return false
      return (← whnf (← inferType e)).isConstOf ``Bool) false
    if isBool then
      return mkConst (if bit then ``Bool.true else ``Bool.false)
    return mkConst (if bit then ``True else ``False)
  match e.getAppFnArgs with
  | (``And, #[a, b]) =>
    return mkApp2 e.getAppFn
      (← replaceBoilerplateAtoms atoms mask a)
      (← replaceBoilerplateAtoms atoms mask b)
  | (``Or, #[a, b]) =>
    return mkApp2 e.getAppFn
      (← replaceBoilerplateAtoms atoms mask a)
      (← replaceBoilerplateAtoms atoms mask b)
  | (``Not, #[a]) =>
    return mkApp e.getAppFn (← replaceBoilerplateAtoms atoms mask a)
  | (``Iff, #[a, b]) =>
    return mkApp2 e.getAppFn
      (← replaceBoilerplateAtoms atoms mask a)
      (← replaceBoilerplateAtoms atoms mask b)
  | (``Exists, #[ty, .lam n d b bi]) =>
    return mkApp2 e.getAppFn ty
      (.lam n d (← replaceBoilerplateAtoms atoms mask b) bi)
  | (``Decidable.decide, #[p, _]) =>
    let p' := evalBoolConsts (← replaceBoilerplateAtoms atoms mask p)
    if isTrueConst p' then
      return mkConst ``Bool.true
    if isFalseConst p' then
      return mkConst ``Bool.false
    return e
  | (``ite, #[_, c, _, t, f]) =>
    let c' := evalBoolConsts (← replaceBoilerplateAtoms atoms mask c)
    if isTrueConst c' then
      replaceBoilerplateAtoms atoms mask t
    else if isFalseConst c' then
      replaceBoilerplateAtoms atoms mask f
    else
      let t' ← replaceBoilerplateAtoms atoms mask t
      let f' ← replaceBoilerplateAtoms atoms mask f
      if t' == t && f' == f then
        return e
      else
        let args := e.getAppArgs
        return mkAppN e.getAppFn ((args.set! 3 t').set! 4 f')
  | (``dite, #[_, c, _, t, f]) =>
    let c' := evalBoolConsts (← replaceBoilerplateAtoms atoms mask c)
    let indepBody? (fn : Expr) : Option Expr :=
      match fn with
      | .lam _ _ b _ => if !b.hasLooseBVars then some b else none
      | _ => none
    if isTrueConst c' then
      if let some tb := indepBody? t then
        return ← replaceBoilerplateAtoms atoms mask tb
    if isFalseConst c' then
      if let some fb := indepBody? f then
        return ← replaceBoilerplateAtoms atoms mask fb
    return e
  | _ =>
    match e with
    | .forallE n d b bi =>
      if b.hasLooseBVars then
        return .forallE n d (← replaceBoilerplateAtoms atoms mask b) bi
      else
        return .forallE n (← replaceBoilerplateAtoms atoms mask d)
          (← replaceBoilerplateAtoms atoms mask b) bi
    | .app .. =>
      let args := e.getAppArgs
      let mut args' := args
      let mut changed := false
      for i in [0:args.size] do
        let a' ← replaceBoilerplateAtoms atoms mask args[i]!
        if a' != args[i]! then
          args' := args'.set! i a'
          changed := true
      if changed then
        let cand := mkAppN e.getAppFn args'
        if e.isAppOfArity ``Eq 3 || e.isAppOfArity ``Ne 3 then
          return cand
        if !cand.hasLooseBVars && (← safely (do check cand; return true) false) then
          return cand
      return e
    | _ => return e

/-- Whether `α` reduces to `Prop` (`Sort 0`). -/
def isPropSort (α : Expr) : CheckM Bool := do
  if α.isProp then
    return true
  return (← safely (whnf α) α).isProp

/-- Whether the `BEq α` instance `inst` satisfies the law class `cls`. -/
def hasBEqLaw (cls : Name) (α inst : Expr) : CheckM Bool :=
  safely (do
    let u ← getDecLevel α
    return (← synthInstance? (mkApp2 (mkConst cls [u]) α inst)).isSome) false

/-- Expose the constructor of a structure-typed term, unless its type is opaque. -/
def whnfStruct (s : Expr) : CheckM Expr := do
  let opaqueTys := (← read).cfg.opaqueStructTypes
  safely (do
    let ty ← whnf (← inferType s)
    if let .const n _ := ty.getAppFn then
      if opaqueTys.contains n then
        return s
    withTransparency .default (whnf s)) s

/--
Push a non-dependent structure projection `build` (either `.proj` or a
non-class projection function) into the branches of `ite`, `cond`, `dite`, or a
non-dependent `match`/`casesOn`. The rewritten expression is kernel-typechecked
against `resTy` before being returned.
-/
def distributeProj? (origE s' : Expr) (build : Expr → Expr) :
    CheckM (Option Expr) := do
  let some resTy ← safely (do return some (← inferType origE)) none | return none
  let verify (cand : Expr) : CheckM (Option Expr) :=
    safely (do
      check cand
      if ← isDefEq (← inferType cand) resTy then
        return some cand
      return none) none
  match s'.getAppFnArgs with
  | (``ite, #[_, c, dec, t, f]) =>
    let some cand ← safely (do
      return some (← mkAppOptM ``ite
        #[some resTy, some c, some dec, some (build t), some (build f)])) none
      | return none
    verify cand
  | (``cond, #[_, c, t, f]) =>
    let some cand ← safely (do
      return some (← mkAppOptM ``cond
        #[some resTy, some c, some (build t), some (build f)])) none
      | return none
    verify cand
  | (``dite, #[_, c, dec, t, f]) =>
    let some cand ← safely (do
      let t' ← withLocalDeclD `h c fun h =>
        mkLambdaFVars #[h] (build (t.beta #[h]))
      let f' ← withLocalDeclD `h (mkNot c) fun h =>
        mkLambdaFVars #[h] (build (f.beta #[h]))
      return some (← mkAppOptM ``dite
        #[some resTy, some c, some dec, some t', some f'])) none
      | return none
    verify cand
  | _ =>
    let some app ← safely (matchMatcherApp? s' (alsoCasesOn := true)) none
      | return none
    unless app.remaining.isEmpty do
      return none
    let motiveOk ← lambdaTelescope app.motive fun xs body =>
      pure !(xs.any fun x => body.containsFVar x.fvarId!)
    unless motiveOk do
      return none
    let some cand ← safely (do
      let uRes ← getLevel resTy
      let matcherLevels :=
        match app.uElimPos? with
        | some pos => app.matcherLevels.set! pos uRes
        | none => app.matcherLevels
      let motive' ← lambdaTelescope app.motive fun xs _ =>
        mkLambdaFVars xs resTy
      let mut alts' : Array Expr := #[]
      for i in [0:app.alts.size] do
        let alt := app.alts[i]!
        let numParams := app.altNumParams[i]!
        let altTy ← inferType alt
        let alt' ← forallBoundedTelescope altTy (some numParams) fun ys _ =>
          mkLambdaFVars ys (build (alt.beta ys))
        alts' := alts'.push alt'
      return some ({ app with
        matcherLevels, motive := motive', alts := alts' }).toExpr) none
      | return none
    verify cand

/--
Head-normalise without unfolding definitions: `mdata`, beta, zeta, iota,
matcher reduction on constructors, and structure projections (primitive or by
projection function) of a term whose constructor `whnfStruct` exposes or whose
head is `ite`/`cond`/`dite`/non-dependent `match`. Class projections are left
alone so that `LE.le`, `BEq.beq`, ... stay recognisable.
-/
partial def headReduce (e : Expr) : CheckM Expr := do
  let e ← instantiateMVars e
  let e ← safely (whnfCore e) e
  match e.getAppFn with
  | .proj structName i s =>
    let extraArgs := e.getAppArgs
    let sCore ← safely (whnfCore s) s
    if let some pushed ← distributeProj? (Expr.proj structName i sCore) sCore
        (fun x => Expr.proj structName i x) then
      return ← headReduce (pushed.beta extraArgs)
    let s' ← whnfStruct sCore
    match ← safely (constructorApp? s') none with
    | some (cv, cargs) =>
      if h : cv.numParams + i < cargs.size then
        headReduce (cargs[cv.numParams + i].beta extraArgs)
      else
        return e
    | none =>
      if s' != sCore then
        if let some pushed ← distributeProj? (Expr.proj structName i s') s'
            (fun x => Expr.proj structName i x) then
          return ← headReduce (pushed.beta extraArgs)
      return e
  | .const fnName lvls =>
    match ← getProjectionFnInfo? fnName with
    | some info =>
      if info.fromClass then
        return e
      let args := e.getAppArgs
      if h : info.numParams < args.size then
        let params := args.extract 0 info.numParams
        let extraArgs := args.extract (info.numParams + 1) args.size
        let build (x : Expr) : Expr :=
          mkApp (mkAppN (mkConst fnName lvls) params) x
        let sCore ← safely (whnfCore args[info.numParams]) args[info.numParams]
        if let some pushed ← distributeProj? (build sCore) sCore build then
          return ← headReduce (pushed.beta extraArgs)
        let s' ← whnfStruct sCore
        match ← safely (constructorApp? s') none with
        | some (cv, cargs) =>
          if cv.name != info.ctorName then
            return e
          if h' : cv.numParams + info.i < cargs.size then
            headReduce (cargs[cv.numParams + info.i].beta extraArgs)
          else
            return e
        | none =>
          if s' != sCore then
            if let some pushed ← distributeProj? (build s') s' build then
              return ← headReduce (pushed.beta extraArgs)
          return e
      else
        return e
    | none => return e
  | _ => return e

/-- Whether the constant `fn` may be head-unfolded in proposition position. -/
def canUnfoldConst (fn : Name) : CheckM Bool := do
  let some info := (← getEnv).find? fn | return false
  unless info matches .defnInfo _ do
    return false
  if (← getProjectionFnInfo? fn).isSome then
    return false
  if ← isIrreducible fn then
    return false
  if ← isInstance fn then
    return false
  if ← isMatcher fn then
    return false
  return true

/-- Unfold the head definition of `e` once, if permitted and fuel remains. -/
def unfoldHead? (e : Expr) : CheckM (Option Expr) := do
  let .const fn _ := e.getAppFn | return none
  unless ← canUnfoldConst fn do
    return none
  let s ← get
  if s.unfolds ≥ (← read).cfg.maxUnfolds then
    set { s with budgetExhausted := true }
    return none
  let r ← safely (withTransparency .default (unfoldDefinition? e)) none
  if r.isSome then
    modify fun s => { s with unfolds := s.unfolds + 1 }
  return r

/-- `x = t` or `t = x` with `x` not free in `t`: the term `t`. -/
def onePoint? (x : Expr) (c : Expr) : Option Expr :=
  match c.getAppFnArgs with
  | (``Eq, #[_, l, r]) =>
    if l == x && !r.containsFVar x.fvarId! then
      some r
    else if r == x && !l.containsFVar x.fvarId! then
      some l
    else
      none
  | _ => none

/-- Reflexivity of `≤` (or irreflexivity of `<`) for the instance at hand. -/
def relLawHolds (isLE : Bool) (rel α inst a : Expr) : CheckM Bool := do
  if α.isConstOf ``Nat &&
      inst.isConstOf (if isLE then ``instLENat else ``instLTNat) then
    return true
  let goal := mkApp4 rel α inst a a
  tryProve (if isLE then goal else mkNot goal) (← read).cfg.probeHeartbeats

/-- Propositional skeleton for exact bounded truth-table simplification. -/
inductive PropForm where
  | tt
  | ff
  | atom (idx : Nat)
  | not (a : PropForm)
  | and (a b : PropForm)
  | or (a b : PropForm)
  | imp (a b : PropForm)
  | iff (a b : PropForm)

def PropForm.eval (mask : Nat) : PropForm → Bool
  | .tt => true
  | .ff => false
  | .atom i => ((mask >>> i) &&& 1) == 1
  | .not a => !(a.eval mask)
  | .and a b => a.eval mask && b.eval mask
  | .or a b => a.eval mask || b.eval mask
  | .imp a b => !(a.eval mask) || b.eval mask
  | .iff a b => a.eval mask == b.eval mask

def PropForm.hasConnective : PropForm → Bool
  | .tt | .ff | .atom _ => false
  | _ => true

partial def parsePropForm (maxAtoms : Nat) (atomsRef : IO.Ref (Array Expr))
    (overflowRef : IO.Ref Bool) (cur : Expr) : CheckM PropForm := do
  if ← overflowRef.get then
    return .tt
  match cur.getAppFnArgs with
  | (``True, #[]) => return .tt
  | (``False, #[]) => return .ff
  | (``Not, #[a]) => return .not (← parsePropForm maxAtoms atomsRef overflowRef a)
  | (``And, #[a, b]) =>
    return .and (← parsePropForm maxAtoms atomsRef overflowRef a)
      (← parsePropForm maxAtoms atomsRef overflowRef b)
  | (``Or, #[a, b]) =>
    return .or (← parsePropForm maxAtoms atomsRef overflowRef a)
      (← parsePropForm maxAtoms atomsRef overflowRef b)
  | (``Iff, #[a, b]) =>
    return .iff (← parsePropForm maxAtoms atomsRef overflowRef a)
      (← parsePropForm maxAtoms atomsRef overflowRef b)
  | _ =>
    if let .forallE _ a b _ := cur then
      if !b.hasLooseBVars && (← safely (isProp a) false) then
        return .imp (← parsePropForm maxAtoms atomsRef overflowRef a)
          (← parsePropForm maxAtoms atomsRef overflowRef b)
    let atoms ← atomsRef.get
    if let some idx := atoms.idxOf? cur then
      return .atom idx
    if atoms.size ≥ maxAtoms then
      overflowRef.set true
      return .tt
    atomsRef.set (atoms.push cur)
    return .atom atoms.size

def rebuildPropForm (atoms : Array Expr) (irrelevant : Array Bool) :
    PropForm → CheckM Expr
  | .tt => return mkConst ``True
  | .ff => return mkConst ``False
  | .atom i =>
    return if irrelevant[i]! then mkConst ``True else atoms[i]!
  | .not a => do mkNotS (← rebuildPropForm atoms irrelevant a)
  | .and a b => do
    mkAndS (← rebuildPropForm atoms irrelevant a)
      (← rebuildPropForm atoms irrelevant b)
  | .or a b => do
    mkOrS (← rebuildPropForm atoms irrelevant a)
      (← rebuildPropForm atoms irrelevant b)
  | .imp a b => do
    mkImpS (← rebuildPropForm atoms irrelevant a)
      (← rebuildPropForm atoms irrelevant b)
  | .iff a b => do
    mkIffS (← rebuildPropForm atoms irrelevant a)
      (← rebuildPropForm atoms irrelevant b)

/--
Exact, 100%-sound propositional simplification over at most 10 distinct atomic
propositions: detects classical tautologies (`True`), contradictions (`False`),
and propositionally irrelevant atoms (absorption, dead branches, exhaustive
case splits, De Morgan, contraposition, Peirce's law), replacing irrelevant
atoms with `True` and re-simplifying.
-/
def propSimplify (e : Expr) : CheckM Expr := do
  let maxAtoms := 10
  let atomsRef ← IO.mkRef (#[] : Array Expr)
  let overflowRef ← IO.mkRef false
  let form ← parsePropForm maxAtoms atomsRef overflowRef e
  if (← overflowRef.get) || !form.hasConnective then
    return e
  let atoms ← atomsRef.get
  let k := atoms.size
  if k == 0 then
    return if form.eval 0 then mkConst ``True else mkConst ``False
  let total := 1 <<< k
  let mut vals : Array Bool := Array.mkEmpty total
  let mut allTrue := true
  let mut allFalse := true
  for mask in [0:total] do
    let v := form.eval mask
    vals := vals.push v
    if v then
      allFalse := false
    else
      allTrue := false
  if allTrue then
    noteDropped e
    return mkConst ``True
  if allFalse then
    noteDropped e
    return mkConst ``False
  let mut irrelevant : Array Bool := Array.replicate k false
  let mut anyIrrel := false
  for i in [0:k] do
    let bit := 1 <<< i
    let mut indep := true
    for mask in [0:total] do
      if (mask &&& bit) == 0 then
        if vals[mask]! != vals[mask ||| bit]! then
          indep := false
          break
    if indep then
      irrelevant := irrelevant.set! i true
      anyIrrel := true
  if !anyIrrel then
    return e
  for i in [0:k] do
    if irrelevant[i]! then
      noteDropped atoms[i]!
  rebuildPropForm atoms irrelevant form

/--
Rewrite `body` with the equations among the conjuncts of the hypothesis
`ante`: under `v = t` (with `v` a variable not in `t`), `C[v]` and `C[t]` are
equivalent, so `v = t → C[v]` may be judged as `v = t → C[t]`. Each candidate
replacement is kernel-typechecked before being accepted so dependent terms
such as `v : Fin n` under `n = 1` are never corrupted. An output variable is
eliminated in preference to an input, which exposes `ret = x → f ret = f x` as
a tautology.
-/
def substHypEqs (ante body : Expr) : CheckM Expr := do
  let outs := (← read).outputs
  let isOut (e : Expr) : Bool := e.isFVar && outs.contains e.fvarId!
  let tryRepl (cur v t : Expr) : CheckM Expr := do
    if !cur.containsFVar v.fvarId! then
      return cur
    let cand := cur.replaceFVar v t
    if ← safely (do check cand; return true) false then
      return cand
    return cur
  let mut body := body
  for c in conjuncts ante do
    if let (``Eq, #[_, l, r]) := c.getAppFnArgs then
      if isOut l && !r.containsFVar l.fvarId! then
        body ← tryRepl body l r
      else if isOut r && !l.containsFVar r.fvarId! then
        body ← tryRepl body r l
      else if l.isFVar && !r.containsFVar l.fvarId! then
        body ← tryRepl body l r
      else if r.isFVar && !l.containsFVar r.fvarId! then
        body ← tryRepl body r l
  return body

/-- Whether some conjunct of `ante` is an equation `substHypEqs` can use. -/
def hasHypEq (ante : Expr) : Bool :=
  (conjuncts ante).any fun c =>
    match c.getAppFnArgs with
    | (``Eq, #[_, l, r]) =>
      (l.isFVar && !r.containsFVar l.fvarId!) ||
        (r.isFVar && !l.containsFVar r.fvarId!)
    | _ => false

/-- Number of designated outputs occurring in `e`. -/
def outputCount (e : Expr) : CheckM Nat := do
  let outs := (← read).outputs
  return (outs.filter fun o => e.containsFVar o).size

/--
Unfold a matcher application into its case tree (nested `casesOn`), with every
beta-redex contracted. A `match` on several discriminants, or with nested
patterns, is stuck as a whole when only *some* discriminant is a constructor;
its case tree is not, and reduces on that discriminant.
-/
def unfoldMatcher? (e : Expr) : CheckM (Option Expr) := do
  let .const n lvls := e.getAppFn | return none
  unless ← isMatcher n do
    return none
  let some info := (← getEnv).find? n | return none
  let some val := info.value? | return none
  let s ← get
  if s.unfolds ≥ (← read).cfg.maxUnfolds then
    set { s with budgetExhausted := true }
    return none
  set { s with unfolds := s.unfolds + 1 }
  let tree := (val.instantiateLevelParams info.levelParams lvls).beta e.getAppArgs
  return some (← safely (Core.betaReduce tree) tree)

mutual

/--
Normalise the proposition `e` to an equivalent residual, with `True` and
`False` as the canonical trivial results. Boilerplate stripping is restricted
strictly to positive conjunctive positions so negated boilerplate cannot
falsely annihilate a genuine postcondition.
-/
partial def simpProp (e : Expr) : CheckM Expr := do
  unless ← tick do
    return e
  let e ← headReduce e
  match e.getAppFnArgs with
  | (``True, #[]) | (``False, #[]) => return e
  | (``And, #[a, b]) => mkAndS (← simpProp a) (← simpProp b)
  | (``Or, #[a, b]) =>
    withoutBoilerplate do
      let res ← mkOrS (← simpProp a) (← simpProp b)
      let ds := disjuncts res
      if ds.size ≤ 1 then
        return res
      -- Classical disjunctive congruence: `(¬E₁ ∨ … ∨ ¬Eₘ) ∨ D` is equivalent
      -- to rewriting each `¬Eᵢ` only by earlier `Eⱼ` (`j < i`, avoiding
      -- circularity) and rewriting non-equation disjuncts `D` by all `E₁..Eₘ`.
      let mut eqDisjs : Array (Expr × Expr) := #[]
      let mut otherDisjs : Array Expr := #[]
      for d in ds do
        match d.getAppFnArgs with
        | (``Not, #[inner]) =>
          if hasHypEq inner then
            eqDisjs := eqDisjs.push (d, inner)
          else
            otherDisjs := otherDisjs.push d
        | _ => otherDisjs := otherDisjs.push d
      if eqDisjs.isEmpty then
        return res
      let mut acc := mkConst ``False
      let mut changed := false
      let mut priorEqs : Array Expr := #[]
      for (d, inner) in eqDisjs do
        if priorEqs.isEmpty then
          acc ← mkOrS acc d
        else
          let d' ← substHypEqs (mkAndN priorEqs) d
          if d' != d then
            changed := true
            acc ← mkOrS acc (← simpProp d')
          else
            acc ← mkOrS acc d
        if isTrueConst acc then
          return acc
        priorEqs := priorEqs.push inner
      let allAnte := mkAndN priorEqs
      for d in otherDisjs do
        let d' ← substHypEqs allAnte d
        if d' != d then
          changed := true
          acc ← mkOrS acc (← simpProp d')
        else
          acc ← mkOrS acc d
        if isTrueConst acc then
          return acc
      return if changed then acc else res
  | (``Not, #[a]) =>
    withoutBoilerplate do mkNotS (← simpProp a)
  | (``Iff, #[a, b]) =>
    withoutBoilerplate do mkIffS (← simpProp a) (← simpProp b)
  | (``Eq, #[α, a, b]) => withoutBoilerplate (simpEq e α a b)
  | (``Ne, #[α, a, b]) => withoutBoilerplate do mkNotS (← simpEq e α a b)
  | (``HEq, #[α, a, β, b]) =>
    withoutBoilerplate do
      if ← sameExpr α β then
        simpEq e α a b
      else
        normData e
  | (``Exists, #[α, p]) => simpExists α p
  | (``LE.le, #[α, inst, a, b]) =>
    withoutBoilerplate (simpRel true e.getAppFn α inst a b)
  | (``LT.lt, #[α, inst, a, b]) =>
    withoutBoilerplate (simpRel false e.getAppFn α inst a b)
  | (``GE.ge, #[α, inst, a, b]) =>
    withoutBoilerplate
      (simpRel true (mkConst ``LE.le e.getAppFn.constLevels!) α inst b a)
  | (``GT.gt, #[α, inst, a, b]) =>
    withoutBoilerplate
      (simpRel false (mkConst ``LT.lt e.getAppFn.constLevels!) α inst b a)
  | (``ite, #[α, c, _, t, f]) =>
    if ← isPropSort α then
      let c' ← withoutBoilerplate (simpProp c)
      -- An equation in the condition rewrites the `then` branch.
      let t' ← simpProp (← substHypEqs c' t)
      simpIte c' t' (← simpProp f)
    else
      withoutBoilerplate (normData e)
  | (``cond, #[α, c, t, f]) =>
    if ← isPropSort α then
      simpIte (← withoutBoilerplate (boolToProp c)) (← simpProp t) (← simpProp f)
    else
      withoutBoilerplate (normData e)
  | (``dite, #[α, c, _, t, f]) =>
    if ← isPropSort α then
      let branch (dom fn : Expr) : Expr :=
        .forallE `h dom ((fn.liftLooseBVars 0 1).beta #[.bvar 0]) .default
      mkAndS (← simpProp (branch c t)) (← simpProp (branch (mkNot c) f))
    else
      withoutBoilerplate (normData e)
  | _ =>
    if e.isForall then
      return ← simpForall e
    if let some r ← collapseMatch? true e then
      return r
    if let .const fn _ := e.getAppFn then
      let ctx ← read
      if ctx.cfg.boilerplate.contains fn then
        modify fun s => { s with sawBoilerplate := true }
        if ctx.stripBoilerplate then
          -- Kept opaque: neither unfolded nor rewritten until cofactoring.
          return ← normData e
    match ← unfoldHead? e with
    | some e' => simpProp e'
    | none => withoutBoilerplate (normData e)

/-- `if c then t else f` on propositions: `(c → t) ∧ (¬c → f)`. -/
partial def simpIte (c t f : Expr) : CheckM Expr := do
  if ← sameExpr t f then
    noteDropped c
    return t
  mkAndS (← mkImpS c t) (← mkImpS (← mkNotS c) f)

partial def simpRel (isLE : Bool) (rel α inst a b : Expr) : CheckM Expr := do
  let a ← normData a
  let b ← normData b
  let e := mkApp4 rel α inst a b
  if ← sameExpr a b then
    if ← relLawHolds isLE rel α inst a then
      noteDropped e
      return mkConst (if isLE then ``True else ``False)
  return e

/--
Equation `a = b` at type `α`; `orig` is the proposition it came from, used only
to attribute a discarded tautology.
-/
partial def simpEq (orig α a b : Expr) : CheckM Expr := do
  if ← isPropSort α then
    return ← mkIffS (← simpProp a) (← simpProp b)
  let a ← normData a
  let b ← normData b
  if ← sameExpr a b then
    noteDropped orig
    return mkConst ``True
  let αn ← safely (whnfR α) α
  if ← typeSubsingleton αn false 0 then
    noteDropped orig
    return mkConst ``True
  if αn.isConstOf ``Bool then
    return ← simpBoolEq a b
  -- Numerals are compared by value at `Nat` only: at `Fin n` or a machine
  -- integer type two distinct literals may denote the same element.
  if αn.isConstOf ``Nat then
    let lit? (e : Expr) : Option Nat := e.rawNatLit? <|> e.nat?
    if let (some m, some n) := (lit? a, lit? b) then
      return mkConst (if m == n then ``True else ``False)
  -- Constructor disjointness and injectivity, at an inductive type in `Type`.
  let (a, ca?) ← exposeCtor αn a
  let (b, cb?) ← exposeCtor αn b
  if let (some (ca, as), some (cb, bs)) := (ca?, cb?) then
    if ca.name != cb.name then
      noteDropped orig
      return mkConst ``False
    let numIndices ← safely (do
      return (← getConstInfoInduct ca.induct).numIndices) 1
    if numIndices == 0 && as.size == bs.size then
      let mut acc := mkConst ``True
      let mut ok := true
      for i in [ca.numParams:as.size] do
        let x := as[i]!
        let y := bs[i]!
        if ← safely (isProof x) false then
          continue
        let tx ← safely (inferType x) x
        let ty ← safely (inferType y) y
        unless ← sameExpr tx ty do
          ok := false
          break
        acc ← mkAndS acc (← simpEq (← safely (mkEq x y) orig) tx x y)
      if ok then
        return acc
  -- Orient the equation canonically, so that `a = b` and `b = a` coincide.
  if b.lt a then
    safely (mkEq b a) orig
  else
    safely (mkEq a b) orig

/--
The constructor application `e` is, at the inductive type `α`. A term that
mentions an output and is headed by an unfoldable definition is evaluated to
weak head normal form first (within the proof-search heartbeat budget), so that
a helper applied to a constructor, such as a projection out of `.returned v m`,
exposes its result.
-/
partial def exposeCtor (α e : Expr) :
    CheckM (Expr × Option (ConstructorVal × Array Expr)) := do
  let ofType (r : Option (ConstructorVal × Array Expr)) :
      Option (ConstructorVal × Array Expr) :=
    r.filter fun (cv, _) => α.getAppFn.isConstOf cv.induct
  if ← safely (isProp α) true then
    return (e, none)
  if let some r := ofType (← safely (constructorApp? e) none) then
    return (e, some r)
  let .const fn _ := e.getAppFn | return (e, none)
  -- Arithmetic helpers are left to the proof search; structured data (lists,
  -- options, `Value`s) is evaluated on either side of an equation.
  let arith := α.isConstOf ``Nat || α.isConstOf ``Int
  unless (!arith || (← mentionsOutput e)) && (← canUnfoldConst fn) do
    return (e, none)
  let budget := (← read).cfg.probeHeartbeats * 1000
  let e' ← safely
    (withCurrHeartbeats <|
      withTheReader Core.Context (fun c => { c with maxHeartbeats := budget }) <|
        withTransparency .default (whnf e)) e
  match ofType (← safely (constructorApp? e') none) with
  | some r => return (← normData e', some r)
  | none => return (e, none)

/-- Equation between two Boolean terms. -/
partial def simpBoolEq (a b : Expr) : CheckM Expr := do
  let lit? (e : Expr) : Option Bool :=
    if e.isConstOf ``Bool.true then some true
    else if e.isConstOf ``Bool.false then some false
    else none
  match lit? a, lit? b with
  | some x, some y => return mkConst (if x == y then ``True else ``False)
  | none, some true => boolToProp a
  | none, some false => mkNotS (← boolToProp a)
  | some true, none => boolToProp b
  | some false, none => mkNotS (← boolToProp b)
  | none, none => mkIffS (← boolToProp a) (← boolToProp b)

/-- A proposition equivalent to `b = true`, for a Boolean term `b`. -/
partial def boolToProp (b : Expr) : CheckM Expr := do
  unless ← tick do
    return ← safely (mkEq b (mkConst ``Bool.true)) b
  let b ← headReduce b
  match b.getAppFnArgs with
  | (``Bool.true, #[]) => return mkConst ``True
  | (``Bool.false, #[]) => return mkConst ``False
  | (``and, #[x, y]) => mkAndS (← boolToProp x) (← boolToProp y)
  | (``or, #[x, y]) => mkOrS (← boolToProp x) (← boolToProp y)
  | (``not, #[x]) => mkNotS (← boolToProp x)
  | (``Decidable.decide, #[p, _]) => simpProp p
  | (``BEq.beq, #[α, inst, x, y]) =>
    if ← hasBEqLaw ``LawfulBEq α inst then
      simpEq (← safely (mkEq x y) b) α x y
    else
      let x ← normData x
      let y ← normData y
      let atom ← safely (mkEq (mkApp4 b.getAppFn α inst x y)
        (mkConst ``Bool.true)) b
      if (← sameExpr x y) && (← hasBEqLaw ``ReflBEq α inst) then
        noteDropped atom
        return mkConst ``True
      return atom
  | (``bne, #[α, inst, x, y]) =>
    mkNotS (← boolToProp
      (mkApp4 (mkConst ``BEq.beq b.getAppFn.constLevels!) α inst x y))
  | (``Nat.ble, #[x, y]) => simpProp (mkNatLE x y)
  | (``Nat.blt, #[x, y]) =>
    simpProp (mkApp4 (mkConst ``LT.lt [Level.zero]) (mkConst ``Nat)
      (mkConst ``instLTNat) x y)
  | (``Nat.beq, #[x, y]) =>
    simpEq (mkNatEq x y) (mkConst ``Nat) x y
  | (``ite, #[_, c, _, t, f]) =>
    simpIte (← simpProp c) (← boolToProp t) (← boolToProp f)
  | (``cond, #[_, c, t, f]) =>
    simpIte (← boolToProp c) (← boolToProp t) (← boolToProp f)
  | _ =>
    if let .const fn _ := b.getAppFn then
      let ctx ← read
      if ctx.cfg.boilerplate.contains fn then
        modify fun s => { s with sawBoilerplate := true }
        if ctx.stripBoilerplate then
          let b ← normData b
          return ← safely (mkEq b (mkConst ``Bool.true)) b
    -- A Boolean-valued definition is a predicate: unfold it at the head.
    if let some b' ← unfoldHead? b then
      return ← boolToProp b'
    -- A Boolean helper applied to constructors evaluates by `whnf`.
    let b' ← safely (withTransparency .default (whnf b)) b
    if b'.isConstOf ``Bool.true then
      noteDropped b
      return mkConst ``True
    if b'.isConstOf ``Bool.false then
      noteDropped b
      return mkConst ``False
    let b ← normData b
    safely (mkEq b (mkConst ``Bool.true)) b

partial def simpExists (α p : Expr) : CheckM Expr := do
  let αIsProp ← safely (isProp α) false
  let α ← if αIsProp then pure α else withoutBoilerplate (normData α)
  -- Curry `Prod` / `PProd` / `Subtype` existentials so one-point rules see
  -- projections (`∃ p : α × β, p.1 = r`, `∃ _ : { y // y = r }, True`).
  if !αIsProp then
    let αn ← safely (whnfR α) α
    match αn.getAppFnArgs with
    | (``Prod, #[α₁, α₂]) | (``PProd, #[α₁, α₂]) =>
      let mkName :=
        if αn.getAppFn.isConstOf ``Prod then ``Prod.mk else ``PProd.mk
      let lvls := αn.getAppFn.constLevels!
      if let some curried ← safely (do
          withLocalDeclD `a α₁ fun a =>
          withLocalDeclD `b α₂ fun b => do
            let pair := mkApp4 (mkConst mkName lvls) α₁ α₂ a b
            let inner ← mkAppM ``Exists #[← mkLambdaFVars #[b] (p.beta #[pair])]
            return some (← mkLambdaFVars #[a] inner)) none then
        return ← simpExists α₁ curried
    | (``Subtype, #[β, pred]) =>
      let lvls := αn.getAppFn.constLevels!
      if let some curried ← safely (do
          withLocalDeclD `a β fun a =>
          withLocalDeclD `h (pred.beta #[a]) fun h => do
            let sub := mkApp4 (mkConst ``Subtype.mk lvls) β pred a h
            let inner ← mkAppM ``Exists #[← mkLambdaFVars #[h] (p.beta #[sub])]
            return some (← mkLambdaFVars #[a] inner)) none then
        return ← simpExists β curried
    | _ => pure ()
  let name := if let .lam n .. := p then n else `x
  withLocalDeclD name α fun x => do
    let body ← propSimplify (← simpProp (p.beta #[x]))
    if isFalseConst body then
      return body
    let cs := conjuncts body
    for i in [0:cs.size] do
      if let some t := onePoint? x cs[i]! then
        let rest := mkAndN (cs.eraseIdxIfInBounds i)
        let cand := rest.replaceFVar x t
        if ← safely (do check cand; return true) false then
          unless rest.containsFVar x.fvarId! do
            noteDropped cs[i]!
          return ← simpProp cand
    if !body.containsFVar x.fvarId! then
      if αIsProp then
        return ← mkAndS (← withoutBoilerplate (simpProp α)) body
      if ← typeNonempty α then
        return body
    safely (do mkAppM ``Exists #[← mkLambdaFVars #[x] body])
      (mkApp2 (mkConst ``Exists [Level.one]) α p)

partial def simpForall (e : Expr) : CheckM Expr := do
  let .forallE name dom body bi := e | return e
  let domIsProp ← safely (isProp dom) false
  if domIsProp && !body.hasLooseBVars then
    let ante ← withoutBoilerplate (simpProp dom)
    -- Equations among the premises rewrite the conclusion.
    let body ← if hasHypEq ante then substHypEqs ante body else pure body
    return ← mkImpS ante (← simpProp body)
  let dom ← if domIsProp then pure dom else withoutBoilerplate (normData dom)
  withLocalDecl name bi dom fun x => do
    let body ← propSimplify (← simpProp (body.instantiate1 x))
    if isTrueConst body then
      return body
    if !body.containsFVar x.fvarId! then
      if domIsProp then
        return ← mkImpS (← withoutBoilerplate (simpProp dom)) body
      if ← typeNonempty dom then
        return body
      return mkForall name bi dom body
    -- One-point rule: `∀ x, x = t ∧ A → C` is `A[t/x] → C[t/x]`.
    if let .forallE _ ante cons _ := body then
      if !cons.hasLooseBVars then
        let cs := conjuncts ante
        for i in [0:cs.size] do
          if let some t := onePoint? x cs[i]! then
            let ante' := mkAndN (cs.eraseIdxIfInBounds i)
            let body' := mkForall `h .default ante' cons
            let cand := body'.replaceFVar x t
            if ← safely (do check cand; return true) false then
              unless body'.containsFVar x.fvarId! do
                noteDropped cs[i]!
              return ← simpProp cand
    mkForallFVars #[x] body

/--
A `match` (or `casesOn`) with a non-dependent motive that is stuck on its
discriminants: normalise the discriminants (which may unblock it), then each
alternative under its exact `altNumParams` pattern variables (never peeling
binders from a function-valued motive return type), and collapse the whole
`match` (including curried applications with non-empty `remaining`) when all
alternatives reduce to one pattern-variable-independent term.
-/
partial def collapseMatch? (propLevel : Bool) (e : Expr) :
    CheckM (Option Expr) := do
  let some app ← safely (matchMatcherApp? e (alsoCasesOn := true)) none
    | return none
  let motiveOk ← lambdaTelescope app.motive fun xs body =>
    pure !(xs.any fun x => body.containsFVar x.fvarId!)
  unless motiveOk do
    return none
  let discrs ← withoutBoilerplate (app.discrs.mapM normData)
  let remaining ← withoutBoilerplate (app.remaining.mapM normData)
  let app := { app with discrs, remaining }
  let e' := app.toExpr
  let e'' ← headReduce e'
  if e'' != e' then
    return some (← if propLevel then simpProp e'' else normData e'')
  let mut alts : Array Expr := #[]
  let mut common? : Option Expr := none
  let mut collapsible := true
  for i in [0:app.alts.size] do
    let alt := app.alts[i]!
    let numParams := app.altNumParams[i]!
    let altTy ← inferType alt
    let (alt', body?) ← forallBoundedTelescope altTy (some numParams) fun ys _ => do
      let rawBody := (alt.beta ys).beta remaining
      let body ←
        if propLevel then
          propSimplify (← simpProp rawBody)
        else
          normData rawBody
      let indep := !(ys.any fun y => body.containsFVar y.fvarId!)
      let rebuilt ←
        if remaining.isEmpty then
          mkLambdaFVars ys body
        else
          pure alt
      return (rebuilt, if indep then some body else none)
    alts := alts.push alt'
    match body?, common? with
    | none, _ => collapsible := false
    | some b, none => common? := some b
    | some b, some c =>
      unless ← sameExpr b c do
        collapsible := false
  if collapsible then
    if let some c := common? then
      for d in app.discrs do
        noteDropped d
      return some c
  let rebuilt? :=
    if remaining.isEmpty then some ({ app with alts := alts }).toExpr else none
  -- Alternative by alternative the `match` does not collapse. When it scrutinises
  -- an output, judge its case tree as well: a constructor discriminant selects a
  -- subtree there even if another discriminant, or a nested pattern, is stuck.
  if (← isMatcher app.matcherName) && (← app.discrs.anyM mentionsOutput) then
    if let some tree ← unfoldMatcher? e' then
      let saved ← get
      let treeRes ←
        if propLevel then propSimplify (← simpProp tree) else normData tree
      if (← outputCount treeRes) < (← outputCount (rebuilt?.getD e')) then
        return some treeRes
      let now ← get
      set { saved with steps := now.steps, unfolds := now.unfolds,
                       budgetExhausted := now.budgetExhausted }
  -- Still stuck and still mentioning an output: split on what it is stuck on.
  if (← read).splitFuel > 0 && (← outputCount (rebuilt?.getD e')) > 0 then
    if let some c ← splitStuckMatch propLevel e' app.discrs then
      return some c
  return rebuilt?

/--
Case split on what a stuck `match` scrutinises. The candidates are its
discriminants that are not constructor applications (`req.args` in
`match ans, req.args with …` once `ans` is `.returned v m`), then the variables
under the constructors of the others (`v` in a nested pattern on
`.returned v m`). If, for one candidate of an inductive type with two to eight
constructors, the `match` normalises at every constructor (applied to fresh
fields) to one and the same term free of the fields, the `match` is that term.
The split is depth-bounded by `splitFuel`, so `[_]` against a list is reached.
-/
partial def splitStuckMatch (propLevel : Bool) (e : Expr) (discrs : Array Expr) :
    CheckM (Option Expr) := do
  let mut stuck : Array Expr := #[]
  let mut nested : Array Expr := #[]
  for d in discrs do
    match ← safely (constructorApp? d) none with
    | none => stuck := stuck.push d
    | some (cv, args) =>
      for a in args.extract cv.numParams args.size do
        if a.isFVar then
          nested := nested.push a
  for d in (stuck ++ nested).extract 0 4 do
    let saved ← get
    if let some c ← splitOn d then
      noteDropped d
      return some c
    let now ← get
    set { saved with steps := now.steps, unfolds := now.unfolds,
                     budgetExhausted := now.budgetExhausted }
  return none
where
  splitOn (d : Expr) : CheckM (Option Expr) := do
    let some ty ← safely (do return some (← whnf (← inferType d))) none
      | return none
    let .const indName lvls := ty.getAppFn | return none
    let some (.inductInfo ind) := (← getEnv).find? indName | return none
    if ind.numIndices != 0 || ind.ctors.length < 2 || ind.ctors.length > 8 then
      return none
    if ← safely (isProp ty) true then
      return none
    let mut common? : Option Expr := none
    for ctorName in ind.ctors do
      let ctor := mkAppN (mkConst ctorName lvls) ty.getAppArgs
      let some ctorTy ← safely (do return some (← inferType ctor)) none
        | return none
      if (← ctorFieldInfo ctor).1 then
        continue
      let r? ← forallTelescopeReducing ctorTy fun fields _ => do
        let inst := e.replace fun sub =>
          if sub == d then some (mkAppN ctor fields) else none
        unless ← safely (do check inst; return true) false do
          return none
        let res ← withReader (fun c => { c with splitFuel := c.splitFuel - 1 }) do
          if propLevel then propSimplify (← simpProp inst) else normData inst
        if fields.any (fun f => res.containsFVar f.fvarId!) then
          return none
        return some res
      match r?, common? with
      | none, _ => return none
      | some r, none => common? := some r
      | some r, some c =>
        unless ← sameExpr r c do
          return none
    return common?

/--
Normalise a term that is not (known to be) a proposition: beta, zeta, eta,
projections and iota everywhere, `decide`/`ite`/`cond`/`dite` on a decided
condition, and collapse of stuck constant `match`es. Definitions are not
unfolded.
-/
partial def normData (e : Expr) : CheckM Expr := do
  unless ← tick do
    return e
  let pre (e : Expr) : CheckM TransformStep := do
    unless ← tick do
      return .done e
    match e with
    | .mdata _ b => return .visit b
    | .letE .. | .proj .. =>
      let e' ← headReduce e
      return if e' == e then .continue else .visit e'
    | .app .. =>
      if e.getAppFn.isLambda then
        return .visit e.headBeta
      match e.getAppFnArgs with
      | (``Decidable.decide, #[p, _]) =>
        let p' ← withoutBoilerplate (simpProp p)
        if isTrueConst p' then
          return .done (mkConst ``Bool.true)
        if isFalseConst p' then
          return .done (mkConst ``Bool.false)
        return .continue
      | (``ite, #[_, c, _, t, f]) =>
        let c' ← withoutBoilerplate (simpProp c)
        if isTrueConst c' then
          return .visit t
        if isFalseConst c' then
          return .visit f
        if ← sameExpr t f then
          noteDropped c
          return .visit t
        return .continue
      | (``cond, #[_, c, t, f]) =>
        let c' ← withoutBoilerplate (boolToProp c)
        if isTrueConst c' then
          return .visit t
        if isFalseConst c' then
          return .visit f
        if ← sameExpr t f then
          noteDropped c
          return .visit t
        return .continue
      | (``dite, #[_, c, _, t, f]) =>
        let c' ← withoutBoilerplate (simpProp c)
        let indepBody? (fn : Expr) : Option Expr :=
          match fn with
          | .lam _ _ b _ => if !b.hasLooseBVars then some b else none
          | _ => none
        if isTrueConst c' then
          if let some tb := indepBody? t then
            return .visit tb
        if isFalseConst c' then
          if let some fb := indepBody? f then
            return .visit fb
        if let (some tb, some fb) := (indepBody? t, indepBody? f) then
          if ← sameExpr tb fb then
            noteDropped c
            return .visit tb
        return .continue
      | _ =>
        let e' ← headReduce e
        if e' != e then
          return .visit e'
        match ← collapseMatch? false e with
        | some r => return .done r
        | none => return .continue
    | _ => return .continue
  Meta.transform e (pre := pre) (post := fun e => pure (.done e.eta))

end

/-- Outcome of normalising one postcondition instance. -/
structure BodyAnalysis where
  residual : Expr
  /-- Per designated output: is it genuinely constrained? -/
  bound : Array Bool
  state : State
  /-- The proof search proved the residual insensitive to some output. -/
  provedInsensitive : Bool := false
  /-- Set when an output is unbound only relative to the precondition. -/
  requiresReason? : Option EnsuresVacuityReason := none
  /--
  Cofactoring over the boilerplate atoms was abandoned (too many atoms or
  cofactors, or an ill-typed cofactor): the user-`ensures` verdict is the
  conservative *binds*.
  -/
  cofactorIncomplete : Bool := false

def BodyAnalysis.anyBound (a : BodyAnalysis) : Bool := a.bound.any id

partial def probeSubPropsGo (cfg : EnsuresCheckConfig)
    (mentions : Expr → Bool) (small : Expr → Bool)
    (budgetRef : IO.Ref Nat) (changedRef : IO.Ref Bool) (cur : Expr) :
    MetaM Expr := do
  let tryLeaf (sub : Expr) : MetaM (Option Expr) := do
    if !mentions sub || !small sub then
      return none
    let rem ← budgetRef.get
    if rem == 0 then
      return none
    budgetRef.set (rem - 1)
    if ← tryProve sub cfg.probeHeartbeats then
      changedRef.set true
      return some (mkConst ``True)
    if ← tryProve (mkNot sub) cfg.probeHeartbeats then
      changedRef.set true
      return some (mkConst ``False)
    return none
  if (← budgetRef.get) == 0 || !mentions cur then
    return cur
  match cur.getAppFnArgs with
  | (``And, #[a, b]) =>
    let a' ← probeSubPropsGo cfg mentions small budgetRef changedRef a
    let b' ← probeSubPropsGo cfg mentions small budgetRef changedRef b
    if a' == a && b' == b then return cur else return mkApp2 (mkConst ``And) a' b'
  | (``Or, #[a, b]) =>
    if let some r ← tryLeaf cur then
      return r
    let a' ← probeSubPropsGo cfg mentions small budgetRef changedRef a
    let b' ← probeSubPropsGo cfg mentions small budgetRef changedRef b
    if a' == a && b' == b then return cur else return mkApp2 (mkConst ``Or) a' b'
  | (``Not, #[a]) =>
    let a' ← probeSubPropsGo cfg mentions small budgetRef changedRef a
    if a' == a then return cur else return mkNot a'
  | (``Iff, #[a, b]) =>
    if let some r ← tryLeaf cur then
      return r
    let a' ← probeSubPropsGo cfg mentions small budgetRef changedRef a
    let b' ← probeSubPropsGo cfg mentions small budgetRef changedRef b
    if a' == a && b' == b then return cur else return mkApp2 (mkConst ``Iff) a' b'
  | _ =>
    if let .forallE n a b bi := cur then
      if !b.hasLooseBVars && (← safely (isProp a) false) then
        if let some r ← tryLeaf cur then
          return r
        let a' ← probeSubPropsGo cfg mentions small budgetRef changedRef a
        let b' ← probeSubPropsGo cfg mentions small budgetRef changedRef b
        if a' == a && b' == b then return cur else return mkForall n bi a' b'
    if let some r ← tryLeaf cur then
      return r
    return cur

/--
Recursively probe strict output-mentioning subformulas of compound (`Or`,
`Not`, `Iff`, implication) conjuncts, replacing any proved tautology by `True`
and any proved contradiction by `False`. Top-level atomic conjuncts are skipped
because the conjunct loop already tested them. Capped at 16 tactic calls.
-/
def probeSubProps (cfg : EnsuresCheckConfig)
    (mentions : Expr → Bool) (small : Expr → Bool) (e : Expr) :
    MetaM (Expr × Bool) := do
  let budgetRef ← IO.mkRef (16 : Nat)
  let changedRef ← IO.mkRef false
  let probeConjunct (c : Expr) : MetaM Expr := do
    if (← budgetRef.get) == 0 || !mentions c then
      return c
    match c.getAppFnArgs with
    | (``Or, #[a, b]) =>
      let a' ← probeSubPropsGo cfg mentions small budgetRef changedRef a
      let b' ← probeSubPropsGo cfg mentions small budgetRef changedRef b
      if a' == a && b' == b then return c else return mkApp2 (mkConst ``Or) a' b'
    | (``Not, #[a]) =>
      let a' ← probeSubPropsGo cfg mentions small budgetRef changedRef a
      if a' == a then return c else return mkNot a'
    | (``Iff, #[a, b]) =>
      let a' ← probeSubPropsGo cfg mentions small budgetRef changedRef a
      let b' ← probeSubPropsGo cfg mentions small budgetRef changedRef b
      if a' == a && b' == b then return c else return mkApp2 (mkConst ``Iff) a' b'
    | _ =>
      if let .forallE n a b bi := c then
        if !b.hasLooseBVars && (← safely (isProp a) false) then
          let a' ← probeSubPropsGo cfg mentions small budgetRef changedRef a
          let b' ← probeSubPropsGo cfg mentions small budgetRef changedRef b
          if a' == a && b' == b then return c else return mkForall n bi a' b'
      return c
  let cs := conjuncts e
  let mut out : Array Expr := #[]
  for c in cs do
    out := out.push (← probeConjunct c)
  return (mkAndN out, ← changedRef.get)

partial def scanSmallOutputHelpers (cfg : EnsuresCheckConfig)
    (mentions : Expr → Bool) (helpersRef : IO.Ref (Array Name)) (cur : Expr) :
    MetaM Unit := do
  if (← helpersRef.get).size ≥ 8 then
    return
  let env ← getEnv
  match cur with
  | .app .. =>
    let fn := cur.getAppFn
    let args := cur.getAppArgs
    if let .const n _ := fn then
      if args.any mentions && !(← helpersRef.get).contains n then
        if let some (.defnInfo d) := env.find? n then
          let eligible ←
            if d.safety != .safe || cfg.boilerplate.contains n ||
                cfg.opaqueStructTypes.contains n ||
                d.value.getUsedConstants.contains n ||
                sizeUpTo 65 d.value > 64 then
              pure false
            else if (← getProjectionFnInfo? n).isSome ||
                (← isIrreducible n) || (← isInstance n) || (← isMatcher n) then
              pure false
            else
              let mut ok := true
              for a in args do
                let ty ← safely (do whnf (← inferType a)) (mkConst ``Unit)
                if let .const tn _ := ty.getAppFn then
                  if cfg.opaqueStructTypes.contains tn then
                    ok := false
                    break
              pure ok
          if eligible then
            helpersRef.modify (·.push n)
    for a in args do
      scanSmallOutputHelpers cfg mentions helpersRef a
  | .lam _ d b _ | .forallE _ d b _ =>
    scanSmallOutputHelpers cfg mentions helpersRef d
    scanSmallOutputHelpers cfg mentions helpersRef b
  | .letE _ t v b _ =>
    scanSmallOutputHelpers cfg mentions helpersRef t
    scanSmallOutputHelpers cfg mentions helpersRef v
    scanSmallOutputHelpers cfg mentions helpersRef b
  | .mdata _ b | .proj _ _ b =>
    scanSmallOutputHelpers cfg mentions helpersRef b
  | _ => pure ()

/--
Collect small, non-recursive, non-opaque helper definitions applied to an
argument mentioning an output in `e`, and unfold them once so the semantic
probe can see through data-level disguises like `constZeroHelper r < x`.
-/
def unfoldSmallOutputHelpers (cfg : EnsuresCheckConfig)
    (mentions : Expr → Bool) (e : Expr) : MetaM (Option Expr) := do
  let helpersRef ← IO.mkRef (#[] : Array Name)
  scanSmallOutputHelpers cfg mentions helpersRef e
  let helpers ← helpersRef.get
  if helpers.isEmpty then
    return none
  let unfolded ← Meta.transform e (pre := fun cur => do
    if let .const n _ := cur.getAppFn then
      if helpers.contains n then
        if let some u ← safely (withTransparency .default (unfoldDefinition? cur)) none then
          return .visit u
    return .continue)
  if unfolded == e then
    return none
  return some unfolded

/--
Case split on the output `outputs[i]` of an inductive type with between two
and eight constructors (`Option`, `Bool`, `Value`, `List`, a user enumeration):
when `body`, instantiated at every constructor applied to fresh fields,
normalises to one and the same proposition that mentions neither the fields nor
the output, the postcondition is that proposition, and the output is not bound.
This is the outcome analysis of `MirCallAns`, for any inductive output; it sees
exhaustive disjunctions such as `r = none ∨ ∃ v, r = some v`. The instances
are judged by the syntactic pass alone and kernel-typechecked before reduction.
Constructors with a field of an empty type are skipped: no output is built
from them (`some` at `Option Empty`).
-/
def caseSplitOutput (cfg : EnsuresCheckConfig)
    (outputs : Array Expr) (i : Nat) (body : Expr) : MetaM (Option Expr) :=
  safely (do
    let o := outputs[i]!
    let ty ← whnf (← inferType o)
    let .const indName lvls := ty.getAppFn | return none
    if indName == ``Nat || indName == ``Int then
      return none
    let some (.inductInfo ind) := (← getEnv).find? indName | return none
    if ind.numIndices != 0 || ind.ctors.length < 2 || ind.ctors.length > 8 then
      return none
    if ← isProp ty then
      return none
    let others := (outputs.extract 0 i) ++ (outputs.extract (i + 1) outputs.size)
    let syntactic := { cfg with semanticProbe := false }
    let mut common? : Option Expr := none
    for ctorName in ind.ctors do
      let ctor := mkAppN (mkConst ctorName lvls) ty.getAppArgs
      -- A constructor with a field of an empty type builds no output.
      if (← ctorFieldInfo ctor).1 then
        continue
      let r? ← forallTelescopeReducing (← inferType ctor) fun fields _ => do
        let inst := body.replaceFVar o (mkAppN ctor fields)
        unless ← safely (do check inst; return true) false do
          return none
        let ctx : Context :=
          { cfg := syntactic
            outputs := (others ++ fields).map Expr.fvarId!
            stripBoilerplate := false }
        let (r, _) ← ((do propSimplify (← simpProp inst)).run ctx).run {}
        if fields.any (fun f => r.containsFVar f.fvarId!) ||
            r.containsFVar o.fvarId! then
          return none
        return some r
      match r?, common? with
      | none, _ => return none
      | some r, none => common? := some r
      | some r, some c =>
        unless r == c do
          return none
    return common?) none

/--
Normalise `body` with `outputs` designated, simplify propositionally, then let
the proof search discharge output-mentioning subformulas and test insensitivity
and subsingleton types output by output (and, when `hyp?` is present, relative
to the precondition).
-/
def analyzeBody (cfg : EnsuresCheckConfig)
    (outputs : Array Expr) (body : Expr) (hyp? : Option Expr := none) :
    MetaM BodyAnalysis := do
  let ctx : Context :=
    { cfg, outputs := outputs.map Expr.fvarId!, stripBoilerplate := false }
  let (res, st) ← ((do propSimplify (← simpProp body)).run ctx).run {}
  let mentions (e : Expr) : Bool :=
    e.hasAnyFVar fun fv => outputs.any fun o => o.fvarId! == fv
  let small (e : Expr) : Bool :=
    sizeUpTo (cfg.probeMaxSize + 1) e ≤ cfg.probeMaxSize
  let mut res := res
  let mut st := st
  if cfg.semanticProbe && mentions res then
    let cs := conjuncts res
    let mut kept : Array Expr := #[]
    let mut refuted := false
    for c in cs do
      if refuted then
        break
      if mentions c && small c && cs.size ≤ 32 then
        unless ← isBareOutputEq outputs c do
          if ← tryProve c cfg.probeHeartbeats (deep := true) then
            st := { st with droppedOutputTaut := true, semanticStrip := true }
            continue
          if ← tryProve (mkNot c) cfg.probeHeartbeats (deep := true) then
            st := { st with droppedOutputTaut := true, semanticStrip := true }
            refuted := true
            continue
      kept := kept.push c
    res := if refuted then mkConst ``False else mkAndN kept
    if !refuted && kept.size ≥ 2 && mentions res && small res then
      let sharedOut := outputs.any fun o =>
        (kept.filter fun c => c.containsFVar o.fvarId!).size ≥ 2
      if sharedOut then
        if ← tryProveCore (← underHyp res (mkConst ``False))
            cfg.probeHeartbeats (deep := true) then
          st := { st with droppedOutputTaut := true, semanticStrip := true }
          res := mkConst ``False
          refuted := true
    if !refuted && mentions res && small res && !(← isBareOutputEq outputs res) then
      let (probed, changed) ← probeSubProps cfg mentions small res
      if changed then
        let (res', st') ← ((do propSimplify (← simpProp probed)).run ctx).run st
        res := res'
        st := { st' with droppedOutputTaut := true, semanticStrip := true }
  let mut bound := outputs.map fun o => res.containsFVar o.fvarId!
  let mut insensitive := false
  -- Any output whose type is a subsingleton (`Unit`, `Fin 1`, `Empty`, ...)
  -- cannot distinguish two outputs (`not_dichotomy_of_subsingleton_output`).
  for i in [0:outputs.size] do
    if bound[i]! then
      let o := outputs[i]!
      let ty ← safely (inferType o) (mkConst ``Nat)
      if ← typeSubsingleton ty cfg.semanticProbe cfg.probeHeartbeats then
        bound := bound.set! i false
        insensitive := true
  let bareEq ← isBareOutputEq outputs res
  if cfg.semanticProbe && small res && !bareEq then
    for i in [0:outputs.size] do
      if bound[i]! then
        let o := outputs[i]!
        let proved ← withLocalDeclD `o' (← inferType o) fun o' =>
          tryProve (mkApp2 (mkConst ``Iff) res (res.replaceFVar o o'))
            cfg.probeHeartbeats (deep := true)
        if proved then
          bound := bound.set! i false
          insensitive := true
  -- Fallback: unfold small non-recursive data helpers applied to bound outputs
  -- once and retry insensitivity without polluting residuals of genuine specs.
  if cfg.semanticProbe && small res && bound.any id && !bareEq then
    if let some rawUnfolded ← unfoldSmallOutputHelpers cfg mentions res then
      let (cand, _) ← ((do propSimplify (← simpProp rawUnfolded)).run ctx).run {}
      if isFalseConst cand then
        res := cand
        bound := Array.replicate outputs.size false
        insensitive := true
      else if small cand then
        for i in [0:outputs.size] do
          if bound[i]! then
            let o := outputs[i]!
            let dropped := !cand.containsFVar o.fvarId!
            let proved ←
              if dropped then
                pure true
              else
                withLocalDeclD `o' (← inferType o) fun o' =>
                  tryProve (mkApp2 (mkConst ``Iff) cand (cand.replaceFVar o o'))
                    cfg.probeHeartbeats
            if proved then
              bound := bound.set! i false
              insensitive := true
  -- Relative to the precondition: `PostconditionDichotomy pre post` ranges over
  -- admissible inputs only, so what is still bound is re-examined under the
  -- (normalised) precondition `hyp`. Its existentials are opened, its equations
  -- rewrite the residual (with kernel typechecking), constructor case splitting
  -- is re-run on the rewritten residual, and remaining facts feed proof search.
  let mut requiresReason? : Option EnsuresVacuityReason := none
  if let some hyp := hyp? then
    if cfg.semanticProbe && cfg.useRequires && bound.any id && small res &&
        small hyp && !bareEq then
      let hb := cfg.probeHeartbeats
      let boundNow := bound
      let resNow := res
      let (reason?, bound', decided?) ← openHyps [hyp] #[] #[] fun ws facts => do
        let mut rewritten := resNow
        let mut facts := facts
        for idx in [0:facts.size] do
          if let some (lhs, rhs) ← rewriteRule? facts[idx]! then
            let rw (e : Expr) : MetaM Expr := do
              let cand := e.replace fun sub => if sub == lhs then some rhs else none
              if cand == e then
                return e
              if ← safely (do check cand; return true) false then
                return cand
              return e
            rewritten ← rw rewritten
            let mut facts' := facts
            for j in [0:facts.size] do
              if j != idx then
                facts' := facts'.set! j (← rw facts[j]!)
            facts := facts'
        let resUnder ←
          if rewritten == resNow then
            pure resNow
          else
            let (r, _) ← ((do propSimplify (← simpProp rewritten)).run ctx).run {}
            pure r
        let wrap (g : Expr) : MetaM Expr :=
          mkForallFVars ws (facts.foldr (fun f acc => mkForall `h .default f acc) g)
        let prove (g : Expr) : MetaM Bool := do
          if ← tryProveFast (← wrap g) hb then
            return true
          match g.getAppFnArgs with
          | (``Iff, #[a, b]) =>
            if (← tryProveFast (← wrap (mkForall `h .default a b)) hb) &&
                (← tryProveFast (← wrap (mkForall `h .default b a)) hb) then
              return true
            tryProveGrind (← wrap g) hb
          | _ => tryProveGrind (← wrap g) hb
        let none' := Array.replicate outputs.size false
        if isTrueConst resUnder || (← prove resUnder) then
          return (some EnsuresVacuityReason.vacuousUnderRequires, none',
            some (mkConst ``True))
        if isFalseConst resUnder || (← prove (mkNot resUnder)) then
          return (some EnsuresVacuityReason.unrealizableUnderRequires, none',
            some (mkConst ``False))
        let mut bound' := boundNow
        let mut reason? : Option EnsuresVacuityReason := none
        for i in [0:outputs.size] do
          if bound'[i]! then
            let o := outputs[i]!
            if !resUnder.containsFVar o.fvarId! then
              bound' := bound'.set! i false
              reason? := some .vacuousUnderRequires
            else
              let mut splitHit := false
              if resUnder != resNow then
                if let some p ← caseSplitOutput cfg outputs i resUnder then
                  if isTrueConst p then
                    return (some EnsuresVacuityReason.vacuousUnderRequires, none',
                      some (mkConst ``True))
                  if isFalseConst p then
                    return (some EnsuresVacuityReason.unrealizableUnderRequires, none',
                      some (mkConst ``False))
                  bound' := bound'.set! i false
                  reason? := some .vacuousUnderRequires
                  splitHit := true
              if !splitHit then
                let unbound ← withLocalDeclD `o' (← inferType o) fun o' =>
                  prove (mkApp2 (mkConst ``Iff) resUnder
                    (resUnder.replaceFVar o o'))
                if unbound then
                  bound' := bound'.set! i false
                  reason? := some .vacuousUnderRequires
        return (reason?, bound', none)
      requiresReason? := reason?
      bound := bound'
      if let some decided := decided? then
        res := decided
  return {
    residual := res, bound, state := st, provedInsensitive := insensitive
    requiresReason? }

/--
`analyzeBody`, followed by a constructor case split on each output it leaves
bound.
-/
def analyzeBodySplit (cfg : EnsuresCheckConfig)
    (outputs : Array Expr) (body : Expr) (hyp? : Option Expr := none) :
    MetaM BodyAnalysis := do
  let mut a ← analyzeBody cfg outputs body hyp?
  for i in [0:outputs.size] do
    if a.bound[i]! then
      if let some p ← caseSplitOutput cfg outputs i body then
        a := { a with
          residual := p
          bound := (outputs.zip (a.bound.set! i false)).map fun (o, b) =>
            b && p.containsFVar o.fvarId!
          state := { a.state with droppedOutputTaut := true } }
  return a

/-- Most boilerplate atoms cofactored exhaustively (`2 ^ 8` assignments). -/
def maxCofactorAtoms : Nat := 8

/-- Most cofactors handed to the full analysis before giving up. -/
def maxCofactorAnalyses : Nat := 64

/--
Determine which outputs are constrained *beyond* the predicates in
`cfg.boilerplate`, by exact cofactoring: normalise with boilerplate kept
opaque, enumerate **every** truth assignment `{True, False}^k` to the distinct
closed boilerplate atoms occurring in the residual, and OR per-output binding
across cofactors. This decides `DichotomyModuloObservation` for the observation
"truth values of those atoms", which for one atom is `DichotomyBeyondPredicate`
(soundness: `not_dichotomyModuloObservation_of_cofactors_insensitive`).

The enumeration is never sampled: a dichotomy modulo the observation lives in
exactly one cofactor (`DichotomyModuloObservation.exists_cofactor_dichotomy`),
and that one may be any of the `2 ^ k`. Whenever the answer is not established
— more than `maxCofactorAtoms` atoms, more than `maxCofactorAnalyses` cofactors
needing the full analysis, or a cofactor that does not typecheck — the result
is `full`, i.e. *binds beyond boilerplate*. Atoms under a binder whose variable
they mention are not observations of the output at all; they stay opaque.

When the full pass never encountered any boilerplate constant (and did not
exhaust its budget), returns `full` immediately at zero extra cost.
-/
def analyzeUserBeyondBoilerplate (cfg : EnsuresCheckConfig)
    (outputs : Array Expr) (body : Expr) (full : BodyAnalysis)
    (hyp? : Option Expr := none) : MetaM BodyAnalysis := do
  if !full.anyBound then
    return full
  if !full.state.sawBoilerplate && !full.state.budgetExhausted then
    return full
  let ctx : Context :=
    { cfg, outputs := outputs.map Expr.fvarId!, stripBoilerplate := true }
  let (bpRes, bpSt) ← ((do propSimplify (← simpProp body)).run ctx).run {}
  let atoms := (collectBoilerplateAtoms cfg.boilerplate bpRes).filter
    fun a => !a.hasLooseBVars
  if atoms.isEmpty then
    return full
  let k := atoms.size
  if k > maxCofactorAtoms then
    return { full with cofactorIncomplete := true }
  let mentions (e : Expr) : Bool :=
    e.hasAnyFVar fun fv => outputs.any fun o => o.fvarId! == fv
  let mut boundAcc := Array.replicate outputs.size false
  let mut best? : Option BodyAnalysis := none
  let mut first? : Option BodyAnalysis := none
  let mut analyses := 0
  -- All-true first: the cofactor a well-formed external spec lives in.
  for mask in (Array.range (1 <<< k)).reverse do
    let cand ← replaceBoilerplateAtoms atoms mask bpRes
    unless ← safely (do check cand; return true) false do
      return { full with cofactorIncomplete := true }
    -- A cofactor that folds to an output-free proposition binds nothing.
    let folded := evalBoolConsts cand
    if !mentions folded then
      if first?.isNone then
        first? := some
          { residual := folded, bound := Array.replicate outputs.size false
            state := {}, provedInsensitive := false, requiresReason? := none }
      continue
    if analyses ≥ maxCofactorAnalyses then
      return { full with cofactorIncomplete := true }
    analyses := analyses + 1
    let a ← analyzeBodySplit cfg outputs cand hyp?
    if first?.isNone then
      first? := some a
    if a.anyBound then
      if best?.isNone then
        best? := some a
      for i in [0:outputs.size] do
        if a.bound[i]! then
          boundAcc := boundAcc.set! i true
      if boundAcc == full.bound then
        break
  let chosen := best?.getD (first?.getD full)
  return { chosen with
    bound := boundAcc
    state := { chosen.state with
      droppedBoilerplate := true
      budgetExhausted := chosen.state.budgetExhausted || bpSt.budgetExhausted } }

/-- The reason attached to an analysis in which no output is bound. -/
def classify (a : BodyAnalysis) : EnsuresVacuityReason :=
  if let some r := a.requiresReason? then
    r
  else if isFalseConst a.residual then
    .unsatisfiable
  else if a.provedInsensitive || a.state.semanticStrip then
    .semanticallyInsensitive
  else if a.state.droppedOutputTaut then
    .reflexiveTautology
  else if isTrueConst a.residual && !a.state.droppedInputTaut then
    .constTrue
  else
    .inputOnly

def budgetNotes (a : BodyAnalysis) : Array String :=
  if a.state.budgetExhausted then
    #["normalisation budget exhausted: the residual is under-normalised and \
      the verdict errs towards `binds output`"]
  else
    #[]

def cofactorNotes (user : BodyAnalysis) : Array String :=
  if user.cofactorIncomplete then
    #["boilerplate cofactoring abandoned (too many boilerplate atoms or \
      cofactors): the user-`ensures` verdict errs towards `binds output`"]
  else
    #[]

def ppResidual (e : Expr) : MetaM String :=
  safely (do return (← ppExpr e).pretty) "<unprintable>"

/-- Generic verdict: binding is occurrence of an output in the residual. -/
def analyzeGeneric (cfg : EnsuresCheckConfig) (kind : String) (body : Expr)
    (binders : Array Expr) (outIdxs retIdxs : Array Nat)
    (hyp? : Option Expr := none) (skipUser : Bool := false) :
    MetaM EnsuresCheckReport := do
  let outs := outIdxs.map (binders[·]!)
  let full ← analyzeBodySplit cfg outs body hyp?
  let user ←
    if skipUser then pure full
    else analyzeUserBeyondBoilerplate cfg outs body full hyp?
  let eff := if cfg.userEnsuresOnly then user else full
  let boundIdxs := (outIdxs.zip eff.bound).filterMap fun (i, b) =>
    if b then some i else none
  let reason? : Option EnsuresVacuityReason :=
    if !full.anyBound then
      some (classify full)
    else if cfg.userEnsuresOnly && !user.anyBound then
      some .boilerplateOnly
    else if cfg.strictReturnValue &&
        retIdxs.any (fun i => !boundIdxs.contains i) then
      some .returnValueUnconstrained
    else
      none
  return {
    kind
    arity := binders.size
    outputIdxs := outIdxs
    boundOutputIdxs := boundIdxs
    reason?
    bindsBeyondBoilerplate := full.anyBound && user.anyBound
    residual := ← ppResidual eff.residual
    notes := budgetNotes full ++ cofactorNotes user }

/--
`MirCallAns` verdict: instantiate the answer at each outcome and judge the
`.returned` instance on `(retVal, memAfter)`.
-/
def analyzeMirCallAns (cfg : EnsuresCheckConfig) (kind : String) (body : Expr)
    (binders : Array Expr) (ansIdx : Nat) (hyp? : Option Expr := none)
    (skipUser : Bool := false) : MetaM EnsuresCheckReport := do
  let ans := binders[ansIdx]!
  let valTy := mkConst ``Value
  let memTy := mkConst ``Memory
  let (full, user, eff, returnedStr, boundNote, fullBudget) ←
    withLocalDeclD `retVal valTy fun v =>
    withLocalDeclD `memAfter memTy fun m => do
      let inst := body.replaceFVar ans (mkApp2 (mkConst ``MirCallAns.returned) v m)
      let full ← analyzeBodySplit cfg #[v, m] inst hyp?
      let user ←
        if skipUser then pure full
        else analyzeUserBeyondBoilerplate cfg #[v, m] inst full hyp?
      let eff := if cfg.userEnsuresOnly then user else full
      let returnedStr ← ppResidual eff.residual
      let boundNote :=
        s!"`.returned retVal memAfter` binds retVal: {eff.bound[0]!}, \
          memAfter: {eff.bound[1]!}"
      return (full, user, eff, returnedStr, boundNote,
        budgetNotes full ++ cofactorNotes user)
  -- `.aborted` and `.panicked`: semantic probing on `.panicked` is only needed
  -- when `.returned` failed to bind, to tell outcome-blind from return-blind.
  let outcomeCfg := if full.anyBound then { cfg with semanticProbe := false } else cfg
  let aborted ← analyzeBody outcomeCfg #[]
    (body.replaceFVar ans (mkConst ``MirCallAns.aborted))
  let abortedStr ← ppResidual aborted.residual
  let (panicked, panickedStr) ← withLocalDeclD `memAfter memTy fun m => do
    let a ← analyzeBody outcomeCfg #[m]
      (body.replaceFVar ans (mkApp (mkConst ``MirCallAns.panicked) m))
    return (a, ← ppResidual a.residual)
  let reason? : Option EnsuresVacuityReason :=
    if !full.anyBound then
      if let some r := full.requiresReason? then
        some r
      else if isFalseConst full.residual then
        some .normalReturnUnsatisfiable
      else if !panicked.anyBound && full.residual == panicked.residual &&
          full.residual == aborted.residual then
        some .outcomeBlind
      else
        some .returnBlind
    else if cfg.userEnsuresOnly && !user.anyBound then
      some .boilerplateOnly
    else if cfg.strictReturnValue && !eff.bound[0]! then
      some .returnValueUnconstrained
    else
      none
  return {
    kind
    arity := binders.size
    outputIdxs := #[ansIdx]
    boundOutputIdxs := if eff.anyBound then #[ansIdx] else #[]
    reason?
    bindsBeyondBoilerplate := full.anyBound && user.anyBound
    residual := returnedStr
    notes := #[boundNote, s!".returned ↦ {returnedStr}",
      s!".panicked ↦ {panickedStr}", s!".aborted ↦ {abortedStr}"] ++
      fullBudget }

/--
Refute `e` structurally across leading existentials, disjunctions (refuting
every disjunct suffices), and conjunctions (using `underHyp` with `deep := true`
on the whole conjunction when it fits `probeMaxSize`, and falling back to
individual conjuncts when a large boilerplate conjunct pushes size over budget
or an inner `Or`/`Exists` needs structural splitting).
-/
partial def refuteUnderExists (cfg : EnsuresCheckConfig)
    (e : Expr) : MetaM Bool := do
  if isFalseConst e then
    return true
  if isTrueConst e then
    return false
  match e.getAppFnArgs with
  | (``Exists, #[α, p]) =>
    withLocalDeclD `x α fun x => refuteUnderExists cfg (p.beta #[x])
  | (``Or, #[a, b]) =>
    return (← refuteUnderExists cfg a) && (← refuteUnderExists cfg b)
  | (``And, #[_, _]) =>
    let cs := conjuncts e
    if cs.any isFalseConst then
      return true
    if !cfg.semanticProbe then
      return false
    let fits := sizeUpTo (cfg.probeMaxSize + 1) e ≤ cfg.probeMaxSize
    if fits then
      if ← tryProveCore (← underHyp e (mkConst ``False))
          cfg.probeHeartbeats (deep := true) then
        return true
    for c in cs do
      if !fits || c.isAppOf ``Or || c.isAppOf ``Exists then
        if ← refuteUnderExists cfg c then
          return true
    return false
  | _ =>
    if !cfg.semanticProbe ||
        sizeUpTo (cfg.probeMaxSize + 1) e > cfg.probeMaxSize then
      return false
    tryProveCore (← underHyp e (mkConst ``False)) cfg.probeHeartbeats
      (deep := true)

/-- `List Value → Memory → Value → Memory → _`: a `StatefulClaim` postcondition. -/
def isStatefulShape (binders : Array Expr) : MetaM Bool := do
  unless binders.size == 4 do
    return false
  let tys ← binders.mapM fun b => do whnfR (← inferType b)
  let valTy := mkConst ``Value
  let memTy := mkConst ``Memory
  return tys[0]! == mkApp (mkConst ``List [Level.zero]) valTy &&
    tys[1]! == memTy && tys[2]! == valTy && tys[3]! == memTy

/--
Resolve the designated outputs of a postcondition `body` over `binders` and
dispatch to the generic or the `MirCallAns` analysis.
-/
def analyzePost (cfg : EnsuresCheckConfig) (kind : String) (body : Expr)
    (binders : Array Expr) (outputParamIdxs : Option (Array Nat))
    (pre? : Option Expr := none) : MetaM EnsuresCheckReport := do
  let arity := binders.size
  if arity == 0 then
    throwError "checkEnsuresBindsOutput: a postcondition needs at least one \
      binder, but this one has none"
  let stateful ← isStatefulShape binders
  let outIdxs :=
    match outputParamIdxs with
    | some idxs => idxs
    | none => if stateful then #[2, 3] else #[arity - 1]
  if outIdxs.isEmpty then
    throwError "checkEnsuresBindsOutput: no output binder designated"
  for i in outIdxs do
    unless i < arity do
      throwError "checkEnsuresBindsOutput: output binder index {i} is out of \
        range for a postcondition of arity {arity}"
  if let some pre := pre? then
    for i in outIdxs do
      if pre.containsFVar binders[i]!.fvarId! then
        throwError "checkEnsuresBindsOutput: the precondition mentions the \
          output binder {i}"
  -- The precondition, normalised, as the hypothesis of the proof search. A
  -- precondition that is itself refuted (or has an empty input domain) admits
  -- no input at all.
  let mut hyp? : Option Expr := none
  let mut preRefuted := false
  if let some pre := pre? then
    if cfg.useRequires then
      let ctx : Context := { cfg, outputs := #[], stripBoilerplate := false }
      let (hyp, _) ← ((do propSimplify (← simpProp pre)).run ctx).run {}
      preRefuted ← refuteUnderExists cfg hyp
      if !preRefuted && cfg.semanticProbe then
        for i in [0:binders.size] do
          if !outIdxs.contains i then
            let bTy ← safely (inferType binders[i]!) (mkConst ``Unit)
            if ← isEmptyDomain bTy cfg.probeHeartbeats then
              preRefuted := true
              break
      if !preRefuted && !isTrueConst hyp then
        hyp? := some hyp
  let retIdxs := if stateful && outIdxs.contains 2 then #[2] else outIdxs
  let mut isAns := false
  if outIdxs.size == 1 then
    let ansTy ← whnfR (← inferType binders[outIdxs[0]!]!)
    isAns := ansTy.isConstOf ``MirCallAns
  let report ←
    if isAns then
      analyzeMirCallAns cfg kind body binders outIdxs[0]! hyp? preRefuted
    else
      analyzeGeneric cfg kind body binders outIdxs retIdxs hyp? preRefuted
  if preRefuted then
    return { report with
      reason? := some .requiresUnsatisfiable
      boundOutputIdxs := #[]
      bindsBeyondBoilerplate := false
      notes := report.notes.push
        "the precondition is unsatisfiable: no input is admissible" }
  return report

end EnsuresCheck

/--
Check whether the postcondition `postExpr` genuinely constrains its output
binders.

`postExpr` may be

* a function `∀ x₁ … xₙ, Prop` (or `Bool`) with `n ≥ 1`, whose outputs are the
  binders `outputParamIdxs` (default: the last binder, or the last two for the
  `StatefulClaim` shape `List Value → Memory → Value → Memory → Prop`), which
  covers `Claim.post`, `MirCallContract.post`, and `extraPost` lambdas; or
* a term of type `MirCallContract`, `Claim`, or `StatefulClaim`, possibly under
  leading parameters, whose `post` field is analysed with the indices counted
  among the binders of `post`.

An output of type `MirCallAns` is analysed outcome by outcome; see the section
documentation.

Binding is judged relative to the precondition when one is known: the `pre`
field of a contract, or, for a function-shaped postcondition, `preExpr?`, a
predicate over a prefix of the binders of `postExpr`.
-/
def checkEnsuresBindsOutput (postExpr : Expr)
    (outputParamIdxs : Option (Array Nat) := none)
    (cfg : EnsuresCheckConfig := {})
    (preExpr? : Option Expr := none) : MetaM EnsuresCheckReport := do
  let postExpr ← instantiateMVars postExpr
  let ty ← inferType postExpr
  forallTelescopeReducing ty fun xs resTy => do
    let resTy ← whnf resTy
    let applied := postExpr.beta xs
    let valTy := mkConst ``Value
    let memTy := mkConst ``Memory
    let argsTy := mkApp (mkConst ``List [Level.zero]) valTy
    -- An explicit precondition is a predicate over a prefix of the binders of
    -- a function-shaped postcondition.
    let functionPre? : MetaM (Option Expr) := do
      let some preExpr := preExpr? | return none
      let preExpr ← instantiateMVars preExpr
      let arity ← forallTelescopeReducing (← inferType preExpr) fun ps _ =>
        pure ps.size
      unless arity ≤ xs.size do
        throwError "checkEnsuresBindsOutput: the precondition takes {arity} \
          arguments, but the postcondition has only {xs.size} binders"
      let pre := preExpr.beta (xs.extract 0 arity)
      try
        check pre
      catch _ =>
        throwError "checkEnsuresBindsOutput: the precondition does not apply \
          to the leading binders of the postcondition"
      let preTy ← whnf (← inferType pre)
      if preTy.isProp then
        return some pre
      if preTy.isConstOf ``Bool then
        return some (← mkEq pre (mkConst ``Bool.true))
      throwError "checkEnsuresBindsOutput: the precondition is not a predicate"
    if resTy.isProp then
      EnsuresCheck.analyzePost cfg "function" applied xs outputParamIdxs
        (← functionPre?)
    else if resTy.isConstOf ``Bool then
      EnsuresCheck.analyzePost cfg "function"
        (← mkEq applied (mkConst ``Bool.true)) xs outputParamIdxs
        (← functionPre?)
    else if resTy.isConstOf ``MirCallContract then
      withLocalDeclD `req (mkConst ``MirCallReq) fun req =>
      withLocalDeclD `ans (mkConst ``MirCallAns) fun ans =>
        EnsuresCheck.analyzePost cfg "MirCallContract"
          (mkApp3 (mkConst ``MirCallContract.post) applied req ans)
          #[req, ans] outputParamIdxs
          (some (mkApp2 (mkConst ``MirCallContract.pre) applied req))
    else if resTy.isConstOf ``Claim then
      withLocalDeclD `args argsTy fun args =>
      withLocalDeclD `ret valTy fun ret =>
        EnsuresCheck.analyzePost cfg "Claim"
          (mkApp3 (mkConst ``Claim.post) applied args ret)
          #[args, ret] outputParamIdxs
          (some (mkApp2 (mkConst ``Claim.pre) applied args))
    else if resTy.isConstOf ``StatefulClaim then
      withLocalDeclD `args argsTy fun args =>
      withLocalDeclD `mem memTy fun mem =>
      withLocalDeclD `ret valTy fun ret =>
      withLocalDeclD `mem' memTy fun mem' =>
        EnsuresCheck.analyzePost cfg "StatefulClaim"
          (mkApp5 (mkConst ``StatefulClaim.post) applied args mem ret mem')
          #[args, mem, ret, mem'] outputParamIdxs
          (some (mkApp3 (mkConst ``StatefulClaim.pre) applied args mem))
    else
      throwError "checkEnsuresBindsOutput: expected a postcondition \
        `∀ x₁ … xₙ, Prop`, a `MirCallContract`, a `Claim`, or a \
        `StatefulClaim`, but the result type is{indentExpr resTy}"

/--
`checkEnsuresBindsOutput` on the constant `declName`: a postcondition function,
a `MirCallContract`, a `Claim`, or a `StatefulClaim` (each possibly under
leading parameters). `preDecl?` names the precondition of a function-shaped
postcondition.
-/
def checkDeclEnsuresBindsOutput (declName : Name)
    (outputParamIdxs : Option (Array Nat) := none)
    (cfg : EnsuresCheckConfig := {})
    (preDecl? : Option Name := none) : MetaM EnsuresCheckReport := do
  let pre? ← preDecl?.mapM mkConstWithLevelParams
  checkEnsuresBindsOutput (← mkConstWithLevelParams declName) outputParamIdxs
    cfg pre?

/-- Fail unless the postcondition `declName` binds its output. -/
def assertEnsuresBindsOutput (declName : Name)
    (outputParamIdxs : Option (Array Nat) := none)
    (cfg : EnsuresCheckConfig := {})
    (preDecl? : Option Name := none) : MetaM Unit := do
  let r ← checkDeclEnsuresBindsOutput declName outputParamIdxs cfg preDecl?
  if let some reason := r.reason? then
    throwError "assertEnsuresBindsOutput: the postcondition of `{declName}` \
      does not bind its output ({reason}).\n{r.describe}"

/--
Fail unless the postcondition `declName` is flagged as vacuous in its output,
for `expectedReason` when one is given.
-/
def assertEnsuresVacuous (declName : Name)
    (expectedReason : Option EnsuresVacuityReason := none)
    (outputParamIdxs : Option (Array Nat) := none)
    (cfg : EnsuresCheckConfig := {})
    (preDecl? : Option Name := none) : MetaM Unit := do
  let r ← checkDeclEnsuresBindsOutput declName outputParamIdxs cfg preDecl?
  match r.reason? with
  | none =>
    throwError "assertEnsuresVacuous: the postcondition of `{declName}` was \
      expected to be flagged as vacuous, but it binds its output.\n{r.describe}"
  | some reason =>
    if let some expected := expectedReason then
      unless reason == expected do
        throwError "assertEnsuresVacuous: the postcondition of `{declName}` \
          is vacuous for reason `{reason}`, but `{expected}` was expected.\
          \n{r.describe}"

/-! ### `requires` refutation -/

/-- Result of `checkRequiresSatisfiable`. -/
structure RequiresCheckReport where
  /-- What was analysed: `function`, `Claim`, `StatefulClaim`, `MirCallContract`. -/
  kind : String
  /-- Number of precondition binders. -/
  arity : Nat
  /--
  The precondition was *proved* unsatisfiable: it normalises to `False`, or
  the proof search refuted it under its leading existentials. `false` means
  only that no refutation was found.
  -/
  refuted : Bool
  /-- The normalised precondition. -/
  residual : String
  deriving Repr, Inhabited

/--
Look for a proof that the precondition `preExpr` is unsatisfiable (vacuity
class 1). `preExpr` is a predicate `∀ x₁ … xₙ, Prop` (or `Bool`), or a
`MirCallContract`, `Claim`, or `StatefulClaim` (possibly under leading
parameters), whose `pre` field is analysed. Satisfiability itself is not
decided: a report with `refuted = false` is not a realizability proof.
-/
def checkRequiresSatisfiable (preExpr : Expr)
    (cfg : EnsuresCheckConfig := {}) : MetaM RequiresCheckReport := do
  let preExpr ← instantiateMVars preExpr
  let ty ← inferType preExpr
  forallTelescopeReducing ty fun xs resTy => do
    let resTy ← whnf resTy
    let applied := preExpr.beta xs
    let valTy := mkConst ``Value
    let argsTy := mkApp (mkConst ``List [Level.zero]) valTy
    let run (kind : String) (body : Expr) (arity : Nat)
        (domainBinders : Array Expr) : MetaM RequiresCheckReport := do
      let ctx : EnsuresCheck.Context :=
        { cfg, outputs := #[], stripBoilerplate := false }
      let (res, _) ←
        ((do EnsuresCheck.propSimplify (← EnsuresCheck.simpProp body)).run ctx).run {}
      let mut refuted ← EnsuresCheck.refuteUnderExists cfg res
      if !refuted && cfg.semanticProbe then
        for b in domainBinders do
          let bTy ← EnsuresCheck.safely (inferType b) (mkConst ``Unit)
          if ← EnsuresCheck.isEmptyDomain bTy cfg.probeHeartbeats then
            refuted := true
            break
      return {
        kind, arity
        refuted
        residual := ← EnsuresCheck.ppResidual res }
    if resTy.isProp then
      run "function" applied xs.size xs
    else if resTy.isConstOf ``Bool then
      run "function" (← mkEq applied (mkConst ``Bool.true)) xs.size xs
    else if resTy.isConstOf ``MirCallContract then
      withLocalDeclD `req (mkConst ``MirCallReq) fun req =>
        run "MirCallContract"
          (mkApp2 (mkConst ``MirCallContract.pre) applied req) 1 #[req]
    else if resTy.isConstOf ``Claim then
      withLocalDeclD `args argsTy fun args =>
        run "Claim" (mkApp2 (mkConst ``Claim.pre) applied args) 1 #[args]
    else if resTy.isConstOf ``StatefulClaim then
      withLocalDeclD `args argsTy fun args =>
      withLocalDeclD `mem (mkConst ``Memory) fun mem =>
        run "StatefulClaim"
          (mkApp3 (mkConst ``StatefulClaim.pre) applied args mem) 2 #[args, mem]
    else
      throwError "checkRequiresSatisfiable: expected a precondition \
        `∀ x₁ … xₙ, Prop`, a `MirCallContract`, a `Claim`, or a \
        `StatefulClaim`, but the result type is{indentExpr resTy}"

/-- `checkRequiresSatisfiable` on the constant `declName`. -/
def checkDeclRequiresSatisfiable (declName : Name)
    (cfg : EnsuresCheckConfig := {}) : MetaM RequiresCheckReport := do
  checkRequiresSatisfiable (← mkConstWithLevelParams declName) cfg

/-- Fail unless the precondition of `declName` was proved unsatisfiable. -/
def assertRequiresRefuted (declName : Name)
    (cfg : EnsuresCheckConfig := {}) : MetaM Unit := do
  let r ← checkDeclRequiresSatisfiable declName cfg
  unless r.refuted do
    throwError "assertRequiresRefuted: the precondition of `{declName}` was \
      expected to be refuted, but no refutation was found.\n  residual: \
      {r.residual}"

/-- Fail if the precondition of `declName` was proved unsatisfiable. -/
def assertRequiresNotRefuted (declName : Name)
    (cfg : EnsuresCheckConfig := {}) : MetaM Unit := do
  let r ← checkDeclRequiresSatisfiable declName cfg
  if r.refuted then
    throwError "assertRequiresNotRefuted: the precondition of `{declName}` is \
      unsatisfiable.\n  residual: {r.residual}"

end Checker

end Anneal.SpecRealizabilityPrototype
