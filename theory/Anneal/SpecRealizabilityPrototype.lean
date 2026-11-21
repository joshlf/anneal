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
  mutant (`postconditionDichotomy_iff_exists_killed_mutant`).

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
A deterministic contract over a subsingleton output type cannot separate
outputs: dichotomy needs two distinct candidates.
-/
theorem not_dichotomy_of_subsingleton_output
    (h : ∀ out₁ out₂ : Output, out₁ = out₂) :
    ¬ PostconditionDichotomy pre post :=
  fun ⟨_, ok, bad, _, hok, hbad⟩ => hbad (h ok bad ▸ hok)

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

end Mir

/-! ## Part II — `MetaM` `ensures`-binding and vacuity checker

`checkEnsuresBindsOutput` decides, syntactically, whether a postcondition
constrains its designated output binders.

**Method.** The postcondition is applied to fresh variables and rewritten to a
*residual* by steps that each preserve its truth value:

* definitional reductions (`mdata`, beta, zeta, eta, iota on constructors,
  structure projections including projection functions applied to unfolded
  structure instances) and head unfolding, under a fuel bound, of definitions
  in proposition position and of Boolean-valued definitions compared with a
  literal. Smart unfolding leaves a recursive definition alone unless its
  recursion can progress, instances and irreducible definitions are never
  unfolded, and data terms are not delta-unfolded, with one exception: a term
  that mentions an output and is equated with a constructor is evaluated to
  weak head normal form, so that a helper applied to `.returned v m` exposes
  its result. A structure of an opaque type (`CapturedMir` by default) is never
  unfolded to reach a field, so captured MIR bodies stay untouched;
* propositional identities (`True ∧ P`, `P ∨ True`, `False → P`, `P → True`,
  `P → P`, `P ↔ P`, `P ∨ ¬P`, `P ∧ ¬P`, double negation, equality of
  conjunctions and disjunctions up to order, `if`/`dite` as a conjunction of
  implications, collapse of a `match` whose alternatives all reduce to one
  proposition that ignores the pattern variables);
* reflexivity of `Eq` (compared up to orientation), `HEq`, `Iff`, of `≤`/`≥`
  (and irreflexivity of `<`/`>`) only where the law is provable for the
  instance at hand, of `BEq.beq` only under a `ReflBEq`/`LawfulBEq` instance,
  and of `Nat.ble`/`Nat.beq`/`decide`; numerals are compared by value at `Nat`
  only;
* injectivity and disjointness of constructors, and the one-point rules
  `∃ y, y = t ∧ P y ↔ P t` and `∀ y, y = t → P y ↔ P t` for `y` not in `t`.

An output is *bound* when it still occurs in the residual and a bounded proof
search (`rfl`, `omega`, `simp +arith`, `decide`) can neither discharge the
conjuncts that mention it nor prove the residual insensitive to it. All
rewrites are equivalences, so a postcondition reported as not binding an output
is semantically insensitive to that output; a postcondition reported as
binding may still be vacuous in a way the search does not see (for example
behind an `opaque` or `irreducible` definition, or `∃ y, r ≤ y`). The one
deliberate exception is `userEnsuresOnly`, which discards the frame and
return-type conjuncts of an external spec *before* judging and so answers a
different question: whether the user `ensures` clause binds the return.

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
  /-- Whether boilerplate conjuncts are discarded. -/
  stripBoilerplate : Bool

/-- What the normaliser discarded on the way to the residual. -/
structure State where
  unfolds : Nat := 0
  steps : Nat := 0
  /-- A tautology (or absorbed subformula) mentioning an output was discarded. -/
  droppedOutputTaut : Bool := false
  /-- A tautology (or absorbed subformula) without outputs was discarded. -/
  droppedInputTaut : Bool := false
  /-- A boilerplate conjunct was discarded. -/
  droppedBoilerplate : Bool := false
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
  return mkAndN acc

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
  return mkOrN acc

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
  return mkApp2 (mkConst ``Iff) a b

/--
Try to close `goal` with a short, heartbeat-bounded tactic portfolio. The
elaboration state is restored whatever happens, so the attempt is unobservable.
-/
def tryProve (goal : Expr) (heartbeats : Nat) : MetaM Bool := do
  let saved ← saveState
  let r ← tryCatchRuntimeEx
    (do
      let mvar ← mkFreshExprMVar goal
      let tac ← `(tactic|
        first | rfl | (intros; omega) | (simp +arith; done) | decide)
      let (goals, _) ← withCurrHeartbeats <|
        withTheReader Core.Context
          (fun c => { c with maxHeartbeats := heartbeats * 1000 }) <|
          Lean.Elab.runTactic mvar.mvarId! tac
      pure goals.isEmpty)
    (fun _ => pure false)
  saved.restore
  return r

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
Head-normalise without unfolding definitions: `mdata`, beta, zeta, iota,
matcher reduction on constructors, and structure projections (primitive or by
projection function) of a term whose constructor `whnfStruct` exposes. Class
projections are left alone so that `LE.le`, `BEq.beq`, ... stay recognisable.
-/
partial def headReduce (e : Expr) : CheckM Expr := do
  let e ← instantiateMVars e
  let e ← safely (whnfCore e) e
  match e.getAppFn with
  | .proj _ i s =>
    let s' ← whnfStruct s
    match ← safely (constructorApp? s') none with
    | some (cv, cargs) =>
      if h : cv.numParams + i < cargs.size then
        headReduce (cargs[cv.numParams + i].beta e.getAppArgs)
      else
        return e
    | none => return e
  | .const fnName _ =>
    match ← getProjectionFnInfo? fnName with
    | some info =>
      if info.fromClass then
        return e
      let args := e.getAppArgs
      if h : info.numParams < args.size then
        let s' ← whnfStruct args[info.numParams]
        match ← safely (constructorApp? s') none with
        | some (cv, cargs) =>
          if cv.name != info.ctorName then
            return e
          if h' : cv.numParams + info.i < cargs.size then
            headReduce (cargs[cv.numParams + info.i].beta
              (args.extract (info.numParams + 1) args.size))
          else
            return e
        | none => return e
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

mutual

/--
Normalise the proposition `e` to an equivalent residual, with `True` and
`False` as the canonical trivial results.
-/
partial def simpProp (e : Expr) : CheckM Expr := do
  unless ← tick do
    return e
  let e ← headReduce e
  match e.getAppFnArgs with
  | (``True, #[]) | (``False, #[]) => return e
  | (``And, #[a, b]) => mkAndS (← simpProp a) (← simpProp b)
  | (``Or, #[a, b]) => mkOrS (← simpProp a) (← simpProp b)
  | (``Not, #[a]) => mkNotS (← simpProp a)
  | (``Iff, #[a, b]) => mkIffS (← simpProp a) (← simpProp b)
  | (``Eq, #[α, a, b]) => simpEq e α a b
  | (``Ne, #[α, a, b]) => mkNotS (← simpEq e α a b)
  | (``HEq, #[α, a, β, b]) =>
    if ← sameExpr α β then
      simpEq e α a b
    else
      normData e
  | (``Exists, #[α, p]) => simpExists α p
  | (``LE.le, #[α, inst, a, b]) => simpRel true e.getAppFn α inst a b
  | (``LT.lt, #[α, inst, a, b]) => simpRel false e.getAppFn α inst a b
  | (``GE.ge, #[α, inst, a, b]) =>
    simpRel true (mkConst ``LE.le e.getAppFn.constLevels!) α inst b a
  | (``GT.gt, #[α, inst, a, b]) =>
    simpRel false (mkConst ``LT.lt e.getAppFn.constLevels!) α inst b a
  | (``ite, #[α, c, _, t, f]) =>
    if α.isProp then
      simpIte (← simpProp c) (← simpProp t) (← simpProp f)
    else
      normData e
  | (``cond, #[α, c, t, f]) =>
    if α.isProp then
      simpIte (← boolToProp c) (← simpProp t) (← simpProp f)
    else
      normData e
  | (``dite, #[α, c, _, t, f]) =>
    if α.isProp then
      let branch (dom fn : Expr) : Expr :=
        .forallE `h dom ((fn.liftLooseBVars 0 1).beta #[.bvar 0]) .default
      mkAndS (← simpProp (branch c t)) (← simpProp (branch (mkNot c) f))
    else
      normData e
  | _ =>
    if e.isForall then
      return ← simpForall e
    if let some r ← collapseMatch? true e then
      return r
    if let .const fn _ := e.getAppFn then
      let ctx ← read
      if ctx.stripBoilerplate && ctx.cfg.boilerplate.contains fn then
        modify fun s => { s with droppedBoilerplate := true }
        return mkConst ``True
    match ← unfoldHead? e with
    | some e' => simpProp e'
    | none => normData e

/-- `if c then t else f` on propositions: `(c → t) ∧ (¬c → f)`. -/
partial def simpIte (c t f : Expr) : CheckM Expr := do
  if t == f then
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
  if α.isProp then
    return ← mkIffS (← simpProp a) (← simpProp b)
  let a ← normData a
  let b ← normData b
  if ← sameExpr a b then
    noteDropped orig
    return mkConst ``True
  let αn ← safely (whnfR α) α
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
  unless (← mentionsOutput e) && (← canUnfoldConst fn) do
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
  let name := if let .lam n .. := p then n else `x
  withLocalDeclD name α fun x => do
    let body ← simpProp (p.beta #[x])
    if isFalseConst body then
      return body
    let cs := conjuncts body
    for i in [0:cs.size] do
      if let some t := onePoint? x cs[i]! then
        let rest := mkAndN (cs.eraseIdxIfInBounds i)
        unless rest.containsFVar x.fvarId! do
          noteDropped cs[i]!
        return ← simpProp (rest.replaceFVar x t)
    if !body.containsFVar x.fvarId! then
      if (← safely (isProp α) false) then
        return ← mkAndS (← simpProp α) body
      if ← typeNonempty α then
        return body
    safely (do mkAppM ``Exists #[← mkLambdaFVars #[x] body])
      (mkApp2 (mkConst ``Exists [Level.one]) α p)

partial def simpForall (e : Expr) : CheckM Expr := do
  let .forallE name dom body bi := e | return e
  let domIsProp ← safely (isProp dom) false
  if domIsProp && !body.hasLooseBVars then
    return ← mkImpS (← simpProp dom) (← simpProp body)
  withLocalDecl name bi dom fun x => do
    let body ← simpProp (body.instantiate1 x)
    if isTrueConst body then
      return body
    if !body.containsFVar x.fvarId! then
      if domIsProp then
        return ← mkImpS (← simpProp dom) body
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
            unless body'.containsFVar x.fvarId! do
              noteDropped cs[i]!
            return ← simpProp (body'.replaceFVar x t)
    mkForallFVars #[x] body

/--
A `match` (or `casesOn`) with a non-dependent motive that is stuck on its
discriminants: normalise the discriminants (which may unblock it), then each
alternative under its pattern variables, and collapse the whole `match` when
all alternatives are one term that ignores them. The result is fully
normalised, so callers do not traverse it again.
-/
partial def collapseMatch? (propLevel : Bool) (e : Expr) :
    CheckM (Option Expr) := do
  let some app ← safely (matchMatcherApp? e (alsoCasesOn := true)) none
    | return none
  unless app.remaining.isEmpty do
    return none
  let motiveOk ← lambdaTelescope app.motive fun xs body =>
    pure !(xs.any fun x => body.containsFVar x.fvarId!)
  unless motiveOk do
    return none
  let discrs ← app.discrs.mapM normData
  let app := { app with discrs }
  let e' := app.toExpr
  let e'' ← headReduce e'
  if e'' != e' then
    return some (← if propLevel then simpProp e'' else normData e'')
  let mut alts : Array Expr := #[]
  let mut common? : Option Expr := none
  let mut collapsible := true
  for alt in app.alts do
    let altTy ← inferType alt
    let (alt', body?) ← forallTelescopeReducing altTy fun ys _ => do
      let body := alt.beta ys
      let body ← if propLevel then simpProp body else normData body
      let indep := !(ys.any fun y => body.containsFVar y.fvarId!)
      return (← mkLambdaFVars ys body, if indep then some body else none)
    alts := alts.push alt'
    match body?, common? with
    | none, _ => collapsible := false
    | some b, none => common? := some b
    | some b, some c =>
      if b != c then
        collapsible := false
  if collapsible then
    if let some c := common? then
      for d in app.discrs do
        noteDropped d
      return some c
  return some ({ app with alts := alts }).toExpr

/--
Normalise a term that is not (known to be) a proposition: beta, zeta, eta,
projections and iota everywhere, `decide`/`ite`/`cond` on a decided condition,
and collapse of stuck constant `match`es. Definitions are not unfolded.
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
        let p' ← simpProp p
        if isTrueConst p' then
          return .done (mkConst ``Bool.true)
        if isFalseConst p' then
          return .done (mkConst ``Bool.false)
        return .continue
      | (``ite, #[_, c, _, t, f]) =>
        let c' ← simpProp c
        if isTrueConst c' then
          return .visit t
        if isFalseConst c' then
          return .visit f
        if t == f then
          noteDropped c
          return .visit t
        return .continue
      | (``cond, #[_, c, t, f]) =>
        let c' ← boolToProp c
        if isTrueConst c' then
          return .visit t
        if isFalseConst c' then
          return .visit f
        if t == f then
          noteDropped c
          return .visit t
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

def BodyAnalysis.anyBound (a : BodyAnalysis) : Bool := a.bound.any id

/--
Normalise `body` with `outputs` designated, then let the proof search discharge
conjuncts mentioning an output and test insensitivity output by output.
-/
def analyzeBody (cfg : EnsuresCheckConfig) (stripBoilerplate : Bool)
    (outputs : Array Expr) (body : Expr) : MetaM BodyAnalysis := do
  let ctx : Context :=
    { cfg, outputs := outputs.map Expr.fvarId!, stripBoilerplate }
  let (res, st) ← ((simpProp body).run ctx).run {}
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
        if ← tryProve c cfg.probeHeartbeats then
          st := { st with droppedOutputTaut := true, semanticStrip := true }
          continue
        if ← tryProve (mkNot c) cfg.probeHeartbeats then
          st := { st with droppedOutputTaut := true, semanticStrip := true }
          refuted := true
          continue
      kept := kept.push c
    res := if refuted then mkConst ``False else mkAndN kept
  let mut bound := outputs.map fun o => res.containsFVar o.fvarId!
  let mut insensitive := false
  if cfg.semanticProbe && small res then
    for i in [0:outputs.size] do
      if bound[i]! then
        let o := outputs[i]!
        let proved ← withLocalDeclD `o' (← inferType o) fun o' =>
          tryProve (mkApp2 (mkConst ``Iff) res (res.replaceFVar o o'))
            cfg.probeHeartbeats
        if proved then
          bound := bound.set! i false
          insensitive := true
  return { residual := res, bound, state := st, provedInsensitive := insensitive }

/-- The reason attached to an analysis in which no output is bound. -/
def classify (a : BodyAnalysis) : EnsuresVacuityReason :=
  if isFalseConst a.residual then
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

def ppResidual (e : Expr) : MetaM String :=
  safely (do return (← ppExpr e).pretty) "<unprintable>"

/-- Generic verdict: binding is occurrence of an output in the residual. -/
def analyzeGeneric (cfg : EnsuresCheckConfig) (kind : String) (body : Expr)
    (binders : Array Expr) (outIdxs retIdxs : Array Nat) :
    MetaM EnsuresCheckReport := do
  let outs := outIdxs.map (binders[·]!)
  let full ← analyzeBody cfg false outs body
  let user ← if full.anyBound then analyzeBody cfg true outs body else pure full
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
    notes := budgetNotes full }

/--
`MirCallAns` verdict: instantiate the answer at each outcome and judge the
`.returned` instance on `(retVal, memAfter)`.
-/
def analyzeMirCallAns (cfg : EnsuresCheckConfig) (kind : String) (body : Expr)
    (binders : Array Expr) (ansIdx : Nat) : MetaM EnsuresCheckReport := do
  let ans := binders[ansIdx]!
  let valTy := mkConst ``Value
  let memTy := mkConst ``Memory
  -- `.aborted` and `.panicked`: only needed to tell outcome-blind from return-blind.
  let aborted ← analyzeBody cfg false #[]
    (body.replaceFVar ans (mkConst ``MirCallAns.aborted))
  let abortedStr ← ppResidual aborted.residual
  let (panicked, panickedStr) ← withLocalDeclD `memAfter memTy fun m => do
    let a ← analyzeBody cfg false #[m]
      (body.replaceFVar ans (mkApp (mkConst ``MirCallAns.panicked) m))
    return (a, ← ppResidual a.residual)
  withLocalDeclD `retVal valTy fun v =>
  withLocalDeclD `memAfter memTy fun m => do
    let inst := body.replaceFVar ans (mkApp2 (mkConst ``MirCallAns.returned) v m)
    let full ← analyzeBody cfg false #[v, m] inst
    let user ← if full.anyBound then analyzeBody cfg true #[v, m] inst
      else pure full
    let eff := if cfg.userEnsuresOnly then user else full
    let reason? : Option EnsuresVacuityReason :=
      if !full.anyBound then
        if isFalseConst full.residual then
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
    let returnedStr ← ppResidual eff.residual
    let boundNote :=
      s!"`.returned retVal memAfter` binds retVal: {eff.bound[0]!}, \
        memAfter: {eff.bound[1]!}"
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
        budgetNotes full }

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
    (binders : Array Expr) (outputParamIdxs : Option (Array Nat)) :
    MetaM EnsuresCheckReport := do
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
  if outIdxs.size == 1 then
    let ansTy ← whnfR (← inferType binders[outIdxs[0]!]!)
    if ansTy.isConstOf ``MirCallAns then
      return ← analyzeMirCallAns cfg kind body binders outIdxs[0]!
  let retIdxs := if stateful && outIdxs.contains 2 then #[2] else outIdxs
  analyzeGeneric cfg kind body binders outIdxs retIdxs

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
-/
def checkEnsuresBindsOutput (postExpr : Expr)
    (outputParamIdxs : Option (Array Nat) := none)
    (cfg : EnsuresCheckConfig := {}) : MetaM EnsuresCheckReport := do
  let postExpr ← instantiateMVars postExpr
  let ty ← inferType postExpr
  forallTelescopeReducing ty fun xs resTy => do
    let resTy ← whnf resTy
    let applied := postExpr.beta xs
    let valTy := mkConst ``Value
    let memTy := mkConst ``Memory
    let argsTy := mkApp (mkConst ``List [Level.zero]) valTy
    if resTy.isProp then
      EnsuresCheck.analyzePost cfg "function" applied xs outputParamIdxs
    else if resTy.isConstOf ``Bool then
      EnsuresCheck.analyzePost cfg "function"
        (← mkEq applied (mkConst ``Bool.true)) xs outputParamIdxs
    else if resTy.isConstOf ``MirCallContract then
      withLocalDeclD `req (mkConst ``MirCallReq) fun req =>
      withLocalDeclD `ans (mkConst ``MirCallAns) fun ans =>
        EnsuresCheck.analyzePost cfg "MirCallContract"
          (mkApp3 (mkConst ``MirCallContract.post) applied req ans)
          #[req, ans] outputParamIdxs
    else if resTy.isConstOf ``Claim then
      withLocalDeclD `args argsTy fun args =>
      withLocalDeclD `ret valTy fun ret =>
        EnsuresCheck.analyzePost cfg "Claim"
          (mkApp3 (mkConst ``Claim.post) applied args ret)
          #[args, ret] outputParamIdxs
    else if resTy.isConstOf ``StatefulClaim then
      withLocalDeclD `args argsTy fun args =>
      withLocalDeclD `mem memTy fun mem =>
      withLocalDeclD `ret valTy fun ret =>
      withLocalDeclD `mem' memTy fun mem' =>
        EnsuresCheck.analyzePost cfg "StatefulClaim"
          (mkApp5 (mkConst ``StatefulClaim.post) applied args mem ret mem')
          #[args, mem, ret, mem'] outputParamIdxs
    else
      throwError "checkEnsuresBindsOutput: expected a postcondition \
        `∀ x₁ … xₙ, Prop`, a `MirCallContract`, a `Claim`, or a \
        `StatefulClaim`, but the result type is{indentExpr resTy}"

/--
`checkEnsuresBindsOutput` on the constant `declName`: a postcondition function,
a `MirCallContract`, a `Claim`, or a `StatefulClaim` (each possibly under
leading parameters).
-/
def checkDeclEnsuresBindsOutput (declName : Name)
    (outputParamIdxs : Option (Array Nat) := none)
    (cfg : EnsuresCheckConfig := {}) : MetaM EnsuresCheckReport := do
  checkEnsuresBindsOutput (← mkConstWithLevelParams declName) outputParamIdxs cfg

/-- Fail unless the postcondition `declName` binds its output. -/
def assertEnsuresBindsOutput (declName : Name)
    (outputParamIdxs : Option (Array Nat) := none)
    (cfg : EnsuresCheckConfig := {}) : MetaM Unit := do
  let r ← checkDeclEnsuresBindsOutput declName outputParamIdxs cfg
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
    (cfg : EnsuresCheckConfig := {}) : MetaM Unit := do
  let r ← checkDeclEnsuresBindsOutput declName outputParamIdxs cfg
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
Refute `e` under its leading existential binders: `¬ ∃ x, P x` follows from
`¬ P x` for a fresh `x`.
-/
partial def EnsuresCheck.refuteUnderExists (cfg : EnsuresCheckConfig)
    (e : Expr) : MetaM Bool := do
  if EnsuresCheck.isFalseConst e then
    return true
  match e.getAppFnArgs with
  | (``Exists, #[α, p]) =>
    withLocalDeclD `x α fun x => refuteUnderExists cfg (p.beta #[x])
  | _ =>
    if !cfg.semanticProbe ||
        EnsuresCheck.sizeUpTo (cfg.probeMaxSize + 1) e > cfg.probeMaxSize then
      return false
    EnsuresCheck.tryProve (mkNot e) cfg.probeHeartbeats

/--
Look for a proof that the precondition `preExpr` is unsatisfiable (vacuity
class 1). `preExpr` is a predicate `∀ x₁ … xₙ, Prop`, or a `MirCallContract`,
`Claim`, or `StatefulClaim` (possibly under leading parameters), whose `pre`
field is analysed. Satisfiability itself is not decided: a report with
`refuted = false` is not a realizability proof.
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
    let run (kind : String) (body : Expr) (arity : Nat) :
        MetaM RequiresCheckReport := do
      let ctx : EnsuresCheck.Context :=
        { cfg, outputs := #[], stripBoilerplate := false }
      let (res, _) ← ((EnsuresCheck.simpProp body).run ctx).run {}
      return {
        kind, arity
        refuted := ← EnsuresCheck.refuteUnderExists cfg res
        residual := ← EnsuresCheck.ppResidual res }
    if resTy.isProp then
      run "function" applied xs.size
    else if resTy.isConstOf ``MirCallContract then
      withLocalDeclD `req (mkConst ``MirCallReq) fun req =>
        run "MirCallContract"
          (mkApp2 (mkConst ``MirCallContract.pre) applied req) 1
    else if resTy.isConstOf ``Claim then
      withLocalDeclD `args argsTy fun args =>
        run "Claim" (mkApp2 (mkConst ``Claim.pre) applied args) 1
    else if resTy.isConstOf ``StatefulClaim then
      withLocalDeclD `args argsTy fun args =>
      withLocalDeclD `mem (mkConst ``Memory) fun mem =>
        run "StatefulClaim"
          (mkApp3 (mkConst ``StatefulClaim.pre) applied args mem) 2
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
