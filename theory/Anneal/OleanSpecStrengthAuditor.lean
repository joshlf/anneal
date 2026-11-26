import Trusted

namespace Anneal.OleanSpecStrengthAuditor

open Trusted.ITree
open Trusted.MirSemantics
open Trusted.VerificationResult

/-!
# Constructive Specification-Strength & Mutant-Kill Certificate Library

Pure, constructive (*DafnyCert*-style, `arXiv:2611.15548`) specification-strength
certificates and negative non-vacuity metatheorems, importing only `Trusted`
(zero `Lean.*` imports, zero `Classical.choice`, zero `partial`, zero `unsafe`,
zero `sorry`).

All definitions and theorems in this module use at most Lean's constructive
axioms (`propext` and `Quot.sound`) and never depend on `Classical.choice`.
-/

universe u v

/-! ## 1. Mutant Categories and Direct Specification-Strength Certificates -/

/-- Classification tags for specification-killing mutants. -/
inductive MutantCategory : Type where
  | wrongReturn
  | wrapOverflow
  | truncatedLength
  | swappedByteOrder
  | offByOneScalar
  | wrongBranchTag
  | unpreservedFrame
  | custom (label : String)
  deriving DecidableEq, BEq, Repr

/--
Single-mutant specification-strength witness for `(req, ens)`:
- `witnessInput` satisfies `req` (refutes vacuous preconditions `V8`),
- `referenceOutput` satisfies `ens witnessInput` (refutes unimplementable postconditions `V9b`),
- `mutantOutput` violates `ens witnessInput` (refutes trivial postconditions `V9a`).
-/
structure SpecStrengthCert {α : Type u} {β : Type v}
    (req : α → Prop) (ens : α → β → Prop) : Type (max u v) where
  witnessInput : α
  witnessValid : req witnessInput
  referenceOutput : β
  referenceAccepted : ens witnessInput referenceOutput
  mutantOutput : β
  mutantRejected : ¬ ens witnessInput mutantOutput

/--
Named, categorized mutant kill at a realizable input (`K1` closure):
requiring an accepted `referenceOutput` on the exact same `input` prevents
vacuous "kills" at inputs where the specification is unimplementable.
-/
structure NamedMutantKill {α : Type u} {β : Type v}
    (req : α → Prop) (ens : α → β → Prop) : Type (max u v) where
  name : String
  category : MutantCategory
  input : α
  inputValid : req input
  referenceOutput : β
  referenceAccepted : ens input referenceOutput
  mutantOutput : β
  mutantRejected : ¬ ens input mutantOutput

/-- Non-empty suite of discriminating, categorized mutant kills. -/
structure MultiMutantSpecCert {α : Type u} {β : Type v}
    (req : α → Prop) (ens : α → β → Prop) : Type (max u v) where
  kills : List (NamedMutantKill req ens)
  nonEmpty : kills ≠ []

/-- Decide whether `cert` contains at least one mutant kill tagged with `cat`. -/
def MultiMutantSpecCert.coversCategory {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (cert : MultiMutantSpecCert req ens) (cat : MutantCategory) : Bool :=
  cert.kills.any (fun k => k.category == cat)

/-- Top-level alias for `MultiMutantSpecCert.coversCategory`. -/
abbrev coversCategory {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (cert : MultiMutantSpecCert req ens) (cat : MutantCategory) : Bool :=
  cert.coversCategory cat

/-- Project any `MultiMutantSpecCert` to a `SpecStrengthCert` constructively. -/
def MultiMutantSpecCert.toSpecStrengthCert {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (cert : MultiMutantSpecCert req ens) : SpecStrengthCert req ens :=
  match h : cert.kills with
  | [] => False.elim (cert.nonEmpty h)
  | k :: _ =>
    { witnessInput := k.input
      witnessValid := k.inputValid
      referenceOutput := k.referenceOutput
      referenceAccepted := k.referenceAccepted
      mutantOutput := k.mutantOutput
      mutantRejected := k.mutantRejected }

/--
Deterministic specification certificate:
- inhabited precondition (`witnessInput`, `witnessValid`),
- non-trivial output domain with a distinct mutant (`mutantDiffers`),
- realizable on every valid input (`realizable`),
- unique accepted output on every valid input (`uniqueOutput`), killing every
  deviating output on every valid input.
-/
structure DeterministicSpecCert {α : Type u} {β : Type v}
    (req : α → Prop) (ens : α → β → Prop) : Type (max u v) where
  witnessInput : α
  witnessValid : req witnessInput
  referenceOutput : β
  referenceAccepted : ens witnessInput referenceOutput
  mutantOutput : β
  mutantDiffers : mutantOutput ≠ referenceOutput
  realizable : ∀ x, req x → ∃ y, ens x y
  uniqueOutput : ∀ x y₁ y₂, req x → ens x y₁ → ens x y₂ → y₁ = y₂

/-- Every deviating output on any valid input is rejected by a deterministic spec. -/
theorem DeterministicSpecCert.killsEveryDeviation {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (cert : DeterministicSpecCert req ens)
    (x : α) (hx : req x) (yRef yMut : β) (href : ens x yRef) (hne : yMut ≠ yRef) :
    ¬ ens x yMut :=
  fun hmut => hne (cert.uniqueOutput x yMut yRef hx hmut href)

/-- Project any `DeterministicSpecCert` to a `SpecStrengthCert` constructively. -/
def DeterministicSpecCert.toSpecStrengthCert {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (cert : DeterministicSpecCert req ens) : SpecStrengthCert req ens where
  witnessInput := cert.witnessInput
  witnessValid := cert.witnessValid
  referenceOutput := cert.referenceOutput
  referenceAccepted := cert.referenceAccepted
  mutantOutput := cert.mutantOutput
  mutantRejected :=
    cert.killsEveryDeviation cert.witnessInput cert.witnessValid
      cert.referenceOutput cert.mutantOutput cert.referenceAccepted cert.mutantDiffers

/--
Input-sensitivity certificate (`S5`): exhibits two valid inputs `(input₁, input₂)`
with accepted outputs `(output₁, output₂)` that are not interchangeable,
rejecting both singleton preconditions (`x = 5`) and input-independent
postconditions (`ens x₁ y ↔ ens x₂ y`).
-/
structure InputSensitiveSpecCert {α : Type u} {β : Type v}
    (req : α → Prop) (ens : α → β → Prop) : Type (max u v) where
  input₁ : α
  valid₁ : req input₁
  output₁ : β
  accepted₁ : ens input₁ output₁
  input₂ : α
  valid₂ : req input₂
  output₂ : β
  accepted₂ : ens input₂ output₂
  nonInterchangeable : ¬ ens input₁ output₂ ∨ ¬ ens input₂ output₁

/-- An `InputSensitiveSpecCert` witnesses that `input₁ ≠ input₂`. -/
theorem InputSensitiveSpecCert.inputs_ne {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (cert : InputSensitiveSpecCert req ens) : cert.input₁ ≠ cert.input₂ := by
  intro hEq
  cases cert.nonInterchangeable with
  | inl h => exact h (hEq ▸ cert.accepted₂)
  | inr h => exact h (hEq ▸ cert.accepted₁)

/-- An `InputSensitiveSpecCert` witnesses that `output₁ ≠ output₂`. -/
theorem InputSensitiveSpecCert.outputs_ne {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (cert : InputSensitiveSpecCert req ens) : cert.output₁ ≠ cert.output₂ := by
  intro hEq
  cases cert.nonInterchangeable with
  | inl h => exact h (hEq ▸ cert.accepted₁)
  | inr h => exact h (hEq ▸ cert.accepted₂)

/-- Constructively derive `Nonempty (SpecStrengthCert req ens)` from input sensitivity. -/
theorem InputSensitiveSpecCert.nonempty_specStrengthCert {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (cert : InputSensitiveSpecCert req ens) : Nonempty (SpecStrengthCert req ens) := by
  cases cert.nonInterchangeable with
  | inl h =>
    exact ⟨{
      witnessInput := cert.input₁
      witnessValid := cert.valid₁
      referenceOutput := cert.output₁
      referenceAccepted := cert.accepted₁
      mutantOutput := cert.output₂
      mutantRejected := h
    }⟩
  | inr h =>
    exact ⟨{
      witnessInput := cert.input₂
      witnessValid := cert.valid₂
      referenceOutput := cert.output₂
      referenceAccepted := cert.accepted₂
      mutantOutput := cert.output₁
      mutantRejected := h
    }⟩

/-! ## 2. Stateful Adapters & Direct Modular Specification Certificates -/

/-- Uncurry a stateful precondition `(List Value → Memory → Prop)` onto `List Value × Memory`. -/
abbrev uncurryPre (pre : List Value → Memory → Prop) : List Value × Memory → Prop :=
  fun p => pre p.1 p.2

/-- Uncurry a stateful postcondition onto `(List Value × Memory) → (Value × Memory) → Prop`. -/
abbrev uncurryPost (post : List Value → Memory → Value → Memory → Prop) :
    List Value × Memory → Value × Memory → Prop :=
  fun p q => post p.1 p.2 q.1 q.2

/-- Direct single-mutant certificate for a `ModularClaim` contract `(envAssumed, pre, post)`. -/
structure ModularSpecStrengthCert
    (envAssumed : ExternalCallHandler → Prop)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Type where
  envNonVacuous : ∃ h, envAssumed h
  specCert : SpecStrengthCert (uncurryPre pre) (uncurryPost post)

/-- Direct multi-mutant certificate for a `ModularClaim` contract `(envAssumed, pre, post)`. -/
structure ModularMultiMutantSpecCert
    (envAssumed : ExternalCallHandler → Prop)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Type where
  envNonVacuous : ∃ h, envAssumed h
  specCert : MultiMutantSpecCert (uncurryPre pre) (uncurryPost post)

/-- Decide whether a modular multi-mutant certificate covers mutant category `cat`. -/
def ModularMultiMutantSpecCert.coversCategory
    {envAssumed : ExternalCallHandler → Prop}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (cert : ModularMultiMutantSpecCert envAssumed pre post)
    (cat : MutantCategory) : Bool :=
  cert.specCert.coversCategory cat

/-- Project a `ModularMultiMutantSpecCert` to a `ModularSpecStrengthCert`. -/
def ModularMultiMutantSpecCert.toModularSpecStrengthCert
    {envAssumed : ExternalCallHandler → Prop}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (cert : ModularMultiMutantSpecCert envAssumed pre post) :
    ModularSpecStrengthCert envAssumed pre post where
  envNonVacuous := cert.envNonVacuous
  specCert := cert.specCert.toSpecStrengthCert

/-- Direct deterministic certificate for a `ModularClaim` contract `(envAssumed, pre, post)`. -/
structure ModularDeterministicSpecCert
    (envAssumed : ExternalCallHandler → Prop)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Type where
  envNonVacuous : ∃ h, envAssumed h
  specCert : DeterministicSpecCert (uncurryPre pre) (uncurryPost post)

/-- Direct input-sensitivity certificate for a `ModularClaim` contract `(envAssumed, pre, post)`. -/
structure ModularInputSensitiveSpecCert
    (envAssumed : ExternalCallHandler → Prop)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Type where
  envNonVacuous : ∃ h, envAssumed h
  specCert : InputSensitiveSpecCert (uncurryPre pre) (uncurryPost post)

/-! ## 3. Typeclass Bridges (`ItemSpec`, `StatefulItemSpec`, `TotalItemSpec`, `ModularItemSpec`) -/

abbrev ItemSpecStrengthCert (defId : String) [inst : ItemSpec defId] : Type :=
  SpecStrengthCert inst.pre inst.post

abbrev ItemMultiMutantSpecCert (defId : String) [inst : ItemSpec defId] : Type :=
  MultiMutantSpecCert inst.pre inst.post

abbrev ItemDeterministicSpecCert (defId : String) [inst : ItemSpec defId] : Type :=
  DeterministicSpecCert inst.pre inst.post

abbrev ItemInputSensitiveSpecCert (defId : String) [inst : ItemSpec defId] : Type :=
  InputSensitiveSpecCert inst.pre inst.post

abbrev StatefulItemSpecStrengthCert (defId : String) [inst : StatefulItemSpec defId] : Type :=
  SpecStrengthCert (uncurryPre inst.pre) (uncurryPost inst.post)

abbrev StatefulItemMultiMutantSpecCert (defId : String) [inst : StatefulItemSpec defId] : Type :=
  MultiMutantSpecCert (uncurryPre inst.pre) (uncurryPost inst.post)

abbrev StatefulItemDeterministicSpecCert (defId : String) [inst : StatefulItemSpec defId] : Type :=
  DeterministicSpecCert (uncurryPre inst.pre) (uncurryPost inst.post)

abbrev StatefulItemInputSensitiveSpecCert (defId : String) [inst : StatefulItemSpec defId] : Type :=
  InputSensitiveSpecCert (uncurryPre inst.pre) (uncurryPost inst.post)

abbrev TotalItemSpecStrengthCert (defId : String) [inst : TotalItemSpec defId] : Type :=
  SpecStrengthCert (uncurryPre inst.pre) (uncurryPost inst.post)

abbrev TotalItemMultiMutantSpecCert (defId : String) [inst : TotalItemSpec defId] : Type :=
  MultiMutantSpecCert (uncurryPre inst.pre) (uncurryPost inst.post)

abbrev TotalItemDeterministicSpecCert (defId : String) [inst : TotalItemSpec defId] : Type :=
  DeterministicSpecCert (uncurryPre inst.pre) (uncurryPost inst.post)

abbrev TotalItemInputSensitiveSpecCert (defId : String) [inst : TotalItemSpec defId] : Type :=
  InputSensitiveSpecCert (uncurryPre inst.pre) (uncurryPost inst.post)

abbrev ModularItemSpecStrengthCert (defId : String) [inst : ModularItemSpec defId] : Type :=
  ModularSpecStrengthCert inst.envAssumed inst.pre inst.post

abbrev ModularItemMultiMutantSpecCert (defId : String) [inst : ModularItemSpec defId] : Type :=
  ModularMultiMutantSpecCert inst.envAssumed inst.pre inst.post

abbrev ModularItemDeterministicSpecCert (defId : String) [inst : ModularItemSpec defId] : Type :=
  ModularDeterministicSpecCert inst.envAssumed inst.pre inst.post

abbrev ModularItemInputSensitiveSpecCert (defId : String) [inst : ModularItemSpec defId] : Type :=
  ModularInputSensitiveSpecCert inst.envAssumed inst.pre inst.post

/-! ## 4. Constructive Negative Metatheorems (`V8`, `V9a`, `V9b`, `V8/Modular`, `S5a`, `S5b`, `K1`) -/

/-- `V8`: No `SpecStrengthCert` can inhabit a vacuous precondition (`∀ x, ¬ req x`). -/
theorem no_cert_of_vacuous_pre {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hVac : ∀ x, ¬ req x) (cert : SpecStrengthCert req ens) : False :=
  hVac cert.witnessInput cert.witnessValid

/-- `V8`: No `MultiMutantSpecCert` can inhabit a vacuous precondition. -/
theorem no_multi_cert_of_vacuous_pre {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hVac : ∀ x, ¬ req x) (cert : MultiMutantSpecCert req ens) : False :=
  no_cert_of_vacuous_pre hVac cert.toSpecStrengthCert

/-- `V8`: No `DeterministicSpecCert` can inhabit a vacuous precondition. -/
theorem no_deterministic_cert_of_vacuous_pre {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hVac : ∀ x, ¬ req x) (cert : DeterministicSpecCert req ens) : False :=
  hVac cert.witnessInput cert.witnessValid

/-- `V8`: No `InputSensitiveSpecCert` can inhabit a vacuous precondition. -/
theorem no_input_sensitive_cert_of_vacuous_pre {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hVac : ∀ x, ¬ req x) (cert : InputSensitiveSpecCert req ens) : False :=
  hVac cert.input₁ cert.valid₁

/-- `V9a`: No `SpecStrengthCert` can inhabit a trivial postcondition (`∀ x y, ens x y`). -/
theorem no_cert_of_trivial_post {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hTriv : ∀ x y, ens x y) (cert : SpecStrengthCert req ens) : False :=
  cert.mutantRejected (hTriv cert.witnessInput cert.mutantOutput)

/-- `V9a`: No `MultiMutantSpecCert` can inhabit a trivial postcondition. -/
theorem no_multi_cert_of_trivial_post {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hTriv : ∀ x y, ens x y) (cert : MultiMutantSpecCert req ens) : False :=
  no_cert_of_trivial_post hTriv cert.toSpecStrengthCert

/-- `V9a`: No `DeterministicSpecCert` can inhabit a trivial postcondition. -/
theorem no_deterministic_cert_of_trivial_post {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hTriv : ∀ x y, ens x y) (cert : DeterministicSpecCert req ens) : False :=
  no_cert_of_trivial_post hTriv cert.toSpecStrengthCert

/-- `V9a`: No `InputSensitiveSpecCert` can inhabit a trivial postcondition. -/
theorem no_input_sensitive_cert_of_trivial_post {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hTriv : ∀ x y, ens x y) (cert : InputSensitiveSpecCert req ens) : False :=
  cert.nonInterchangeable.elim
    (fun h => h (hTriv cert.input₁ cert.output₂))
    (fun h => h (hTriv cert.input₂ cert.output₁))

/-- `V9b`: No `SpecStrengthCert` can inhabit an unimplementable postcondition (`∀ x y, ¬ ens x y`). -/
theorem no_cert_of_unimplementable_post {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hUnimpl : ∀ x y, ¬ ens x y) (cert : SpecStrengthCert req ens) : False :=
  hUnimpl cert.witnessInput cert.referenceOutput cert.referenceAccepted

/-- `V9b`: No `MultiMutantSpecCert` can inhabit an unimplementable postcondition. -/
theorem no_multi_cert_of_unimplementable_post {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hUnimpl : ∀ x y, ¬ ens x y) (cert : MultiMutantSpecCert req ens) : False :=
  no_cert_of_unimplementable_post hUnimpl cert.toSpecStrengthCert

/-- `V9b`: No `DeterministicSpecCert` can inhabit an unimplementable postcondition. -/
theorem no_deterministic_cert_of_unimplementable_post {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hUnimpl : ∀ x y, ¬ ens x y) (cert : DeterministicSpecCert req ens) : False :=
  hUnimpl cert.witnessInput cert.referenceOutput cert.referenceAccepted

/-- `V9b`: No `InputSensitiveSpecCert` can inhabit an unimplementable postcondition. -/
theorem no_input_sensitive_cert_of_unimplementable_post {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hUnimpl : ∀ x y, ¬ ens x y) (cert : InputSensitiveSpecCert req ens) : False :=
  hUnimpl cert.input₁ cert.output₁ cert.accepted₁

/-- `K1`: No `NamedMutantKill` can occur at an unimplementable input `x`. -/
theorem no_kill_at_unimplementable_input {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    {x : α} (hUnimpl : ∀ y, ¬ ens x y)
    (k : NamedMutantKill req ens) (hIn : k.input = x) : False :=
  hUnimpl k.referenceOutput (hIn ▸ k.referenceAccepted)

/-- `V8/Modular`: No `ModularSpecStrengthCert` can inhabit a vacuous rely (`∀ h, ¬ envAssumed h`). -/
theorem no_modular_cert_of_vacuous_envAssumed
    {envAssumed : ExternalCallHandler → Prop}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (hVac : ∀ h, ¬ envAssumed h)
    (cert : ModularSpecStrengthCert envAssumed pre post) : False :=
  let ⟨h, hh⟩ := cert.envNonVacuous
  hVac h hh

/-- `V8/Modular`: No `ModularMultiMutantSpecCert` can inhabit a vacuous rely. -/
theorem no_modular_multi_cert_of_vacuous_envAssumed
    {envAssumed : ExternalCallHandler → Prop}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (hVac : ∀ h, ¬ envAssumed h)
    (cert : ModularMultiMutantSpecCert envAssumed pre post) : False :=
  let ⟨h, hh⟩ := cert.envNonVacuous
  hVac h hh

/-- `V8/Modular`: No `ModularDeterministicSpecCert` can inhabit a vacuous rely. -/
theorem no_modular_deterministic_cert_of_vacuous_envAssumed
    {envAssumed : ExternalCallHandler → Prop}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (hVac : ∀ h, ¬ envAssumed h)
    (cert : ModularDeterministicSpecCert envAssumed pre post) : False :=
  let ⟨h, hh⟩ := cert.envNonVacuous
  hVac h hh

/-- `V8/Modular`: No `ModularInputSensitiveSpecCert` can inhabit a vacuous rely. -/
theorem no_modular_input_sensitive_cert_of_vacuous_envAssumed
    {envAssumed : ExternalCallHandler → Prop}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (hVac : ∀ h, ¬ envAssumed h)
    (cert : ModularInputSensitiveSpecCert envAssumed pre post) : False :=
  let ⟨h, hh⟩ := cert.envNonVacuous
  hVac h hh

/-- `S5a`: A singleton precondition (`∀ x₁ x₂, req x₁ → req x₂ → x₁ = x₂`) cannot inhabit
`InputSensitiveSpecCert`. -/
theorem no_input_sensitive_cert_of_singleton_req {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hSing : ∀ x₁ x₂, req x₁ → req x₂ → x₁ = x₂)
    (cert : InputSensitiveSpecCert req ens) : False :=
  cert.inputs_ne (hSing cert.input₁ cert.input₂ cert.valid₁ cert.valid₂)

/-- `S5b`: An input-independent postcondition (`∀ x₁ x₂ y, ens x₁ y ↔ ens x₂ y`) cannot inhabit
`InputSensitiveSpecCert`. -/
theorem no_input_sensitive_cert_of_input_independent_ens {α : Type u} {β : Type v}
    {req : α → Prop} {ens : α → β → Prop}
    (hIndep : ∀ x₁ x₂ y, ens x₁ y ↔ ens x₂ y)
    (cert : InputSensitiveSpecCert req ens) : False :=
  cert.nonInterchangeable.elim
    (fun h => h ((hIndep cert.input₂ cert.input₁ cert.output₂).mp cert.accepted₂))
    (fun h => h ((hIndep cert.input₁ cert.input₂ cert.output₁).mp cert.accepted₁))

/-- `S5a/Modular`: A singleton stateful precondition cannot inhabit `ModularInputSensitiveSpecCert`. -/
theorem no_modular_input_sensitive_cert_of_singleton_pre
    {envAssumed : ExternalCallHandler → Prop}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (hSing : ∀ p₁ p₂, uncurryPre pre p₁ → uncurryPre pre p₂ → p₁ = p₂)
    (cert : ModularInputSensitiveSpecCert envAssumed pre post) : False :=
  no_input_sensitive_cert_of_singleton_req hSing cert.specCert

/-- `S5b/Modular`: An input-independent stateful postcondition cannot inhabit
`ModularInputSensitiveSpecCert`. -/
theorem no_modular_input_sensitive_cert_of_input_independent_post
    {envAssumed : ExternalCallHandler → Prop}
    {pre : List Value → Memory → Prop}
    {post : List Value → Memory → Value → Memory → Prop}
    (hIndep : ∀ p₁ p₂ q, uncurryPost post p₁ q ↔ uncurryPost post p₂ q)
    (cert : ModularInputSensitiveSpecCert envAssumed pre post) : False :=
  no_input_sensitive_cert_of_input_independent_ens hIndep cert.specCert

/-! ## 5. Faithful Constructive Model: `fxfs_storage_boundary::vmo_subslice_bounds_valid` -/

/--
Faithful model of `Specs.FxfsStorageBoundary.vmo_subslice_bounds_valid.pre`:
universal precondition over `(base_offset, buf_len, sub_start, sub_end)` with
`sub_start ≤ sub_end ≤ buf_len` and `base_offset + buf_len < 2^64`.
-/
def fxfsVmoSubslicePre (args : List Value) : Prop :=
  ∃ (base len s e : Nat),
    s ≤ e ∧
    e ≤ len ∧
    base + len < 18446744073709551616 ∧
    args =
      [ .scalar { bits := base, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := s, sizeBytes := 8 }
      , .scalar { bits := e, sizeBytes := 8 } ]

/--
Faithful model of `Specs.FxfsStorageBoundary.vmo_subslice_bounds_valid.post`:
exact return value `base + (e - s)` as an 8-byte scalar.
-/
def fxfsVmoSubslicePost (args : List Value) (ret : Value) : Prop :=
  ∀ (base len s e : Nat),
    args =
      [ .scalar { bits := base, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := s, sizeBytes := 8 }
      , .scalar { bits := e, sizeBytes := 8 } ] →
    ret = .scalar { bits := base + (e - s), sizeBytes := 8 }

private def fxfsArgs (base len s e : Nat) : List Value :=
  [ .scalar { bits := base, sizeBytes := 8 }
  , .scalar { bits := len, sizeBytes := 8 }
  , .scalar { bits := s, sizeBytes := 8 }
  , .scalar { bits := e, sizeBytes := 8 } ]

private theorem fxfsVmoSubslicePost_of_args (base len s e : Nat) :
    fxfsVmoSubslicePost (fxfsArgs base len s e)
      (.scalar { bits := base + (e - s), sizeBytes := 8 }) := by
  intro base' len' s' e' hEq
  dsimp [fxfsArgs] at hEq
  injection hEq with h1 t1
  injection t1 with h2 t2
  injection t2 with h3 t3
  injection t3 with h4 _
  injection h1 with h1s
  injection h1s with hb _
  injection h3 with h3s
  injection h3s with hs _
  injection h4 with h4s
  injection h4s with he _
  subst hb; subst hs; subst he
  rfl

private theorem fxfsVmoSubslicePost_reject (base len s e badBits : Nat)
    (hne : badBits ≠ base + (e - s)) :
    ¬ fxfsVmoSubslicePost (fxfsArgs base len s e)
        (.scalar { bits := badBits, sizeBytes := 8 }) := by
  intro hPost
  have h := hPost base len s e rfl
  injection h with hs
  injection hs with hbits _
  exact hne hbits

/--
5-kill `MultiMutantSpecCert` for `fxfs_storage_boundary::vmo_subslice_bounds_valid`
covering `wrongReturn`, `wrapOverflow`, `truncatedLength`, `swappedByteOrder`,
and `offByOneScalar` (0 axioms).
-/
def fxfsVmoSubsliceMultiCert : MultiMutantSpecCert fxfsVmoSubslicePre fxfsVmoSubslicePost where
  kills :=
    [ { name := "fxfs_wrong_return_zero"
        category := .wrongReturn
        input := fxfsArgs 100 64 10 30
        inputValid := ⟨100, 64, 10, 30, Nat.le_add_right 10 20, Nat.le_add_right 30 34, by decide, rfl⟩
        referenceOutput := .scalar { bits := 120, sizeBytes := 8 }
        referenceAccepted := fxfsVmoSubslicePost_of_args 100 64 10 30
        mutantOutput := .scalar { bits := 0, sizeBytes := 8 }
        mutantRejected := fxfsVmoSubslicePost_reject 100 64 10 30 0 (by decide) }
    , { name := "fxfs_wrap_overflow_u32_trunc"
        category := .wrapOverflow
        input := fxfsArgs 4294967296 64 0 16
        inputValid := ⟨4294967296, 64, 0, 16, Nat.zero_le 16, by decide, by decide, rfl⟩
        referenceOutput := .scalar { bits := 4294967312, sizeBytes := 8 }
        referenceAccepted := fxfsVmoSubslicePost_of_args 4294967296 64 0 16
        mutantOutput := .scalar { bits := 16, sizeBytes := 8 }
        mutantRejected := fxfsVmoSubslicePost_reject 4294967296 64 0 16 16 (by decide) }
    , { name := "fxfs_truncated_length_drops_subslice"
        category := .truncatedLength
        input := fxfsArgs 100 64 8 40
        inputValid := ⟨100, 64, 8, 40, by decide, by decide, by decide, rfl⟩
        referenceOutput := .scalar { bits := 132, sizeBytes := 8 }
        referenceAccepted := fxfsVmoSubslicePost_of_args 100 64 8 40
        mutantOutput := .scalar { bits := 100, sizeBytes := 8 }
        mutantRejected := fxfsVmoSubslicePost_reject 100 64 8 40 100 (by decide) }
    , { name := "fxfs_swapped_byte_order"
        category := .swappedByteOrder
        input := fxfsArgs 0x0102 0x0040 0 0x0010
        inputValid := ⟨0x0102, 0x0040, 0, 0x0010, Nat.zero_le _, by decide, by decide, rfl⟩
        referenceOutput := .scalar { bits := 0x0112, sizeBytes := 8 }
        referenceAccepted := fxfsVmoSubslicePost_of_args 0x0102 0x0040 0 0x0010
        mutantOutput := .scalar { bits := 0x1201, sizeBytes := 8 }
        mutantRejected := fxfsVmoSubslicePost_reject 0x0102 0x0040 0 0x0010 0x1201 (by decide) }
    , { name := "fxfs_off_by_one_scalar"
        category := .offByOneScalar
        input := fxfsArgs 100 64 10 30
        inputValid := ⟨100, 64, 10, 30, by decide, by decide, by decide, rfl⟩
        referenceOutput := .scalar { bits := 120, sizeBytes := 8 }
        referenceAccepted := fxfsVmoSubslicePost_of_args 100 64 10 30
        mutantOutput := .scalar { bits := 121, sizeBytes := 8 }
        mutantRejected := fxfsVmoSubslicePost_reject 100 64 10 30 121 (by decide) }
    ]
  nonEmpty := by intro h; nomatch h

/-- Constructive `DeterministicSpecCert` for `fxfs_storage_boundary::vmo_subslice_bounds_valid` (0 axioms). -/
def fxfsVmoSubslice_deterministic :
    DeterministicSpecCert fxfsVmoSubslicePre fxfsVmoSubslicePost where
  witnessInput := fxfsArgs 100 64 10 30
  witnessValid := ⟨100, 64, 10, 30, by decide, by decide, by decide, rfl⟩
  referenceOutput := .scalar { bits := 120, sizeBytes := 8 }
  referenceAccepted := fxfsVmoSubslicePost_of_args 100 64 10 30
  mutantOutput := .scalar { bits := 121, sizeBytes := 8 }
  mutantDiffers := by intro h; injection h with hs; injection hs with hb; exact absurd hb (by decide)
  realizable := by
    intro args ⟨base, len, s, e, _, _, _, hArgs⟩
    refine ⟨.scalar { bits := base + (e - s), sizeBytes := 8 }, ?_⟩
    rw [hArgs]
    exact fxfsVmoSubslicePost_of_args base len s e
  uniqueOutput := by
    intro args y₁ y₂ ⟨base, len, s, e, _, _, _, hArgs⟩ hy₁ hy₂
    have h1 := hy₁ base len s e hArgs
    have h2 := hy₂ base len s e hArgs
    exact h1.trans h2.symm

/-- Constructive `InputSensitiveSpecCert` for `fxfs_storage_boundary::vmo_subslice_bounds_valid` (0 axioms). -/
def fxfsVmoSubsliceInputSensitive :
    InputSensitiveSpecCert fxfsVmoSubslicePre fxfsVmoSubslicePost where
  input₁ := fxfsArgs 100 64 10 30
  valid₁ := ⟨100, 64, 10, 30, by decide, by decide, by decide, rfl⟩
  output₁ := .scalar { bits := 120, sizeBytes := 8 }
  accepted₁ := fxfsVmoSubslicePost_of_args 100 64 10 30
  input₂ := fxfsArgs 200 64 10 30
  valid₂ := ⟨200, 64, 10, 30, by decide, by decide, by decide, rfl⟩
  output₂ := .scalar { bits := 220, sizeBytes := 8 }
  accepted₂ := fxfsVmoSubslicePost_of_args 200 64 10 30
  nonInterchangeable := Or.inl (fxfsVmoSubslicePost_reject 100 64 10 30 220 (by decide))

/-- Model-scoped `ItemSpec` instance for `fxfs_storage_boundary::vmo_subslice_bounds_valid`
(namespaced with `anneal_model::` so it never collides with crate `Specs.*` instances). -/
instance instFxfsModelItemSpec :
    ItemSpec "anneal_model::fxfs_storage_boundary::vmo_subslice_bounds_valid" where
  pre := fxfsVmoSubslicePre
  post := fxfsVmoSubslicePost

/-- Model-scoped `StatefulItemSpec` instance for `fxfs_storage_boundary::vmo_subslice_bounds_valid`. -/
instance instFxfsModelStatefulItemSpec :
    StatefulItemSpec "anneal_model::fxfs_storage_boundary::vmo_subslice_bounds_valid" where
  pre := fun args mem => fxfsVmoSubslicePre args ∧ mem = emptyMemory
  post := fun args _ ret _ => fxfsVmoSubslicePost args ret

def fxfsModelItemMultiCert :
    ItemMultiMutantSpecCert "anneal_model::fxfs_storage_boundary::vmo_subslice_bounds_valid" :=
  fxfsVmoSubsliceMultiCert

def fxfsModelItemDetCert :
    ItemDeterministicSpecCert "anneal_model::fxfs_storage_boundary::vmo_subslice_bounds_valid" :=
  fxfsVmoSubslice_deterministic

def fxfsModelItemInputSensitiveCert :
    ItemInputSensitiveSpecCert "anneal_model::fxfs_storage_boundary::vmo_subslice_bounds_valid" :=
  fxfsVmoSubsliceInputSensitive

/-! ## 6. Faithful Constructive Model: `fuchsia_usercopy::usercopy_copyin_bracketed` -/

/--
Faithful model of `Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.pre`:
universal precondition over `(in_range, dest_len, fault_offset, normal_mode_dest_valid)`.
-/
def fuchsiaUsercopyCopyinPre (args : List Value) (mem : Memory) : Prop :=
  ∃ (in_range dest_len fo v : Nat),
    (in_range = 0 ∨ in_range = 1) ∧
    fo ≤ dest_len ∧
    dest_len < 18446744073709551616 ∧
    (v = 0 ∨ v = 1) ∧
    args =
      [ .scalar { bits := in_range, sizeBytes := 1 }
      , .scalar { bits := dest_len, sizeBytes := 8 }
      , .scalar { bits := fo, sizeBytes := 8 }
      , .scalar { bits := v, sizeBytes := 1 } ] ∧
    mem = emptyMemory

/--
Faithful model of `Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.post`:
preserves `mem` and returns `(fo, dest_len - fo)` when `in_range = 1` or
`(0, dest_len)` when `in_range = 0`.
-/
def fuchsiaUsercopyCopyinPost (args : List Value) (mem : Memory)
    (ret : Value) (mem' : Memory) : Prop :=
  mem' = mem ∧
  ∀ (in_range dest_len fo v : Nat),
    args =
      [ .scalar { bits := in_range, sizeBytes := 1 }
      , .scalar { bits := dest_len, sizeBytes := 8 }
      , .scalar { bits := fo, sizeBytes := 8 }
      , .scalar { bits := v, sizeBytes := 1 } ] →
    if in_range = 1 then
      ret = .aggregate 0
        [ .scalar { bits := fo, sizeBytes := 8 }
        , .scalar { bits := dest_len - fo, sizeBytes := 8 } ]
    else
      ret = .aggregate 0
        [ .scalar { bits := 0, sizeBytes := 8 }
        , .scalar { bits := dest_len, sizeBytes := 8 } ]

/-- Faithful model of `Specs.FuchsiaUsercopy.hermetic_copy_stub.pre`. -/
def fuchsiaHermeticStubPre (args : List Value) (mem : Memory) : Prop :=
  ∃ (count fault_offset v : Nat),
    fault_offset ≤ count ∧
    count < 18446744073709551616 ∧
    (v = 0 ∨ v = 1) ∧
    args =
      [ .scalar { bits := count, sizeBytes := 8 }
      , .scalar { bits := fault_offset, sizeBytes := 8 }
      , .scalar { bits := v, sizeBytes := 1 } ] ∧
    mem = emptyMemory

/-- Faithful model of `Specs.FuchsiaUsercopy.hermetic_copy_stub.post`. -/
def fuchsiaHermeticStubPost (args : List Value) (mem : Memory)
    (ret : Value) (mem' : Memory) : Prop :=
  mem' = mem ∧
  ∀ (count fault_offset v : Nat),
    args =
      [ .scalar { bits := count, sizeBytes := 8 }
      , .scalar { bits := fault_offset, sizeBytes := 8 }
      , .scalar { bits := v, sizeBytes := 1 } ] →
    ret = .scalar { bits := fault_offset, sizeBytes := 8 } ∧
    fault_offset ≤ count

/-- Modular call contract modeling `hermetic_copy_stub.ubExceptionClaim.callContract`. -/
def fuchsiaHermeticStubCallContract : MirCallContract where
  pre req :=
    req.defPath = "fuchsia_usercopy::hermetic_copy_stub" ∧
    fuchsiaHermeticStubPre req.args req.memory
  post req ans :=
    ∃ retVal mem',
      ans = .returned retVal mem' ∧
      fuchsiaHermeticStubPost req.args req.memory retVal mem'

/-- Rely predicate `envAssumed` for `fuchsia_usercopy::usercopy_copyin_bracketed`. -/
def fuchsiaUsercopyCopyinRely : ExternalCallHandler → Prop :=
  fuchsiaHermeticStubCallContract.holdsOn

/-- Pure constructive `ExternalCallHandler` witness returning `ITree.ret` (0 `Classical.choice`). -/
def fuchsiaHermeticStubWitnessHandler : ExternalCallHandler := fun req =>
  match req.args with
  | [_, .scalar fo, _] =>
    ITree.ret (.returned (.scalar { bits := fo.bits, sizeBytes := 8 }) req.memory)
  | _ =>
    ITree.ret .aborted

private theorem tauStar_ret_eq {E : Trusted.Effect.Effect.{0}} {R : Type} {r : R} {u : ITree E R}
    (h : TauStar (ITree.ret r) u) : u = ITree.ret r := by
  cases h with
  | refl => rfl
  | step hObs _ =>
    rw [ITree.observe_ret] at hObs
    nomatch hObs

private theorem reaches_ret_eq {E : Trusted.Effect.Effect.{0}} {R : Type} [Trusted.Effect.FaultEffect E]
    {r : R} {tr : List (Trusted.Effect.Event E)} {u : ITree E R}
    (h : Reaches (ITree.ret r) tr u) : tr = [] ∧ u = ITree.ret r := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | tau hObs _ =>
    rw [ITree.observe_ret] at hObs
    nomatch hObs
  | vis hObs _ _ _ =>
    rw [ITree.observe_ret] at hObs
    nomatch hObs

private theorem treeSafe_ret {E : Trusted.Effect.Effect.{0}} {R : Type} [Trusted.Effect.FaultEffect E]
    (r : R) : TreeSafe (ITree.ret (E := E) r) := by
  intro tr u hReach ⟨t', i, k, hTau, hObs, _⟩
  have ⟨_, hu⟩ := reaches_ret_eq hReach
  subst hu
  have ht := tauStar_ret_eq hTau
  subst ht
  rw [ITree.observe_ret] at hObs
  nomatch hObs

private theorem reachesRet_ret_eq {E : Trusted.Effect.Effect.{0}} {R : Type} [Trusted.Effect.FaultEffect E]
    {r ans : R} {tr : List (Trusted.Effect.Event E)}
    (h : ReachesRet (ITree.ret (E := E) r) tr ans) : ans = r := by
  rcases h with ⟨u, hReach, hObs⟩
  have ⟨_, hu⟩ := reaches_ret_eq hReach
  subst hu
  rw [ITree.observe_ret] at hObs
  injection hObs with hEq
  exact hEq.symm

/-- Constructive non-vacuity proof for `fuchsiaUsercopyCopyinRely` (axioms `⊆ [propext, Quot.sound]`,
zero `Classical.choice`). -/
theorem fuchsiaUsercopyCopyinRely_nonVacuous : ∃ h, fuchsiaUsercopyCopyinRely h := by
  refine ⟨fuchsiaHermeticStubWitnessHandler, ?_⟩
  intro req ⟨_, hPre⟩
  rcases hPre with ⟨count, fo, v, hLe, _, _, hArgs, _⟩
  have hHandler :
      fuchsiaHermeticStubWitnessHandler req =
        ITree.ret (.returned (.scalar { bits := fo, sizeBytes := 8 }) req.memory) := by
    dsimp [fuchsiaHermeticStubWitnessHandler]
    rw [hArgs]
  rw [hHandler]
  refine ⟨treeSafe_ret _, ?_⟩
  intro tr ans hRet
  have hAns := reachesRet_ret_eq hRet
  subst hAns
  refine ⟨.scalar { bits := fo, sizeBytes := 8 }, req.memory, rfl, rfl, ?_⟩
  intro count' fo' v' hArgs'
  rw [hArgs] at hArgs'
  injection hArgs' with h1 t1
  injection t1 with h2 _
  injection h1 with h1s
  injection h1s with hc _
  injection h2 with h2s
  injection h2s with hfo _
  subst hc; subst hfo
  exact ⟨rfl, hLe⟩

private def usercopyArgs (in_range dest_len fo v : Nat) : List Value :=
  [ .scalar { bits := in_range, sizeBytes := 1 }
  , .scalar { bits := dest_len, sizeBytes := 8 }
  , .scalar { bits := fo, sizeBytes := 8 }
  , .scalar { bits := v, sizeBytes := 1 } ]

private def usercopyPair (a b : Nat) : Value :=
  .aggregate 0 [ .scalar { bits := a, sizeBytes := 8 }, .scalar { bits := b, sizeBytes := 8 } ]

private theorem usercopyPost_of_args (in_range dest_len fo v : Nat) (mem : Memory) :
    fuchsiaUsercopyCopyinPost (usercopyArgs in_range dest_len fo v) mem
      (if in_range = 1 then usercopyPair fo (dest_len - fo) else usercopyPair 0 dest_len) mem := by
  refine ⟨rfl, ?_⟩
  intro ir' dl' fo' v' hEq
  dsimp [usercopyArgs] at hEq
  injection hEq with h1 t1
  injection t1 with h2 t2
  injection t2 with h3 _
  injection h1 with h1s; injection h1s with hir _
  injection h2 with h2s; injection h2s with hdl _
  injection h3 with h3s; injection h3s with hfo _
  subst hir; subst hdl; subst hfo
  split <;> rfl

private theorem usercopyPost_reject_val (in_range dest_len fo v a b : Nat) (mem : Memory)
    (hne : usercopyPair a b ≠
      (if in_range = 1 then usercopyPair fo (dest_len - fo) else usercopyPair 0 dest_len)) :
    ¬ fuchsiaUsercopyCopyinPost (usercopyArgs in_range dest_len fo v) mem
        (usercopyPair a b) mem := by
  intro ⟨_, h⟩
  have hEq := h in_range dest_len fo v rfl
  split at hEq
  · rename_i h1
    split at hne
    · exact hne hEq
    · rename_i h0; exact h0 h1
  · rename_i h0
    split at hne
    · rename_i h1; exact h0 h1
    · exact hne hEq

private def mutatedFrameMem : Memory :=
  { emptyMemory with nextAllocId := 1 }

private theorem mutatedFrameMem_ne_empty : mutatedFrameMem ≠ emptyMemory := by
  intro h
  have hId : mutatedFrameMem.nextAllocId = emptyMemory.nextAllocId :=
    congrArg (fun m : Memory => m.nextAllocId) h
  exact Nat.noConfusion hId

/--
5-kill `MultiMutantSpecCert` for `fuchsia_usercopy::usercopy_copyin_bracketed`
covering `wrongBranchTag` (both directions), `truncatedLength`, `offByOneScalar`,
and `unpreservedFrame` (0 axioms).
-/
def fuchsiaUsercopyCopyinMultiCert :
    MultiMutantSpecCert (uncurryPre fuchsiaUsercopyCopyinPre) (uncurryPost fuchsiaUsercopyCopyinPost) where
  kills :=
    [ { name := "usercopy_wrong_branch_in_range_true_takes_false_arm"
        category := .wrongBranchTag
        input := (usercopyArgs 1 64 16 1, emptyMemory)
        inputValid := ⟨1, 64, 16, 1, Or.inr rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
        referenceOutput := (usercopyPair 16 48, emptyMemory)
        referenceAccepted := usercopyPost_of_args 1 64 16 1 emptyMemory
        mutantOutput := (usercopyPair 0 64, emptyMemory)
        mutantRejected := usercopyPost_reject_val 1 64 16 1 0 64 emptyMemory (by
          intro h; injection h with _ hL; injection hL with h0 _; injection h0 with hs
          injection hs with hb _; exact absurd hb (by decide)) }
    , { name := "usercopy_wrong_branch_in_range_false_takes_true_arm"
        category := .wrongBranchTag
        input := (usercopyArgs 0 64 16 1, emptyMemory)
        inputValid := ⟨0, 64, 16, 1, Or.inl rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
        referenceOutput := (usercopyPair 0 64, emptyMemory)
        referenceAccepted := usercopyPost_of_args 0 64 16 1 emptyMemory
        mutantOutput := (usercopyPair 16 48, emptyMemory)
        mutantRejected := usercopyPost_reject_val 0 64 16 1 16 48 emptyMemory (by
          intro h; injection h with _ hL; injection hL with h0 _; injection h0 with hs
          injection hs with hb _; exact absurd hb (by decide)) }
    , { name := "usercopy_truncated_length_zero_remaining"
        category := .truncatedLength
        input := (usercopyArgs 1 64 16 1, emptyMemory)
        inputValid := ⟨1, 64, 16, 1, Or.inr rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
        referenceOutput := (usercopyPair 16 48, emptyMemory)
        referenceAccepted := usercopyPost_of_args 1 64 16 1 emptyMemory
        mutantOutput := (usercopyPair 16 0, emptyMemory)
        mutantRejected := usercopyPost_reject_val 1 64 16 1 16 0 emptyMemory (by
          intro h; injection h with _ hL; injection hL with _ hT; injection hT with h1 _
          injection h1 with hs; injection hs with hb _; exact absurd hb (by decide)) }
    , { name := "usercopy_off_by_one_fault_offset"
        category := .offByOneScalar
        input := (usercopyArgs 1 64 16 1, emptyMemory)
        inputValid := ⟨1, 64, 16, 1, Or.inr rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
        referenceOutput := (usercopyPair 16 48, emptyMemory)
        referenceAccepted := usercopyPost_of_args 1 64 16 1 emptyMemory
        mutantOutput := (usercopyPair 17 48, emptyMemory)
        mutantRejected := usercopyPost_reject_val 1 64 16 1 17 48 emptyMemory (by
          intro h; injection h with _ hL; injection hL with h0 _; injection h0 with hs
          injection hs with hb _; exact absurd hb (by decide)) }
    , { name := "usercopy_unpreserved_memory_frame"
        category := .unpreservedFrame
        input := (usercopyArgs 1 64 16 1, emptyMemory)
        inputValid := ⟨1, 64, 16, 1, Or.inr rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
        referenceOutput := (usercopyPair 16 48, emptyMemory)
        referenceAccepted := usercopyPost_of_args 1 64 16 1 emptyMemory
        mutantOutput := (usercopyPair 16 48, mutatedFrameMem)
        mutantRejected := fun ⟨hMem, _⟩ => mutatedFrameMem_ne_empty hMem }
    ]
  nonEmpty := by intro h; nomatch h

/-- Constructive `DeterministicSpecCert` for `fuchsia_usercopy::usercopy_copyin_bracketed` (0 axioms). -/
def fuchsiaUsercopyCopyin_deterministic :
    DeterministicSpecCert (uncurryPre fuchsiaUsercopyCopyinPre) (uncurryPost fuchsiaUsercopyCopyinPost) where
  witnessInput := (usercopyArgs 1 64 16 1, emptyMemory)
  witnessValid := ⟨1, 64, 16, 1, Or.inr rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
  referenceOutput := (usercopyPair 16 48, emptyMemory)
  referenceAccepted := usercopyPost_of_args 1 64 16 1 emptyMemory
  mutantOutput := (usercopyPair 16 48, mutatedFrameMem)
  mutantDiffers := fun h => mutatedFrameMem_ne_empty (congrArg Prod.snd h)
  realizable := by
    intro ⟨args, mem⟩ ⟨ir, dl, fo, v, _, _, _, _, hArgs, _⟩
    dsimp [uncurryPre] at hArgs
    refine ⟨(if ir = 1 then usercopyPair fo (dl - fo) else usercopyPair 0 dl, mem), ?_⟩
    dsimp [uncurryPost]
    rw [hArgs]
    exact usercopyPost_of_args ir dl fo v mem
  uniqueOutput := by
    intro ⟨args, mem⟩ ⟨r₁, m₁⟩ ⟨r₂, m₂⟩ ⟨ir, dl, fo, v, _, _, _, _, hArgs, _⟩ ⟨hm₁, hr₁⟩ ⟨hm₂, hr₂⟩
    dsimp [uncurryPre] at hArgs
    have h1 := hr₁ ir dl fo v hArgs
    have h2 := hr₂ ir dl fo v hArgs
    have hMemEq : m₁ = m₂ := hm₁.trans hm₂.symm
    have hRetEq : r₁ = r₂ := by
      split at h1
      · rename_i hpos
        split at h2
        · exact h1.trans h2.symm
        · rename_i hneg; exact absurd hpos hneg
      · rename_i hneg
        split at h2
        · rename_i hpos; exact absurd hpos hneg
        · exact h1.trans h2.symm
    cases hRetEq; cases hMemEq; rfl

/-- Constructive `InputSensitiveSpecCert` for `fuchsia_usercopy::usercopy_copyin_bracketed` (0 axioms). -/
def fuchsiaUsercopyCopyinInputSensitive :
    InputSensitiveSpecCert (uncurryPre fuchsiaUsercopyCopyinPre) (uncurryPost fuchsiaUsercopyCopyinPost) where
  input₁ := (usercopyArgs 1 64 16 1, emptyMemory)
  valid₁ := ⟨1, 64, 16, 1, Or.inr rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
  output₁ := (usercopyPair 16 48, emptyMemory)
  accepted₁ := usercopyPost_of_args 1 64 16 1 emptyMemory
  input₂ := (usercopyArgs 0 64 16 1, emptyMemory)
  valid₂ := ⟨0, 64, 16, 1, Or.inl rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
  output₂ := (usercopyPair 0 64, emptyMemory)
  accepted₂ := usercopyPost_of_args 0 64 16 1 emptyMemory
  nonInterchangeable := Or.inl (usercopyPost_reject_val 1 64 16 1 0 64 emptyMemory (by
    intro h; injection h with _ hL; injection hL with h0 _; injection h0 with hs
    injection hs with hb _; exact absurd hb (by decide)))

/-- Direct modular multi-mutant certificate for `fuchsia_usercopy::usercopy_copyin_bracketed`
(constructive `[propext, Quot.sound]`, zero `Classical.choice`). -/
def fuchsiaUsercopyCopyinModularDirectMultiCert :
    ModularMultiMutantSpecCert fuchsiaUsercopyCopyinRely
      fuchsiaUsercopyCopyinPre fuchsiaUsercopyCopyinPost where
  envNonVacuous := fuchsiaUsercopyCopyinRely_nonVacuous
  specCert := fuchsiaUsercopyCopyinMultiCert

/-- Direct modular deterministic certificate for `fuchsia_usercopy::usercopy_copyin_bracketed`. -/
def fuchsiaUsercopyCopyinModularDirectDetCert :
    ModularDeterministicSpecCert fuchsiaUsercopyCopyinRely
      fuchsiaUsercopyCopyinPre fuchsiaUsercopyCopyinPost where
  envNonVacuous := fuchsiaUsercopyCopyinRely_nonVacuous
  specCert := fuchsiaUsercopyCopyin_deterministic

/-- Direct modular input-sensitivity certificate for `fuchsia_usercopy::usercopy_copyin_bracketed`. -/
def fuchsiaUsercopyCopyinModularDirectInputSensitiveCert :
    ModularInputSensitiveSpecCert fuchsiaUsercopyCopyinRely
      fuchsiaUsercopyCopyinPre fuchsiaUsercopyCopyinPost where
  envNonVacuous := fuchsiaUsercopyCopyinRely_nonVacuous
  specCert := fuchsiaUsercopyCopyinInputSensitive

/-- Model-scoped `StatefulItemSpec` instance for `fuchsia_usercopy::usercopy_copyin_bracketed`. -/
instance instFuchsiaModelStatefulItemSpec :
    StatefulItemSpec "anneal_model::fuchsia_usercopy::usercopy_copyin_bracketed" where
  pre := fuchsiaUsercopyCopyinPre
  post := fuchsiaUsercopyCopyinPost

/-- Model-scoped `ModularItemSpec` instance for `fuchsia_usercopy::usercopy_copyin_bracketed`. -/
instance instFuchsiaModelModularItemSpec :
    ModularItemSpec "anneal_model::fuchsia_usercopy::usercopy_copyin_bracketed" where
  envAssumed := fuchsiaUsercopyCopyinRely
  pre := fuchsiaUsercopyCopyinPre
  post := fuchsiaUsercopyCopyinPost

def fuchsiaModelStatefulItemMultiCert :
    StatefulItemMultiMutantSpecCert "anneal_model::fuchsia_usercopy::usercopy_copyin_bracketed" :=
  fuchsiaUsercopyCopyinMultiCert

def fuchsiaModelModularItemMultiCert :
    ModularItemMultiMutantSpecCert "anneal_model::fuchsia_usercopy::usercopy_copyin_bracketed" :=
  fuchsiaUsercopyCopyinModularDirectMultiCert

def fuchsiaModelModularItemDetCert :
    ModularItemDeterministicSpecCert "anneal_model::fuchsia_usercopy::usercopy_copyin_bracketed" :=
  fuchsiaUsercopyCopyinModularDirectDetCert

def fuchsiaModelModularItemInputSensitiveCert :
    ModularItemInputSensitiveSpecCert "anneal_model::fuchsia_usercopy::usercopy_copyin_bracketed" :=
  fuchsiaUsercopyCopyinModularDirectInputSensitiveCert

/-! ## 7. Weak-Specification Contrast: `weak_vmo_subslice_upper_bound_only` -/

/-- Weakened postcondition that only checks `ret ≤ base + len` instead of pinning `base + (e - s)`. -/
def weak_vmo_subslice_upper_bound_only (args : List Value) (ret : Value) : Prop :=
  ∀ (base len s e : Nat),
    args =
      [ .scalar { bits := base, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := s, sizeBytes := 8 }
      , .scalar { bits := e, sizeBytes := 8 } ] →
    ∃ bits : Nat, ret = .scalar { bits, sizeBytes := 8 } ∧ bits ≤ base + len

/-- A single-mutant `SpecStrengthCert` still passes the weak upper-bound-only spec
(by killing an out-of-bounds return `base + len + 1`). -/
def weakVmoSubsliceSingleCert :
    SpecStrengthCert fxfsVmoSubslicePre weak_vmo_subslice_upper_bound_only where
  witnessInput := fxfsArgs 100 64 10 30
  witnessValid := ⟨100, 64, 10, 30, by decide, by decide, by decide, rfl⟩
  referenceOutput := .scalar { bits := 120, sizeBytes := 8 }
  referenceAccepted := by
    intro base len s e hEq
    dsimp [fxfsArgs] at hEq
    injection hEq with h1 t1
    injection t1 with h2 _
    injection h1 with h1s; injection h1s with hb _
    injection h2 with h2s; injection h2s with hl _
    subst hb; subst hl
    exact ⟨120, rfl, by decide⟩
  mutantOutput := .scalar { bits := 165, sizeBytes := 8 }
  mutantRejected := by
    intro hPost
    rcases hPost 100 64 10 30 rfl with ⟨bits, hVal, hLe⟩
    injection hVal with hs
    injection hs with hb _
    subst hb
    exact absurd hLe (by decide)

/-- Truncated mutant that always returns `base` (ignoring `sub_end - sub_start`). -/
def truncatedVmoSubsliceMutant (args : List Value) : Value :=
  match args with
  | .scalar b :: _ => .scalar { bits := b.bits, sizeBytes := 8 }
  | _ => .scalar { bits := 0, sizeBytes := 8 }

/-- `truncatedVmoSubsliceMutant` survives `weak_vmo_subslice_upper_bound_only` on EVERY valid input! -/
theorem truncatedVmoSubsliceMutant_survives_weak_spec (args : List Value)
    (hPre : fxfsVmoSubslicePre args) :
    weak_vmo_subslice_upper_bound_only args (truncatedVmoSubsliceMutant args) := by
  rcases hPre with ⟨base, len, s, e, _, _, _, hArgs⟩
  intro base' len' s' e' hEq
  rw [hArgs] at hEq
  injection hEq with h1 t1
  injection t1 with h2 _
  injection h1 with h1s; injection h1s with hb _
  injection h2 with h2s; injection h2s with hl _
  subst hb; subst hl
  rw [hArgs]
  exact ⟨base, rfl, Nat.le_add_right base len⟩

/-- `weak_vmo_subslice_upper_bound_only` is provably NOT deterministic (0 axioms). -/
theorem weak_vmo_subslice_not_deterministic :
    ¬ Nonempty (DeterministicSpecCert fxfsVmoSubslicePre weak_vmo_subslice_upper_bound_only) := by
  intro ⟨cert⟩
  have hValid : fxfsVmoSubslicePre (fxfsArgs 100 64 10 30) :=
    ⟨100, 64, 10, 30, by decide, by decide, by decide, rfl⟩
  have hAccept1 :
      weak_vmo_subslice_upper_bound_only (fxfsArgs 100 64 10 30)
        (.scalar { bits := 100, sizeBytes := 8 }) := by
    intro base len s e hEq
    dsimp [fxfsArgs] at hEq
    injection hEq with h1 t1; injection t1 with h2 _
    injection h1 with h1s; injection h1s with hb _
    injection h2 with h2s; injection h2s with hl _
    subst hb; subst hl
    exact ⟨100, rfl, by decide⟩
  have hAccept2 :
      weak_vmo_subslice_upper_bound_only (fxfsArgs 100 64 10 30)
        (.scalar { bits := 120, sizeBytes := 8 }) := by
    intro base len s e hEq
    dsimp [fxfsArgs] at hEq
    injection hEq with h1 t1; injection t1 with h2 _
    injection h1 with h1s; injection h1s with hb _
    injection h2 with h2s; injection h2s with hl _
    subst hb; subst hl
    exact ⟨120, rfl, by decide⟩
  have hEq := cert.uniqueOutput (fxfsArgs 100 64 10 30)
    (.scalar { bits := 100, sizeBytes := 8 })
    (.scalar { bits := 120, sizeBytes := 8 })
    hValid hAccept1 hAccept2
  injection hEq with hs
  injection hs with hb _
  exact absurd hb (by decide)

end Anneal.OleanSpecStrengthAuditor
