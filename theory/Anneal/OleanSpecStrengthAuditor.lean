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

Sections 1–7 hold the certificates and the live models they are checked against.
Sections 8–11 hold decidable models of the compiled-environment auditor's four hardened
vectors, together with soundness and non-evasion theorems about them:
- V1: `_private` name de-mangling and namespace spoofing.
- V2: whole-module unreferenced axiom sweep (`leanprover/lean4#16781`).
- V3: artifact root containment and acyclic compacted-region bounds (`leanprover/lean4#16737`).
- V4: the `Init.ShareCommon` ban, compiler-override hooks, and the non-blocking
  `leanprover/lean4#14896` readiness scanner.
`tests/mir/OleanShadowAndOverrideAuditTests.lean` exercises and pins the V1–V4 models.

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

/-! ## 8. V1 — `_private.<mod>.0.<user>` Structural De-Mangling & Namespace-Spoofing Model

Pure model of the compiled-environment auditor's private-name check: a private name is accepted
only in the exact shape `_private.<module segments>.0.<user segments>` (leading marker, non-empty
string module, a single numeric `0` separator, non-empty all-string user suffix without a second
marker), its user suffix may not spoof a reserved root, and a private name that claims a module
other than the one storing it must be a verified realized auxiliary (never an axiom or opaque).
`_at_` specialization names of IR helpers are modeled separately (`checkIRAtSpecModel`) and
exercised end-to-end by the self-test fixtures.
The production auditor additionally admits, after a separate kernel check, `Trusted` matcher
realizations stored by the module that realizes them, and IR-only auxiliaries (`_redArg`,
`_cstage1`, `_cstage2`, `_boxed_const_<k>`) of a foreign private helper that the storing module
compiled; this model omits both allowances (a kind-less foreign name is always
`foreignOutsideRealizedAux`) and is therefore stricter than the production check on those names.
-/

/-- Eliminate the left conjunct of a Boolean conjunction. -/
theorem band_elim_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact h
  | true => rfl

/-- Eliminate the right conjunct of a Boolean conjunction. -/
theorem band_elim_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false =>
    have h' : false = true := h
    cases h'
  | true => exact h

/-- Introduce a Boolean disjunction from its left disjunct. -/
theorem bor_intro_left {a b : Bool} (h : a = true) : (a || b) = true := by
  rw [h]
  rfl

/-- Introduce a Boolean disjunction from its right disjunct. -/
theorem bor_intro_right {a b : Bool} (h : b = true) : (a || b) = true := by
  rw [h]
  exact Bool.or_true a

/-- One component of a hierarchical declaration name. -/
inductive AuditNameComp : Type where
  | str (s : String)
  | num (n : Nat)
  deriving DecidableEq, Repr

/-- A hierarchical declaration name, root component first. -/
abbrev AuditName : Type := List AuditNameComp

/-- Embed string segments as name components. -/
def AuditName.ofStrings (ss : List String) : AuditName := ss.map AuditNameComp.str

/-- UTF-8 bytes of a string. Every substring test below works on bytes: the character-level
`String` operations of the pinned toolchain depend on `Classical.choice`, while `String.toUTF8`
and `Array.toList` are axiom-free. Byte-level infix tests coincide with character-level ones on
valid UTF-8, and the ASCII bytes tested for (`/`, `\\`, digits) never occur inside a multi-byte
sequence. -/
def strBytes (s : String) : List UInt8 := s.toUTF8.data.toList

/-- Does `pat` occur as a contiguous infix of the second byte list? -/
def bytesHaveInfix (pat : List UInt8) : List UInt8 → Bool
  | [] => pat.isEmpty
  | c :: cs => pat.isPrefixOf (c :: cs) || bytesHaveInfix pat cs

/-- A string segment that is, starts with, or embeds the private-name marker. -/
def strMentionsPrivate (s : String) : Bool :=
  s == "_private" || (strBytes "_private.").isPrefixOf (strBytes s) ||
    bytesHaveInfix (strBytes "._private") (strBytes s)

/-- Component-level private-marker test (numeric components never mention it). -/
def AuditNameComp.mentionsPrivate : AuditNameComp → Bool
  | .str s => strMentionsPrivate s
  | .num _ => false

/-- Does any component of `n` mention the private-name marker? -/
def hasPrivateMentionModel (n : AuditName) : Bool := n.any AuditNameComp.mentionsPrivate

/-- A module-name segment that is non-empty and free of path syntax. -/
def validModuleSegModel (s : String) : Bool :=
  s != "" && s != "." && s != ".." && !(strBytes s).contains 47 && !(strBytes s).contains 92

/-- Split `<module segments>.0.<tail>`: string segments up to the first numeric component, which
must be exactly `0`. Any other numeric component, or no separator at all, fails. -/
def splitPrivateModule : AuditName → Option (List String × AuditName)
  | [] => none
  | .str s :: rest => (splitPrivateModule rest).map (fun p => (s :: p.1, p.2))
  | .num 0 :: rest => some ([], rest)
  | .num (_ + 1) :: _ => none

/-- Project a name to its string segments; fails on any numeric component. -/
def allStrComps : AuditName → Option (List String)
  | [] => some []
  | .str s :: rest => (allStrComps rest).map (fun us => s :: us)
  | .num _ :: _ => none

/-- Result of strict private-name de-mangling. -/
structure PrivateParseResult where
  moduleSegs : List String
  userComps : List String
  deriving DecidableEq, Repr

/-- Side conditions of the strict shape: no second marker in the tail, non-empty module and user
suffix, and well-formed module segments. -/
def privateShapeOk (ms : List String) (tail : AuditName) (us : List String) : Bool :=
  !hasPrivateMentionModel tail && (!ms.isEmpty && (!us.isEmpty && ms.all validModuleSegModel))

/-- De-mangle the components after the leading marker. -/
def parsePrivateBody (rest : AuditName) : Option PrivateParseResult :=
  (splitPrivateModule rest).bind fun p =>
    (allStrComps p.2).bind fun us =>
      if privateShapeOk p.1 p.2 us then some ⟨p.1, us⟩ else none

/-- Strict structural de-mangling of `_private.<mod>.0.<user>`. -/
def parseStrictPrivateName : AuditName → Option PrivateParseResult
  | .str s :: rest => if s == "_private" then parsePrivateBody rest else none
  | _ => none

/-- The canonical mangled private name of `us` in module `ms`. -/
def mkPrivateName (ms us : List String) : AuditName :=
  .str "_private" :: (AuditName.ofStrings ms ++ .num 0 :: AuditName.ofStrings us)

theorem splitPrivateModule_ofStrings (ms : List String) (tail : AuditName) :
    splitPrivateModule (AuditName.ofStrings ms ++ AuditNameComp.num 0 :: tail) = some (ms, tail) := by
  induction ms with
  | nil => rfl
  | cons s ms ih =>
    show (splitPrivateModule (AuditName.ofStrings ms ++ AuditNameComp.num 0 :: tail)).map
      (fun p => (s :: p.1, p.2)) = some (s :: ms, tail)
    rw [ih]
    rfl

theorem allStrComps_ofStrings (us : List String) :
    allStrComps (AuditName.ofStrings us) = some us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    show (allStrComps (AuditName.ofStrings us)).map (fun t => u :: t) = some (u :: us)
    rw [ih]
    rfl

theorem allStrComps_embedded_num (pre : AuditName) (k : Nat) (post : AuditName) :
    allStrComps (pre ++ AuditNameComp.num k :: post) = none := by
  induction pre with
  | nil => rfl
  | cons c pre ih =>
    cases c with
    | str s =>
      show (allStrComps (pre ++ AuditNameComp.num k :: post)).map (fun t => s :: t) = none
      rw [ih]
      rfl
    | num j => rfl

theorem splitPrivateModule_some_inv (n : AuditName) :
    ∀ (ms : List String) (tail : AuditName), splitPrivateModule n = some (ms, tail) →
      n = AuditName.ofStrings ms ++ AuditNameComp.num 0 :: tail := by
  induction n with
  | nil => intro ms tail h; cases h
  | cons c rest ih =>
    intro ms tail h
    cases c with
    | str s =>
      have h' : (splitPrivateModule rest).map (fun p => (s :: p.1, p.2)) = some (ms, tail) := h
      cases hr : splitPrivateModule rest with
      | none => rw [hr] at h'; cases h'
      | some p =>
        rw [hr] at h'
        have hp : (s :: p.1, p.2) = (ms, tail) := Option.some.inj h'
        cases p with
        | mk ms' tail' =>
          cases hp
          rw [ih ms' tail' hr]
          rfl
    | num k =>
      cases k with
      | zero =>
        have hp : (([] : List String), rest) = (ms, tail) := Option.some.inj h
        cases hp
        rfl
      | succ k => cases h

theorem allStrComps_some_inv (n : AuditName) :
    ∀ (us : List String), allStrComps n = some us → n = AuditName.ofStrings us := by
  induction n with
  | nil =>
    intro us h
    have hp : ([] : List String) = us := Option.some.inj h
    cases hp
    rfl
  | cons c rest ih =>
    intro us h
    cases c with
    | str s =>
      have h' : (allStrComps rest).map (fun t => s :: t) = some us := h
      cases hr : allStrComps rest with
      | none => rw [hr] at h'; cases h'
      | some us' =>
        rw [hr] at h'
        have hp : s :: us' = us := Option.some.inj h'
        cases hp
        rw [ih us' hr]
        rfl
    | num k => cases h

theorem parsePrivateBody_eq_of (rest : AuditName) (ms : List String) (tail : AuditName)
    (us : List String) (h1 : splitPrivateModule rest = some (ms, tail))
    (h2 : allStrComps tail = some us) :
    parsePrivateBody rest = if privateShapeOk ms tail us then some ⟨ms, us⟩ else none := by
  unfold parsePrivateBody
  rw [h1]
  show (allStrComps tail).bind
    (fun us => if privateShapeOk ms tail us then some (PrivateParseResult.mk ms us) else none) = _
  rw [h2]
  rfl

theorem parsePrivateBody_none_of_tail (rest : AuditName) (ms : List String) (tail : AuditName)
    (h1 : splitPrivateModule rest = some (ms, tail)) (h2 : allStrComps tail = none) :
    parsePrivateBody rest = none := by
  unfold parsePrivateBody
  rw [h1]
  show (allStrComps tail).bind
    (fun us => if privateShapeOk ms tail us then some (PrivateParseResult.mk ms us) else none) = none
  rw [h2]
  rfl

theorem parseStrictPrivateName_marker (rest : AuditName) :
    parseStrictPrivateName (AuditNameComp.str "_private" :: rest) = parsePrivateBody rest := by
  show (if ("_private" == "_private") = true then parsePrivateBody rest else none) =
    parsePrivateBody rest
  rfl

/-- **V1 soundness (round trip).** Every canonical `_private.<mod>.0.<user>` name with a
non-empty well-formed module, a non-empty user suffix, and no second marker de-mangles to
exactly its module and user suffix. -/
theorem parseStrictPrivate_roundtrip (ms us : List String)
    (hms : ms ≠ []) (hus : us ≠ []) (hvalid : ms.all validModuleSegModel = true)
    (hclean : hasPrivateMentionModel (AuditName.ofStrings us) = false) :
    parseStrictPrivateName (mkPrivateName ms us) = some ⟨ms, us⟩ := by
  have hshape : privateShapeOk ms (AuditName.ofStrings us) us = true := by
    cases ms with
    | nil => exact absurd rfl hms
    | cons m ms' =>
      cases us with
      | nil => exact absurd rfl hus
      | cons u us' =>
        unfold privateShapeOk
        rw [hclean, hvalid]
        rfl
  unfold mkPrivateName
  rw [parseStrictPrivateName_marker,
    parsePrivateBody_eq_of _ ms _ us (splitPrivateModule_ofStrings ms _) (allStrComps_ofStrings us),
    hshape]
  rfl

/-- **V1 completeness.** The strict parser accepts *only* canonical names: any accepted name is
literally `mkPrivateName` of its result, with non-empty parts and a marker-free user suffix. -/
theorem parseStrictPrivate_some_inv (n : AuditName) (r : PrivateParseResult)
    (h : parseStrictPrivateName n = some r) :
    n = mkPrivateName r.moduleSegs r.userComps ∧ r.moduleSegs ≠ [] ∧ r.userComps ≠ [] ∧
      hasPrivateMentionModel (AuditName.ofStrings r.userComps) = false := by
  cases n with
  | nil => cases h
  | cons c rest =>
    cases c with
    | num k => cases h
    | str s =>
      have h' : (if (s == "_private") = true then parsePrivateBody rest else none) = some r := h
      cases hb : (s == "_private") with
      | false => rw [hb] at h'; cases h'
      | true =>
        rw [hb] at h'
        have hbody : parsePrivateBody rest = some r := h'
        have hs : s = "_private" := eq_of_beq hb
        cases hsp : splitPrivateModule rest with
        | none =>
          unfold parsePrivateBody at hbody
          rw [hsp] at hbody
          cases hbody
        | some p =>
          cases p with
          | mk ms tail =>
            cases hu : allStrComps tail with
            | none =>
              rw [parsePrivateBody_none_of_tail rest ms tail hsp hu] at hbody
              cases hbody
            | some us =>
              rw [parsePrivateBody_eq_of rest ms tail us hsp hu] at hbody
              cases hok : privateShapeOk ms tail us with
              | false => rw [hok] at hbody; cases hbody
              | true =>
                rw [hok] at hbody
                have hr : PrivateParseResult.mk ms us = r := Option.some.inj hbody
                cases hr
                have htail : tail = AuditName.ofStrings us := allStrComps_some_inv tail us hu
                have hrest := splitPrivateModule_some_inv rest ms tail hsp
                have hmention : hasPrivateMentionModel tail = false := by
                  cases hm : hasPrivateMentionModel tail with
                  | false => rfl
                  | true =>
                    unfold privateShapeOk at hok
                    rw [hm] at hok
                    cases hok
                have hrestOk := band_elim_right hok
                have hmsNe : ms ≠ [] := by
                  intro hnil
                  rw [hnil] at hrestOk
                  cases hrestOk
                have husNe : us ≠ [] := by
                  intro hnil
                  have h3 := band_elim_left (band_elim_right hrestOk)
                  rw [hnil] at h3
                  cases h3
                refine ⟨?_, hmsNe, husNe, ?_⟩
                · rw [hs, hrest, htail]
                  rfl
                · rw [← htail]
                  exact hmention

/-- **V1 non-evasion (embedded numeric tail).** A numeric component anywhere in the user tail
(`_private.M.0.Innocent.0.Trusted.foo`) never de-mangles. -/
theorem parseStrictPrivate_rejects_embedded_num (ms : List String) (pre : AuditName) (k : Nat)
    (post : AuditName) :
    parseStrictPrivateName (AuditNameComp.str "_private" ::
      (AuditName.ofStrings ms ++ AuditNameComp.num 0 :: (pre ++ AuditNameComp.num k :: post))) =
      none := by
  rw [parseStrictPrivateName_marker]
  exact parsePrivateBody_none_of_tail _ ms _ (splitPrivateModule_ofStrings ms _)
    (allStrComps_embedded_num pre k post)

/-- **V1 non-evasion (nested marker).** A second private marker anywhere in the user tail never
de-mangles. -/
theorem parseStrictPrivate_rejects_nested (ms : List String) (tail : AuditName)
    (h : hasPrivateMentionModel tail = true) :
    parseStrictPrivateName (AuditNameComp.str "_private" ::
      (AuditName.ofStrings ms ++ AuditNameComp.num 0 :: tail)) = none := by
  rw [parseStrictPrivateName_marker]
  cases hu : allStrComps tail with
  | none => exact parsePrivateBody_none_of_tail _ ms tail (splitPrivateModule_ofStrings ms _) hu
  | some us =>
    rw [parsePrivateBody_eq_of _ ms tail us (splitPrivateModule_ofStrings ms _) hu]
    have hs : privateShapeOk ms tail us = false := by
      unfold privateShapeOk
      rw [h]
      rfl
    rw [hs]
    rfl

/-- **V1 non-evasion (non-leading marker).** A name whose first component is not the string
`_private` never de-mangles, wherever else the marker appears. -/
theorem parseStrictPrivate_rejects_nonleading (c : AuditNameComp) (rest : AuditName)
    (h : c ≠ AuditNameComp.str "_private") : parseStrictPrivateName (c :: rest) = none := by
  cases c with
  | num k => rfl
  | str s =>
    have hs : (s == "_private") = false := by
      cases hb : (s == "_private") with
      | false => rfl
      | true => exact absurd (congrArg AuditNameComp.str (eq_of_beq hb)) h
    show (if (s == "_private") = true then parsePrivateBody rest else none) = none
    rw [hs]
    rfl

/-- Roots no private user suffix may claim, in any module. -/
def reservedAlwaysRootsModel : List String :=
  ["Init", "Std", "Lean", "ShareCommon", "Classical", "Quot", "sorryAx"]

/-- Domain roots a private user suffix may claim only inside a module of the same root. -/
def reservedDomainRootsModel : List String := ["Trusted", "Assumptions", "Verify", "CrateVerify"]

/-- Structural prefix test on segment lists. -/
def segsPrefixOf : List String → List String → Bool
  | [], _ => true
  | _ :: _, [] => false
  | r :: rs, t :: ts => r == t && segsPrefixOf rs ts

/-- Does a native symbol name target the structural-sharing runtime? -/
def externSymMentionsShareCommon (sym : String) : Bool :=
  bytesHaveInfix (strBytes "lean_sharecommon") (strBytes sym) ||
    bytesHaveInfix (strBytes "lean_state_sharecommon") (strBytes sym)

/-- Root segments owned by the structural-sharing library. -/
def shareCommonRootsModel : List String :=
  ["ShareCommon", "MonadShareCommon", "withShareCommon", "shareCommonM", "ShareCommonT",
    "ShareCommonM", "StateFactoryBuilder", "StateFactory"]

/-- Does a dotted name reference the structural-sharing library (`leanprover/lean4#16779`)? -/
def isShareCommonNameModel (n : List String) : Bool :=
  segsPrefixOf ["Init", "ShareCommon"] n ||
    n.any (fun s => shareCommonRootsModel.contains s || externSymMentionsShareCommon s)

/-- Declaration kinds distinguished by the audit models. -/
inductive DeclKindModel : Type where
  | axiomDecl | opaqueDecl | defnDecl | thmDecl | inductDecl | ctorDecl | recDecl | quotDecl
  deriving DecidableEq, Repr

/-- One declaration of the loaded environment, as seen by the private-name check. -/
structure EnvDeclModel where
  name : AuditName
  kind : DeclKindModel
  origin : List String
  deriving DecidableEq, Repr

/-- Environment facts consulted by the private-name check. -/
structure PrivateAuditEnv where
  loadedModules : List (List String)
  toolchainModules : List (List String) := []
  toolchainNames : List (List String) := []
  compilerReservedNames : List (List String) := []
  decls : List EnvDeclModel := []
  deriving DecidableEq, Repr

/-- Reserved-root, compiler-reserved, and toolchain-name spoofing classifier for a private user
suffix `us` claimed by module `ms`. An empty suffix fails closed. -/
def privateUserForbiddenModel (env : PrivateAuditEnv) (ms us : List String) : Bool :=
  match us with
  | [] => true
  | r :: _ =>
    reservedAlwaysRootsModel.contains r ||
      (reservedDomainRootsModel.contains r && !(ms.head? == some r)) ||
      env.compilerReservedNames.contains us || env.toolchainNames.contains us ||
      isShareCommonNameModel us

/-- Strip a byte prefix. -/
def stripBytePrefix : List UInt8 → List UInt8 → Option (List UInt8)
  | [], s => some s
  | _ :: _, [] => none
  | p :: ps, c :: cs => if p == c then stripBytePrefix ps cs else none

/-- Value of an ASCII decimal digit string (accumulator form); fails on any non-digit. -/
def decDigitsValue : List UInt8 → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc =>
    if 48 ≤ c.toNat && c.toNat ≤ 57 then decDigitsValue cs (acc * 10 + (c.toNat - 48)) else none

/-- Canonical decimal digits: `"0"` or a non-zero digit followed by ASCII digits (rejects leading
zeros such as `"01"` so `eq_01` cannot spoof `eq_1`). -/
def isCanonicalDecDigits : List UInt8 → Bool
  | [] => false
  | [c] => 48 ≤ c.toNat && c.toNat ≤ 57
  | c :: rest => 49 ≤ c.toNat && c.toNat ≤ 57 && rest.all (fun d => 48 ≤ d.toNat && d.toNat ≤ 57)

/-- Parse `<pfx><decimal>` with canonical decimal digits (no leading zeros on multi-digit values). -/
def parseDecSuffixModel (pfx s : String) : Option Nat :=
  match stripBytePrefix (strBytes pfx) (strBytes s) with
  | some ds => if isCanonicalDecDigits ds then decDigitsValue ds 0 else none
  | none => none

/-- The closed set of lazily realized auxiliary suffixes a foreign private name may carry. -/
inductive RealizedAuxSuffix : Type where
  | matcher (k : Nat)
  | eqn (k : Nat)
  | eqDef
  | proof (k : Nat)
  | sparseCasesOn (k : Nat)
  deriving DecidableEq, Repr

/-- Classify the last segment of a declaration name as a realized auxiliary suffix. -/
def classifyRealizedAuxSuffix (s : String) : Option RealizedAuxSuffix :=
  match parseDecSuffixModel "match_" s with
  | some k => some (.matcher k)
  | none =>
    match parseDecSuffixModel "eq_" s with
    | some k => some (.eqn k)
    | none =>
      if s == "eq_def" then some .eqDef
      else
        match parseDecSuffixModel "proof_" s with
        | some k => some (.proof k)
        | none =>
          match parseDecSuffixModel "_sparseCasesOn_" s with
          | some k => some (.sparseCasesOn k)
          | none => none

/-- Look a declaration up by name. -/
def PrivateAuditEnv.find? (env : PrivateAuditEnv) (n : AuditName) : Option EnvDeclModel :=
  env.decls.find? (fun d => d.name == n)

/-- Is `n` a declaration of kind `k` attributed to module `m`? -/
def PrivateAuditEnv.ownedWithKind (env : PrivateAuditEnv) (n : AuditName) (m : List String)
    (k : Option DeclKindModel) : Bool :=
  match env.find? n with
  | some d => d.origin == m && (match k with | some k => d.kind == k | none => true)
  | none => false

/-- Does a sibling `base.<pfx><k>` exist (the predecessor of a numbered auxiliary)? -/
def PrivateAuditEnv.hasNumberedSibling (env : PrivateAuditEnv) (base : AuditName) (pfx : String)
    (k : Nat) : Bool :=
  env.decls.any fun d =>
    d.name.dropLast == base &&
      (match d.name.getLast? with
       | some (.str s) => parseDecSuffixModel pfx s == some k
       | _ => false)

/-- Closed-set realized-auxiliary allowlist for a foreign private declaration `n` of kind `kind`
claiming module `pMod`. `shapeEvidence` abstracts the kind-specific kernel evidence (matcher
registration, an `Eq`-of-base conclusion, or the base referencing the proof). -/
def realizedAuxAllowedModel (env : PrivateAuditEnv) (pMod : List String) (n : AuditName)
    (kind : DeclKindModel) (shapeEvidence : Bool) : Bool :=
  match n.getLast? with
  | some (.str last) =>
    let base := n.dropLast
    match classifyRealizedAuxSuffix last with
    | some (.matcher k) =>
      decide (1 ≤ k) && kind == .defnDecl && env.ownedWithKind base pMod none && shapeEvidence
    | some (.eqn k) =>
      decide (1 ≤ k) && kind == .thmDecl && env.ownedWithKind base pMod (some .defnDecl) &&
        (k == 1 || env.hasNumberedSibling base "eq_" (k - 1)) && shapeEvidence
    | some .eqDef =>
      kind == .thmDecl && env.ownedWithKind base pMod (some .defnDecl) && shapeEvidence
    | some (.proof k) =>
      decide (1 ≤ k) && kind == .thmDecl && env.ownedWithKind base pMod none &&
        (k == 1 || env.hasNumberedSibling base "proof_" (k - 1)) && shapeEvidence
    | some (.sparseCasesOn _) =>
      kind == .defnDecl && env.ownedWithKind base pMod none && shapeEvidence
    | none => false
  | _ => false

/-- One declaration name submitted to the private-name check. -/
structure PrivateCheckInput where
  /-- Module whose compiled artifact stores the declaration. -/
  declaringMod : List String
  name : AuditName
  /-- Kernel declaration kind; `none` for an IR-only or extension-only symbol. -/
  kind : Option DeclKindModel
  shapeEvidence : Bool := true
  deriving DecidableEq, Repr

/-- Verdict of the private-name check. -/
inductive PrivateVerdict : Type where
  | notPrivate
  | accepted
  | malformedShape
  | reservedUserSpoof
  | unloadedModule
  | foreignAxiomOrOpaque
  | foreignOutsideRealizedAux
  deriving DecidableEq, Repr

/-- Is the verdict a `privateNamespaceSpoofed` rejection? -/
def PrivateVerdict.isRejection : PrivateVerdict → Bool
  | .notPrivate | .accepted => false
  | _ => true

/-- Kind-specific verdict for a foreign private name of a loaded module: axioms and opaque
constants are refused outright; anything else must be a verified realized auxiliary; an IR-only
or extension-only symbol is refused. -/
def foreignKindVerdict (env : PrivateAuditEnv) (inp : PrivateCheckInput) (r : PrivateParseResult) :
    Option DeclKindModel → PrivateVerdict
  | none => .foreignOutsideRealizedAux
  | some k =>
    if k == .axiomDecl || k == .opaqueDecl then .foreignAxiomOrOpaque
    else if realizedAuxAllowedModel env r.moduleSegs inp.name k inp.shapeEvidence then .accepted
    else .foreignOutsideRealizedAux

/-- Foreign-module branch of the private-name check: `r.moduleSegs` differs from the storing
module. -/
def checkForeignPrivateModel (env : PrivateAuditEnv) (inp : PrivateCheckInput)
    (r : PrivateParseResult) : PrivateVerdict :=
  if env.loadedModules.contains r.moduleSegs then foreignKindVerdict env inp r inp.kind
  else .unloadedModule

/-- Parsed branch of the private-name check. -/
def checkParsedPrivateModel (env : PrivateAuditEnv) (inp : PrivateCheckInput)
    (r : PrivateParseResult) : PrivateVerdict :=
  if privateUserForbiddenModel env r.moduleSegs r.userComps then .reservedUserSpoof
  else if r.moduleSegs == inp.declaringMod then .accepted
  else checkForeignPrivateModel env inp r

/-- Structural de-mangling, reserved-root guard, provenance binding, and closed-set foreign
realized-auxiliary check of one declaration name. Names without a private marker, and names
stored by pinned toolchain modules, are outside this check. -/
def checkPrivateNameModel (env : PrivateAuditEnv) (inp : PrivateCheckInput) : PrivateVerdict :=
  if hasPrivateMentionModel inp.name && !env.toolchainModules.contains inp.declaringMod then
    match parseStrictPrivateName inp.name with
    | some r => checkParsedPrivateModel env inp r
    | none => .malformedShape
  else .notPrivate

/-- Summary of a private-name audit (mirrors the `privateNamesAudited` diagnostic). -/
structure PrivateAuditSummary where
  privateNamesAudited : Nat
  violations : List AuditName
  deriving DecidableEq, Repr

/-- Audit a batch of declaration names. -/
def auditPrivateNamesModel (env : PrivateAuditEnv) (inputs : List PrivateCheckInput) :
    PrivateAuditSummary where
  privateNamesAudited :=
    (inputs.filter (fun i => decide (checkPrivateNameModel env i ≠ .notPrivate))).length
  violations :=
    (inputs.filter (fun i => (checkPrivateNameModel env i).isRejection)).map (·.name)

theorem checkPrivateNameModel_of_parse (env : PrivateAuditEnv) (inp : PrivateCheckInput)
    (r : PrivateParseResult) (hm : hasPrivateMentionModel inp.name = true)
    (htool : env.toolchainModules.contains inp.declaringMod = false)
    (hparse : parseStrictPrivateName inp.name = some r) :
    checkPrivateNameModel env inp = checkParsedPrivateModel env inp r := by
  unfold checkPrivateNameModel
  rw [hm, htool, hparse]
  rfl

/-- **V1 non-evasion (malformed shape).** Any non-toolchain name mentioning `_private` that fails
strict structural de-mangling (embedded numeric tail, nested marker, non-leading marker, non-zero
or double-zero separator) is rejected as `malformedShape`. -/
theorem checkPrivateName_rejects_malformed (env : PrivateAuditEnv) (inp : PrivateCheckInput)
    (hm : hasPrivateMentionModel inp.name = true)
    (htool : env.toolchainModules.contains inp.declaringMod = false)
    (hnone : parseStrictPrivateName inp.name = none) :
    checkPrivateNameModel env inp = .malformedShape := by
  unfold checkPrivateNameModel
  rw [hm, htool, hnone]
  rfl

/-- A successfully de-mangled name always mentions the marker (it leads with it). -/
theorem parseStrictPrivate_some_mentions (n : AuditName) (r : PrivateParseResult)
    (h : parseStrictPrivateName n = some r) : hasPrivateMentionModel n = true := by
  rw [(parseStrictPrivate_some_inv n r h).1]
  rfl

/-- **V1 non-evasion (reserved user suffix).** A well-shaped private name whose user suffix is
classified as reserved is rejected as `reservedUserSpoof` for every storing module, kind, and
environment — including the module the name itself claims. -/
theorem checkPrivateName_rejects_reserved_user_spoof (env : PrivateAuditEnv)
    (inp : PrivateCheckInput) (r : PrivateParseResult)
    (htool : env.toolchainModules.contains inp.declaringMod = false)
    (hparse : parseStrictPrivateName inp.name = some r)
    (hforb : privateUserForbiddenModel env r.moduleSegs r.userComps = true) :
    checkPrivateNameModel env inp = .reservedUserSpoof := by
  rw [checkPrivateNameModel_of_parse env inp r (parseStrictPrivate_some_mentions _ r hparse) htool
    hparse]
  unfold checkParsedPrivateModel
  rw [hforb]
  rfl

/-- A user suffix rooted at a reserved domain root (`Trusted`, `Assumptions`, ...) is forbidden in
every module whose own root differs (`_private.M.0.Trusted.foo`). -/
theorem privateUserForbidden_reserved_domain_root (env : PrivateAuditEnv) (ms : List String)
    (root : String) (us : List String) (hr : reservedDomainRootsModel.contains root = true)
    (hm : (ms.head? == some root) = false) :
    privateUserForbiddenModel env ms (root :: us) = true := by
  show (reservedAlwaysRootsModel.contains root ||
    (reservedDomainRootsModel.contains root && !(ms.head? == some root)) ||
    env.compilerReservedNames.contains (root :: us) || env.toolchainNames.contains (root :: us) ||
    isShareCommonNameModel (root :: us)) = true
  rw [hr, hm]
  cases reservedAlwaysRootsModel.contains root <;> rfl

/-- A user suffix rooted at an always-reserved root (`Init`, `Lean`, `sorryAx`, ...) is forbidden
in every module. -/
theorem privateUserForbidden_reserved_always_root (env : PrivateAuditEnv) (ms : List String)
    (root : String) (us : List String) (hr : reservedAlwaysRootsModel.contains root = true) :
    privateUserForbiddenModel env ms (root :: us) = true := by
  show (reservedAlwaysRootsModel.contains root ||
    (reservedDomainRootsModel.contains root && !(ms.head? == some root)) ||
    env.compilerReservedNames.contains (root :: us) || env.toolchainNames.contains (root :: us) ||
    isShareCommonNameModel (root :: us)) = true
  rw [hr]
  rfl

/-- A user suffix matching a compiler-reserved intrinsic name is forbidden in every module. -/
theorem privateUserForbidden_compiler_reserved (env : PrivateAuditEnv) (ms : List String)
    (root : String) (us : List String)
    (hc : env.compilerReservedNames.contains (root :: us) = true) :
    privateUserForbiddenModel env ms (root :: us) = true := by
  show (reservedAlwaysRootsModel.contains root ||
    (reservedDomainRootsModel.contains root && !(ms.head? == some root)) ||
    env.compilerReservedNames.contains (root :: us) || env.toolchainNames.contains (root :: us) ||
    isShareCommonNameModel (root :: us)) = true
  rw [hc]
  exact bor_intro_left (bor_intro_left (bor_intro_right rfl))

/-- **V1 non-evasion (foreign axiom / opaque).** A private axiom or opaque constant whose name
claims a module other than the one storing it is never accepted, whatever its suffix, shape
evidence, or environment. -/
theorem checkPrivateName_rejects_foreign_axiom (env : PrivateAuditEnv) (inp : PrivateCheckInput)
    (r : PrivateParseResult)
    (htool : env.toolchainModules.contains inp.declaringMod = false)
    (hparse : parseStrictPrivateName inp.name = some r)
    (hforeign : (r.moduleSegs == inp.declaringMod) = false)
    (hkind : inp.kind = some .axiomDecl ∨ inp.kind = some .opaqueDecl) :
    (checkPrivateNameModel env inp).isRejection = true := by
  rw [checkPrivateNameModel_of_parse env inp r (parseStrictPrivate_some_mentions _ r hparse) htool
    hparse]
  unfold checkParsedPrivateModel
  cases hf : privateUserForbiddenModel env r.moduleSegs r.userComps with
  | true => rfl
  | false =>
    rw [hforeign]
    show (checkForeignPrivateModel env inp r).isRejection = true
    unfold checkForeignPrivateModel
    cases hl : env.loadedModules.contains r.moduleSegs with
    | false => rfl
    | true =>
      cases hkind with
      | inl hk => rw [hk]; rfl
      | inr hk => rw [hk]; rfl

/-- **V1 positive control.** A well-shaped private name stored by the module it claims, with a
non-reserved user suffix, is accepted for every kind (`_private.M.0.Outside.helper` in `M`). -/
theorem checkPrivateName_accepts_same_module_helper (env : PrivateAuditEnv)
    (inp : PrivateCheckInput) (r : PrivateParseResult)
    (htool : env.toolchainModules.contains inp.declaringMod = false)
    (hparse : parseStrictPrivateName inp.name = some r)
    (hforb : privateUserForbiddenModel env r.moduleSegs r.userComps = false)
    (hsame : (r.moduleSegs == inp.declaringMod) = true) :
    checkPrivateNameModel env inp = .accepted := by
  rw [checkPrivateNameModel_of_parse env inp r (parseStrictPrivate_some_mentions _ r hparse) htool
    hparse]
  unfold checkParsedPrivateModel
  rw [hforb, hsame]
  rfl

theorem checkParsedPrivate_accepted_inv (env : PrivateAuditEnv) (inp : PrivateCheckInput)
    (r : PrivateParseResult) (h : checkParsedPrivateModel env inp r = .accepted) :
    privateUserForbiddenModel env r.moduleSegs r.userComps = false ∧
      ((r.moduleSegs == inp.declaringMod) = true ∨
        checkForeignPrivateModel env inp r = .accepted) := by
  unfold checkParsedPrivateModel at h
  cases hf : privateUserForbiddenModel env r.moduleSegs r.userComps with
  | true => rw [hf] at h; cases h
  | false =>
    refine ⟨rfl, ?_⟩
    cases hs : (r.moduleSegs == inp.declaringMod) with
    | true => exact Or.inl rfl
    | false => rw [hf, hs] at h; exact Or.inr h

theorem checkForeignPrivate_accepted_inv (env : PrivateAuditEnv) (inp : PrivateCheckInput)
    (r : PrivateParseResult) (h : checkForeignPrivateModel env inp r = .accepted) :
    env.loadedModules.contains r.moduleSegs = true ∧
      foreignKindVerdict env inp r inp.kind = .accepted := by
  unfold checkForeignPrivateModel at h
  cases hl : env.loadedModules.contains r.moduleSegs with
  | false => rw [hl] at h; cases h
  | true => rw [hl] at h; exact ⟨rfl, h⟩

theorem foreignKindVerdict_accepted_inv (env : PrivateAuditEnv) (inp : PrivateCheckInput)
    (r : PrivateParseResult) (kind : Option DeclKindModel)
    (h : foreignKindVerdict env inp r kind = .accepted) :
    ∃ k, kind = some k ∧ k ≠ .axiomDecl ∧ k ≠ .opaqueDecl ∧
      realizedAuxAllowedModel env r.moduleSegs inp.name k inp.shapeEvidence = true := by
  cases kind with
  | none => cases h
  | some k =>
    have h' : (if (k == DeclKindModel.axiomDecl || k == DeclKindModel.opaqueDecl) = true then
        PrivateVerdict.foreignAxiomOrOpaque
      else if realizedAuxAllowedModel env r.moduleSegs inp.name k inp.shapeEvidence = true then
        PrivateVerdict.accepted
      else PrivateVerdict.foreignOutsideRealizedAux) = PrivateVerdict.accepted := h
    cases hax : (k == DeclKindModel.axiomDecl || k == DeclKindModel.opaqueDecl) with
    | true => rw [hax] at h'; cases h'
    | false =>
      rw [hax] at h'
      cases ha : realizedAuxAllowedModel env r.moduleSegs inp.name k inp.shapeEvidence with
      | false => rw [ha] at h'; cases h'
      | true =>
        refine ⟨k, rfl, ?_, ?_, ha⟩
        · intro hk; rw [hk] at hax; exact absurd hax (by decide)
        · intro hk; rw [hk] at hax; exact absurd hax (by decide)

/-- **V1 soundness of acceptance.** An accepted private name is canonical, has a non-reserved
user suffix, and is either stored by the module it claims or is a non-axiom, non-opaque verified
realized auxiliary of a loaded module. -/
theorem checkPrivateName_accepted_sound (env : PrivateAuditEnv) (inp : PrivateCheckInput)
    (h : checkPrivateNameModel env inp = .accepted) :
    ∃ r, parseStrictPrivateName inp.name = some r ∧
      inp.name = mkPrivateName r.moduleSegs r.userComps ∧
      privateUserForbiddenModel env r.moduleSegs r.userComps = false ∧
      ((r.moduleSegs == inp.declaringMod) = true ∨
        (env.loadedModules.contains r.moduleSegs = true ∧
          ∃ k, inp.kind = some k ∧ k ≠ .axiomDecl ∧ k ≠ .opaqueDecl ∧
            realizedAuxAllowedModel env r.moduleSegs inp.name k inp.shapeEvidence = true)) := by
  cases hp : parseStrictPrivateName inp.name with
  | none =>
    unfold checkPrivateNameModel at h
    rw [hp] at h
    cases hc : (hasPrivateMentionModel inp.name &&
      !env.toolchainModules.contains inp.declaringMod) with
    | false => rw [hc] at h; cases h
    | true => rw [hc] at h; cases h
  | some r =>
    have h' : checkParsedPrivateModel env inp r = .accepted := by
      unfold checkPrivateNameModel at h
      rw [hp] at h
      cases hc : (hasPrivateMentionModel inp.name &&
        !env.toolchainModules.contains inp.declaringMod) with
      | false => rw [hc] at h; cases h
      | true => rw [hc] at h; exact h
    obtain ⟨hforb, hcase⟩ := checkParsedPrivate_accepted_inv env inp r h'
    refine ⟨r, rfl, (parseStrictPrivate_some_inv _ r hp).1, hforb, ?_⟩
    rcases hcase with hsame | hforeign
    · exact Or.inl hsame
    · obtain ⟨hl, hk⟩ := checkForeignPrivate_accepted_inv env inp r hforeign
      exact Or.inr ⟨hl, foreignKindVerdict_accepted_inv env inp r inp.kind hk⟩

/-- Split a hierarchical name on `.str "_at_"` separators for IR specialization-name auditing. -/
def splitOnAt : AuditName → List AuditName
  | [] => [[]]
  | .str s :: rest =>
    if s == "_at_" then [] :: splitOnAt rest
    else match splitOnAt rest with
      | [] => [[.str s]]
      | seg :: segs => (.str s :: seg) :: segs
  | .num k :: rest =>
    match splitOnAt rest with
    | [] => [[.num k]]
    | seg :: segs => (.num k :: seg) :: segs

/-- Compiler-emitted IR auxiliary suffixes allowed at the tail of specialization sites. -/
def isIRAuxSuffixModel (s : String) : Bool :=
  s == "_redArg" || s == "_cstage1" || s == "_cstage2" ||
    (parseDecSuffixModel "_boxed_const_" s).isSome

/-- Strip trailing `_boxed` / IR-aux / `spec_<k>` suffixes from a reversed site segment. -/
def stripSpecTailRev : Nat → AuditName → Nat → Option (AuditName × Nat)
  | 0, rev, sp => if rev.isEmpty then none else some (rev.reverse, sp)
  | fuel + 1, rev, sp =>
    match rev with
    | .str s :: r =>
      if isIRAuxSuffixModel s || s == "_boxed" then stripSpecTailRev fuel r sp
      else if (parseDecSuffixModel "spec_" s).isSome then stripSpecTailRev fuel r (sp + 1)
      else some (rev.reverse, sp)
    | _ => if rev.isEmpty then none else some (rev.reverse, sp)

/-- Strip trailing specialization suffixes from an `_at_` site segment, returning `(site, specs)`. -/
def stripSpecTailModel (seg : AuditName) : Option (AuditName × Nat) :=
  stripSpecTailRev 6 seg.reverse 0

/-- Check the base declaration head of a `_private` `_at_` specialization IR helper. -/
def checkIRAtHeadModel (env : PrivateAuditEnv) (head : AuditName) : Bool :=
  if head.isEmpty then false
  else if hasPrivateMentionModel head then
    match parseStrictPrivateName head with
    | some r =>
      env.loadedModules.contains r.moduleSegs && !isShareCommonNameModel r.userComps &&
        (env.toolchainModules.contains r.moduleSegs ||
          !privateUserForbiddenModel env r.moduleSegs r.userComps)
    | none => false
  else
    match allStrComps head with
    | some us => !isShareCommonNameModel us
    | none => false

/-- Check one `_at_` specialization site segment (`isLast = true` for the final site). -/
def checkIRAtSiteModel (env : PrivateAuditEnv) (declaringMod : List String) (isLast : Bool)
    (seg : AuditName) : Option Nat :=
  (stripSpecTailModel seg).bind fun p =>
    let site := p.1
    let sp := p.2
    if isLast && sp == 0 then none
    else if hasPrivateMentionModel site then
      match parseStrictPrivateName site with
      | some r =>
        if env.loadedModules.contains r.moduleSegs &&
            !privateUserForbiddenModel env r.moduleSegs r.userComps &&
            (!isLast || r.moduleSegs == declaringMod) then some sp
        else none
      | none => none
    else
      match allStrComps site with
      | some us =>
        if !isShareCommonNameModel us &&
            (!isLast || !privateUserForbiddenModel env declaringMod us) then some sp
        else none
      | none => none

/-- Check all `_at_` site tails in order and sum their `spec_<k>` counts. -/
def checkIRAtTailsModel (env : PrivateAuditEnv) (declaringMod : List String) :
    List AuditName → Option Nat
  | [] => some 0
  | [seg] => checkIRAtSiteModel env declaringMod true seg
  | seg :: rest =>
    (checkIRAtSiteModel env declaringMod false seg).bind fun sp =>
      (checkIRAtTailsModel env declaringMod rest).map (fun tot => sp + tot)

/-- Model of the IR-helper `_at_` specialization name audit (`OleanEnvAuditor.checkPrivateName`). -/
def checkIRAtSpecModel (env : PrivateAuditEnv) (declaringMod : List String)
    (n : AuditName) : Bool :=
  match splitOnAt n with
  | head :: t :: ts =>
    checkIRAtHeadModel env head &&
      (match checkIRAtTailsModel env declaringMod (t :: ts) with
       | some tot => tot == (t :: ts).length
       | none => false)
  | _ => false

theorem checkIRAtSiteModel_none_of_forbidden_last (env : PrivateAuditEnv)
    (declaringMod : List String) (seg : AuditName) (us : List String) (sp : Nat)
    (hstrip : stripSpecTailModel seg = some (AuditName.ofStrings us, sp))
    (hclean : hasPrivateMentionModel (AuditName.ofStrings us) = false)
    (hforb : privateUserForbiddenModel env declaringMod us = true) :
    checkIRAtSiteModel env declaringMod true seg = none := by
  unfold checkIRAtSiteModel
  rw [hstrip]
  show (if (true && sp == 0) = true then none
    else if hasPrivateMentionModel (AuditName.ofStrings us) = true then
      match parseStrictPrivateName (AuditName.ofStrings us) with
      | some r =>
        if env.loadedModules.contains r.moduleSegs &&
            !privateUserForbiddenModel env r.moduleSegs r.userComps &&
            (!true || r.moduleSegs == declaringMod) then some sp
        else none
      | none => none
    else
      match allStrComps (AuditName.ofStrings us) with
      | some us' =>
        if !isShareCommonNameModel us' && (!true || !privateUserForbiddenModel env declaringMod us') then
          some sp
        else none
      | none => none) = none
  cases hsp : (sp == 0) with
  | true => rfl
  | false =>
    rw [hclean, allStrComps_ofStrings us]
    show (if (!isShareCommonNameModel us && (!true || !privateUserForbiddenModel env declaringMod us)) = true then
      some sp else none) = none
    rw [hforb]
    cases isShareCommonNameModel us <;> rfl

theorem checkIRAtTailsModel_none_of_last (env : PrivateAuditEnv) (declaringMod : List String)
    (mid : List AuditName) (last : AuditName)
    (hlast : checkIRAtSiteModel env declaringMod true last = none) :
    checkIRAtTailsModel env declaringMod (mid ++ [last]) = none := by
  induction mid with
  | nil => exact hlast
  | cons seg rest ih =>
    cases rest with
    | nil =>
      show (checkIRAtSiteModel env declaringMod false seg).bind (fun sp =>
        (checkIRAtTailsModel env declaringMod [last]).map (fun tot => sp + tot)) = none
      have hl : checkIRAtTailsModel env declaringMod [last] = none := hlast
      rw [hl]
      cases checkIRAtSiteModel env declaringMod false seg <;> rfl
    | cons seg2 rest2 =>
      show (checkIRAtSiteModel env declaringMod false seg).bind (fun sp =>
        (checkIRAtTailsModel env declaringMod ((seg2 :: rest2) ++ [last])).map
          (fun tot => sp + tot)) = none
      rw [ih]
      cases checkIRAtSiteModel env declaringMod false seg <;> rfl

/-- **V1 non-evasion (`_at_` site spoofing).** Any `_at_` specialization name whose final site
resolves to a reserved/forbidden namespace (such as `Trusted.forged_site.spec_0`) is rejected. -/
theorem checkIRAtSpec_rejects_forged_site (env : PrivateAuditEnv) (declaringMod : List String)
    (n head : AuditName) (mid : List AuditName) (last : AuditName) (us : List String) (sp : Nat)
    (hsplit : splitOnAt n = head :: (mid ++ [last]))
    (hstrip : stripSpecTailModel last = some (AuditName.ofStrings us, sp))
    (hclean : hasPrivateMentionModel (AuditName.ofStrings us) = false)
    (hforb : privateUserForbiddenModel env declaringMod us = true) :
    checkIRAtSpecModel env declaringMod n = false := by
  have hnone : checkIRAtTailsModel env declaringMod (mid ++ [last]) = none :=
    checkIRAtTailsModel_none_of_last env declaringMod mid last
      (checkIRAtSiteModel_none_of_forbidden_last env declaringMod last us sp hstrip hclean hforb)
  unfold checkIRAtSpecModel
  rw [hsplit]
  cases hm : mid with
  | nil =>
    rw [hm] at hnone
    have hnone' : checkIRAtTailsModel env declaringMod [last] = none := hnone
    show (checkIRAtHeadModel env head &&
      (match checkIRAtTailsModel env declaringMod [last] with
       | some tot => tot == ([last]).length
       | none => false)) = false
    rw [hnone']
    exact Bool.and_false _
  | cons seg rest =>
    rw [hm] at hnone
    have hnone' : checkIRAtTailsModel env declaringMod (seg :: (rest ++ [last])) = none := hnone
    show (checkIRAtHeadModel env head &&
      (match checkIRAtTailsModel env declaringMod (seg :: (rest ++ [last])) with
       | some tot => tot == (seg :: (rest ++ [last])).length
       | none => false)) = false
    rw [hnone']
    exact Bool.and_false _

theorem checkIRAtSiteModel_none_of_foreign_private_last (env : PrivateAuditEnv)
    (declaringMod : List String) (seg site : AuditName) (r : PrivateParseResult) (sp : Nat)
    (hstrip : stripSpecTailModel seg = some (site, sp))
    (hparse : parseStrictPrivateName site = some r)
    (hforeign : (r.moduleSegs == declaringMod) = false) :
    checkIRAtSiteModel env declaringMod true seg = none := by
  have hm := parseStrictPrivate_some_mentions site r hparse
  unfold checkIRAtSiteModel
  rw [hstrip]
  show (if (true && sp == 0) = true then none
    else if hasPrivateMentionModel site = true then
      match parseStrictPrivateName site with
      | some r' =>
        if env.loadedModules.contains r'.moduleSegs &&
            !privateUserForbiddenModel env r'.moduleSegs r'.userComps &&
            (!true || r'.moduleSegs == declaringMod) then some sp
        else none
      | none => none
    else
      match allStrComps site with
      | some us =>
        if !isShareCommonNameModel us && (!true || !privateUserForbiddenModel env declaringMod us) then
          some sp
        else none
      | none => none) = none
  cases hsp : (sp == 0) with
  | true => rfl
  | false =>
    rw [hm, hparse]
    show (if (env.loadedModules.contains r.moduleSegs &&
        !privateUserForbiddenModel env r.moduleSegs r.userComps &&
        (!true || r.moduleSegs == declaringMod)) = true then some sp else none) = none
    rw [hforeign]
    have hfalse : (env.loadedModules.contains r.moduleSegs &&
        !privateUserForbiddenModel env r.moduleSegs r.userComps && (!true || false)) = false :=
      Bool.and_false _
    rw [hfalse]
    rfl

/-- **V1 non-evasion (foreign private `_at_` final site).** Any `_at_` specialization name whose
final site is a private name claiming a module other than `declaringMod` is rejected. -/
theorem checkIRAtSpec_rejects_foreign_private_last_site (env : PrivateAuditEnv)
    (declaringMod : List String) (n head : AuditName) (mid : List AuditName)
    (last site : AuditName) (r : PrivateParseResult) (sp : Nat)
    (hsplit : splitOnAt n = head :: (mid ++ [last]))
    (hstrip : stripSpecTailModel last = some (site, sp))
    (hparse : parseStrictPrivateName site = some r)
    (hforeign : (r.moduleSegs == declaringMod) = false) :
    checkIRAtSpecModel env declaringMod n = false := by
  have hnone : checkIRAtTailsModel env declaringMod (mid ++ [last]) = none :=
    checkIRAtTailsModel_none_of_last env declaringMod mid last
      (checkIRAtSiteModel_none_of_foreign_private_last env declaringMod last site r sp hstrip
        hparse hforeign)
  unfold checkIRAtSpecModel
  rw [hsplit]
  cases hm : mid with
  | nil =>
    rw [hm] at hnone
    have hnone' : checkIRAtTailsModel env declaringMod [last] = none := hnone
    show (checkIRAtHeadModel env head &&
      (match checkIRAtTailsModel env declaringMod [last] with
       | some tot => tot == ([last]).length
       | none => false)) = false
    rw [hnone']
    exact Bool.and_false _
  | cons seg rest =>
    rw [hm] at hnone
    have hnone' : checkIRAtTailsModel env declaringMod (seg :: (rest ++ [last])) = none := hnone
    show (checkIRAtHeadModel env head &&
      (match checkIRAtTailsModel env declaringMod (seg :: (rest ++ [last])) with
       | some tot => tot == (seg :: (rest ++ [last])).length
       | none => false)) = false
    rw [hnone']
    exact Bool.and_false _

/-! ## 9. V2 — Whole-Module Unreferenced Top-Level Axiom Sweep (`leanprover/lean4#16781`)

Reachability-only axiom auditing (`#print axioms`-style closure from the claims) cannot see a
top-level axiom nothing refers to. The whole-module sweep inspects every stored constant of every
audited module, the live second-stage constant map, and every transitively imported non-toolchain
module, independently of reachability.
-/

/-- One stored declaration, as seen by the axiom sweep. -/
structure DeclEntryModel where
  kind : DeclKindModel
  name : String
  /-- Module whose compiled artifact stores the entry. -/
  declaringMod : String
  /-- Module the loaded environment attributes the name to. -/
  originMod : String
  /-- `declaringMod` is one of the request's file-local test-axiom modules. -/
  isLocalAxiomMod : Bool := false
  /-- The name is one of the foundational axioms (`propext`, `Quot.sound`, `Classical.choice`). -/
  isFoundational : Bool := false
  /-- The name is rooted at `Assumptions`. -/
  isAssumptionsPrefix : Bool := false
  /-- `declaringMod` is a pinned toolchain module. -/
  isToolchainMod : Bool := false
  /-- `declaringMod` is rooted at `Assumptions`. -/
  inAssumptionsMod : Bool := false
  /-- The name is `Classical.choice`. -/
  isClassicalChoice : Bool := false
  /-- The name is `sorryAx`. -/
  isSorry : Bool := false
  /-- The name is a native-evaluation axiom (`Lean.ofReduceBool`, `Lean.ofReduceNat`,
  `Lean.trustCompiler`, or `_native.ax_*`). -/
  isNative : Bool := false
  /-- Constants the declaration's type and value refer to. -/
  deps : List String := []
  deriving DecidableEq, Repr

/-- Everything the sweep inspects for one audit request. -/
structure ModuleInventoryModel where
  /-- Stored constants of every audited non-toolchain module. -/
  constants : List DeclEntryModel
  /-- Live entries of the second-stage constant map (`env.constants.map₂`). -/
  stage2 : List DeclEntryModel := []
  /-- Kernel constants of transitively imported modules outside the audited set. -/
  transitiveDeps : List DeclEntryModel := []
  deriving DecidableEq, Repr

/-- Every entry the sweep inspects. -/
def ModuleInventoryModel.allEntries (inv : ModuleInventoryModel) : List DeclEntryModel :=
  inv.constants ++ inv.stage2 ++ inv.transitiveDeps

/-- Axiom policy for one stored axiom: it must be stored by the module it is attributed to, must
never be `sorryAx` or a native-evaluation axiom, and must either be a foundational axiom of a
pinned toolchain module (with `Classical.choice` subject to the constructive policy), or be a
non-foundational file-local test axiom whose `Assumptions.*` name, if any, lives in an
`Assumptions.*` module. -/
abbrev AxiomEntryAuthorized (allowClassical : Bool) (e : DeclEntryModel) : Prop :=
  e.originMod = e.declaringMod ∧ e.isSorry = false ∧ e.isNative = false ∧
  ((e.isToolchainMod = true ∧ e.isFoundational = true ∧
      (e.isClassicalChoice = true → allowClassical = true)) ∨
   (e.isToolchainMod = false ∧ e.isFoundational = false ∧
      (e.isAssumptionsPrefix = true → e.inAssumptionsMod = true) ∧ e.isLocalAxiomMod = true))

/-- A sweep violation: an axiom that is unauthorized, or any axiom at all in the live
second-stage map. -/
abbrev SweepViolation (allowClassical stage2 : Bool) (e : DeclEntryModel) : Prop :=
  e.kind = .axiomDecl ∧ (stage2 = true ∨ ¬ AxiomEntryAuthorized allowClassical e)

/-- Names of the violating entries of one inventory part. -/
def sweepViolations (allowClassical stage2 : Bool) (es : List DeclEntryModel) : List String :=
  (es.filter (fun e => decide (SweepViolation allowClassical stage2 e))).map (·.name)

/-- Result of the whole-module sweep (mirrors the `moduleConstantsAxiomSwept` diagnostic). -/
structure UnreferencedAxiomSummary where
  sweptAxioms : Nat
  violations : List String
  deriving DecidableEq, Repr

/-- Did the sweep find no violation? -/
def UnreferencedAxiomSummary.ok (s : UnreferencedAxiomSummary) : Bool := s.violations.isEmpty

/-- Whole-module axiom sweep over stored constants, the live second-stage map, and transitive
non-toolchain imports. It never consults reachability. -/
def wholeModuleAxiomSweep (allowClassical : Bool) (inv : ModuleInventoryModel) :
    UnreferencedAxiomSummary where
  sweptAxioms := (inv.allEntries.filter (fun e => decide (e.kind = .axiomDecl))).length
  violations :=
    sweepViolations allowClassical false inv.constants ++
      sweepViolations allowClassical true inv.stage2 ++
      sweepViolations allowClassical false inv.transitiveDeps

/-- Dependencies of the named declaration (none if it is not stored). -/
def depsOfModel (es : List DeclEntryModel) (n : String) : List String :=
  match es.find? (fun e => e.name == n) with
  | some e => e.deps
  | none => []

/-- One breadth-first step of the reference closure. -/
def reachStepModel (es : List DeclEntryModel) (seen : List String) : List String :=
  seen ++ (seen.flatMap (depsOfModel es)).filter (fun d => !seen.contains d)

/-- Fuel-bounded reference closure from `seen`. -/
def reachClosureModel (es : List DeclEntryModel) : Nat → List String → List String
  | 0, seen => seen
  | fuel + 1, seen => reachClosureModel es fuel (reachStepModel es seen)

/-- The legacy policy: audit only axioms reachable from `roots` through references. -/
def reachabilityOnlyAxioms (allowClassical : Bool) (inv : ModuleInventoryModel)
    (roots : List String) : List String :=
  sweepViolations allowClassical false
    (inv.allEntries.filter (fun e =>
      (reachClosureModel inv.allEntries inv.allEntries.length roots).contains e.name))

theorem mem_sweepViolations {ac s2 : Bool} {es : List DeclEntryModel} {e : DeclEntryModel}
    (he : e ∈ es) (hv : SweepViolation ac s2 e) : e.name ∈ sweepViolations ac s2 es :=
  List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, decide_eq_true hv⟩, rfl⟩

theorem sweepViolations_sound {ac s2 : Bool} {es : List DeclEntryModel} {n : String}
    (h : n ∈ sweepViolations ac s2 es) : ∃ e, e ∈ es ∧ e.name = n ∧ SweepViolation ac s2 e := by
  obtain ⟨e, hmem, hname⟩ := List.mem_map.mp h
  have hf := List.mem_filter.mp hmem
  exact ⟨e, hf.1, hname, of_decide_eq_true hf.2⟩

/-- A concrete audited module with an unreferenced top-level `axiom unused_cheat : False`. -/
def unusedCheatInventory : ModuleInventoryModel where
  constants := [
    { kind := .axiomDecl, name := "unused_cheat", declaringMod := "M", originMod := "M" },
    { kind := .defnDecl, name := "helper", declaringMod := "M", originMod := "M" },
    { kind := .thmDecl, name := "claim", declaringMod := "M", originMod := "M",
      deps := ["helper"] }]

/-- **V2 (a).** Reachability-only auditing admits a module containing an unreferenced top-level
`axiom unused_cheat : False`; the whole-module sweep rejects that same module. -/
theorem reachabilityOnly_misses_unreferenced_axiom :
    reachabilityOnlyAxioms false unusedCheatInventory ["claim"] = [] ∧
      (wholeModuleAxiomSweep false unusedCheatInventory).violations = ["unused_cheat"] ∧
      (wholeModuleAxiomSweep false unusedCheatInventory).ok = false := by
  decide

/-- **V2 (b).** The sweep reports every unauthorized axiom stored anywhere in the inventory —
audited modules, the live second-stage map, or transitive imports — with no reachability
hypothesis at all. -/
theorem wholeModuleAxiomSweep_complete (allowClassical : Bool) (inv : ModuleInventoryModel)
    (e : DeclEntryModel) (hmem : e ∈ inv.allEntries) (hax : e.kind = .axiomDecl)
    (hun : ¬ AxiomEntryAuthorized allowClassical e) :
    e.name ∈ (wholeModuleAxiomSweep allowClassical inv).violations := by
  show e.name ∈ sweepViolations allowClassical false inv.constants ++
    sweepViolations allowClassical true inv.stage2 ++
    sweepViolations allowClassical false inv.transitiveDeps
  have hv : SweepViolation allowClassical false e := ⟨hax, Or.inr hun⟩
  have hmem' : e ∈ inv.constants ++ inv.stage2 ++ inv.transitiveDeps := hmem
  rcases List.mem_append.mp hmem' with h12 | h3
  · rcases List.mem_append.mp h12 with h1 | h2
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (mem_sweepViolations h1 hv))))
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
        (Or.inr (mem_sweepViolations h2 ⟨hax, Or.inl rfl⟩))))
  · exact List.mem_append.mpr (Or.inr (mem_sweepViolations h3 hv))

/-- **V2 (b′).** Every axiom in the live second-stage constant map is reported, authorized or
not. -/
theorem wholeModuleAxiomSweep_flags_stage2_axiom (allowClassical : Bool)
    (inv : ModuleInventoryModel) (e : DeclEntryModel) (hmem : e ∈ inv.stage2)
    (hax : e.kind = .axiomDecl) :
    e.name ∈ (wholeModuleAxiomSweep allowClassical inv).violations := by
  show e.name ∈ sweepViolations allowClassical false inv.constants ++
    sweepViolations allowClassical true inv.stage2 ++
    sweepViolations allowClassical false inv.transitiveDeps
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inr (mem_sweepViolations hmem ⟨hax, Or.inl rfl⟩))))

/-- **V2 soundness of acceptance.** If the sweep reports nothing, every stored axiom is
authorized and the live second-stage map holds no axiom. -/
theorem wholeModuleAxiomSweep_ok_sound (allowClassical : Bool) (inv : ModuleInventoryModel)
    (hok : (wholeModuleAxiomSweep allowClassical inv).ok = true) :
    (∀ e, e ∈ inv.allEntries → e.kind = .axiomDecl → AxiomEntryAuthorized allowClassical e) ∧
      (∀ e, e ∈ inv.stage2 → e.kind ≠ .axiomDecl) := by
  have hnil : (wholeModuleAxiomSweep allowClassical inv).violations = [] :=
    List.isEmpty_iff.mp hok
  refine ⟨fun e hmem hax => Decidable.byContradiction fun hun => ?_, fun e hmem hax => ?_⟩
  · have hin := wholeModuleAxiomSweep_complete allowClassical inv e hmem hax hun
    rw [hnil] at hin
    cases hin
  · have hin := wholeModuleAxiomSweep_flags_stage2_axiom allowClassical inv e hmem hax
    rw [hnil] at hin
    cases hin

/-- **V2 subsumption.** Everything reachability-only auditing reports, the sweep reports. -/
theorem wholeModuleAxiomSweep_subsumes_reachability (allowClassical : Bool)
    (inv : ModuleInventoryModel) (roots : List String) (n : String)
    (h : n ∈ reachabilityOnlyAxioms allowClassical inv roots) :
    n ∈ (wholeModuleAxiomSweep allowClassical inv).violations := by
  obtain ⟨e, hmem, hname, hv⟩ := sweepViolations_sound h
  have hall : e ∈ inv.allEntries := (List.mem_filter.mp hmem).1
  have hun : ¬ AxiomEntryAuthorized allowClassical e := hv.2.resolve_left (by decide)
  rw [← hname]
  exact wholeModuleAxiomSweep_complete allowClassical inv e hall hv.1 hun

/-- A foundational axiom name declared outside the pinned toolchain is never authorized. -/
theorem axiomEntry_foundational_redecl_unauthorized (allowClassical : Bool) (e : DeclEntryModel)
    (hf : e.isFoundational = true) (ht : e.isToolchainMod = false) :
    ¬ AxiomEntryAuthorized allowClassical e := by
  intro h
  rcases h.2.2.2 with ⟨ht', _⟩ | ⟨_, hf', _⟩
  · rw [ht] at ht'; cases ht'
  · rw [hf] at hf'; cases hf'

/-- An `Assumptions.*` axiom declared outside an `Assumptions.*` module is never authorized. -/
theorem axiomEntry_foreign_assumptions_unauthorized (allowClassical : Bool) (e : DeclEntryModel)
    (hp : e.isAssumptionsPrefix = true) (hm : e.inAssumptionsMod = false)
    (ht : e.isToolchainMod = false) : ¬ AxiomEntryAuthorized allowClassical e := by
  intro h
  rcases h.2.2.2 with ⟨ht', _⟩ | ⟨_, _, ha, _⟩
  · rw [ht] at ht'; cases ht'
  · have hin := ha hp
    rw [hm] at hin
    cases hin

/-- **V2 (c).** A non-toolchain re-declaration of a foundational axiom is rejected even inside a
file-local test-axiom module, under every `Classical.choice` policy. -/
theorem wholeModuleAxiomSweep_rejects_foundational_redecl (allowClassical : Bool)
    (inv : ModuleInventoryModel) (e : DeclEntryModel) (hmem : e ∈ inv.allEntries)
    (hax : e.kind = .axiomDecl) (hf : e.isFoundational = true) (ht : e.isToolchainMod = false) :
    e.name ∈ (wholeModuleAxiomSweep allowClassical inv).violations :=
  wholeModuleAxiomSweep_complete allowClassical inv e hmem hax
    (axiomEntry_foundational_redecl_unauthorized allowClassical e hf ht)

/-- **V2 (c).** A foreign `Assumptions.*` axiom is rejected even inside a file-local test-axiom
module. -/
theorem wholeModuleAxiomSweep_rejects_foreign_assumptions (allowClassical : Bool)
    (inv : ModuleInventoryModel) (e : DeclEntryModel) (hmem : e ∈ inv.allEntries)
    (hax : e.kind = .axiomDecl) (hp : e.isAssumptionsPrefix = true)
    (hm : e.inAssumptionsMod = false) (ht : e.isToolchainMod = false) :
    e.name ∈ (wholeModuleAxiomSweep allowClassical inv).violations :=
  wholeModuleAxiomSweep_complete allowClassical inv e hmem hax
    (axiomEntry_foreign_assumptions_unauthorized allowClassical e hp hm ht)

/-- **V2 (d).** `sorryAx` is never authorized, even inside a file-local test-axiom module. -/
theorem wholeModuleAxiomSweep_rejects_sorry_in_local_mod (allowClassical : Bool)
    (inv : ModuleInventoryModel) (e : DeclEntryModel) (hmem : e ∈ inv.allEntries)
    (hax : e.kind = .axiomDecl) (hs : e.isSorry = true) :
    e.name ∈ (wholeModuleAxiomSweep allowClassical inv).violations :=
  wholeModuleAxiomSweep_complete allowClassical inv e hmem hax fun h => by
    have hsf := h.2.1
    rw [hs] at hsf
    cases hsf

/-- **V2 (e).** Native-evaluation axioms (`Lean.ofReduceBool`, `_native.ax_*`, ...) are never
authorized, even inside a file-local test-axiom module. -/
theorem wholeModuleAxiomSweep_rejects_native_in_local_mod (allowClassical : Bool)
    (inv : ModuleInventoryModel) (e : DeclEntryModel) (hmem : e ∈ inv.allEntries)
    (hax : e.kind = .axiomDecl) (hn : e.isNative = true) :
    e.name ∈ (wholeModuleAxiomSweep allowClassical inv).violations :=
  wholeModuleAxiomSweep_complete allowClassical inv e hmem hax fun h => by
    have hnf := h.2.2.1
    rw [hn] at hnf
    cases hnf

/-- **V2 (f).** A masked top-level axiom re-declaration (`originMod ≠ declaringMod`) is always
rejected. -/
theorem wholeModuleAxiomSweep_rejects_masked_redecl (allowClassical : Bool)
    (inv : ModuleInventoryModel) (e : DeclEntryModel) (hmem : e ∈ inv.allEntries)
    (hax : e.kind = .axiomDecl) (hne : e.originMod ≠ e.declaringMod) :
    e.name ∈ (wholeModuleAxiomSweep allowClassical inv).violations :=
  wholeModuleAxiomSweep_complete allowClassical inv e hmem hax fun h => hne h.1

/-- **V2 (g).** Under constructive policy (`allowClassical = false`), `Classical.choice` is always
rejected even when declared by a pinned toolchain module as a foundational axiom. -/
theorem wholeModuleAxiomSweep_rejects_classical_in_constructive (inv : ModuleInventoryModel)
    (e : DeclEntryModel) (hmem : e ∈ inv.allEntries) (hax : e.kind = .axiomDecl)
    (hc : e.isClassicalChoice = true) (hf : e.isFoundational = true) :
    e.name ∈ (wholeModuleAxiomSweep false inv).violations :=
  wholeModuleAxiomSweep_complete false inv e hmem hax fun h => by
    rcases h.2.2.2 with ⟨_, _, hallow⟩ | ⟨_, hnf, _⟩
    · cases hallow hc
    · rw [hf] at hnf; cases hnf

/-! ## 10. V3 — Artifact Root Containment & Acyclic Compacted-Region Bounds (`leanprover/lean4#16737`)

Loading a compiled artifact maps its compacted object region into memory and trusts every
pointer in it, so the region is validated *before* it is imported: artifact paths must lie inside
an approved build root at a component boundary, and every reachable object must be immortal, of
a known kind, in bounds, and point strictly downward inside its own region.
-/

/-- One component of a canonical absolute path. -/
structure PathCompModel where
  name : String
  isSymlink : Bool := false
  deriving DecidableEq, Repr

/-- A component that is a real directory entry: not empty, `.`, `..`, a symlink, or containing
path separators (`/`) or NUL bytes. -/
def pathCompClean (c : PathCompModel) : Bool :=
  c.name != "" && c.name != "." && c.name != ".." && !c.isSymlink &&
    !(strBytes c.name).contains 47 && !(strBytes c.name).contains 0

/-- Component-boundary containment of `target` inside `root`. -/
def pathWithinRootModel (root target : List PathCompModel) : Bool :=
  root.all pathCompClean && target.all pathCompClean &&
    segsPrefixOf (root.map (·.name)) (target.map (·.name))

/-- The flawed string-prefix containment test. -/
def naivePrefixWithinModel (root target : String) : Bool := (strBytes root).isPrefixOf (strBytes target)

theorem segsPrefixOf_sibling (pre : List String) (r t : String) (rest : List String)
    (h : r ≠ t) : segsPrefixOf (pre ++ [r]) (pre ++ t :: rest) = false := by
  induction pre with
  | nil =>
    have hb : (r == t) = false := by
      cases hb : (r == t) with
      | false => rfl
      | true => exact absurd (eq_of_beq hb) h
    show (r == t && segsPrefixOf [] rest) = false
    rw [hb]
    rfl
  | cons p pre ih =>
    show (p == p && segsPrefixOf (pre ++ [r]) (pre ++ t :: rest)) = false
    rw [ih]
    exact Bool.and_false _

theorem segsPrefixOf_sound (root : List String) :
    ∀ (target : List String), segsPrefixOf root target = true → ∃ rest, target = root ++ rest := by
  induction root with
  | nil => intro target _; exact ⟨target, rfl⟩
  | cons r rs ih =>
    intro target h
    cases target with
    | nil => cases h
    | cons t ts =>
      have h' : (r == t && segsPrefixOf rs ts) = true := h
      have hrt : r = t := eq_of_beq (band_elim_left h')
      obtain ⟨rest, hrest⟩ := ih ts (band_elim_right h')
      exact ⟨rest, by rw [hrt, hrest]; rfl⟩

/-- **V3 (a).** A sibling directory that merely shares a name prefix with the last component of
the approved root (`/tmp/root_evil` vs `/tmp/root`) is never inside it. -/
theorem pathWithinRoot_rejects_prefix_confusion (pre : List PathCompModel) (r t : PathCompModel)
    (rest : List PathCompModel) (hne : r.name ≠ t.name) :
    pathWithinRootModel (pre ++ [r]) (pre ++ t :: rest) = false := by
  have h3 : segsPrefixOf ((pre ++ [r]).map (·.name)) ((pre ++ t :: rest).map (·.name)) = false := by
    rw [List.map_append, List.map_append]
    exact segsPrefixOf_sibling _ _ _ _ hne
  unfold pathWithinRootModel
  rw [h3]
  exact Bool.and_false _

/-- The string-prefix test accepts exactly the sibling the component-boundary test rejects. -/
theorem naivePrefix_accepts_prefix_confusion :
    naivePrefixWithinModel "/tmp/root" "/tmp/root_evil/Evil.olean" = true ∧
      pathWithinRootModel [⟨"tmp", false⟩, ⟨"root", false⟩]
        [⟨"tmp", false⟩, ⟨"root_evil", false⟩, ⟨"Evil.olean", false⟩] = false := by
  decide

/-- **V3 containment soundness.** An accepted target extends the root by whole components, and no
component of it is `..` or a symlink. -/
theorem pathWithinRoot_sound (root target : List PathCompModel)
    (h : pathWithinRootModel root target = true) :
    (∃ rest, target.map (·.name) = root.map (·.name) ++ rest) ∧
      ∀ c, c ∈ target → pathCompClean c = true :=
  ⟨segsPrefixOf_sound _ _ (band_elim_right h),
    fun c hc => List.all_eq_true.mp (band_elim_right (band_elim_left h)) c hc⟩

/-- Compacted-object kinds admitted inside a region, by header tag byte. -/
inductive CompactedTag : Type where
  | ctor (idx : Nat)
  | array
  | scalarArray
  | string
  | mpz
  deriving DecidableEq, Repr

/-- Classify a header tag byte: constructors are `≤ 243`; `246`, `248`, `249`, `250` are arrays,
scalar arrays, strings, and big integers. Closures, struct arrays, thunks, tasks, references,
external objects, and reserved tags never occur in a compacted region. -/
def CompactedTag.ofByte? (t : Nat) : Option CompactedTag :=
  if t ≤ 243 then some (.ctor t)
  else if t = 246 then some .array
  else if t = 248 then some .scalarArray
  else if t = 249 then some .string
  else if t = 250 then some .mpz
  else none

/-- One object of a compacted region, with its header and kind-specific size fields decoded. -/
structure CompactedObjModel where
  /-- Byte offset of the object header in the artifact (`address - base`). -/
  off : Nat
  /-- Reference count; compacted objects are immortal (`0`). -/
  rc : Nat := 0
  /-- Constructor byte size from the header (`0` for big objects). -/
  csSz : Nat := 0
  /-- Constructor field count, or scalar-array element size. -/
  other : Nat := 0
  tag : Nat
  /-- Array / scalar-array / string size, or big-integer limb count. -/
  size : Nat := 0
  /-- Array / scalar-array / string capacity, or big-integer limb allocation. -/
  capacity : Nat := 0
  /-- Big-integer limb pointer. -/
  dataPtr : Nat := 0
  /-- String code-point length. -/
  strLen : Nat := 0
  /-- The string's last byte (`data[size - 1]`) is NUL. -/
  strNulOk : Bool := true
  /-- Object-pointer slots: constructor fields or array elements. -/
  fields : List Nat := []
  deriving DecidableEq, Repr

/-- A previously validated lower layer of the same artifact chain. -/
structure ParentLayerModel where
  base : Nat
  size : Nat
  rootPtr : Nat
  rootKids : List Nat := []
  /-- Addresses of the layer's validated reachable objects. -/
  reachable : List Nat := []
  deriving DecidableEq, Repr

/-- Decoded artifact header. -/
structure OleanHeaderModel where
  /-- Magic, format version, flags, pinned toolchain version, padding, and githash all match. -/
  headerOk : Bool := true
  /-- Address the region is mapped at. -/
  base : Nat
  rootPtr : Nat
  deriving DecidableEq, Repr

/-- One compacted region: header, byte size, reachable objects, validated parent layers of the same
chain, and separate-chain layers (e.g. `.olean*` when validating `.ir*`) that must stay disjoint
and cannot be pointed into or re-exported as parents. -/
structure CompactedRegionModel where
  header : OleanHeaderModel
  fileSize : Nat
  objs : List CompactedObjModel := []
  parents : List ParentLayerModel := []
  disjointLayers : List ParentLayerModel := []
  deriving DecidableEq, Repr

/-- Address the region is mapped at. -/
abbrev CompactedRegionModel.base (r : CompactedRegionModel) : Nat := r.header.base

/-- Kind-specific header consistency and in-bounds extent of one object.
For `tag = 250` (`LeanMPZ`), `capacity` models the raw 32-bit `_mp_alloc` word (must be `< 2^31`
so signed `int32` `_mp_alloc` is non-negative) and `size` models `|_mp_size|`. -/
abbrev ObjExtentOk (r : CompactedRegionModel) (o : CompactedObjModel) : Prop :=
  (o.tag ≤ 243 ∧ (o.csSz = 0 ∨ 8 + 8 * o.other ≤ o.csSz) ∧
      o.off + max o.csSz (8 + 8 * o.other) ≤ r.fileSize) ∨
  (o.tag = 246 ∧ o.size ≤ o.capacity ∧ o.off + 24 + 8 * o.capacity ≤ r.fileSize) ∨
  (o.tag = 248 ∧ 0 < o.other ∧ o.size ≤ o.capacity ∧
      o.off + 24 + o.other * o.capacity ≤ r.fileSize) ∨
  (o.tag = 249 ∧ 1 ≤ o.size ∧ o.size ≤ o.capacity ∧ o.strNulOk = true ∧ o.strLen < o.size ∧
      o.off + 32 + o.capacity ≤ r.fileSize) ∨
  (o.tag = 250 ∧ (o.csSz = 0 ∨ 24 ≤ o.csSz) ∧ o.capacity < 2147483648 ∧ o.size ≤ o.capacity ∧
      (o.capacity = 0 ∨ (o.dataPtr % 8 = 0 ∧ r.base + 96 ≤ o.dataPtr ∧
        o.dataPtr + 8 * o.capacity ≤ r.base + r.fileSize)) ∧
      o.off + max o.csSz 24 ≤ r.fileSize)

/-- An aligned pointer into the region's own objects, strictly below the pointing object
(`base + 96 ≤ ptr < base + off`): compaction is post-order. -/
abbrev OwnDownwardPtr (r : CompactedRegionModel) (o : CompactedObjModel) (c : Nat) : Prop :=
  c % 8 = 0 ∧ r.base + 96 ≤ c ∧ c < r.base + o.off

/-- An aligned pointer to a validated reachable object of a parent layer. -/
abbrev ParentPtr (r : CompactedRegionModel) (c : Nat) : Prop :=
  c % 8 = 0 ∧ ∃ p ∈ r.parents, p.base + 96 ≤ c ∧ c + 8 ≤ p.base + p.size ∧ c ∈ p.reachable

/-- A pointer slot is a strictly downward own-region pointer to a walked object, a boxed scalar,
or a validated parent pointer. -/
abbrev FieldPtrOk (r : CompactedRegionModel) (o : CompactedObjModel) (c : Nat) : Prop :=
  (OwnDownwardPtr r o c ∧ ∃ t ∈ r.objs, r.base + t.off = c) ∨ c % 2 = 1 ∨ ParentPtr r c

/-- Number of object-pointer slots implied by the header. -/
def objFieldCount (o : CompactedObjModel) : Nat :=
  if o.tag ≤ 243 then o.other else if o.tag = 246 then o.size else 0

/-- Well-formedness of one reachable object. -/
abbrev ObjWF (r : CompactedRegionModel) (o : CompactedObjModel) : Prop :=
  o.rc = 0 ∧ o.off % 8 = 0 ∧ 96 ≤ o.off ∧ ObjExtentOk r o ∧
    o.fields.length = objFieldCount o ∧ ∀ c ∈ o.fields, FieldPtrOk r o c

/-- The root pointer addresses an object header inside the region. -/
abbrev RootInRegion (r : CompactedRegionModel) : Prop :=
  r.base + 96 ≤ r.header.rootPtr ∧ r.header.rootPtr + 8 ≤ r.base + r.fileSize

/-- The address `c` could hold an own-region object header. -/
abbrev OwnHeaderAddr (r : CompactedRegionModel) (c : Nat) : Prop :=
  c % 8 = 0 ∧ r.base + 96 ≤ c ∧ c + 8 ≤ r.base + r.fileSize

/-- Slot `k` of the module-data root: an own-region `Array` object, or exactly the same slot of
a validated parent root. -/
abbrev RootKidOk (r : CompactedRegionModel) (k c : Nat) : Prop :=
  (OwnHeaderAddr r c ∧ ∃ t ∈ r.objs, r.base + t.off = c ∧ t.tag = 246) ∨
  (¬ OwnHeaderAddr r c ∧ ∃ p ∈ r.parents, p.rootKids[k]? = some c)

/-- Check the root's slots in order, starting at slot index `k`. -/
def rootKidsOk (r : CompactedRegionModel) : Nat → List Nat → Bool
  | _, [] => true
  | k, c :: cs => decide (RootKidOk r k c) && rootKidsOk r (k + 1) cs

/-- The root is the pinned module-data shape: tag `0`, five object fields, 56 bytes, with every
slot an own `Array` or a parent's same slot. -/
abbrev RootShapeOk (r : CompactedRegionModel) : Prop :=
  r.header.rootPtr % 8 = 0 ∧
    ∃ o ∈ r.objs, r.base + o.off = r.header.rootPtr ∧ o.rc = 0 ∧ o.tag = 0 ∧ o.other = 5 ∧
      o.csSz = 56 ∧ o.off + 56 ≤ r.fileSize ∧ rootKidsOk r 0 o.fields = true

/-- The region overlaps no validated parent layer or separate-chain disjoint layer. -/
abbrev LayersDisjoint (r : CompactedRegionModel) : Prop :=
  ∀ p ∈ r.parents ++ r.disjointLayers, r.base + r.fileSize ≤ p.base ∨ p.base + p.size ≤ r.base

/-- A 96-byte empty delta layer: header only, re-exporting a parent's root. -/
abbrev EmptyDeltaLayer (r : CompactedRegionModel) : Prop :=
  r.parents ≠ [] ∧ r.fileSize = 96 ∧ (∃ p ∈ r.parents, p.rootPtr = r.header.rootPtr) ∧ r.objs = []

/-- Either the root is an in-region module-data object and every reachable object is
well-formed, or the layer is a 96-byte empty delta. -/
def RegionBodyWF (r : CompactedRegionModel) : Prop :=
  (RootInRegion r ∧ RootShapeOk r ∧ ∀ o ∈ r.objs, ObjWF r o) ∨
    (¬ RootInRegion r ∧ EmptyDeltaLayer r)

instance (r : CompactedRegionModel) : Decidable (RegionBodyWF r) :=
  @instDecidableOr _ _
    (@instDecidableAnd _ _ (inferInstance : Decidable (RootInRegion r))
      (@instDecidableAnd _ _ (inferInstance : Decidable (RootShapeOk r))
        (inferInstance : Decidable (∀ o ∈ r.objs, ObjWF r o))))
    (@instDecidableAnd _ _ (inferInstance : Decidable (¬ RootInRegion r))
      (inferInstance : Decidable (EmptyDeltaLayer r)))

/-- Well-formedness of one compacted region. -/
abbrev RegionWF (r : CompactedRegionModel) : Prop :=
  r.header.headerOk = true ∧ 96 ≤ r.fileSize ∧ r.fileSize ≤ 268435456 ∧ 0 < r.base ∧
    r.base % 8 = 0 ∧ r.base + r.fileSize < 18446744073709551616 ∧ LayersDisjoint r ∧
    RegionBodyWF r

/-- Decidable pre-import validator of one compacted region. -/
def validateOleanRegionModel (r : CompactedRegionModel) : Bool := decide (RegionWF r)

theorem validateOleanRegion_iff (r : CompactedRegionModel) :
    validateOleanRegionModel r = true ↔ RegionWF r :=
  decide_eq_true_iff

theorem validateOleanRegion_false (r : CompactedRegionModel) (h : RegionWF r → False) :
    validateOleanRegionModel r = false :=
  decide_eq_false h

theorem regionWF_objs (r : CompactedRegionModel) (h : RegionWF r) :
    ∀ o, o ∈ r.objs → ObjWF r o := by
  intro o ho
  obtain ⟨_, _, _, _, _, _, _, hbody⟩ := h
  rcases hbody with ⟨_, _, hall⟩ | ⟨_, _, _, _, hempty⟩
  · exact hall o ho
  · rw [hempty] at ho
    cases ho

/-- Layers are disjoint, so a parent pointer never lands inside the region itself. -/
theorem parentPtr_not_own (r : CompactedRegionModel) (c : Nat) (hdis : LayersDisjoint r)
    (hp : ParentPtr r c) : ¬ (r.base ≤ c ∧ c < r.base + r.fileSize) := by
  obtain ⟨_, p, hpm, hlo, hhi, _⟩ := hp
  intro hown
  rcases hdis p (List.mem_append.mpr (Or.inl hpm)) with h | h
  · exact Nat.lt_irrefl c (Nat.lt_of_lt_of_le hown.2
      (Nat.le_trans h (Nat.le_trans (Nat.le_add_right _ _) hlo)))
  · have hc8 : c < c + 8 := Nat.lt_add_of_pos_right (by decide)
    exact Nat.lt_irrefl c (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le hc8 hhi) h) hown.1)

/-- In a valid region, every even (non-boxed) pointer slot that lands inside the region itself
points strictly below the object holding it. -/
theorem regionWF_own_field_downward (r : CompactedRegionModel) (h : RegionWF r)
    (o : CompactedObjModel) (ho : o ∈ r.objs) (c : Nat) (hc : c ∈ o.fields) (heven : c % 2 = 0)
    (hge : r.base ≤ c) (hlt : c < r.base + r.fileSize) :
    r.base + 96 ≤ c ∧ c < r.base + o.off := by
  have hdis : LayersDisjoint r := h.2.2.2.2.2.2.1
  obtain ⟨_, _, _, _, _, hfields⟩ := regionWF_objs r h o ho
  rcases hfields c hc with ⟨⟨_, hlo, hdown⟩, _⟩ | hodd | hpar
  · exact ⟨hlo, hdown⟩
  · rw [heven] at hodd
    exact absurd hodd (by decide)
  · exact absurd ⟨hge, hlt⟩ (parentPtr_not_own r c hdis hpar)

/-- An own-region edge: the object at address `a` holds a non-boxed pointer `b` into the region
itself. -/
def OwnEdge (r : CompactedRegionModel) (a b : Nat) : Prop :=
  ∃ o, o ∈ r.objs ∧ r.base + o.off = a ∧ b ∈ o.fields ∧ b % 2 = 0 ∧ r.base ≤ b ∧
    b < r.base + r.fileSize

/-- A path of at least one own-region edge. -/
inductive OwnPath (r : CompactedRegionModel) : Nat → Nat → Prop where
  | single {a b : Nat} : OwnEdge r a b → OwnPath r a b
  | cons {a b c : Nat} : OwnEdge r a b → OwnPath r b c → OwnPath r a c

theorem ownEdge_lt (r : CompactedRegionModel) (h : RegionWF r) {a b : Nat} (e : OwnEdge r a b) :
    b < a := by
  obtain ⟨o, ho, ha, hb, heven, hge, hlt⟩ := e
  rw [← ha]
  exact (regionWF_own_field_downward r h o ho b hb heven hge hlt).2

theorem ownPath_lt (r : CompactedRegionModel) (h : RegionWF r) {a b : Nat} (p : OwnPath r a b) :
    b < a := by
  induction p with
  | single e => exact ownEdge_lt r h e
  | cons e _ ih => exact Nat.lt_trans ih (ownEdge_lt r h e)

/-- **V3 (b).** In a region the validator accepts, addresses strictly decrease along every
own-region edge, so no cycle of length `≥ 1` exists in the own-region object graph. -/
theorem downwardPointers_no_cycle (r : CompactedRegionModel)
    (h : validateOleanRegionModel r = true) (a : Nat) : ¬ OwnPath r a a :=
  fun p => Nat.lt_irrefl a (ownPath_lt r ((validateOleanRegion_iff r).mp h) p)

/-- **V3 (c).** A region containing any own-region cycle is rejected. -/
theorem validateOleanRegion_rejects_cycle (r : CompactedRegionModel) (a : Nat)
    (p : OwnPath r a a) : validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h => Nat.lt_irrefl a (ownPath_lt r h p)

/-- **V3 (c).** A self-loop or forward own-region pointer is rejected. -/
theorem validateOleanRegion_rejects_non_downward (r : CompactedRegionModel)
    (o : CompactedObjModel) (ho : o ∈ r.objs) (c : Nat) (hc : c ∈ o.fields) (heven : c % 2 = 0)
    (hge : r.base + o.off ≤ c) (hlt : c < r.base + r.fileSize) :
    validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h =>
    Nat.lt_irrefl c (Nat.lt_of_lt_of_le
      (regionWF_own_field_downward r h o ho c hc heven
        (Nat.le_trans (Nat.le_add_right _ _) hge) hlt).2 hge)

/-- **V3 (c).** A reachable object with a non-zero reference count is rejected. -/
theorem validateOleanRegion_rejects_nonzero_rc (r : CompactedRegionModel) (o : CompactedObjModel)
    (ho : o ∈ r.objs) (hrc : o.rc ≠ 0) : validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h => hrc (regionWF_objs r h o ho).1

/-- **V3 (c).** A reachable object with a forged kind tag (`244`, `245`, `247`, `≥ 251`) is
rejected. -/
theorem validateOleanRegion_rejects_forged_tag (r : CompactedRegionModel) (o : CompactedObjModel)
    (ho : o ∈ r.objs) (h1 : 243 < o.tag) (h2 : o.tag ≠ 246) (h3 : o.tag ≠ 248)
    (h4 : o.tag ≠ 249) (h5 : o.tag ≠ 250) : validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h => by
    obtain ⟨_, _, _, hext, _⟩ := regionWF_objs r h o ho
    rcases hext with ⟨hle, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 hle)
    · exact h2 he
    · exact h3 he
    · exact h4 he
    · exact h5 he

/-- **V3 (c).** An `Array` whose capacity runs past the end of the artifact, or whose size
exceeds its capacity, is rejected. -/
theorem validateOleanRegion_rejects_oob_array (r : CompactedRegionModel) (o : CompactedObjModel)
    (ho : o ∈ r.objs) (htag : o.tag = 246)
    (hoob : r.fileSize < o.off + 24 + 8 * o.capacity ∨ o.capacity < o.size) :
    validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h => by
    obtain ⟨_, _, _, hext, _⟩ := regionWF_objs r h o ho
    rcases hext with ⟨hle, _⟩ | ⟨_, hsz, hend⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
    · rw [htag] at hle; exact absurd hle (by decide)
    · rcases hoob with hlt | hlt
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hend)
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hsz)
    · rw [htag] at he; exact absurd he (by decide)
    · rw [htag] at he; exact absurd he (by decide)
    · rw [htag] at he; exact absurd he (by decide)

/-- **V3 (c).** A big integer whose limb pointer or limb extent leaves the region is rejected. -/
theorem validateOleanRegion_rejects_oob_mpz (r : CompactedRegionModel) (o : CompactedObjModel)
    (ho : o ∈ r.objs) (htag : o.tag = 250) (hpos : 0 < o.capacity)
    (hoob : o.dataPtr < r.base + 96 ∨ r.base + r.fileSize < o.dataPtr + 8 * o.capacity) :
    validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h => by
    obtain ⟨_, _, _, hext, _⟩ := regionWF_objs r h o ho
    rcases hext with ⟨hle, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨_, _, _, _, hlimbs, _⟩
    · rw [htag] at hle; exact absurd hle (by decide)
    · rw [htag] at he; exact absurd he (by decide)
    · rw [htag] at he; exact absurd he (by decide)
    · rw [htag] at he; exact absurd he (by decide)
    · rcases hlimbs with h0 | ⟨_, hlo, hhi⟩
      · rw [h0] at hpos; exact Nat.lt_irrefl 0 hpos
      · rcases hoob with hlt | hlt
        · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hlo)
        · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hhi)

/-- **V3 (c).** A big integer with a negative signed 32-bit `_mp_alloc` (`≥ 2^31`) is rejected. -/
theorem validateOleanRegion_rejects_negative_mpz_alloc (r : CompactedRegionModel)
    (o : CompactedObjModel) (ho : o ∈ r.objs) (htag : o.tag = 250)
    (hneg : 2147483648 ≤ o.capacity) : validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h => by
    obtain ⟨_, _, _, hext, _⟩ := regionWF_objs r h o ho
    rcases hext with ⟨hle, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨_, _, hlt, _⟩
    · rw [htag] at hle; exact absurd hle (by decide)
    · rw [htag] at he; exact absurd he (by decide)
    · rw [htag] at he; exact absurd he (by decide)
    · rw [htag] at he; exact absurd he (by decide)
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hneg)

/-- **V3 (c).** A scalar array with element size `0` is rejected. -/
theorem validateOleanRegion_rejects_zero_elem_scalarArray (r : CompactedRegionModel)
    (o : CompactedObjModel) (ho : o ∈ r.objs) (htag : o.tag = 248) (helem : o.other = 0) :
    validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h => by
    obtain ⟨_, _, _, hext, _⟩ := regionWF_objs r h o ho
    rcases hext with ⟨hle, _⟩ | ⟨he, _⟩ | ⟨_, hpos, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
    · rw [htag] at hle; exact absurd hle (by decide)
    · rw [htag] at he; exact absurd he (by decide)
    · rw [helem] at hpos; exact Nat.lt_irrefl 0 hpos
    · rw [htag] at he; exact absurd he (by decide)
    · rw [htag] at he; exact absurd he (by decide)

/-- **V3 (c).** A string without its trailing NUL byte is rejected. -/
theorem validateOleanRegion_rejects_string_without_nul (r : CompactedRegionModel)
    (o : CompactedObjModel) (ho : o ∈ r.objs) (htag : o.tag = 249) (hnul : o.strNulOk = false) :
    validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h => by
    obtain ⟨_, _, _, hext, _⟩ := regionWF_objs r h o ho
    rcases hext with ⟨hle, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨_, _, _, hok, _⟩ | ⟨he, _⟩
    · rw [htag] at hle; exact absurd hle (by decide)
    · rw [htag] at he; exact absurd he (by decide)
    · rw [htag] at he; exact absurd he (by decide)
    · rw [hnul] at hok; cases hok
    · rw [htag] at he; exact absurd he (by decide)

/-- **V3 (c).** An artifact shorter than its 96-byte header is rejected. -/
theorem validateOleanRegion_rejects_truncated (r : CompactedRegionModel) (h96 : r.fileSize < 96) :
    validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h96 h.2.1)

/-- **V3 (c).** A region overlapping a validated parent layer is rejected. -/
theorem validateOleanRegion_rejects_overlap (r : CompactedRegionModel) (p : ParentLayerModel)
    (hp : p ∈ r.parents) (h1 : p.base < r.base + r.fileSize) (h2 : r.base < p.base + p.size) :
    validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h => by
    rcases h.2.2.2.2.2.2.1 p (List.mem_append.mpr (Or.inl hp)) with hd | hd
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 hd)
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 hd)

/-- **V3 (c).** A region (such as `.ir`) overlapping a separate-chain disjoint layer (such as
`.olean`) is rejected. -/
theorem validateOleanRegion_rejects_disjoint_overlap (r : CompactedRegionModel)
    (p : ParentLayerModel) (hp : p ∈ r.disjointLayers) (h1 : p.base < r.base + r.fileSize)
    (h2 : r.base < p.base + p.size) : validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h => by
    rcases h.2.2.2.2.2.2.1 p (List.mem_append.mpr (Or.inr hp)) with hd | hd
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 hd)
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 hd)

/-- **V3 (c).** An in-region root whose object does not match the 56-byte, 5-field, tag-`0`
`ModuleData` root header is rejected. -/
theorem validateOleanRegion_rejects_short_root (r : CompactedRegionModel) (hin : RootInRegion r)
    (hbad : ∀ o ∈ r.objs, r.base + o.off = r.header.rootPtr →
      o.tag ≠ 0 ∨ o.other ≠ 5 ∨ o.csSz ≠ 56) : validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h => by
    rcases h.2.2.2.2.2.2.2 with ⟨_, ⟨_, o, ho, haddr, _, htag, hoth, hcs, _⟩, _⟩ | ⟨hnin, _⟩
    · rcases hbad o ho haddr with h1 | h2 | h3
      · exact h1 htag
      · exact h2 hoth
      · exact h3 hcs
    · exact hnin hin

/-- **V3 (c).** An out-of-region root pointer that is not a 96-byte empty delta layer over a
validated parent chain is rejected. -/
theorem validateOleanRegion_rejects_bad_empty_delta (r : CompactedRegionModel)
    (hout : ¬ RootInRegion r) (hbad : r.parents = [] ∨ r.fileSize ≠ 96) :
    validateOleanRegionModel r = false :=
  validateOleanRegion_false r fun h => by
    rcases h.2.2.2.2.2.2.2 with ⟨hin, _⟩ | ⟨_, hne, h96, _⟩
    · exact hout hin
    · rcases hbad with hnil | hne96
      · exact hne hnil
      · exact hne96 h96

/-! ## 11. V4 — `Init.ShareCommon` Ban (`leanprover/lean4#16779`), Compiler-Override Hook Summary
(`google/zerocopy#4321`), and Non-Blocking `leanprover/lean4#14896` Readiness Scanner -/

/-- One reference a module makes that the structural-sharing ban inspects. -/
inductive ShareCommonRef : Type where
  | directImport (module : List String)
  | kernelConst (name : List String)
  | lcnfConst (name : List String)
  | lcnfProj (structName : List String)
  | lcnfCases (typeName : List String)
  | irBody (callee : List String)
  | externSymbol (sym : String)
  deriving DecidableEq, Repr

/-- Is the reference a use of the structural-sharing library? A plain `import Init` is not. -/
def isShareCommonRef : ShareCommonRef → Bool
  | .directImport m => segsPrefixOf ["Init", "ShareCommon"] m
  | .kernelConst n => isShareCommonNameModel n
  | .lcnfConst n => isShareCommonNameModel n
  | .lcnfProj n => isShareCommonNameModel n
  | .lcnfCases n => isShareCommonNameModel n
  | .irBody n => isShareCommonNameModel n
  | .externSymbol s => externSymMentionsShareCommon s

/-- Every import, kernel constant, LCNF node, IR body, and native symbol of one module. -/
structure ShareCommonAuditModel where
  refs : List ShareCommonRef
  deriving DecidableEq, Repr

/-- The forbidden references of a module. -/
def auditShareCommonModel (m : ShareCommonAuditModel) : List ShareCommonRef :=
  m.refs.filter isShareCommonRef

/-- Does the module pass the structural-sharing ban? -/
def ShareCommonAuditModel.ok (m : ShareCommonAuditModel) : Bool := (auditShareCommonModel m).isEmpty

/-- **V4 ban completeness.** Every forbidden reference of a module is reported, whichever layer
(import, kernel term, LCNF `.const`/`.proj`/`.cases`, IR body, native symbol) it sits in. -/
theorem auditShareCommon_complete (m : ShareCommonAuditModel) (x : ShareCommonRef)
    (hx : x ∈ m.refs) (h : isShareCommonRef x = true) : x ∈ auditShareCommonModel m :=
  List.mem_filter.mpr ⟨hx, h⟩

/-- **V4 ban soundness of acceptance.** A passing module makes no forbidden reference. -/
theorem auditShareCommon_ok_sound (m : ShareCommonAuditModel) (hok : m.ok = true)
    (x : ShareCommonRef) (hx : x ∈ m.refs) : isShareCommonRef x = false := by
  cases hr : isShareCommonRef x with
  | false => rfl
  | true =>
    have hin := auditShareCommon_complete m x hx hr
    rw [List.isEmpty_iff.mp hok] at hin
    cases hin

/-- A direct import of `Init.ShareCommon`, or of any submodule, is forbidden. -/
theorem isShareCommonRef_direct_import (rest : List String) :
    isShareCommonRef (.directImport ("Init" :: "ShareCommon" :: rest)) = true :=
  rfl

/-- Compiler-override hooks recorded in compiled artifacts. -/
inductive CompilerHookKind : Type where
  | implementedBy | extern | export | init | builtinInit | csimp | cpass | folder
  | taggedReturn | unbox | neverExtract | macroInline
  deriving DecidableEq, Repr

/-- One compiler-override hook entry. -/
structure CompilerHookEntry where
  kind : CompilerHookKind
  decl : String
  /-- The hook is owned by a pinned toolchain module. -/
  isToolchainOwned : Bool := false
  /-- The declaration is `I.ctorIdx` of an inductive `I` of the same module. -/
  isCtorIdxOfLocalInductive : Bool := false
  /-- Constructor count of that inductive. -/
  numCtors : Nat := 0
  /-- The compiled body is the raw literal `0`. -/
  bodyIsRawZero : Bool := false
  deriving DecidableEq, Repr

/-- The only admitted hooks: toolchain-owned ones, and the compiler-generated `@[macro_inline]`
on `I.ctorIdx` of a *single*-constructor inductive whose body is the raw literal `0`. -/
abbrev HookEntryAdmitted (e : CompilerHookEntry) : Prop :=
  e.isToolchainOwned = true ∨
    (e.kind = .macroInline ∧ e.isCtorIdxOfLocalInductive = true ∧ e.numCtors = 1 ∧
      e.bodyIsRawZero = true)

/-- Simple return shape of one compilation phase of a declaration. -/
inductive SimpleRetModel : Type where
  | param (idx : Nat)
  | natLit (v : Nat)
  | strLit (v : String)
  | ctor (name : String)
  | other
  deriving DecidableEq, Repr

/-- Two phase summaries are compatible unless they are both literals of different value, or
different simple shapes. Unknown and constructor shapes are compatible with everything. -/
def simpleRetCompatModel : SimpleRetModel → SimpleRetModel → Bool
  | .other, _ => true
  | _, .other => true
  | .ctor _, _ => true
  | _, .ctor _ => true
  | .natLit x, .natLit y => x == y
  | .strLit x, .strLit y => x == y
  | .param _, .param _ => true
  | _, _ => false

/-- Return shapes of one declaration in the kernel term and its three compiled phases. -/
structure PhaseReturnModel where
  decl : String
  kernel : SimpleRetModel
  base : SimpleRetModel
  mono : SimpleRetModel
  ir : SimpleRetModel
  deriving DecidableEq, Repr

/-- Kernel, base-phase, mono-phase, and IR return shapes are pairwise compatible. -/
def PhaseReturnModel.consistent (p : PhaseReturnModel) : Bool :=
  simpleRetCompatModel p.kernel p.base && simpleRetCompatModel p.kernel p.mono &&
    simpleRetCompatModel p.kernel p.ir && simpleRetCompatModel p.base p.mono &&
    simpleRetCompatModel p.mono p.ir && simpleRetCompatModel p.base p.ir

/-- Compiler-hook inventory of one module across its `.olean` and `.ir` artifacts. -/
structure CompilerHookSummary where
  /-- Hooks recorded by `.olean` extension entries. -/
  oleanHooks : List CompilerHookEntry := []
  /-- Hooks recorded only by the `.ir` companion. -/
  irHooks : List CompilerHookEntry := []
  /-- Live specialization-cache entries (never admitted). -/
  specCacheEntries : List String := []
  phaseReturns : List PhaseReturnModel := []
  deriving DecidableEq, Repr

/-- Declarations violating the compiler-override policy. -/
def CompilerHookSummary.violations (s : CompilerHookSummary) : List String :=
  ((s.oleanHooks ++ s.irHooks).filter (fun e => decide (¬ HookEntryAdmitted e))).map (·.decl) ++
    s.specCacheEntries ++ (s.phaseReturns.filter (fun p => !p.consistent)).map (·.decl)

/-- Does the module pass the compiler-override policy? -/
def CompilerHookSummary.ok (s : CompilerHookSummary) : Bool := s.violations.isEmpty

theorem compilerHookSummary_flags (s : CompilerHookSummary) (e : CompilerHookEntry)
    (hmem : e ∈ s.oleanHooks ++ s.irHooks) (h : ¬ HookEntryAdmitted e) : e.decl ∈ s.violations :=
  List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
    (List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨hmem, decide_eq_true h⟩, rfl⟩))))

/-- **V4 hook non-evasion (IR-only).** A non-toolchain hook of any kind other than
`macro_inline` is a violation even when it is recorded *only* by the `.ir` companion. -/
theorem compilerHookSummary_flags_ir_only_hook (s : CompilerHookSummary) (e : CompilerHookEntry)
    (hmem : e ∈ s.irHooks) (htool : e.isToolchainOwned = false) (hkind : e.kind ≠ .macroInline) :
    e.decl ∈ s.violations :=
  compilerHookSummary_flags s e (List.mem_append.mpr (Or.inr hmem)) fun h => by
    rcases h with ht | ⟨hk, _⟩
    · rw [htool] at ht; cases ht
    · exact hkind hk

/-- **V4 hook non-evasion (forged `ctorIdx`).** `@[macro_inline]` on a non-toolchain declaration
is a violation unless the inductive has exactly one constructor and the body is the raw `0`. -/
theorem compilerHookSummary_rejects_forged_ctorIdx (s : CompilerHookSummary)
    (e : CompilerHookEntry) (hmem : e ∈ s.oleanHooks ++ s.irHooks)
    (htool : e.isToolchainOwned = false) (hbad : e.numCtors ≠ 1 ∨ e.bodyIsRawZero = false) :
    e.decl ∈ s.violations :=
  compilerHookSummary_flags s e hmem fun h => by
    rcases h with ht | ⟨_, _, hn, hz⟩
    · rw [htool] at ht; cases ht
    · rcases hbad with hb | hb
      · exact hb hn
      · rw [hb] at hz; cases hz

/-- **V4 phase consistency.** A declaration whose phases return contradictory values is a
violation. -/
theorem compilerHookSummary_flags_phase_mismatch (s : CompilerHookSummary) (p : PhaseReturnModel)
    (hmem : p ∈ s.phaseReturns) (h : p.consistent = false) : p.decl ∈ s.violations :=
  List.mem_append.mpr (Or.inr (List.mem_map.mpr
    ⟨p, List.mem_filter.mpr ⟨hmem, by rw [h]; rfl⟩, rfl⟩))

/-- **V4 hook soundness of acceptance.** In a passing module every hook, from either artifact,
is admitted, the specialization cache is empty, and every recorded phase return is consistent. -/
theorem compilerHookSummary_ok_sound (s : CompilerHookSummary) (hok : s.ok = true) :
    (∀ e, e ∈ s.oleanHooks ++ s.irHooks → HookEntryAdmitted e) ∧ s.specCacheEntries = [] ∧
      (∀ p, p ∈ s.phaseReturns → p.consistent = true) := by
  have hnil : s.violations = [] := List.isEmpty_iff.mp hok
  refine ⟨fun e hmem => Decidable.byContradiction fun hbad => ?_, ?_, fun p hmem => ?_⟩
  · have hin := compilerHookSummary_flags s e hmem hbad
    rw [hnil] at hin
    cases hin
  · cases hsc : s.specCacheEntries with
    | nil => rfl
    | cons x xs =>
      have hin : x ∈ s.violations :=
        List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (by rw [hsc]; exact List.mem_cons_self))))
      rw [hnil] at hin
      cases hin
  · cases hc : p.consistent with
    | true => rfl
    | false =>
      have hin := compilerHookSummary_flags_phase_mismatch s p hmem hc
      rw [hnil] at hin
      cases hin

/-- Expression skeleton scanned for `leanprover/lean4#14896` readiness: once theorems become
opaque to delta reduction, a theorem sitting in a recursor major premise or a projection
scrutinee — directly, wrapped, or via a `let`-binding — no longer reduces. -/
inductive ReadinessExpr : Type where
  | const (name : String) (isTheorem : Bool)
  | bvar (idx : Nat)
  | app (f a : ReadinessExpr)
  | lam (body : ReadinessExpr)
  | letE (value body : ReadinessExpr)
  | proj (scrutinee : ReadinessExpr)
  | recursorApp (minors major : ReadinessExpr)
  deriving DecidableEq, Repr

/-- Does de Bruijn index `i` refer to a `let`-bound theorem-carrying local in `bm`? -/
def bvarHasThm : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: rest, i + 1 => bvarHasThm rest i

/-- Pointwise monotonicity of theorem-carrying local environments. -/
abbrev BmLe (bm1 bm2 : List Bool) : Prop :=
  ∀ i, bvarHasThm bm1 i = true → bvarHasThm bm2 i = true

theorem bmLe_nil (bm : List Bool) : BmLe [] bm := fun _ h => by cases h

theorem bmLe_cons {a b : Bool} {bm1 bm2 : List Bool} (hab : a = true → b = true)
    (h : BmLe bm1 bm2) : BmLe (a :: bm1) (b :: bm2) := by
  intro i hi
  cases i with
  | zero => exact hab hi
  | succ i' => exact h i' hi

/-- Is the head of the application spine a theorem constant (the direct form)? -/
def ReadinessExpr.headIsTheorem : ReadinessExpr → Bool
  | .const _ t => t
  | .app f _ => f.headIsTheorem
  | _ => false

/-- Does a scrutinee carry a theorem constant under local `let`-binding environment `bm`, directly
or through wrapper applications (`@id T thm`) and `let` bodies? -/
def ReadinessExpr.carriesTheoremAt (bm : List Bool) : ReadinessExpr → Bool
  | .const _ t => t
  | .bvar i => bvarHasThm bm i
  | .app f a => f.carriesTheoremAt bm || a.carriesTheoremAt bm
  | .lam _ => false
  | .letE v b => v.carriesTheoremAt bm || b.carriesTheoremAt (v.carriesTheoremAt bm :: bm)
  | .proj s => s.carriesTheoremAt bm
  | .recursorApp minors major => minors.carriesTheoremAt bm || major.carriesTheoremAt bm

/-- Closed-environment scrutinee theorem test (`bm = []`). -/
def ReadinessExpr.carriesTheorem (e : ReadinessExpr) : Bool := e.carriesTheoremAt []

/-- Does the expression put a theorem in a recursor major premise or projection scrutinee,
at any depth under local `let`-binding environment `bm`? -/
def ReadinessExpr.flaggedAt (bm : List Bool) : ReadinessExpr → Bool
  | .const _ _ => false
  | .bvar _ => false
  | .app f a => f.flaggedAt bm || a.flaggedAt bm
  | .lam b => b.flaggedAt (false :: bm)
  | .letE v b => v.flaggedAt bm || b.flaggedAt (v.carriesTheoremAt bm :: bm)
  | .proj s => s.carriesTheoremAt bm || s.flaggedAt bm
  | .recursorApp minors major =>
    major.carriesTheoremAt bm || minors.flaggedAt bm || major.flaggedAt bm

/-- Does the closed expression put a theorem in a recursor major premise or projection scrutinee? -/
def ReadinessExpr.flagged (e : ReadinessExpr) : Bool := e.flaggedAt []

/-- Every scrutinee position (recursor major premise, projection target) is theorem-free under
local `let`-binding environment `bm`. -/
def ReadinessExpr.scrutineesTheoremFreeAt (bm : List Bool) : ReadinessExpr → Bool
  | .const _ _ => true
  | .bvar _ => true
  | .app f a => f.scrutineesTheoremFreeAt bm && a.scrutineesTheoremFreeAt bm
  | .lam b => b.scrutineesTheoremFreeAt (false :: bm)
  | .letE v b =>
    v.scrutineesTheoremFreeAt bm && b.scrutineesTheoremFreeAt (v.carriesTheoremAt bm :: bm)
  | .proj s => !s.carriesTheoremAt bm && s.scrutineesTheoremFreeAt bm
  | .recursorApp minors major =>
    !major.carriesTheoremAt bm && minors.scrutineesTheoremFreeAt bm &&
      major.scrutineesTheoremFreeAt bm

/-- Every scrutinee position of the closed expression is theorem-free. -/
def ReadinessExpr.scrutineesTheoremFree (e : ReadinessExpr) : Bool := e.scrutineesTheoremFreeAt []

theorem carriesTheoremAt_mono (e : ReadinessExpr) :
    ∀ {bm1 bm2 : List Bool}, BmLe bm1 bm2 →
      e.carriesTheoremAt bm1 = true → e.carriesTheoremAt bm2 = true := by
  induction e with
  | const n t => intro _ _ _ h; exact h
  | bvar i => intro _ _ hle h; exact hle i h
  | app f a ihf iha =>
    intro bm1 bm2 hle h
    cases hf : f.carriesTheoremAt bm1 with
    | true => exact bor_intro_left (ihf hle hf)
    | false =>
      have h' : (f.carriesTheoremAt bm1 || a.carriesTheoremAt bm1) = true := h
      rw [hf] at h'
      exact bor_intro_right (iha hle h')
  | lam _ _ => intro _ _ _ h; cases h
  | letE v b ihv ihb =>
    intro bm1 bm2 hle h
    cases hv : v.carriesTheoremAt bm1 with
    | true => exact bor_intro_left (ihv hle hv)
    | false =>
      have h' : (v.carriesTheoremAt bm1 || b.carriesTheoremAt (v.carriesTheoremAt bm1 :: bm1)) = true := h
      rw [hv] at h'
      have hb : b.carriesTheoremAt (false :: bm1) = true := h'
      exact bor_intro_right (ihb (bmLe_cons (fun hc => by cases hc) hle) hb)
  | proj s ihs => intro _ _ hle h; exact ihs hle h
  | recursorApp minors major ihm ihM =>
    intro bm1 bm2 hle h
    cases hm : minors.carriesTheoremAt bm1 with
    | true => exact bor_intro_left (ihm hle hm)
    | false =>
      have h' : (minors.carriesTheoremAt bm1 || major.carriesTheoremAt bm1) = true := h
      rw [hm] at h'
      exact bor_intro_right (ihM hle h')

theorem flaggedAt_mono (e : ReadinessExpr) :
    ∀ {bm1 bm2 : List Bool}, BmLe bm1 bm2 →
      e.flaggedAt bm1 = true → e.flaggedAt bm2 = true := by
  induction e with
  | const _ _ => intro _ _ _ h; cases h
  | bvar _ => intro _ _ _ h; cases h
  | app f a ihf iha =>
    intro bm1 bm2 hle h
    cases hf : f.flaggedAt bm1 with
    | true => exact bor_intro_left (ihf hle hf)
    | false =>
      have h' : (f.flaggedAt bm1 || a.flaggedAt bm1) = true := h
      rw [hf] at h'
      exact bor_intro_right (iha hle h')
  | lam b ihb =>
    intro bm1 bm2 hle h
    exact ihb (bmLe_cons (fun hc => hc) hle) h
  | letE v b ihv ihb =>
    intro bm1 bm2 hle h
    cases hv : v.flaggedAt bm1 with
    | true => exact bor_intro_left (ihv hle hv)
    | false =>
      have h' : (v.flaggedAt bm1 || b.flaggedAt (v.carriesTheoremAt bm1 :: bm1)) = true := h
      rw [hv] at h'
      exact bor_intro_right (ihb (bmLe_cons (carriesTheoremAt_mono v hle) hle) h')
  | proj s ihs =>
    intro bm1 bm2 hle h
    cases hc : s.carriesTheoremAt bm1 with
    | true => exact bor_intro_left (carriesTheoremAt_mono s hle hc)
    | false =>
      have h' : (s.carriesTheoremAt bm1 || s.flaggedAt bm1) = true := h
      rw [hc] at h'
      exact bor_intro_right (ihs hle h')
  | recursorApp minors major ihm ihM =>
    intro bm1 bm2 hle h
    cases hc : major.carriesTheoremAt bm1 with
    | true => exact bor_intro_left (bor_intro_left (carriesTheoremAt_mono major hle hc))
    | false =>
      have h' : (major.carriesTheoremAt bm1 || minors.flaggedAt bm1 || major.flaggedAt bm1) = true := h
      rw [hc] at h'
      cases hm : minors.flaggedAt bm1 with
      | true => exact bor_intro_left (bor_intro_right (ihm hle hm))
      | false =>
        have h'' : (false || minors.flaggedAt bm1 || major.flaggedAt bm1) = true := h'
        rw [hm] at h''
        exact bor_intro_right (ihM hle h'')

/-- One declaration submitted to the readiness scanner. -/
structure ReadinessDecl where
  name : String
  type : ReadinessExpr
  value : Option ReadinessExpr := none
  /-- Head-normal forms (δ/β/ζ, theorems never unfolded) of reducible application subterms:
  wrappers such as `WellFounded.fix` / `accWrap` unfolding to a non-K/non-eta recursor (`Acc.rec`)
  or a projection wrapper unfolding to `.proj` (structure-eta `And.casesOn` and K-rule `cast`
  reduce away before stopping and produce no flagged unfolded form). -/
  unfolded : List ReadinessExpr := []
  deriving DecidableEq, Repr

/-- Scan one declaration's type, value, and the head-normal forms of its applications. -/
def scanDeclOpaqueTheoremReadiness (d : ReadinessDecl) : Bool :=
  d.type.flagged || (match d.value with | some v => v.flagged | none => false) ||
    d.unfolded.any ReadinessExpr.flagged

/-- Readiness report (mirrors the `opaqueTheoremReadinessFlags` diagnostic). It is advisory:
`blocking` is `false` in every report the scanner produces. -/
structure OpaqueTheoremReadinessSummary where
  scannedDecls : Nat
  flaggedDecls : List String
  blocking : Bool := false
  deriving DecidableEq, Repr

/-- Does the report block the audit verdict? -/
def OpaqueTheoremReadinessSummary.isBlocking (s : OpaqueTheoremReadinessSummary) : Bool :=
  s.blocking

/-- Number of flagged declarations. -/
def OpaqueTheoremReadinessSummary.flagCount (s : OpaqueTheoremReadinessSummary) : Nat :=
  s.flaggedDecls.length

/-- Scan a module. With the check disabled nothing is scanned and nothing is flagged. -/
def scanModuleOpaqueTheoremReadiness (enabled : Bool) (ds : List ReadinessDecl) :
    OpaqueTheoremReadinessSummary where
  scannedDecls := if enabled then ds.length else 0
  flaggedDecls :=
    if enabled then (ds.filter scanDeclOpaqueTheoremReadiness).map (·.name) else []
  blocking := false

/-- Audit verdict from the blocking violations and a readiness report. -/
def auditVerdictWithReadiness (violations : List String) (s : OpaqueTheoremReadinessSummary) :
    Bool :=
  violations.isEmpty && !s.isBlocking

/-- **V4 readiness (a).** No report the scanner produces is blocking. -/
theorem OpaqueTheoremReadinessSummary.isBlocking_eq_false (enabled : Bool) (ds : List ReadinessDecl) :
    (scanModuleOpaqueTheoremReadiness enabled ds).isBlocking = false :=
  rfl

/-- **V4 readiness (a′).** The audit verdict is a function of the blocking violations alone:
readiness flags, however many, never turn an accept into a reject (or the reverse). -/
theorem readinessScanner_never_changes_verdict (violations : List String) (enabled : Bool)
    (ds : List ReadinessDecl) :
    auditVerdictWithReadiness violations (scanModuleOpaqueTheoremReadiness enabled ds) =
      violations.isEmpty :=
  Bool.and_true _

/-- **V4 readiness.** With the check disabled the report is empty. -/
theorem readinessScanner_disabled_zero_flags (ds : List ReadinessDecl) :
    (scanModuleOpaqueTheoremReadiness false ds).flagCount = 0 :=
  rfl

/-- The model's scrutinee test covers the direct head test. -/
theorem ReadinessExpr.carriesTheorem_of_headIsTheorem (e : ReadinessExpr)
    (h : e.headIsTheorem = true) : e.carriesTheorem = true := by
  induction e with
  | const n t => exact h
  | bvar _ => cases h
  | app f a ihf _ =>
    show (f.carriesTheorem || a.carriesTheorem) = true
    rw [ihf h]
    rfl
  | lam b _ => cases h
  | letE v b _ _ => cases h
  | proj s _ => cases h
  | recursorApp minors major _ _ => cases h

/-- **V4 readiness (b).** A theorem carried by a recursor major premise — directly, or behind
wrapper applications such as `@id T thm` — is flagged. -/
theorem readinessScanner_flags_major_premise_theorem (minors major : ReadinessExpr)
    (h : major.carriesTheorem = true) : (ReadinessExpr.recursorApp minors major).flagged = true := by
  show (major.carriesTheorem || minors.flagged || major.flagged) = true
  rw [h]
  rfl

/-- **V4 readiness (b).** A theorem carried by a projection scrutinee is flagged. -/
theorem readinessScanner_flags_proj_scrutinee_theorem (s : ReadinessExpr)
    (h : s.carriesTheorem = true) : (ReadinessExpr.proj s).flagged = true := by
  show (s.carriesTheorem || s.flagged) = true
  rw [h]
  rfl

/-- **V4 readiness (b′).** A `let`-bound theorem placed in a recursor major premise (directly or
through a wrapper such as `wrap h`) is flagged. -/
theorem readinessScanner_flags_let_bound_theorem (v minors : ReadinessExpr)
    (hv : v.carriesTheorem = true) :
    (ReadinessExpr.letE v (.recursorApp minors (.bvar 0))).flagged = true := by
  show (v.flaggedAt [] ||
    (bvarHasThm (v.carriesTheoremAt [] :: []) 0 ||
      minors.flaggedAt (v.carriesTheoremAt [] :: []) || false)) = true
  have hv' : v.carriesTheoremAt [] = true := hv
  rw [hv']
  exact bor_intro_right rfl

/-- **V4 readiness (b″).** A `let`-bound theorem placed in a projection scrutinee is flagged. -/
theorem readinessScanner_flags_let_bound_proj (v : ReadinessExpr)
    (hv : v.carriesTheorem = true) :
    (ReadinessExpr.letE v (.proj (.bvar 0))).flagged = true := by
  show (v.flaggedAt [] || (bvarHasThm (v.carriesTheoremAt [] :: []) 0 || false)) = true
  have hv' : v.carriesTheoremAt [] = true := hv
  rw [hv']
  exact bor_intro_right rfl

/-- The direct and `@id`-wrapped major-premise forms, for every theorem name and minor premise. -/
theorem readinessScanner_flags_direct_and_id_wrapped (minors ty : ReadinessExpr) (thm : String) :
    (ReadinessExpr.recursorApp minors (.const thm true)).flagged = true ∧
      (ReadinessExpr.recursorApp minors
        (.app (.app (.const "id" false) ty) (.const thm true))).flagged = true := by
  refine ⟨rfl, readinessScanner_flags_major_premise_theorem _ _ ?_⟩
  show ((false || ty.carriesTheorem) || true) = true
  exact Bool.or_true _

/-- One-step subterm relation. -/
inductive ReadinessExpr.Child : ReadinessExpr → ReadinessExpr → Prop where
  | appFn (f a : ReadinessExpr) : Child f (.app f a)
  | appArg (f a : ReadinessExpr) : Child a (.app f a)
  | lamBody (b : ReadinessExpr) : Child b (.lam b)
  | letValue (v b : ReadinessExpr) : Child v (.letE v b)
  | letBody (v b : ReadinessExpr) : Child b (.letE v b)
  | projScrutinee (s : ReadinessExpr) : Child s (.proj s)
  | recMinors (minors major : ReadinessExpr) : Child minors (.recursorApp minors major)
  | recMajor (minors major : ReadinessExpr) : Child major (.recursorApp minors major)

/-- **V4 readiness non-evasion.** A flagged subterm flags every enclosing term: no amount of
wrapping in applications, binders, `let`s, projections, or recursors hides it. -/
theorem readinessScanner_flag_propagates {s e : ReadinessExpr} (hc : ReadinessExpr.Child s e)
    (h : s.flagged = true) : e.flagged = true := by
  cases hc with
  | appFn f a => exact bor_intro_left h
  | appArg f a => exact bor_intro_right h
  | lamBody _ => exact flaggedAt_mono s (bmLe_nil _) h
  | letValue _ _ => exact bor_intro_left h
  | letBody _ _ => exact bor_intro_right (flaggedAt_mono s (bmLe_nil _) h)
  | projScrutinee s => exact bor_intro_right h
  | recMinors minors major => exact bor_intro_left (bor_intro_right h)
  | recMajor minors major => exact bor_intro_right h

theorem readinessScanner_clean_zero_flags_at (e : ReadinessExpr) :
    ∀ (bm : List Bool), e.scrutineesTheoremFreeAt bm = true → e.flaggedAt bm = false := by
  induction e with
  | const _ _ => intro _ _; rfl
  | bvar _ => intro _ _; rfl
  | app f a ihf iha =>
    intro bm h
    have h' : (f.scrutineesTheoremFreeAt bm && a.scrutineesTheoremFreeAt bm) = true := h
    show (f.flaggedAt bm || a.flaggedAt bm) = false
    rw [ihf bm (band_elim_left h'), iha bm (band_elim_right h')]
    rfl
  | lam b ih => intro bm h; exact ih (false :: bm) h
  | letE v b ihv ihb =>
    intro bm h
    have h' : (v.scrutineesTheoremFreeAt bm &&
      b.scrutineesTheoremFreeAt (v.carriesTheoremAt bm :: bm)) = true := h
    show (v.flaggedAt bm || b.flaggedAt (v.carriesTheoremAt bm :: bm)) = false
    rw [ihv bm (band_elim_left h'), ihb (v.carriesTheoremAt bm :: bm) (band_elim_right h')]
    rfl
  | proj s ih =>
    intro bm h
    have h' : (!s.carriesTheoremAt bm && s.scrutineesTheoremFreeAt bm) = true := h
    show (s.carriesTheoremAt bm || s.flaggedAt bm) = false
    rw [ih bm (band_elim_right h')]
    cases hs : s.carriesTheoremAt bm with
    | false => rfl
    | true => rw [hs] at h'; cases h'
  | recursorApp minors major ihm ihM =>
    intro bm h
    have h' : (!major.carriesTheoremAt bm && minors.scrutineesTheoremFreeAt bm &&
      major.scrutineesTheoremFreeAt bm) = true := h
    show (major.carriesTheoremAt bm || minors.flaggedAt bm || major.flaggedAt bm) = false
    rw [ihm bm (band_elim_right (band_elim_left h')), ihM bm (band_elim_right h')]
    cases hs : major.carriesTheoremAt bm with
    | false => rfl
    | true => rw [hs] at h'; cases h'

/-- **V4 readiness (c).** An expression whose scrutinee positions are all theorem-free is not
flagged, however many theorems it uses elsewhere. -/
theorem readinessScanner_clean_zero_flags (e : ReadinessExpr)
    (h : e.scrutineesTheoremFree = true) : e.flagged = false :=
  readinessScanner_clean_zero_flags_at e [] h

/-- Exact Boolean duality: `flaggedAt bm` is literally `!scrutineesTheoremFreeAt bm` (zero slack
between the scanner and the clean-scrutinee predicate). -/
theorem readinessScanner_flaggedAt_eq_not_cleanAt (e : ReadinessExpr) :
    ∀ (bm : List Bool), e.flaggedAt bm = !e.scrutineesTheoremFreeAt bm := by
  induction e with
  | const _ _ => intro _; rfl
  | bvar _ => intro _; rfl
  | app f a ihf iha =>
    intro bm
    show (f.flaggedAt bm || a.flaggedAt bm) =
      !(f.scrutineesTheoremFreeAt bm && a.scrutineesTheoremFreeAt bm)
    rw [ihf bm, iha bm]
    cases f.scrutineesTheoremFreeAt bm <;> cases a.scrutineesTheoremFreeAt bm <;> rfl
  | lam b ih => intro bm; exact ih (false :: bm)
  | letE v b ihv ihb =>
    intro bm
    show (v.flaggedAt bm || b.flaggedAt (v.carriesTheoremAt bm :: bm)) =
      !(v.scrutineesTheoremFreeAt bm && b.scrutineesTheoremFreeAt (v.carriesTheoremAt bm :: bm))
    rw [ihv bm, ihb (v.carriesTheoremAt bm :: bm)]
    cases v.scrutineesTheoremFreeAt bm <;>
      cases b.scrutineesTheoremFreeAt (v.carriesTheoremAt bm :: bm) <;> rfl
  | proj s ih =>
    intro bm
    show (s.carriesTheoremAt bm || s.flaggedAt bm) =
      !(!s.carriesTheoremAt bm && s.scrutineesTheoremFreeAt bm)
    rw [ih bm]
    cases s.carriesTheoremAt bm <;> cases s.scrutineesTheoremFreeAt bm <;> rfl
  | recursorApp minors major ihm ihM =>
    intro bm
    show (major.carriesTheoremAt bm || minors.flaggedAt bm || major.flaggedAt bm) =
      !(!major.carriesTheoremAt bm && minors.scrutineesTheoremFreeAt bm &&
        major.scrutineesTheoremFreeAt bm)
    rw [ihm bm, ihM bm]
    cases major.carriesTheoremAt bm <;> cases minors.scrutineesTheoremFreeAt bm <;>
      cases major.scrutineesTheoremFreeAt bm <;> rfl

/-- **V4 readiness exact characterization.** A closed expression has `flagged = false` if and only
if every scrutinee position is theorem-free (`scrutineesTheoremFree = true`). -/
theorem readinessScanner_flagged_iff_not_clean (e : ReadinessExpr) :
    e.flagged = false ↔ e.scrutineesTheoremFree = true := by
  show e.flaggedAt [] = false ↔ e.scrutineesTheoremFreeAt [] = true
  rw [readinessScanner_flaggedAt_eq_not_cleanAt e []]
  cases e.scrutineesTheoremFreeAt [] with
  | false => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | true => exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- Filtering with a predicate that is `false` on every element yields `[]`. -/
theorem filter_nil_of_all_false {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (∀ x, x ∈ xs → p x = false) → xs.filter p = []
  | [], _ => rfl
  | x :: xs, h => by
    have hx : p x = false := h x (List.mem_cons.mpr (Or.inl rfl))
    show (match p x with | true => x :: xs.filter p | false => xs.filter p) = []
    rw [hx]
    exact filter_nil_of_all_false p xs (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))

/-- **V4 readiness (δ-wrapped recursors).** A recursor reached only after unfolding a definition
(`accWrap accZero`, `WellFounded.fix` unfolding to `Acc.rec`) is flagged even when the surface
type and value put no theorem in any scrutinee position. -/
theorem readinessScanner_flags_delta_wrapped_recursor (d : ReadinessDecl) (minors major : ReadinessExpr)
    (hmem : ReadinessExpr.recursorApp minors major ∈ d.unfolded) (h : major.carriesTheorem = true) :
    scanDeclOpaqueTheoremReadiness d = true :=
  bor_intro_right (List.any_eq_true.mpr
    ⟨_, hmem, readinessScanner_flags_major_premise_theorem minors major h⟩)

/-- **V4 readiness (δ-wrapped projections).** A `.proj` scrutinee reached after unfolding a
definition (`projDef myPBox`) is flagged even when the surface term holds no raw `.proj`. -/
theorem readinessScanner_flags_delta_wrapped_proj (d : ReadinessDecl) (s : ReadinessExpr)
    (hmem : ReadinessExpr.proj s ∈ d.unfolded) (h : s.carriesTheorem = true) :
    scanDeclOpaqueTheoremReadiness d = true :=
  bor_intro_right (List.any_eq_true.mpr
    ⟨_, hmem, readinessScanner_flags_proj_scrutinee_theorem s h⟩)

/-- Every surface and unfolded scrutinee position of a declaration is theorem-free. -/
def ReadinessDecl.clean (d : ReadinessDecl) : Bool :=
  d.type.scrutineesTheoremFree &&
    (match d.value with | some v => v.scrutineesTheoremFree | none => true) &&
    d.unfolded.all ReadinessExpr.scrutineesTheoremFree

/-- **V4 readiness (c′′).** A declaration whose type, value, and unfolded forms are all
scrutinee-theorem-free is never flagged. -/
theorem readinessScanner_clean_decl_false (d : ReadinessDecl) (h : d.clean = true) :
    scanDeclOpaqueTheoremReadiness d = false := by
  have htv := band_elim_left h
  have ht := readinessScanner_clean_zero_flags d.type (band_elim_left htv)
  have hv : (match d.value with | some v => v.flagged | none => false) = false := by
    cases hd : d.value with
    | none => rfl
    | some v =>
      have hv0 := band_elim_right htv
      rw [hd] at hv0
      exact readinessScanner_clean_zero_flags v hv0
  have hu : d.unfolded.any ReadinessExpr.flagged = false := by
    cases ha : d.unfolded.any ReadinessExpr.flagged with
    | false => rfl
    | true =>
      obtain ⟨e, he, hfe⟩ := List.any_eq_true.mp ha
      have hce := List.all_eq_true.mp (band_elim_right h) e he
      rw [readinessScanner_clean_zero_flags e hce] at hfe
      cases hfe
  unfold scanDeclOpaqueTheoremReadiness
  rw [ht, hv, hu]
  rfl

/-- **V4 readiness (c′).** A module whose declarations are all clean produces `0` flags. -/
theorem readinessScanner_clean_module_zero_flags (enabled : Bool) (ds : List ReadinessDecl)
    (h : ∀ d, d ∈ ds → scanDeclOpaqueTheoremReadiness d = false) :
    (scanModuleOpaqueTheoremReadiness enabled ds).flagCount = 0 := by
  have hnil : ds.filter scanDeclOpaqueTheoremReadiness = [] := filter_nil_of_all_false _ ds h
  cases enabled with
  | false => rfl
  | true =>
    show ((ds.filter scanDeclOpaqueTheoremReadiness).map (·.name)).length = 0
    rw [hnil]
    rfl

end Anneal.OleanSpecStrengthAuditor
