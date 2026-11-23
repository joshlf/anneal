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
import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Init.Data.Option.Basic
import Init.WF

universe u v w x y z

namespace Anneal.ParametricCore

/-!
# MIR-Dialect-Parametric Loop-Invariant and Simulation Combinators
(`Anneal.ParametricCore.LoopInv`)

This module restates the CFG loop-invariant library `Anneal.LoopInv` (`#4059`)
over a thin weakest-precondition interface, `MirWpOps State`, instead of one
fixed MIR model. It imports only `Init.*` modules of the Pass-1 foundation
lock, so every MIR dialect (`V2026_06_01`, `V2026_08_01`, the candidate
`MirModel`) can instantiate it without adding to the trusted base.

1. **Step interface (`StepOutcome`, `MirWpOps`):** `MirWpOps State Out Fault`
   gives a machine with states `State`, outcomes `Out` and faults `Fault` a
   monotone single-step weakest precondition `stepWp`; `Out` and `Fault` are
   determined by `State`. `MirWpOps.ofDetStep` and `MirWpOps.ofChoiceStep`
   build instances from a deterministic step function and from a
   `valid`-quantified nondeterministic one; any other monotone `stepWp` (for
   example a coalgebraic interaction-tree node) is an instance as well.
2. **Fuel-free checkpoints (`wpUntil`, `wpOutcome`):** `wpUntil` is an
   inductive predicate, so a proof never mentions a step budget. The
   `@Nat.rec` predicates `wpUntilFuel` and `wpOutcomeFuel` are the bounded
   counterparts; they always imply the fuel-free ones, and are equivalent to
   them (`∃ fuel, ...`) for every `FuelContinuous` interface, which includes
   all deterministic ones.
3. **Loop rules:** well-founded (`wpLoop_inv`), ranked, counting, list and
   state-measure invariants, each with early exit through `onDone`, plus
   strict variants (`wpStepUntil`) that demand at least one step per
   iteration.
4. **Simulation rules:** `wpSim_step`, `wpSim_det`, `wpSim_det_run` and
   `wpSim_rel` relate a machine to an abstract transition system.
5. **Self-test:** `countDownToy_spec` proves a two-block countdown machine
   correct for every input with these rules and no step budget.
-/

/-! ## Part I: Step Outcomes and the `MirWpOps` Interface -/

/-- Result of one machine step: continue in `next`, terminate with `out`, or
fault with `err`. -/
inductive StepOutcome (State : Type u) (Out : Type v) (Fault : Type w) :
    Type (max u v w) where
  /-- Continue execution in state `next`. -/
  | step (next : State) : StepOutcome State Out Fault
  /-- Terminate with outcome `out`. -/
  | done (out : Out) : StepOutcome State Out Fault
  /-- Fault with error `err`. -/
  | fault (err : Fault) : StepOutcome State Out Fault

namespace StepOutcome

variable {State : Type u} {Out : Type v} {Fault : Type w}

/-- Weakest precondition of a single step result: dispatch to the predicate
that matches the constructor. -/
def wp (r : StepOutcome State Out Fault) (onStep : State → Prop)
    (onDone : Out → Prop) (onFault : Fault → Prop) : Prop :=
  match r with
  | .step s' => onStep s'
  | .done o => onDone o
  | .fault f => onFault f

/-- `wp` of a `.step` result is the continuation predicate at the next state. -/
theorem wp_step_iff {s' : State} {onStep : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} :
    (StepOutcome.step s' : StepOutcome State Out Fault).wp
      onStep onDone onFault ↔ onStep s' :=
  Iff.rfl

/-- `wp` of a `.done` result is the terminal predicate at the outcome. -/
theorem wp_done_iff {o : Out} {onStep : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} :
    (StepOutcome.done o : StepOutcome State Out Fault).wp
      onStep onDone onFault ↔ onDone o :=
  Iff.rfl

/-- `wp` of a `.fault` result is the fault predicate at the error. -/
theorem wp_fault_iff {f : Fault} {onStep : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} :
    (StepOutcome.fault f : StepOutcome State Out Fault).wp
      onStep onDone onFault ↔ onFault f :=
  Iff.rfl

/-- `wp` is monotone in all three predicates. -/
theorem wp_mono {r : StepOutcome State Out Fault}
    {P₁ P₂ : State → Prop} {Q₁ Q₂ : Out → Prop} {R₁ R₂ : Fault → Prop}
    (hP : ∀ s', P₁ s' → P₂ s') (hQ : ∀ o, Q₁ o → Q₂ o)
    (hR : ∀ f, R₁ f → R₂ f) (h : r.wp P₁ Q₁ R₁) : r.wp P₂ Q₂ R₂ := by
  cases r with
  | step s' => exact hP s' h
  | done o => exact hQ o h
  | fault f => exact hR f h

/-- `wp` distributes over conjunction of its predicates. -/
theorem wp_conj {r : StepOutcome State Out Fault}
    {P₁ P₂ : State → Prop} {Q₁ Q₂ : Out → Prop} {R₁ R₂ : Fault → Prop}
    (h₁ : r.wp P₁ Q₁ R₁) (h₂ : r.wp P₂ Q₂ R₂) :
    r.wp (fun s' => P₁ s' ∧ P₂ s') (fun o => Q₁ o ∧ Q₂ o)
      (fun f => R₁ f ∧ R₂ f) := by
  cases r with
  | step s' => exact ⟨h₁, h₂⟩
  | done o => exact ⟨h₁, h₂⟩
  | fault f => exact ⟨h₁, h₂⟩

/-- `wp` commutes with a countable union of continuation predicates: a single
step result needs only one member of the family. -/
theorem wp_exists_nat {r : StepOutcome State Out Fault}
    {P : Nat → State → Prop} {Q : Out → Prop} {R : Fault → Prop}
    (h : r.wp (fun s' => ∃ n, P n s') Q R) : ∃ n, r.wp (P n) Q R := by
  cases r with
  | step s' =>
    let ⟨n, hn⟩ := (h : ∃ n, P n s')
    exact ⟨n, hn⟩
  | done o => exact ⟨0, h⟩
  | fault f => exact ⟨0, h⟩

/-- Successor state of a step result, or `none` once it terminates or
faults. -/
def next? (r : StepOutcome State Out Fault) : Option State :=
  match r with
  | .step s' => some s'
  | .done _ => none
  | .fault _ => none

/-- `next?` returns `some s'` exactly for the result `.step s'`. -/
theorem next?_eq_some_iff {r : StepOutcome State Out Fault} {s' : State} :
    r.next? = some s' ↔ r = .step s' := by
  cases r with
  | step t =>
    constructor
    · intro h
      injection h with hEq
      rw [hEq]
    · intro h
      injection h with hEq
      rw [hEq]
      rfl
  | done o =>
    constructor
    · intro h
      cases h
    · intro h
      cases h
  | fault f =>
    constructor
    · intro h
      cases h
    · intro h
      cases h

end StepOutcome

/-- Single-step weakest-precondition interface of a machine with states
`State`.

`stepWp s onStep onDone onFault` holds when every step the machine can take
from `s` either continues in a state satisfying `onStep`, terminates with an
outcome satisfying `onDone`, or faults with an error satisfying `onFault`.
The only law is monotonicity, so the interface covers deterministic step
functions, `valid`-quantified nondeterministic ones, and coalgebraic steps
whose effects are interpreted by an effect weakest precondition.

`Out` and `Fault` are `outParam` class parameters, so typeclass resolution
synthesizes them as concrete types (allowing dot-notation on outcome
constructors and arithmetic/pattern matching without type-spelled wrappers).
`blockTag?` optionally exposes the basic block a state is at, for
loop-header and stage cutpoints; it defaults to `none` for machines without a
control-flow graph. -/
class MirWpOps (State : Type u) (Out : outParam (Type v))
    (Fault : outParam (Type w)) where
  /-- Single-step weakest precondition. -/
  stepWp : State → (State → Prop) → (Out → Prop) → (Fault → Prop) → Prop
  /-- `stepWp` is monotone in the continuation, terminal and fault
  predicates. -/
  stepWp_mono : ∀ {s : State} {P₁ P₂ : State → Prop} {Q₁ Q₂ : Out → Prop}
      {R₁ R₂ : Fault → Prop},
      (∀ s', P₁ s' → P₂ s') → (∀ o, Q₁ o → Q₂ o) → (∀ f, R₁ f → R₂ f) →
      stepWp s P₁ Q₁ R₁ → stepWp s P₂ Q₂ R₂
  /-- Basic-block tag of a state, when the machine has one. -/
  blockTag? : State → Option Nat := fun _ => none

namespace MirWpOps

/-- `MirWpOps` instance of a deterministic step function. On a concrete state
`stepWp` reduces by `rfl` to the predicate selected by `step s`. -/
@[reducible] def ofDetStep {State : Type u} {Out : Type v} {Fault : Type w}
    (step : State → StepOutcome State Out Fault)
    (blockTag? : State → Option Nat := fun _ => none) :
    MirWpOps State Out Fault where
  stepWp s onStep onDone onFault := (step s).wp onStep onDone onFault
  stepWp_mono := fun hP hQ hR h => StepOutcome.wp_mono hP hQ hR h
  blockTag? := blockTag?

/-- `MirWpOps` instance of a nondeterministic step function `step c s` whose
admissible choices at `s` are those with `valid s c`. A step is safe when some
choice is admissible and every admissible choice behaves as required, which is
the `ValidChoice`-quantified shape of `#4059`. -/
@[reducible] def ofChoiceStep {State : Type u} {Out : Type v}
    {Fault : Type w} (Choice : Type x) (valid : State → Choice → Prop)
    (step : Choice → State → StepOutcome State Out Fault)
    (blockTag? : State → Option Nat := fun _ => none) :
    MirWpOps State Out Fault where
  stepWp s onStep onDone onFault :=
    (∃ c₀ : Choice, valid s c₀) ∧
      ∀ c : Choice, valid s c → (step c s).wp onStep onDone onFault
  stepWp_mono := fun hP hQ hR h =>
    ⟨h.1, fun c hc => StepOutcome.wp_mono hP hQ hR (h.2 c hc)⟩
  blockTag? := blockTag?

section Constructors

variable {State : Type u} {Out : Type v} {Fault : Type w}

/-- `stepWp` of `ofDetStep` is `StepOutcome.wp` of the step result. -/
theorem stepWp_ofDetStep_iff
    {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {s : State} {onStep : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} :
    (ofDetStep step tag).stepWp s onStep onDone onFault ↔
      (step s).wp onStep onDone onFault :=
  Iff.rfl

/-- `stepWp` of `ofChoiceStep` quantifies over the admissible choices. -/
theorem stepWp_ofChoiceStep_iff {Choice : Type x}
    {valid : State → Choice → Prop}
    {step : Choice → State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {s : State} {onStep : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} :
    (ofChoiceStep Choice valid step tag).stepWp s onStep onDone onFault ↔
      ((∃ c₀ : Choice, valid s c₀) ∧
        ∀ c : Choice, valid s c → (step c s).wp onStep onDone onFault) :=
  Iff.rfl

/-- Deterministic lifting for `ofChoiceStep`: when `c₀` is admissible at `s`
and is the only admissible choice, it suffices to consider the step
`step c₀ s`. -/
theorem stepWp_of_detChoice {Choice : Type x}
    {valid : State → Choice → Prop}
    {step : Choice → State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {s : State} {c₀ : Choice}
    (hValid : valid s c₀) (hUniq : ∀ c, valid s c → c = c₀)
    {onStep : State → Prop} {onDone : Out → Prop} {onFault : Fault → Prop}
    (h : (step c₀ s).wp onStep onDone onFault) :
    (ofChoiceStep Choice valid step tag).stepWp s onStep onDone onFault := by
  refine ⟨⟨c₀, hValid⟩, fun c hc => ?_⟩
  rw [hUniq c hc]
  exact h

/-- Converse of `stepWp_of_detChoice`: an admissible choice `c₀` is one of the
steps that `stepWp` accounts for. -/
theorem stepWp_detChoice_elim {Choice : Type x}
    {valid : State → Choice → Prop}
    {step : Choice → State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {s : State} {c₀ : Choice}
    (hValid : valid s c₀)
    {onStep : State → Prop} {onDone : Out → Prop} {onFault : Fault → Prop}
    (h : (ofChoiceStep Choice valid step tag).stepWp s
      onStep onDone onFault) :
    (step c₀ s).wp onStep onDone onFault :=
  h.2 c₀ hValid

/-- With a unique admissible choice `c₀` at `s`, `ofChoiceStep` agrees with
the deterministic interface of `step c₀`. -/
theorem stepWp_detChoice_iff {Choice : Type x}
    {valid : State → Choice → Prop}
    {step : Choice → State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {s : State} {c₀ : Choice}
    (hValid : valid s c₀) (hUniq : ∀ c, valid s c → c = c₀)
    {onStep : State → Prop} {onDone : Out → Prop} {onFault : Fault → Prop} :
    (ofChoiceStep Choice valid step tag).stepWp s onStep onDone onFault ↔
      (ofDetStep (step c₀) tag).stepWp s onStep onDone onFault :=
  ⟨stepWp_detChoice_elim hValid, stepWp_of_detChoice hValid hUniq⟩

end Constructors

variable {State : Type u} {Out : Type v} {Fault : Type w}

/-- States whose basic-block tag is `tag`. -/
def atBlock (ops : MirWpOps State Out Fault) (tag : Nat) (s : State) :
    Prop :=
  ops.blockTag? s = some tag

/-- A state is at block `tag` exactly when `blockTag?` reports `tag`. -/
theorem atBlock_iff {ops : MirWpOps State Out Fault} {tag : Nat}
    {s : State} : ops.atBlock tag s ↔ ops.blockTag? s = some tag :=
  Iff.rfl

/-- A state is at no more than one block. -/
theorem atBlock_unique {ops : MirWpOps State Out Fault} {t₁ t₂ : Nat}
    {s : State} (h₁ : ops.atBlock t₁ s) (h₂ : ops.atBlock t₂ s) :
    t₁ = t₂ := by
  have hEq : some t₁ = some t₂ := h₁.symm.trans h₂
  injection hEq

/-- A step interface is conjunctive when two step proofs for the same state
combine into one for the conjoined predicates. Deterministic and
`valid`-quantified interfaces are conjunctive. -/
def Conjunctive (ops : MirWpOps State Out Fault) : Prop :=
  ∀ (s : State) (P₁ P₂ : State → Prop) (Q₁ Q₂ : Out → Prop)
    (R₁ R₂ : Fault → Prop),
    ops.stepWp s P₁ Q₁ R₁ → ops.stepWp s P₂ Q₂ R₂ →
    ops.stepWp s (fun s' => P₁ s' ∧ P₂ s') (fun o => Q₁ o ∧ Q₂ o)
      (fun f => R₁ f ∧ R₂ f)

/-- A step interface is fuel-continuous when a step into the union of an
increasing chain of predicates is already a step into one member of the chain.
This is what makes a fuel-free proof yield a finite step budget. Deterministic
interfaces are fuel-continuous; an interface that quantifies over infinitely
many successors (for example over the answers of an external call) need not
be. -/
def FuelContinuous (ops : MirWpOps State Out Fault) : Prop :=
  ∀ (s : State) (P : Nat → State → Prop) (Q : Out → Prop)
    (R : Fault → Prop),
    (∀ n s', P n s' → P (n + 1) s') →
    ops.stepWp s (fun s' => ∃ n, P n s') Q R →
    ∃ n, ops.stepWp s (P n) Q R

/-- A step interface is strict when no state can step with all three
predicates empty, so a weakest precondition can never be discharged
vacuously. -/
def Strict (ops : MirWpOps State Out Fault) : Prop :=
  ∀ (s : State),
    ¬ ops.stepWp s (fun _ => False) (fun _ => False) (fun _ => False)

section ConstructorLaws

/-- Deterministic interfaces are conjunctive. -/
theorem ofDetStep_conjunctive (step : State → StepOutcome State Out Fault)
    (tag : State → Option Nat) : (ofDetStep step tag).Conjunctive :=
  fun _ _ _ _ _ _ _ h₁ h₂ => StepOutcome.wp_conj h₁ h₂

/-- Deterministic interfaces are fuel-continuous. -/
theorem ofDetStep_fuelContinuous
    (step : State → StepOutcome State Out Fault)
    (tag : State → Option Nat) : (ofDetStep step tag).FuelContinuous :=
  fun _ _ _ _ _ h => StepOutcome.wp_exists_nat h

/-- Deterministic interfaces are strict. -/
theorem ofDetStep_strict (step : State → StepOutcome State Out Fault)
    (tag : State → Option Nat) : (ofDetStep step tag).Strict := by
  intro s h
  have h' : (step s).wp (fun _ => False) (fun _ => False)
      (fun _ => False) := h
  cases hStep : step s with
  | step s' =>
    rw [hStep] at h'
    exact h'
  | done o =>
    rw [hStep] at h'
    exact h'
  | fault f =>
    rw [hStep] at h'
    exact h'

/-- `valid`-quantified interfaces are conjunctive. -/
theorem ofChoiceStep_conjunctive (Choice : Type x)
    (valid : State → Choice → Prop)
    (step : Choice → State → StepOutcome State Out Fault)
    (tag : State → Option Nat) :
    (ofChoiceStep Choice valid step tag).Conjunctive :=
  fun _ _ _ _ _ _ _ h₁ h₂ =>
    ⟨h₁.1, fun c hc => StepOutcome.wp_conj (h₁.2 c hc) (h₂.2 c hc)⟩

/-- `valid`-quantified interfaces are strict: an admissible choice exists and
its step result satisfies one of the three predicates. -/
theorem ofChoiceStep_strict (Choice : Type x)
    (valid : State → Choice → Prop)
    (step : Choice → State → StepOutcome State Out Fault)
    (tag : State → Option Nat) :
    (ofChoiceStep Choice valid step tag).Strict := by
  intro s h
  let ⟨c₀, hc₀⟩ := h.1
  have h' : (step c₀ s).wp (fun _ => False) (fun _ => False)
      (fun _ => False) := h.2 c₀ hc₀
  cases hStep : step c₀ s with
  | step s' =>
    rw [hStep] at h'
    exact h'
  | done o =>
    rw [hStep] at h'
    exact h'
  | fault f =>
    rw [hStep] at h'
    exact h'

/-- A `valid`-quantified interface whose admissible choice is unique at every
state is fuel-continuous. -/
theorem ofChoiceStep_fuelContinuous_of_unique (Choice : Type x)
    (valid : State → Choice → Prop)
    (step : Choice → State → StepOutcome State Out Fault)
    (tag : State → Option Nat)
    (hUniq : ∀ s c₁ c₂, valid s c₁ → valid s c₂ → c₁ = c₂) :
    (ofChoiceStep Choice valid step tag).FuelContinuous := by
  intro s P Q R _ h
  let ⟨c₀, hc₀⟩ := h.1
  let ⟨n, hn⟩ := StepOutcome.wp_exists_nat (h.2 c₀ hc₀)
  exact ⟨n, stepWp_of_detChoice hc₀ (fun c hc => hUniq s c c₀ hc hc₀) hn⟩

end ConstructorLaws

end MirWpOps

/-! ## Part II: Fuel-Free Checkpoint Weakest Precondition (`wpUntil`) -/

/-- Fuel-free weakest precondition up to a checkpoint.

`wpUntil stop onDone onFault s` holds when every execution from `s` reaches a
state satisfying `stop` after finitely many steps, unless it first terminates
with an outcome satisfying `onDone` or first faults with an error satisfying
`onFault`. It is the least predicate closed under `here` and `step`, so there
is no step budget to compute or to align between proofs.

The `step` constructor takes an intermediate predicate `mid`. The direct
recursive form `ops.stepWp s (wpUntil stop onDone onFault) onDone onFault` is
not strictly positive, because `stepWp` is an abstract field of the interface,
and the kernel rejects it. Quantifying over `mid` gives the same predicate:
`wpUntil_step` and `wpUntil_unfold_iff` recover the direct form from
`stepWp_mono`. -/
inductive wpUntil {State : Type u} {Out : Type v} {Fault : Type w}
    [ops : MirWpOps State Out Fault]
    (stop : State → Prop) (onDone : Out → Prop)
    (onFault : Fault → Prop) : State → Prop where
  /-- The current state already satisfies the checkpoint. -/
  | here {s : State} (h : stop s) : wpUntil stop onDone onFault s
  /-- One step leads into `mid`, and every `mid` state reaches the
  checkpoint. -/
  | step {s : State} (mid : State → Prop)
      (hStep : ops.stepWp s mid onDone onFault)
      (hMid : ∀ s', mid s' → wpUntil stop onDone onFault s') :
      wpUntil stop onDone onFault s

section Checkpoint

variable {State : Type u} {Out : Type v} {Fault : Type w}
  [ops : MirWpOps State Out Fault]

/-- A state that satisfies `stop` satisfies `wpUntil`. -/
theorem wpUntil_here {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} (h : stop s) :
    wpUntil stop onDone onFault s :=
  .here h

/-- Single-step introduction rule for `wpUntil` in its direct recursive
form. -/
theorem wpUntil_step {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State}
    (h : ops.stepWp s (wpUntil stop onDone onFault) onDone onFault) :
    wpUntil stop onDone onFault s :=
  .step (wpUntil stop onDone onFault) h (fun _ h' => h')

/-- Unfold `wpUntil` by one step: either the current state satisfies `stop`,
or one step leads into states that satisfy `wpUntil`. -/
theorem wpUntil_unfold_iff {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} :
    wpUntil stop onDone onFault s ↔
      (stop s ∨
        ops.stepWp s (wpUntil stop onDone onFault) onDone onFault) := by
  constructor
  · intro h
    cases h with
    | here hs => exact Or.inl hs
    | step mid hStep hMid =>
      exact Or.inr
        (ops.stepWp_mono hMid (fun _ hq => hq) (fun _ hr => hr) hStep)
  · intro h
    cases h with
    | inl hs => exact .here hs
    | inr hr => exact wpUntil_step hr

/-- Rule of consequence for `wpUntil`: weaken the checkpoint, the terminal
predicate and the set of accepted faults. -/
theorem wpUntil_mono {stop₁ stop₂ : State → Prop}
    {onDone₁ onDone₂ : Out → Prop}
    {onFault₁ onFault₂ : Fault → Prop}
    (hStop : ∀ s, stop₁ s → stop₂ s)
    (hDone : ∀ o, onDone₁ o → onDone₂ o)
    (hFault : ∀ f, onFault₁ f → onFault₂ f)
    {s : State} (h : wpUntil stop₁ onDone₁ onFault₁ s) :
    wpUntil stop₂ onDone₂ onFault₂ s := by
  induction h with
  | here hs => exact .here (hStop _ hs)
  | step mid hStep _ ih =>
    exact .step mid
      (ops.stepWp_mono (fun _ hm => hm) hDone hFault hStep) ih

/-- Weaken only the checkpoint of `wpUntil`. -/
theorem wpUntil_mono_stop {stop₁ stop₂ : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hStop : ∀ s, stop₁ s → stop₂ s)
    {s : State} (h : wpUntil stop₁ onDone onFault s) :
    wpUntil stop₂ onDone onFault s :=
  wpUntil_mono hStop (fun _ hq => hq) (fun _ hr => hr) h

/-- Sequential composition of checkpoints: if `s` reaches `mid` and every
`mid` state reaches `stop`, then `s` reaches `stop`. -/
theorem wpUntil_bind {mid stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State}
    (h : wpUntil mid onDone onFault s)
    (hK : ∀ s', mid s' → wpUntil stop onDone onFault s') :
    wpUntil stop onDone onFault s := by
  induction h with
  | here hs => exact hK _ hs
  | step P hStep _ ih => exact .step P hStep ih

/-- Checkpoints are idempotent: reaching states that reach `stop` is the same
as reaching `stop`. -/
theorem wpUntil_idem_iff {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} :
    wpUntil (wpUntil stop onDone onFault) onDone onFault s ↔
      wpUntil stop onDone onFault s :=
  ⟨fun h => wpUntil_bind h (fun _ h' => h'), fun h => .here h⟩

/-- Induction principle for `wpUntil` in least-fixed-point form: a predicate
that contains every `stop` state and is closed under one backward step
contains every state that satisfies `wpUntil stop`. It hides the intermediate
predicate of the `step` constructor, so it is the eliminator to use when a
checkpoint proof is transported into another notion of convergence. -/
theorem wpUntil_induction {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {C : State → Prop}
    (hStop : ∀ s, stop s → C s)
    (hStep : ∀ s, ops.stepWp s C onDone onFault → C s)
    {s : State} (h : wpUntil stop onDone onFault s) : C s := by
  induction h with
  | here hs => exact hStop _ hs
  | step mid hMidStep _ ih =>
    exact hStep _
      (ops.stepWp_mono ih (fun _ hq => hq) (fun _ hr => hr) hMidStep)

/-- `wpUntil stop` is exactly the least predicate that contains `stop` and is
closed under one backward step. The `step` constructor quantifies over an
intermediate predicate only to stay strictly positive; this characterization
shows that the result is the least fixed point of the direct recursive form
`stop s ∨ stepWp s (wpUntil stop ..) ..`. -/
theorem wpUntil_iff_forall_closed {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State} :
    wpUntil stop onDone onFault s ↔
      ∀ C : State → Prop, (∀ s', stop s' → C s') →
        (∀ s', ops.stepWp s' C onDone onFault → C s') → C s :=
  ⟨fun h _ hStop hStep => wpUntil_induction hStop hStep h,
   fun h => h (wpUntil stop onDone onFault) (fun _ hs => .here hs)
     (fun _ hs => wpUntil_step hs)⟩

/-- If no state satisfies `stop`, the execution must end through `onDone` or
`onFault`, so a checkpoint proof for `stop` is a checkpoint proof for every
other checkpoint. -/
theorem wpUntil_of_stop_empty {stop stop' : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State}
    (hEmpty : ∀ s', ¬ stop s') (h : wpUntil stop onDone onFault s) :
    wpUntil stop' onDone onFault s :=
  wpUntil_mono_stop (fun s' hs => False.elim (hEmpty s' hs)) h

/-- Constructive conjunction rule for `wpUntil` at a common checkpoint over a
conjunctive interface (`0` axioms). -/
theorem wpUntil_conj (hConj : ops.Conjunctive)
    {stop : State → Prop}
    {onDone₁ onDone₂ : Out → Prop}
    {onFault₁ onFault₂ : Fault → Prop} {s : State}
    (h₁ : wpUntil stop onDone₁ onFault₁ s)
    (h₂ : wpUntil stop onDone₂ onFault₂ s) :
    wpUntil stop (fun o => onDone₁ o ∧ onDone₂ o)
      (fun f => onFault₁ f ∧ onFault₂ f) s := by
  induction h₁ with
  | here hs => exact .here hs
  | step mid hStep _ ih =>
    cases wpUntil_unfold_iff.mp h₂ with
    | inl hs => exact .here hs
    | inr hStep₂ =>
      have hBoth := hConj _ _ _ _ _ _ _ hStep hStep₂
      exact .step (fun s' => mid s' ∧ wpUntil stop onDone₂ onFault₂ s') hBoth
        (fun s' hs' => ih s' hs'.1 hs'.2)

/-- Checkpoint weakest precondition that forbids every fault. -/
abbrev wpUntilOk (stop : State → Prop) (onDone : Out → Prop)
    (s : State) : Prop :=
  wpUntil stop onDone (fun _ => False) s

/-- Checkpoint weakest precondition that forbids both early termination and
faults: every execution from `s` reaches a state satisfying `stop`. -/
abbrev wpReach (stop : State → Prop) (s : State) : Prop :=
  wpUntil (ops := ops) stop (fun _ => False) (fun _ => False) s

/-- Fuel-free weakest precondition of a whole execution: every execution from
`s` terminates with an outcome satisfying `onDone` or faults with an error
satisfying `onFault`. It is `wpUntil` with an unreachable checkpoint. -/
def wpOutcome (onDone : Out → Prop) (onFault : Fault → Prop)
    (s : State) : Prop :=
  wpUntil (fun _ => False) onDone onFault s

/-- Fuel-free weakest precondition of a whole execution that forbids every
fault. -/
abbrev wpStateOk (onDone : Out → Prop) (s : State) : Prop :=
  wpOutcome onDone (fun _ => False) s

/-- `wpOutcome` is `wpUntil` with a checkpoint that no state satisfies. -/
theorem wpOutcome_iff_wpUntil_false {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} :
    wpOutcome onDone onFault s ↔
      wpUntil (fun _ => False) onDone onFault s :=
  Iff.rfl

/-- `wpOutcome` is `wpUntil` for any checkpoint that no state satisfies. -/
theorem wpOutcome_iff_wpUntil_of_stop_empty {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State}
    (hEmpty : ∀ s', ¬ stop s') :
    wpOutcome onDone onFault s ↔ wpUntil stop onDone onFault s :=
  ⟨fun h => wpUntil_mono_stop (fun _ hf => False.elim hf) h,
   fun h => wpUntil_of_stop_empty hEmpty h⟩

/-- Single-step introduction rule for `wpOutcome`. -/
theorem wpOutcome_step {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State}
    (h : ops.stepWp s (wpOutcome onDone onFault) onDone onFault) :
    wpOutcome onDone onFault s :=
  wpUntil_step h

/-- Unfold `wpOutcome` by one step. -/
theorem wpOutcome_unfold_iff {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} :
    wpOutcome onDone onFault s ↔
      ops.stepWp s (wpOutcome onDone onFault) onDone onFault := by
  constructor
  · intro h
    cases wpUntil_unfold_iff.mp h with
    | inl hf => exact False.elim hf
    | inr hr => exact hr
  · intro h
    exact wpOutcome_step h

/-- Induction principle for `wpOutcome`: a predicate closed under one backward
step contains every state whose executions all terminate as required. -/
theorem wpOutcome_induction {onDone : Out → Prop} {onFault : Fault → Prop}
    {C : State → Prop}
    (hStep : ∀ s, ops.stepWp s C onDone onFault → C s)
    {s : State} (h : wpOutcome onDone onFault s) : C s :=
  wpUntil_induction (fun _ hf => False.elim hf) hStep h

/-- Rule of consequence for `wpOutcome`. -/
theorem wpOutcome_mono {onDone₁ onDone₂ : Out → Prop}
    {onFault₁ onFault₂ : Fault → Prop}
    (hDone : ∀ o, onDone₁ o → onDone₂ o)
    (hFault : ∀ f, onFault₁ f → onFault₂ f)
    {s : State} (h : wpOutcome onDone₁ onFault₁ s) :
    wpOutcome onDone₂ onFault₂ s :=
  wpUntil_mono (fun _ hf => hf) hDone hFault h

/-- Hand a checkpoint proof over to `wpOutcome`: if `s` reaches `stop` and
every `stop` state terminates as required, then so does `s`. -/
theorem wpUntil_to_wpOutcome {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State}
    (h : wpUntil stop onDone onFault s)
    (hK : ∀ s', stop s' → wpOutcome onDone onFault s') :
    wpOutcome onDone onFault s :=
  wpUntil_bind h hK

/-- A terminating execution satisfies every checkpoint proof: `wpOutcome`
implies `wpUntil` for any `stop`. -/
theorem wpUntil_of_wpOutcome {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State}
    (h : wpOutcome onDone onFault s) : wpUntil stop onDone onFault s :=
  wpUntil_mono_stop (fun _ hf => False.elim hf) h

/-- Hand a fault-free checkpoint proof over to `wpStateOk`. -/
theorem wpUntilOk_to_wpStateOk {stop : State → Prop}
    {onDone : Out → Prop} {s : State}
    (h : wpUntilOk stop onDone s)
    (hK : ∀ s', stop s' → wpStateOk onDone s') :
    wpStateOk onDone s :=
  wpUntil_to_wpOutcome h hK

/-- A pure reachability proof composes with any continuation: `wpReach` never
terminates or faults before `mid`, so it places no demand on `onDone` and
`onFault`. -/
theorem wpReach_bind {mid stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State}
    (h : wpReach mid s)
    (hK : ∀ s', mid s' → wpUntil stop onDone onFault s') :
    wpUntil stop onDone onFault s :=
  wpUntil_bind
    (wpUntil_mono (fun _ hs => hs) (fun _ hf => False.elim hf)
      (fun _ hf => False.elim hf) h)
    hK

/-- Hand a pure reachability proof over to `wpOutcome`. -/
theorem wpReach_to_wpOutcome {mid : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State}
    (h : wpReach mid s)
    (hK : ∀ s', mid s' → wpOutcome onDone onFault s') :
    wpOutcome onDone onFault s :=
  wpReach_bind h hK

/-- Pair a checkpoint proof with a whole-execution proof over a conjunctive
interface: the checkpoint carries the whole-execution obligation forward. -/
theorem wpUntil_conj_wpOutcome (hConj : ops.Conjunctive)
    {stop : State → Prop}
    {onDone₁ onDone₂ : Out → Prop}
    {onFault₁ onFault₂ : Fault → Prop} {s : State}
    (h₁ : wpUntil stop onDone₁ onFault₁ s)
    (h₂ : wpOutcome onDone₂ onFault₂ s) :
    wpUntil (fun s' => stop s' ∧ wpOutcome onDone₂ onFault₂ s')
      (fun o => onDone₁ o ∧ onDone₂ o)
      (fun f => onFault₁ f ∧ onFault₂ f) s := by
  induction h₁ with
  | here hs => exact .here ⟨hs, h₂⟩
  | step mid hStep _ ih =>
    have hBoth := hConj _ _ _ _ _ _ _ hStep (wpOutcome_unfold_iff.mp h₂)
    exact .step (fun s' => mid s' ∧ wpOutcome onDone₂ onFault₂ s') hBoth
      (fun s' hs' => ih s' hs'.1 hs'.2)

/-- Conjunction rule for `wpOutcome` over a conjunctive interface: two proofs
about the same execution combine without re-proving termination. -/
theorem wpOutcome_conj (hConj : ops.Conjunctive)
    {onDone₁ onDone₂ : Out → Prop}
    {onFault₁ onFault₂ : Fault → Prop} {s : State}
    (h₁ : wpOutcome onDone₁ onFault₁ s)
    (h₂ : wpOutcome onDone₂ onFault₂ s) :
    wpOutcome (fun o => onDone₁ o ∧ onDone₂ o)
      (fun f => onFault₁ f ∧ onFault₂ f) s :=
  wpUntil_conj hConj h₁ h₂

/-- Excluded miracle for `wpOutcome` over a strict interface: no execution
satisfies the empty postcondition. -/
theorem wpOutcome_not_false (hStrict : ops.Strict) {s : State} :
    ¬ wpOutcome (ops := ops) (fun _ => False) (fun _ => False) s := by
  intro h
  induction h with
  | here hf => exact hf
  | step mid hStep _ ih =>
    exact hStrict _
      (ops.stepWp_mono (fun s' hm => ih s' hm) (fun _ hq => hq)
        (fun _ hr => hr) hStep)

/-- Transfer a checkpoint proof along a morphism of step interfaces across
arbitrary independent state, outcome and fault universes. `f` maps states, `g`
outcomes and `e` faults of `ops₁` to those of `ops₂`, and every step of `ops₁`
is matched by a step of `ops₂` at the image state. -/
theorem wpUntil_map {S₁ : Type u} {Out₁ : Type v} {Fault₁ : Type w}
    {S₂ : Type x} {Out₂ : Type y} {Fault₂ : Type z}
    [ops₁ : MirWpOps S₁ Out₁ Fault₁] [ops₂ : MirWpOps S₂ Out₂ Fault₂]
    (f : S₁ → S₂) (g : Out₁ → Out₂) (e : Fault₁ → Fault₂)
    (hStep : ∀ (s : S₁) (P : S₂ → Prop) (Q : Out₂ → Prop)
      (R : Fault₂ → Prop),
      ops₁.stepWp s (fun s' => P (f s')) (fun o => Q (g o))
        (fun k => R (e k)) →
      ops₂.stepWp (f s) P Q R)
    {stop : S₂ → Prop} {onDone : Out₂ → Prop}
    {onFault : Fault₂ → Prop} {s : S₁}
    (h : wpUntil (fun s' => stop (f s')) (fun o => onDone (g o))
      (fun k => onFault (e k)) s) :
    wpUntil stop onDone onFault (f s) := by
  induction h with
  | here hs => exact .here hs
  | step mid hMidStep _ ih =>
    refine wpUntil_step (hStep _ _ _ _ ?_)
    exact ops₁.stepWp_mono ih (fun _ hq => hq) (fun _ hr => hr) hMidStep

/-- Transfer a whole-execution proof along a morphism of step interfaces. -/
theorem wpOutcome_map {S₁ : Type u} {Out₁ : Type v} {Fault₁ : Type w}
    {S₂ : Type x} {Out₂ : Type y} {Fault₂ : Type z}
    [ops₁ : MirWpOps S₁ Out₁ Fault₁] [ops₂ : MirWpOps S₂ Out₂ Fault₂]
    (f : S₁ → S₂) (g : Out₁ → Out₂) (e : Fault₁ → Fault₂)
    (hStep : ∀ (s : S₁) (P : S₂ → Prop) (Q : Out₂ → Prop)
      (R : Fault₂ → Prop),
      ops₁.stepWp s (fun s' => P (f s')) (fun o => Q (g o))
        (fun k => R (e k)) →
      ops₂.stepWp (f s) P Q R)
    {onDone : Out₂ → Prop} {onFault : Fault₂ → Prop} {s : S₁}
    (h : wpOutcome (fun o => onDone (g o)) (fun k => onFault (e k)) s) :
    wpOutcome onDone onFault (f s) :=
  wpUntil_map f g e hStep h

/-! ### Strict Checkpoints (`wpStepUntil`) -/

/-- Strict checkpoint weakest precondition: take one step, then reach `stop`.
Unlike `wpUntil`, it cannot be discharged at a state that already satisfies
`stop`, which is what a loop header that is its own cutpoint needs. -/
def wpStepUntil (stop : State → Prop) (onDone : Out → Prop)
    (onFault : Fault → Prop) (s : State) : Prop :=
  ops.stepWp s (wpUntil stop onDone onFault) onDone onFault

/-- A strict checkpoint proof is a checkpoint proof. -/
theorem wpUntil_of_wpStepUntil {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State}
    (h : wpStepUntil stop onDone onFault s) :
    wpUntil stop onDone onFault s :=
  wpUntil_step h

/-- A checkpoint proof either holds at once or is a strict one. -/
theorem wpUntil_iff_stop_or_wpStepUntil {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State} :
    wpUntil stop onDone onFault s ↔
      (stop s ∨ wpStepUntil stop onDone onFault s) :=
  wpUntil_unfold_iff

/-- A checkpoint proof from a state outside `stop` makes at least one step. -/
theorem wpStepUntil_of_wpUntil_of_not_stop {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State}
    (h : wpUntil stop onDone onFault s) (hNot : ¬ stop s) :
    wpStepUntil stop onDone onFault s := by
  cases wpUntil_unfold_iff.mp h with
  | inl hs => exact False.elim (hNot hs)
  | inr hr => exact hr

/-- Rule of consequence for `wpStepUntil`. -/
theorem wpStepUntil_mono {stop₁ stop₂ : State → Prop}
    {onDone₁ onDone₂ : Out → Prop}
    {onFault₁ onFault₂ : Fault → Prop}
    (hStop : ∀ s, stop₁ s → stop₂ s)
    (hDone : ∀ o, onDone₁ o → onDone₂ o)
    (hFault : ∀ f, onFault₁ f → onFault₂ f)
    {s : State} (h : wpStepUntil stop₁ onDone₁ onFault₁ s) :
    wpStepUntil stop₂ onDone₂ onFault₂ s :=
  ops.stepWp_mono (fun _ h' => wpUntil_mono hStop hDone hFault h')
    hDone hFault h

/-- Sequential composition of a strict checkpoint with a checkpoint. -/
theorem wpStepUntil_bind {mid stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State}
    (h : wpStepUntil mid onDone onFault s)
    (hK : ∀ s', mid s' → wpUntil stop onDone onFault s') :
    wpStepUntil stop onDone onFault s :=
  ops.stepWp_mono (fun _ h' => wpUntil_bind h' hK) (fun _ hq => hq)
    (fun _ hr => hr) h

/-- Sequential composition of a checkpoint with a strict checkpoint: the
composite makes at least the step of the second segment. -/
theorem wpUntil_bind_wpStepUntil {mid stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State}
    (h : wpUntil mid onDone onFault s)
    (hK : ∀ s', mid s' → wpStepUntil stop onDone onFault s') :
    wpStepUntil stop onDone onFault s := by
  cases wpUntil_unfold_iff.mp h with
  | inl hs => exact hK s hs
  | inr hr =>
    exact ops.stepWp_mono
      (fun _ h' => wpUntil_bind h' (fun s' hm => wpUntil_step (hK s' hm)))
      (fun _ hq => hq) (fun _ hr' => hr') hr

end Checkpoint

/-! ## Part III: Fuel-Bounded Counterparts (`wpUntilFuel`, `wpOutcomeFuel`) -/

section Fuel

variable {State : Type u} {Out : Type v} {Fault : Type w}
  [ops : MirWpOps State Out Fault]

/-- Fuel-bounded weakest precondition up to a checkpoint: as `wpUntil`, but
the checkpoint must be reached within `fuel` steps. Running out of fuel is
accepted only in a state that satisfies `stop`. Defined by `@Nat.rec` into
`Prop`, so it unfolds by `rfl` at every literal budget. -/
def wpUntilFuel (stop : State → Prop) (onDone : Out → Prop)
    (onFault : Fault → Prop) (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun st => stop st)
    (fun _ ih st => stop st ∨ ops.stepWp st ih onDone onFault)
    fuel s

/-- Fuel-bounded weakest precondition of a whole execution: the execution
must terminate or fault as required within `fuel` steps, and running out of
fuel is never accepted. -/
def wpOutcomeFuel (onDone : Out → Prop) (onFault : Fault → Prop)
    (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => False)
    (fun _ ih st => ops.stepWp st ih onDone onFault)
    fuel s

/-- Unfold `wpUntilFuel` at fuel `0`: the current state must satisfy
`stop`. -/
theorem wpUntilFuel_zero_iff {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State} :
    wpUntilFuel stop onDone onFault 0 s ↔ stop s :=
  Iff.rfl

/-- Unfold `wpUntilFuel` at fuel `fuel + 1`. -/
theorem wpUntilFuel_succ_iff {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {fuel : Nat}
    {s : State} :
    wpUntilFuel stop onDone onFault (fuel + 1) s ↔
      (stop s ∨
        ops.stepWp s (wpUntilFuel stop onDone onFault fuel)
          onDone onFault) :=
  Iff.rfl

/-- `wpOutcomeFuel` never holds at fuel `0`. -/
theorem wpOutcomeFuel_zero_elim {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} :
    ¬ wpOutcomeFuel onDone onFault 0 s :=
  fun h => h

/-- Unfold `wpOutcomeFuel` at fuel `fuel + 1`. -/
theorem wpOutcomeFuel_succ_iff {onDone : Out → Prop}
    {onFault : Fault → Prop} {fuel : Nat} {s : State} :
    wpOutcomeFuel onDone onFault (fuel + 1) s ↔
      ops.stepWp s (wpOutcomeFuel onDone onFault fuel) onDone onFault :=
  Iff.rfl

/-- A state that satisfies `stop` satisfies `wpUntilFuel` at every fuel. -/
theorem wpUntilFuel_here {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {fuel : Nat} {s : State} (h : stop s) :
    wpUntilFuel stop onDone onFault fuel s := by
  cases fuel with
  | zero => exact wpUntilFuel_zero_iff.mpr h
  | succ fuel => exact wpUntilFuel_succ_iff.mpr (Or.inl h)

/-- Single-step introduction rule for `wpUntilFuel`. -/
theorem wpUntilFuel_step {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {fuel : Nat} {s : State}
    (h : ops.stepWp s (wpUntilFuel stop onDone onFault fuel)
      onDone onFault) :
    wpUntilFuel stop onDone onFault (fuel + 1) s :=
  wpUntilFuel_succ_iff.mpr (Or.inr h)

/-- Fuel monotonicity for `wpUntilFuel`: a checkpoint reached within `f₁`
steps is reached within any larger budget `f₂`. At fuel `0` the checkpoint
holds, which every larger budget accepts. -/
theorem wpUntilFuel_mono {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {f₁ f₂ : Nat} {s : State}
    (hLe : f₁ ≤ f₂) (h : wpUntilFuel stop onDone onFault f₁ s) :
    wpUntilFuel stop onDone onFault f₂ s := by
  induction f₁ generalizing f₂ s with
  | zero => exact wpUntilFuel_here (wpUntilFuel_zero_iff.mp h)
  | succ f₁ ih =>
    cases f₂ with
    | zero => exact False.elim (Nat.not_succ_le_zero f₁ hLe)
    | succ f₂ =>
      cases wpUntilFuel_succ_iff.mp h with
      | inl hs => exact wpUntilFuel_here hs
      | inr hr =>
        exact wpUntilFuel_step
          (ops.stepWp_mono
            (fun _ h' => ih (Nat.le_of_succ_le_succ hLe) h')
            (fun _ hq => hq) (fun _ hr' => hr') hr)

/-- Fuel monotonicity for `wpOutcomeFuel`. At fuel `0` the premise is
`False`, so there is no base case to weaken. -/
theorem wpOutcomeFuel_mono {onDone : Out → Prop}
    {onFault : Fault → Prop} {f₁ f₂ : Nat} {s : State}
    (hLe : f₁ ≤ f₂) (h : wpOutcomeFuel onDone onFault f₁ s) :
    wpOutcomeFuel onDone onFault f₂ s := by
  induction f₁ generalizing f₂ s with
  | zero => exact False.elim (wpOutcomeFuel_zero_elim h)
  | succ f₁ ih =>
    cases f₂ with
    | zero => exact False.elim (Nat.not_succ_le_zero f₁ hLe)
    | succ f₂ =>
      exact wpOutcomeFuel_succ_iff.mpr
        (ops.stepWp_mono
          (fun _ h' => ih (Nat.le_of_succ_le_succ hLe) h')
          (fun _ hq => hq) (fun _ hr => hr) (wpOutcomeFuel_succ_iff.mp h))

/-- Rule of consequence for `wpUntilFuel` at a fixed budget. -/
theorem wpUntilFuel_weaken {stop₁ stop₂ : State → Prop}
    {onDone₁ onDone₂ : Out → Prop}
    {onFault₁ onFault₂ : Fault → Prop}
    (hStop : ∀ s, stop₁ s → stop₂ s)
    (hDone : ∀ o, onDone₁ o → onDone₂ o)
    (hFault : ∀ f, onFault₁ f → onFault₂ f)
    {fuel : Nat} {s : State}
    (h : wpUntilFuel stop₁ onDone₁ onFault₁ fuel s) :
    wpUntilFuel stop₂ onDone₂ onFault₂ fuel s := by
  induction fuel generalizing s with
  | zero => exact wpUntilFuel_zero_iff.mpr (hStop s (wpUntilFuel_zero_iff.mp h))
  | succ fuel ih =>
    cases wpUntilFuel_succ_iff.mp h with
    | inl hs => exact wpUntilFuel_here (hStop s hs)
    | inr hr =>
      exact wpUntilFuel_step
        (ops.stepWp_mono (fun _ h' => ih h') hDone hFault hr)

/-- Rule of consequence for `wpOutcomeFuel` at a fixed budget. -/
theorem wpOutcomeFuel_weaken {onDone₁ onDone₂ : Out → Prop}
    {onFault₁ onFault₂ : Fault → Prop}
    (hDone : ∀ o, onDone₁ o → onDone₂ o)
    (hFault : ∀ f, onFault₁ f → onFault₂ f)
    {fuel : Nat} {s : State}
    (h : wpOutcomeFuel onDone₁ onFault₁ fuel s) :
    wpOutcomeFuel onDone₂ onFault₂ fuel s := by
  induction fuel generalizing s with
  | zero => exact False.elim (wpOutcomeFuel_zero_elim h)
  | succ fuel ih =>
    exact wpOutcomeFuel_succ_iff.mpr
      (ops.stepWp_mono (fun _ h' => ih h') hDone hFault
        (wpOutcomeFuel_succ_iff.mp h))

/-- `wpOutcomeFuel` is `wpUntilFuel` with a checkpoint that no state
satisfies. -/
theorem wpOutcomeFuel_iff_wpUntilFuel_false {onDone : Out → Prop}
    {onFault : Fault → Prop} {fuel : Nat} {s : State} :
    wpOutcomeFuel onDone onFault fuel s ↔
      wpUntilFuel (fun _ => False) onDone onFault fuel s := by
  induction fuel generalizing s with
  | zero => exact Iff.rfl
  | succ fuel ih =>
    constructor
    · intro h
      exact wpUntilFuel_step
        (ops.stepWp_mono (fun _ h' => ih.mp h') (fun _ hq => hq)
          (fun _ hr => hr) (wpOutcomeFuel_succ_iff.mp h))
    · intro h
      cases wpUntilFuel_succ_iff.mp h with
      | inl hf => exact False.elim hf
      | inr hr =>
        exact wpOutcomeFuel_succ_iff.mpr
          (ops.stepWp_mono (fun _ h' => ih.mpr h') (fun _ hq => hq)
            (fun _ hr' => hr') hr)

/-- Every bounded checkpoint derivation is a fuel-free one. -/
theorem wpUntil_of_wpUntilFuel {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {fuel : Nat}
    {s : State} (h : wpUntilFuel stop onDone onFault fuel s) :
    wpUntil stop onDone onFault s := by
  induction fuel generalizing s with
  | zero => exact .here (wpUntilFuel_zero_iff.mp h)
  | succ fuel ih =>
    cases wpUntilFuel_succ_iff.mp h with
    | inl hs => exact .here hs
    | inr hr =>
      exact .step (wpUntilFuel stop onDone onFault fuel) hr
        (fun _ h' => ih h')

/-- Every bounded whole-execution derivation is a fuel-free one. -/
theorem wpOutcome_of_wpOutcomeFuel {onDone : Out → Prop}
    {onFault : Fault → Prop} {fuel : Nat} {s : State}
    (h : wpOutcomeFuel onDone onFault fuel s) :
    wpOutcome onDone onFault s :=
  wpUntil_of_wpUntilFuel (wpOutcomeFuel_iff_wpUntilFuel_false.mp h)

/-- Over a fuel-continuous interface, a fuel-free checkpoint proof has a
finite step budget, so `wpUntil` is exactly `∃ fuel, wpUntilFuel`. -/
theorem wpUntil_iff_exists_fuel (hCont : ops.FuelContinuous)
    {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} :
    wpUntil stop onDone onFault s ↔
      ∃ fuel, wpUntilFuel stop onDone onFault fuel s := by
  constructor
  · intro h
    induction h with
    | here hs => exact ⟨0, wpUntilFuel_zero_iff.mpr hs⟩
    | step mid hStep _ ih =>
      have hUnion : ops.stepWp _
          (fun s' => ∃ n, wpUntilFuel stop onDone onFault n s')
          onDone onFault :=
        ops.stepWp_mono ih (fun _ hq => hq) (fun _ hr => hr) hStep
      let ⟨n, hn⟩ := hCont _
        (fun n s' => wpUntilFuel stop onDone onFault n s') _ _
        (fun n _ h' => wpUntilFuel_mono (Nat.le_succ n) h') hUnion
      exact ⟨n + 1, wpUntilFuel_step hn⟩
  · intro h
    let ⟨_, hFuel⟩ := h
    exact wpUntil_of_wpUntilFuel hFuel

/-- Over a fuel-continuous interface, `wpOutcome` is exactly
`∃ fuel, wpOutcomeFuel`. -/
theorem wpOutcome_iff_exists_fuel (hCont : ops.FuelContinuous)
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State} :
    wpOutcome onDone onFault s ↔
      ∃ fuel, wpOutcomeFuel onDone onFault fuel s := by
  constructor
  · intro h
    let ⟨fuel, hFuel⟩ := (wpUntil_iff_exists_fuel hCont).mp h
    exact ⟨fuel, wpOutcomeFuel_iff_wpUntilFuel_false.mpr hFuel⟩
  · intro h
    let ⟨_, hFuel⟩ := h
    exact wpOutcome_of_wpOutcomeFuel hFuel

/-- Sequential composition of bounded checkpoints: budgets add. -/
theorem wpUntilFuel_bind {mid stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {f₁ f₂ : Nat}
    {s : State} (h : wpUntilFuel mid onDone onFault f₁ s)
    (hK : ∀ s', mid s' → wpUntilFuel stop onDone onFault f₂ s') :
    wpUntilFuel stop onDone onFault (f₁ + f₂) s := by
  induction f₁ generalizing s with
  | zero =>
    exact wpUntilFuel_mono (Nat.le_add_left f₂ 0)
      (hK s (wpUntilFuel_zero_iff.mp h))
  | succ f₁ ih =>
    cases wpUntilFuel_succ_iff.mp h with
    | inl hm =>
      exact wpUntilFuel_mono (Nat.le_add_left f₂ (f₁ + 1)) (hK s hm)
    | inr hr =>
      rw [Nat.succ_add]
      exact wpUntilFuel_step
        (ops.stepWp_mono (fun _ h' => ih h') (fun _ hq => hq)
          (fun _ hr' => hr') hr)

/-- Hand a bounded checkpoint proof over to `wpOutcomeFuel`: budgets add. -/
theorem wpUntilFuel_to_wpOutcomeFuel {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {f₁ f₂ : Nat}
    {s : State} (h : wpUntilFuel stop onDone onFault f₁ s)
    (hK : ∀ s', stop s' → wpOutcomeFuel onDone onFault f₂ s') :
    wpOutcomeFuel onDone onFault (f₁ + f₂) s :=
  wpOutcomeFuel_iff_wpUntilFuel_false.mpr
    (wpUntilFuel_bind h
      (fun s' hs => wpOutcomeFuel_iff_wpUntilFuel_false.mp (hK s' hs)))

/-- Exact fixed-budget countdown loop rule (`n * stepFuel`, matching `#4059`):
if `Inv 0` implies `exit` and one iteration from `Inv (n + 1)` reaches
`Inv n ∨ exit` within `stepFuel` steps, then `Inv n` reaches `exit` within
`n * stepFuel` steps. -/
theorem wpLoop_countdown_fuel {Inv : Nat → State → Prop}
    {exit : State → Prop} {onDone : Out → Prop} {onFault : Fault → Prop}
    {stepFuel : Nat}
    (hBase : ∀ s, Inv 0 s → exit s)
    (hStep : ∀ n s, Inv (n + 1) s →
      wpUntilFuel (fun s' => Inv n s' ∨ exit s') onDone onFault stepFuel s)
    (n : Nat) (s : State) (hInv : Inv n s) :
    wpUntilFuel exit onDone onFault (n * stepFuel) s := by
  induction n generalizing s with
  | zero =>
    rw [Nat.zero_mul]
    exact wpUntilFuel_here (hBase s hInv)
  | succ n ih =>
    rw [Nat.succ_mul, Nat.add_comm]
    refine wpUntilFuel_bind (hStep n s hInv) ?_
    intro s' hMid
    cases hMid with
    | inl hCont => exact ih s' hCont
    | inr hExit => exact wpUntilFuel_here hExit

end Fuel

/-! ### Deterministic Interfaces (`ofDetStep`) -/

section Deterministic

variable {State : Type u} {Out : Type v} {Fault : Type w}

/-- Deterministic counterpart of `wpUntilFuel`, stated over the step function
itself. On a concrete state each step reduces by `rfl`. -/
def execUntilFuel (step : State → StepOutcome State Out Fault)
    (stop : State → Prop) (onDone : Out → Prop) (onFault : Fault → Prop)
    (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun st => stop st)
    (fun _ ih st => stop st ∨ (step st).wp ih onDone onFault)
    fuel s

/-- Deterministic counterpart of `wpOutcomeFuel`, stated over the step
function itself. -/
def execOutcomeFuel (step : State → StepOutcome State Out Fault)
    (onDone : Out → Prop) (onFault : Fault → Prop)
    (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => False)
    (fun _ ih st => (step st).wp ih onDone onFault)
    fuel s

/-- `wpUntilFuel` over `ofDetStep step` is `execUntilFuel step`. -/
theorem wpUntilFuel_det_iff_execUntilFuel
    {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {fuel : Nat}
    {s : State} :
    wpUntilFuel (ops := MirWpOps.ofDetStep step tag) stop onDone onFault
      fuel s ↔
      execUntilFuel step stop onDone onFault fuel s :=
  Iff.rfl

/-- `wpOutcomeFuel` over `ofDetStep step` is `execOutcomeFuel step`. -/
theorem wpOutcomeFuel_det_iff_execOutcomeFuel
    {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {onDone : Out → Prop}
    {onFault : Fault → Prop} {fuel : Nat} {s : State} :
    wpOutcomeFuel (ops := MirWpOps.ofDetStep step tag) onDone onFault
      fuel s ↔
      execOutcomeFuel step onDone onFault fuel s :=
  Iff.rfl

/-- Exact equivalence for deterministic interfaces: a fuel-free checkpoint
proof holds exactly when some step budget suffices. -/
theorem wpUntil_det_iff_exists_fuel
    {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State} :
    wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault s ↔
      ∃ fuel, wpUntilFuel (ops := MirWpOps.ofDetStep step tag) stop
        onDone onFault fuel s :=
  wpUntil_iff_exists_fuel (ops := MirWpOps.ofDetStep step tag)
    (MirWpOps.ofDetStep_fuelContinuous step tag)

/-- Exact equivalence for deterministic interfaces: a fuel-free
whole-execution proof holds exactly when some step budget suffices. -/
theorem wpOutcome_det_iff_exists_fuel
    {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} :
    wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s ↔
      ∃ fuel, wpOutcomeFuel (ops := MirWpOps.ofDetStep step tag)
        onDone onFault fuel s :=
  wpOutcome_iff_exists_fuel (ops := MirWpOps.ofDetStep step tag)
    (MirWpOps.ofDetStep_fuelContinuous step tag)

/-- Extend `wpUntil` backwards across one deterministic step
`step s = .step s'`. -/
theorem wpUntil_det_step_eq {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s s' : State}
    (hStep : step s = .step s')
    (h : wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault
      s') :
    wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault s := by
  refine wpUntil_step (ops := MirWpOps.ofDetStep step tag) ?_
  change (step s).wp _ onDone onFault
  rw [hStep]
  exact h

/-- A deterministic step that terminates with an accepted outcome satisfies
`wpUntil`. -/
theorem wpUntil_det_done_eq {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State} {out : Out}
    (hStep : step s = .done out) (h : onDone out) :
    wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault s := by
  refine wpUntil_step (ops := MirWpOps.ofDetStep step tag) ?_
  change (step s).wp _ onDone onFault
  rw [hStep]
  exact h

/-- A deterministic step that faults with an accepted error satisfies
`wpUntil`. -/
theorem wpUntil_det_fault_eq {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State} {err : Fault}
    (hStep : step s = .fault err) (h : onFault err) :
    wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault s := by
  refine wpUntil_step (ops := MirWpOps.ofDetStep step tag) ?_
  change (step s).wp _ onDone onFault
  rw [hStep]
  exact h

/-- A deterministic step `step s = .step s'` followed by a checkpoint proof at
`s'` is a strict checkpoint proof at `s`. -/
theorem wpStepUntil_det_step_eq
    {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s s' : State}
    (hStep : step s = .step s')
    (h : wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault
      s') :
    wpStepUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault
      s := by
  change (step s).wp _ onDone onFault
  rw [hStep]
  exact h

/-- Extend `wpOutcome` backwards across one deterministic step. -/
theorem wpOutcome_det_step_eq {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s s' : State}
    (hStep : step s = .step s')
    (h : wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s') :
    wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s :=
  wpUntil_det_step_eq hStep h

/-- A deterministic step that terminates with an accepted outcome satisfies
`wpOutcome`. -/
theorem wpOutcome_det_done_eq {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} {out : Out}
    (hStep : step s = .done out) (h : onDone out) :
    wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s :=
  wpUntil_det_done_eq hStep h

/-- A deterministic step that faults with an accepted error satisfies
`wpOutcome`. -/
theorem wpOutcome_det_fault_eq {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} {err : Fault}
    (hStep : step s = .fault err) (h : onFault err) :
    wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s :=
  wpUntil_det_fault_eq hStep h

/-- Inversion for a deterministic `.step`: a checkpoint proof at a state
outside `stop` continues at the successor. -/
theorem wpUntil_det_step_inv {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s s' : State}
    (hStep : step s = .step s') (hNot : ¬ stop s)
    (h : wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault
      s) :
    wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault s' := by
  cases (wpUntil_unfold_iff (ops := MirWpOps.ofDetStep step tag)).mp h with
  | inl hs => exact False.elim (hNot hs)
  | inr hr =>
    have hr' : (step s).wp
        (wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault)
        onDone onFault := hr
    rw [hStep] at hr'
    exact hr'

/-- Inversion for a deterministic `.done`: the outcome satisfies `onDone`. -/
theorem wpOutcome_det_done_inv {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} {out : Out}
    (hStep : step s = .done out)
    (h : wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s) :
    onDone out := by
  have hr : (step s).wp
      (wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault)
      onDone onFault :=
    (wpOutcome_unfold_iff (ops := MirWpOps.ofDetStep step tag)).mp h
  rw [hStep] at hr
  exact hr

/-- Inversion for a deterministic `.fault`: the error satisfies `onFault`, so
a fault-free proof (`wpStateOk`) is impossible at a faulting state. -/
theorem wpOutcome_det_fault_inv {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} {err : Fault}
    (hStep : step s = .fault err)
    (h : wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s) :
    onFault err := by
  have hr : (step s).wp
      (wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault)
      onDone onFault :=
    (wpOutcome_unfold_iff (ops := MirWpOps.ofDetStep step tag)).mp h
  rw [hStep] at hr
  exact hr

/-- Induction principle for a deterministic checkpoint proof, by cases on the
step function: a predicate that contains every `stop` state, is closed
backwards under `.step` transitions, and contains every state whose step
terminates or faults as accepted, contains every state that satisfies
`wpUntil stop`. Instantiating `C` with an external convergence predicate
turns its single-step rules into a bridge from `wpUntil`. -/
theorem wpUntil_det_induction {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {C : State → Prop}
    (hStop : ∀ s, stop s → C s)
    (hStep : ∀ s s', step s = .step s' → C s' → C s)
    (hDone : ∀ s out, step s = .done out → onDone out → C s)
    (hFault : ∀ s err, step s = .fault err → onFault err → C s)
    {s : State}
    (h : wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault
      s) :
    C s := by
  refine wpUntil_induction (ops := MirWpOps.ofDetStep step tag) hStop ?_ h
  intro t hWp
  have hWp' : (step t).wp C onDone onFault := hWp
  cases hEv : step t with
  | step t' =>
    rw [hEv] at hWp'
    exact hStep t t' hEv hWp'
  | done out =>
    rw [hEv] at hWp'
    exact hDone t out hEv hWp'
  | fault err =>
    rw [hEv] at hWp'
    exact hFault t err hEv hWp'

/-- Induction principle for a deterministic whole-execution proof, by cases on
the step function. -/
theorem wpOutcome_det_induction {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {onDone : Out → Prop}
    {onFault : Fault → Prop} {C : State → Prop}
    (hStep : ∀ s s', step s = .step s' → C s' → C s)
    (hDone : ∀ s out, step s = .done out → onDone out → C s)
    (hFault : ∀ s err, step s = .fault err → onFault err → C s)
    {s : State}
    (h : wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s) :
    C s :=
  wpUntil_det_induction (fun _ hf => False.elim hf) hStep hDone hFault h

/-- With a single admissible choice `c₀` at every state, the
`valid`-quantified interface and the deterministic interface of `step c₀`
prove the same checkpoints. -/
theorem wpUntil_choice_iff_det {Choice : Type x}
    {valid : State → Choice → Prop}
    {step : Choice → State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {c₀ : Choice}
    (hValid : ∀ s, valid s c₀) (hUniq : ∀ s c, valid s c → c = c₀)
    {stop : State → Prop} {onDone : Out → Prop} {onFault : Fault → Prop}
    {s : State} :
    wpUntil (ops := MirWpOps.ofChoiceStep Choice valid step tag) stop
      onDone onFault s ↔
      wpUntil (ops := MirWpOps.ofDetStep (step c₀) tag) stop onDone
        onFault s := by
  constructor
  · intro h
    exact wpUntil_map
      (ops₁ := MirWpOps.ofChoiceStep Choice valid step tag)
      (ops₂ := MirWpOps.ofDetStep (step c₀) tag)
      (fun s' => s') (fun o => o) (fun k => k)
      (fun s' _ _ _ hs =>
        MirWpOps.stepWp_detChoice_elim (hValid s') hs) h
  · intro h
    exact wpUntil_map
      (ops₁ := MirWpOps.ofDetStep (step c₀) tag)
      (ops₂ := MirWpOps.ofChoiceStep Choice valid step tag)
      (fun s' => s') (fun o => o) (fun k => k)
      (fun s' _ _ _ hs =>
        MirWpOps.stepWp_of_detChoice (hValid s') (hUniq s') hs) h

end Deterministic

/-! ## Part IV: Fuel-Free Loop-Invariant Induction Combinators -/

section Loops

variable {State : Type u} {Out : Type v} {Fault : Type w}
  [ops : MirWpOps State Out Fault]

/-- General well-founded loop rule.

`Inv a` holds at the loop head with ghost value `a`, and `r` is a well-founded
relation on ghost values. From every `Inv a` state that is not yet an `exit`
state, one iteration reaches an `exit` state or an `Inv a'` state with
`r a' a`. Then every `Inv` state reaches `exit`. An iteration may also end the
execution through `onDone` (an early `return` inside the loop) or through an
accepted fault. -/
theorem wpLoop_inv {α : Sort x} {r : α → α → Prop} (hWf : WellFounded r)
    {Inv : α → State → Prop} {exit : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hStep : ∀ a s, Inv a s →
      exit s ∨
        wpUntil (fun s' => exit s' ∨ ∃ a', r a' a ∧ Inv a' s')
          onDone onFault s)
    (a₀ : α) (s₀ : State) (hInv : Inv a₀ s₀) :
    wpUntil exit onDone onFault s₀ := by
  revert s₀
  refine hWf.induction
    (C := fun a => ∀ s, Inv a s → wpUntil exit onDone onFault s) a₀ ?_
  intro a ih s hInvA
  cases hStep a s hInvA with
  | inl hExit => exact .here hExit
  | inr hIter =>
    refine wpUntil_bind hIter ?_
    intro s' hMid
    cases hMid with
    | inl hExit => exact .here hExit
    | inr hNext =>
      let ⟨a', hLt, hInv'⟩ := hNext
      exact ih a' hLt s' hInv'

/-- Ranked loop rule: `wpLoop_inv` with the well-founded relation given by a
`Nat`-valued rank on ghost values that strictly decreases every iteration. -/
theorem wpLoop_inv_rank {α : Sort x} (rank : α → Nat)
    {Inv : α → State → Prop} {exit : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hStep : ∀ a s, Inv a s →
      exit s ∨
        wpUntil (fun s' => exit s' ∨ ∃ a', rank a' < rank a ∧ Inv a' s')
          onDone onFault s)
    (a₀ : α) (s₀ : State) (hInv : Inv a₀ s₀) :
    wpUntil exit onDone onFault s₀ :=
  wpLoop_inv (r := InvImage (fun m n : Nat => m < n) rank)
    (InvImage.wf rank Nat.lt_wfRel.wf) hStep a₀ s₀ hInv

/-- Strict well-founded loop rule: every iteration makes at least one step.

The iteration premise is a strict checkpoint (`wpStepUntil`), so it cannot be
discharged by observing that the loop head already satisfies the next
invariant; a self-loop has to execute its body. The conclusion is strict as
well: the loop makes progress before it reaches `exit`. -/
theorem wpLoop_inv_strict {α : Sort x} {r : α → α → Prop}
    (hWf : WellFounded r)
    {Inv : α → State → Prop} {exit : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hStep : ∀ a s, Inv a s →
      wpStepUntil (fun s' => exit s' ∨ ∃ a', r a' a ∧ Inv a' s')
        onDone onFault s)
    (a₀ : α) (s₀ : State) (hInv : Inv a₀ s₀) :
    wpStepUntil exit onDone onFault s₀ := by
  refine wpStepUntil_bind (hStep a₀ s₀ hInv) ?_
  intro s' hMid
  cases hMid with
  | inl hExit => exact .here hExit
  | inr hNext =>
    let ⟨a', _, hInv'⟩ := hNext
    exact wpLoop_inv hWf
      (fun a s h => Or.inr (wpUntil_of_wpStepUntil (hStep a s h)))
      a' s' hInv'

/-- Strict ranked loop rule: `wpLoop_inv_strict` for a `Nat`-valued rank. -/
theorem wpLoop_inv_rank_strict {α : Sort x} (rank : α → Nat)
    {Inv : α → State → Prop} {exit : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hStep : ∀ a s, Inv a s →
      wpStepUntil (fun s' => exit s' ∨ ∃ a', rank a' < rank a ∧ Inv a' s')
        onDone onFault s)
    (a₀ : α) (s₀ : State) (hInv : Inv a₀ s₀) :
    wpStepUntil exit onDone onFault s₀ :=
  wpLoop_inv_strict (r := InvImage (fun m n : Nat => m < n) rank)
    (InvImage.wf rank Nat.lt_wfRel.wf) hStep a₀ s₀ hInv

/-- Progress for the general loop rule: under the hypotheses of `wpLoop_inv`,
an `Inv` state that is not an `exit` state makes at least one step on its way
to `exit`. -/
theorem wpLoop_inv_progress {α : Sort x} {r : α → α → Prop}
    (hWf : WellFounded r)
    {Inv : α → State → Prop} {exit : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hStep : ∀ a s, Inv a s →
      exit s ∨
        wpUntil (fun s' => exit s' ∨ ∃ a', r a' a ∧ Inv a' s')
          onDone onFault s)
    (a₀ : α) (s₀ : State) (hInv : Inv a₀ s₀) (hNotExit : ¬ exit s₀) :
    wpStepUntil exit onDone onFault s₀ :=
  wpStepUntil_of_wpUntil_of_not_stop (wpLoop_inv hWf hStep a₀ s₀ hInv)
    hNotExit

/-- Upward counting loop rule with a variable stride. `Inv i` holds at the
loop head with counter `i ≤ hi`; one iteration from `i < hi` reaches `exit` or
an `Inv j` state with `i < j ≤ hi`; and `Inv hi` implies `exit`. -/
theorem wpLoop_nat_exists {Inv : Nat → State → Prop} {exit : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {hi : Nat}
    (hDone : ∀ s, Inv hi s → exit s)
    (hStep : ∀ i s, i < hi → Inv i s →
      wpUntil (fun s' => exit s' ∨ ∃ j, i < j ∧ j ≤ hi ∧ Inv j s')
        onDone onFault s)
    (i : Nat) (hLe : i ≤ hi) (s : State) (hInv : Inv i s) :
    wpUntil exit onDone onFault s := by
  refine wpLoop_inv_rank (α := Nat) (fun k => hi - k)
    (Inv := fun k s' => k ≤ hi ∧ Inv k s') ?_ i s ⟨hLe, hInv⟩
  intro k t hk
  cases Nat.eq_or_lt_of_le hk.1 with
  | inl hEq =>
    have hInvHi : Inv hi t := by
      rw [← hEq]
      exact hk.2
    exact Or.inl (hDone t hInvHi)
  | inr hLt =>
    refine Or.inr (wpUntil_mono_stop ?_ (hStep k t hLt hk.2))
    intro t' hMid
    cases hMid with
    | inl hExit => exact Or.inl hExit
    | inr hNext =>
      let ⟨j, hkj, hjHi, hInvJ⟩ := hNext
      exact Or.inr ⟨j, Nat.sub_lt_sub_left hLt hkj, hjHi, hInvJ⟩

/-- Upward counting loop rule for a bounded counter `i .. hi`: one iteration
from `i < hi` reaches `exit` or `Inv (i + 1)`, and `Inv hi` implies `exit`.
The loop runs zero times when `i = hi`. -/
theorem wpLoop_nat {Inv : Nat → State → Prop} {exit : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {hi : Nat}
    (hDone : ∀ s, Inv hi s → exit s)
    (hStep : ∀ i s, i < hi → Inv i s →
      wpUntil (fun s' => exit s' ∨ Inv (i + 1) s') onDone onFault s)
    (i : Nat) (hLe : i ≤ hi) (s : State) (hInv : Inv i s) :
    wpUntil exit onDone onFault s := by
  refine wpLoop_nat_exists hDone ?_ i hLe s hInv
  intro k t hLt hInvK
  refine wpUntil_mono_stop ?_ (hStep k t hLt hInvK)
  intro t' hMid
  cases hMid with
  | inl hExit => exact Or.inl hExit
  | inr hNext =>
    exact Or.inr ⟨k + 1, Nat.lt_succ_self k, Nat.succ_le_of_lt hLt, hNext⟩

/-- Exact countdown loop rule. `Inv n` records that exactly `n` iterations
remain: `Inv 0` implies `exit`, and one iteration from `Inv (n + 1)` reaches
`Inv n` or `exit`. -/
theorem wpLoop_countdown {Inv : Nat → State → Prop} {exit : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hBase : ∀ s, Inv 0 s → exit s)
    (hStep : ∀ n s, Inv (n + 1) s →
      wpUntil (fun s' => Inv n s' ∨ exit s') onDone onFault s)
    (n : Nat) (s : State) (hInv : Inv n s) :
    wpUntil exit onDone onFault s := by
  induction n generalizing s with
  | zero => exact .here (hBase s hInv)
  | succ n ih =>
    refine wpUntil_bind (hStep n s hInv) ?_
    intro s' hMid
    cases hMid with
    | inl hCont => exact ih s' hCont
    | inr hExit => exact .here hExit

/-- List-traversal loop rule. `Inv xs` records the elements that remain to be
processed: `Inv []` implies `exit`, and one iteration from `Inv (y :: ys)`
reaches `Inv ys` or `exit`. -/
theorem wpLoop_list {β : Type x} {Inv : List β → State → Prop}
    {exit : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop}
    (hBase : ∀ s, Inv [] s → exit s)
    (hStep : ∀ y ys s, Inv (y :: ys) s →
      wpUntil (fun s' => Inv ys s' ∨ exit s') onDone onFault s)
    (xs : List β) (s : State) (hInv : Inv xs s) :
    wpUntil exit onDone onFault s := by
  induction xs generalizing s with
  | nil => exact .here (hBase s hInv)
  | cons y ys ih =>
    refine wpUntil_bind (hStep y ys s hInv) ?_
    intro s' hMid
    cases hMid with
    | inl hCont => exact ih s' hCont
    | inr hExit => exact .here hExit

/-- A suffix is no longer than the list it ends. -/
theorem length_le_append {β : Type x} (pre rest : List β) :
    rest.length ≤ (pre ++ rest).length := by
  induction pre with
  | nil => exact Nat.le_refl rest.length
  | cons y pre ih => exact Nat.le_succ_of_le ih

/-- Removing a non-empty prefix strictly shortens a list. -/
theorem length_lt_append_of_ne_nil {β : Type x} (pre rest : List β)
    (hNe : pre ≠ []) : rest.length < (pre ++ rest).length := by
  cases pre with
  | nil => exact False.elim (hNe rfl)
  | cons y pre => exact Nat.lt_succ_of_le (length_le_append pre rest)

/-- List loop rule by length: each iteration from a non-empty `Inv xs` state
reaches an `Inv ys` state for some strictly shorter list `ys`, or `exit`. -/
theorem wpLoop_list_measure {β : Type x} {Inv : List β → State → Prop}
    {exit : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop}
    (hBase : ∀ s, Inv [] s → exit s)
    (hStep : ∀ xs s, Inv xs s → xs ≠ [] →
      wpUntil
        (fun s' => (∃ ys, ys.length < xs.length ∧ Inv ys s') ∨ exit s')
        onDone onFault s)
    (xs : List β) (s : State) (hInv : Inv xs s) :
    wpUntil exit onDone onFault s := by
  refine wpLoop_inv_rank (α := List β) (fun ys => ys.length)
    (Inv := Inv) ?_ xs s hInv
  intro ys t hInvYs
  cases ys with
  | nil => exact Or.inl (hBase t hInvYs)
  | cons y rest =>
    have hNe : y :: rest ≠ [] := by
      intro hEq
      cases hEq
    refine Or.inr (wpUntil_mono_stop ?_ (hStep (y :: rest) t hInvYs hNe))
    intro t' hMid
    cases hMid with
    | inl hCont => exact Or.inr hCont
    | inr hExit => exact Or.inl hExit

/-- Chunked list-traversal loop rule: each iteration from a non-empty
`Inv xs` state consumes some non-empty prefix `pre` of `xs = pre ++ rest` and
reaches `Inv rest`, or reaches `exit`. This covers loops that process a
variable number of elements per iteration. -/
theorem wpLoop_list_split {β : Type x} {Inv : List β → State → Prop}
    {exit : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop}
    (hBase : ∀ s, Inv [] s → exit s)
    (hStep : ∀ xs s, Inv xs s → xs ≠ [] →
      wpUntil
        (fun s' =>
          (∃ pre rest, xs = pre ++ rest ∧ pre ≠ [] ∧ Inv rest s') ∨
            exit s')
        onDone onFault s)
    (xs : List β) (s : State) (hInv : Inv xs s) :
    wpUntil exit onDone onFault s := by
  refine wpLoop_list_measure (Inv := Inv) hBase ?_ xs s hInv
  intro ys t hInvYs hNe
  refine wpUntil_mono_stop ?_ (hStep ys t hInvYs hNe)
  intro t' hMid
  cases hMid with
  | inl hSplit =>
    let ⟨pre, rest, hEq, hPre, hInvRest⟩ := hSplit
    refine Or.inl ⟨rest, ?_, hInvRest⟩
    rw [hEq]
    exact length_lt_append_of_ne_nil pre rest hPre
  | inr hExit => exact Or.inr hExit

/-- State-measure loop rule: the variant `rank` is read directly off the
state. From every `Inv` state that is not an `exit` state, one iteration
reaches `exit` or an `Inv` state of strictly smaller rank. -/
theorem wpLoop_state {Inv exit : State → Prop} {rank : State → Nat}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hStep : ∀ s, Inv s →
      exit s ∨
        wpUntil (fun s' => exit s' ∨ (Inv s' ∧ rank s' < rank s))
          onDone onFault s)
    (s : State) (hInv : Inv s) :
    wpUntil exit onDone onFault s := by
  refine wpLoop_inv_rank (α := State) rank
    (Inv := fun a t => a = t ∧ Inv t) ?_ s s ⟨rfl, hInv⟩
  intro a t hAt
  have hEq : a = t := hAt.1
  cases hStep t hAt.2 with
  | inl hExit => exact Or.inl hExit
  | inr hIter =>
    refine Or.inr (wpUntil_mono_stop ?_ hIter)
    intro t' hMid
    cases hMid with
    | inl hExit => exact Or.inl hExit
    | inr hNext =>
      refine Or.inr ⟨t', ?_, rfl, hNext.1⟩
      rw [hEq]
      exact hNext.2

/-- Breakable state-measure loop rule: the loop of `wpLoop_state`, followed by
a terminating continuation from every `exit` state, terminates. An iteration
may also end the execution directly through `onDone`. -/
theorem wpLoop_nat_or_done {Inv exit : State → Prop} {rank : State → Nat}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hStep : ∀ s, Inv s →
      exit s ∨
        wpUntil (fun s' => exit s' ∨ (Inv s' ∧ rank s' < rank s))
          onDone onFault s)
    (hExit : ∀ s, exit s → wpOutcome onDone onFault s)
    (s : State) (hInv : Inv s) :
    wpOutcome onDone onFault s :=
  wpUntil_to_wpOutcome (wpLoop_state hStep s hInv) hExit

/-- Fault-free state-measure loop rule with a postcondition: the variant is
read directly off the state, no iteration may fault, and every `exit` state
terminates with an outcome satisfying `post`. -/
theorem wpLoop_state_exists {Inv exit : State → Prop} {rank : State → Nat}
    {post : Out → Prop}
    (hStep : ∀ s, Inv s →
      exit s ∨
        wpUntilOk (fun s' => exit s' ∨ (Inv s' ∧ rank s' < rank s))
          post s)
    (hExit : ∀ s, exit s → wpStateOk post s)
    (s : State) (hInv : Inv s) :
    wpStateOk post s :=
  wpLoop_nat_or_done hStep hExit s hInv

/-- Fuel-free two-exit loop rule for loops with both normal termination
(`normalExit`) and mid-loop early-return / `?` / `break` cleanup
(`earlyClean`), generalizing `#4069`'s `wpOutcomeState_loop_early_return_sound`
without fixed step budgets. -/
theorem wpLoop_early_return {α : Sort x} {r : α → α → Prop}
    (hWf : WellFounded r)
    {Inv : α → State → Prop} {normalExit earlyClean : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hStep : ∀ a s, Inv a s →
      normalExit s ∨ earlyClean s ∨
        wpUntil
          (fun s' => normalExit s' ∨ earlyClean s' ∨
            ∃ a', r a' a ∧ Inv a' s')
          onDone onFault s)
    (hNorm : ∀ s, normalExit s → wpOutcome onDone onFault s)
    (hEarly : ∀ s, earlyClean s → wpOutcome onDone onFault s)
    (a₀ : α) (s₀ : State) (hInv : Inv a₀ s₀) :
    wpOutcome onDone onFault s₀ := by
  refine wpUntil_to_wpOutcome
    (wpLoop_inv hWf (exit := fun s => normalExit s ∨ earlyClean s)
      ?_ a₀ s₀ hInv) ?_
  · intro a s hA
    cases hStep a s hA with
    | inl hN => exact Or.inl (Or.inl hN)
    | inr hRest =>
      cases hRest with
      | inl hE => exact Or.inl (Or.inr hE)
      | inr hWp =>
        refine Or.inr (wpUntil_mono_stop ?_ hWp)
        intro s' hMid
        cases hMid with
        | inl hN => exact Or.inl (Or.inl hN)
        | inr hRest' =>
          cases hRest' with
          | inl hE => exact Or.inl (Or.inr hE)
          | inr hNext => exact Or.inr hNext
  · intro s' hEx
    cases hEx with
    | inl hN => exact hNorm s' hN
    | inr hE => exact hEarly s' hE

/-- Loop-header rule over `blockTag?`: `wpLoop_inv_strict` for an invariant
that is only required at the header block `header`. Each iteration starts at
the header, executes at least one step, and comes back to the header with a
smaller ghost value or reaches `exit`. -/
theorem wpLoop_header {α : Sort x} {r : α → α → Prop} (hWf : WellFounded r)
    (header : Nat) {Inv : α → State → Prop} {exit : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hStep : ∀ a s, ops.atBlock header s → Inv a s →
      wpStepUntil
        (fun s' => exit s' ∨ ∃ a', r a' a ∧ ops.atBlock header s' ∧ Inv a' s')
        onDone onFault s)
    (a₀ : α) (s₀ : State) (hAt : ops.atBlock header s₀) (hInv : Inv a₀ s₀) :
    wpStepUntil exit onDone onFault s₀ :=
  wpLoop_inv_strict hWf
    (Inv := fun a s => ops.atBlock header s ∧ Inv a s)
    (fun a s h => hStep a s h.1 h.2) a₀ s₀ ⟨hAt, hInv⟩

end Loops

/-! ## Part V: Simulation Combinators -/

/-- Reflexive-transitive closure of an abstract step relation. -/
inductive ReflTrans {α : Type x} (step : α → α → Prop) : α → α → Prop where
  /-- Every state reaches itself. -/
  | refl (a : α) : ReflTrans step a a
  /-- Prepend one step to a run. -/
  | head {a b c : α} : step a b → ReflTrans step b c → ReflTrans step a c

/-- Append one step to a run. -/
theorem ReflTrans.tail {α : Type x} {step : α → α → Prop} {a b c : α}
    (hRun : ReflTrans step a b) (hStep : step b c) : ReflTrans step a c := by
  induction hRun with
  | refl a => exact .head hStep (.refl c)
  | head hab _ ih => exact .head hab (ih hStep)

/-- Runs compose. -/
theorem ReflTrans.trans {α : Type x} {step : α → α → Prop} {a b c : α}
    (h₁ : ReflTrans step a b) (h₂ : ReflTrans step b c) :
    ReflTrans step a c := by
  induction h₁ with
  | refl a => exact h₂
  | head hab _ ih => exact .head hab (ih h₂)

/-- Iterate the abstract step function `stepAbs` at most `k` times, stopping
at the first state where it returns `none`. -/
def runAbsFuel {α : Type x} (stepAbs : α → Option α) (k : Nat) (a : α) : α :=
  @Nat.rec (fun _ => α → α)
    (fun a => a)
    (fun _ ih a =>
      match stepAbs a with
      | some a' => ih a'
      | none => a)
    k a

/-- `runAbsFuel` with no iterations is the identity. -/
theorem runAbsFuel_zero {α : Type x} (stepAbs : α → Option α) (a : α) :
    runAbsFuel stepAbs 0 a = a :=
  rfl

/-- One more iteration of `runAbsFuel` from a state that can step. -/
theorem runAbsFuel_succ_of_some {α : Type x} {stepAbs : α → Option α}
    {a a' : α} (h : stepAbs a = some a') (k : Nat) :
    runAbsFuel stepAbs (k + 1) a = runAbsFuel stepAbs k a' := by
  change (match stepAbs a with
    | some b => runAbsFuel stepAbs k b
    | none => a) = runAbsFuel stepAbs k a'
  rw [h]

/-- `runAbsFuel` stays at a halted state. -/
theorem runAbsFuel_of_none {α : Type x} {stepAbs : α → Option α} {a : α}
    (h : stepAbs a = none) (k : Nat) : runAbsFuel stepAbs k a = a := by
  cases k with
  | zero => rfl
  | succ k =>
    change (match stepAbs a with
      | some b => runAbsFuel stepAbs k b
      | none => a) = a
    rw [h]

section Simulation

variable {State : Type u} {Out : Type v} {Fault : Type w}
  [ops : MirWpOps State Out Fault]

/-- Relational simulation rule. `R` relates abstract states to machine states
and `rank` decreases along abstract steps. If every related pair is either
finished (`DoneAbs` and `Exit`) or admits an abstract step whose target the
machine reaches again in relation `R`, then the machine reaches an `Exit`
state for some finished abstract state reachable from the initial one. -/
theorem wpSim_rel {α : Type x} {StepAbs : α → α → Prop}
    {DoneAbs : α → Prop} {R : α → State → Prop} {Exit : α → State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (DoneAbs a ∧ Exit a s) ∨
      (∃ a', StepAbs a a' ∧ rank a' < rank a ∧
        wpUntil (fun s' => R a' s') onDone onFault s))
    (a : α) (s : State) (hR : R a s) :
    wpUntil
      (fun s' => ∃ a', ReflTrans StepAbs a a' ∧ DoneAbs a' ∧ Exit a' s')
      onDone onFault s := by
  refine wpLoop_inv_rank (α := α) rank
    (Inv := fun b t => R b t ∧ ReflTrans StepAbs a b) ?_ a s
    ⟨hR, .refl a⟩
  intro b t hInv
  cases hSim b t hInv.1 with
  | inl hDone => exact Or.inl ⟨b, hInv.2, hDone.1, hDone.2⟩
  | inr hNext =>
    let ⟨b', hAbs, hLt, hIter⟩ := hNext
    refine Or.inr (wpUntil_mono_stop ?_ hIter)
    intro t' hR'
    exact Or.inr ⟨b', hLt, hR', hInv.2.tail hAbs⟩

/-- Deterministic simulation rule with an exact abstract run. `stepAbs` is an
abstract step function whose result `none` means that the abstract machine has
halted, `R` relates abstract states to machine states, and `rank` decreases
along abstract steps. If a halted related pair satisfies `Exit` and the
machine follows every abstract step, then from any related pair the machine
reaches a state related to `runAbsFuel stepAbs k a` for some `k ≤ rank a` at
which the abstract machine has halted. -/
theorem wpSim_det_run {α : Type x} {stepAbs : α → Option α}
    {R : α → State → Prop} {Exit : α → State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (stepAbs a = none → Exit a s) ∧
      (∀ a', stepAbs a = some a' →
        rank a' < rank a ∧
        wpUntil (fun s' => R a' s') onDone onFault s))
    (a : α) (s : State) (hR : R a s) :
    wpUntil
      (fun s' => ∃ k, k ≤ rank a ∧
        stepAbs (runAbsFuel stepAbs k a) = none ∧
        R (runAbsFuel stepAbs k a) s' ∧
        Exit (runAbsFuel stepAbs k a) s')
      onDone onFault s := by
  have hAux : ∀ (n : Nat) (a : α) (s : State), R a s → rank a ≤ n →
      wpUntil
        (fun s' => ∃ k, k ≤ n ∧
          stepAbs (runAbsFuel stepAbs k a) = none ∧
          R (runAbsFuel stepAbs k a) s' ∧
          Exit (runAbsFuel stepAbs k a) s')
        onDone onFault s := by
    intro n
    induction n with
    | zero =>
      intro a s hR hLe
      cases hOpt : stepAbs a with
      | none =>
        exact .here ⟨0, Nat.le_refl 0, hOpt, hR, (hSim a s hR).1 hOpt⟩
      | some a' =>
        exact False.elim
          (Nat.not_lt_zero (rank a')
            (Nat.lt_of_lt_of_le ((hSim a s hR).2 a' hOpt).1 hLe))
    | succ n ih =>
      intro a s hR hLe
      cases hOpt : stepAbs a with
      | none =>
        exact .here
          ⟨0, Nat.zero_le (n + 1), hOpt, hR, (hSim a s hR).1 hOpt⟩
      | some a' =>
        have hNext := (hSim a s hR).2 a' hOpt
        refine wpUntil_bind hNext.2 ?_
        intro s' hR'
        refine wpUntil_mono_stop ?_
          (ih a' s' hR'
            (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hNext.1 hLe)))
        intro t hStop
        let ⟨k, hk, hNone, hRk, hEk⟩ := hStop
        have hRun :
            runAbsFuel stepAbs (k + 1) a = runAbsFuel stepAbs k a' :=
          runAbsFuel_succ_of_some hOpt k
        refine ⟨k + 1, Nat.succ_le_succ hk, ?_, ?_, ?_⟩
        · rw [hRun]
          exact hNone
        · rw [hRun]
          exact hRk
        · rw [hRun]
          exact hEk
  exact hAux (rank a) a s hR (Nat.le_refl (rank a))

/-- Deterministic simulation rule: under the hypotheses of `wpSim_det_run`,
the machine reaches a state related to some halted abstract state. -/
theorem wpSim_det {α : Type x} {stepAbs : α → Option α}
    {R : α → State → Prop} {Exit : α → State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (stepAbs a = none → Exit a s) ∧
      (∀ a', stepAbs a = some a' →
        rank a' < rank a ∧
        wpUntil (fun s' => R a' s') onDone onFault s))
    (a : α) (s : State) (hR : R a s) :
    wpUntil
      (fun s' => ∃ aFinal,
        stepAbs aFinal = none ∧ R aFinal s' ∧ Exit aFinal s')
      onDone onFault s := by
  refine wpUntil_mono_stop ?_ (wpSim_det_run hSim a s hR)
  intro t hStop
  let ⟨k, _, hNone, hRk, hEk⟩ := hStop
  exact ⟨runAbsFuel stepAbs k a, hNone, hRk, hEk⟩

/-- Lock-step simulation rule: every abstract step is matched by exactly one
machine step (`stepWp` into the relation at the abstract successor). The
conclusion is that of `wpSim_det_run`. -/
theorem wpSim_step {α : Type x} {stepAbs : α → Option α}
    {R : α → State → Prop} {Exit : α → State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (stepAbs a = none → Exit a s) ∧
      (∀ a', stepAbs a = some a' →
        rank a' < rank a ∧
        ops.stepWp s (fun s' => R a' s') onDone onFault))
    (a : α) (s : State) (hR : R a s) :
    wpUntil
      (fun s' => ∃ k, k ≤ rank a ∧
        stepAbs (runAbsFuel stepAbs k a) = none ∧
        R (runAbsFuel stepAbs k a) s' ∧
        Exit (runAbsFuel stepAbs k a) s')
      onDone onFault s := by
  refine wpSim_det_run (fun b t hRb => ⟨(hSim b t hRb).1, ?_⟩) a s hR
  intro b' hOpt
  have hNext := (hSim b t hRb).2 b' hOpt
  exact ⟨hNext.1, .step (fun s' => R b' s') hNext.2 (fun _ h' => .here h')⟩

end Simulation

/-! ## Part VI: Non-Vacuity Self-Test on a Toy Countdown Machine

A two-block countdown machine checks that the interface, the fuel-free
checkpoint and the loop rules fit together on a loop whose trip count is an
input. Block `0` is the loop header: it returns `acc` when `i = 0` and
otherwise enters block `1`, which decrements `i`, increments `acc` and jumps
back. Any other block faults. -/

/-- State of the toy countdown machine: current block, remaining counter and
accumulator. -/
structure ToyState where
  /-- Current basic block. -/
  block : Nat
  /-- Remaining iterations. -/
  i : Nat
  /-- Number of completed iterations. -/
  acc : Nat

/-- One step of the toy countdown machine. -/
def toyStep (s : ToyState) : StepOutcome ToyState Nat Unit :=
  match s.block with
  | 0 =>
    match s.i with
    | 0 => .done s.acc
    | _ + 1 => .step { block := 1, i := s.i, acc := s.acc }
  | 1 => .step { block := 0, i := Nat.pred s.i, acc := s.acc + 1 }
  | _ => .fault ()

/-- Deterministic step interface of the toy countdown machine, exposing the
current block as its tag. -/
@[reducible] def toyOps : MirWpOps ToyState Nat Unit :=
  MirWpOps.ofDetStep toyStep (fun s => some s.block)

/-- One loop iteration of the toy machine: from the header with `n + 1`
iterations left, two steps lead back to the header with `n` left. -/
theorem toy_iteration (n acc : Nat) {stop : ToyState → Prop}
    {onDone : Nat → Prop} {onFault : Unit → Prop}
    (h : stop { block := 0, i := n, acc := acc + 1 }) :
    wpStepUntil (ops := toyOps) stop onDone onFault
      { block := 0, i := n + 1, acc := acc } :=
  wpStepUntil_det_step_eq (step := toyStep)
    (s' := { block := 1, i := n + 1, acc := acc }) rfl
    (wpUntil_det_step_eq (step := toyStep)
      (s' := { block := 0, i := n, acc := acc + 1 }) rfl
      (wpUntil_here (ops := toyOps) h))

/-- Non-vacuity self-test via `wpLoop_countdown`: for every `n`, the toy
countdown machine started at the header with counter `n` and accumulator `0`
terminates without faulting and returns `n`. No step budget appears. -/
theorem countDownToy_spec (n : Nat) :
    wpStateOk (ops := toyOps) (fun out => out = n)
      { block := 0, i := n, acc := 0 } := by
  have hLoop : wpUntilOk (ops := toyOps)
      (fun s => s.block = 0 ∧ s.i = 0 ∧ s.acc = n) (fun out => out = n)
      { block := 0, i := n, acc := 0 } := by
    refine wpLoop_countdown (ops := toyOps)
      (Inv := fun k s => s.block = 0 ∧ s.i = k ∧ s.acc + k = n)
      ?_ ?_ n _ ⟨rfl, rfl, Nat.zero_add n⟩
    · intro s hInv
      exact ⟨hInv.1, hInv.2.1, hInv.2.2⟩
    · intro k s hInv
      cases s with
      | mk block i acc =>
        have hBlock : block = 0 := hInv.1
        have hI : i = k + 1 := hInv.2.1
        have hAcc : acc + (k + 1) = n := hInv.2.2
        subst hBlock
        subst hI
        refine wpUntil_of_wpStepUntil (ops := toyOps)
          (toy_iteration k acc (Or.inl ?_))
        refine ⟨rfl, rfl, ?_⟩
        rw [Nat.add_assoc, Nat.add_comm 1 k]
        exact hAcc
  refine wpUntilOk_to_wpStateOk (ops := toyOps) hLoop ?_
  intro s hExit
  cases s with
  | mk block i acc =>
    have hBlock : block = 0 := hExit.1
    have hI : i = 0 := hExit.2.1
    have hAcc : acc = n := hExit.2.2
    subst hBlock
    subst hI
    exact wpOutcome_det_done_eq (step := toyStep) (out := acc) rfl hAcc

/-- The same specification through the general well-founded rule
`wpLoop_inv`, with the remaining counter as ghost value. -/
theorem countDownToy_spec_of_wpLoop_inv (n : Nat) :
    wpStateOk (ops := toyOps) (fun out => out = n)
      { block := 0, i := n, acc := 0 } := by
  have hLoop : wpUntilOk (ops := toyOps)
      (fun s => s.block = 0 ∧ s.i = 0 ∧ s.acc = n) (fun out => out = n)
      { block := 0, i := n, acc := 0 } := by
    refine wpLoop_inv_rank (ops := toyOps) (α := Nat) (fun k => k)
      (Inv := fun k s => s.block = 0 ∧ s.i = k ∧ s.acc + k = n)
      ?_ n _ ⟨rfl, rfl, Nat.zero_add n⟩
    intro k s hInv
    cases s with
    | mk block i acc =>
      have hBlock : block = 0 := hInv.1
      have hI : i = k := hInv.2.1
      have hAcc : acc + k = n := hInv.2.2
      subst hBlock
      subst hI
      cases i with
      | zero => exact Or.inl ⟨rfl, rfl, hAcc⟩
      | succ j =>
        refine Or.inr
          (wpUntil_of_wpStepUntil (ops := toyOps)
            (toy_iteration j acc (Or.inr ?_)))
        refine ⟨j, Nat.lt_succ_self j, rfl, rfl, ?_⟩
        rw [Nat.add_assoc, Nat.add_comm 1 j]
        exact hAcc
  refine wpUntilOk_to_wpStateOk (ops := toyOps) hLoop ?_
  intro s hExit
  cases s with
  | mk block i acc =>
    have hBlock : block = 0 := hExit.1
    have hI : i = 0 := hExit.2.1
    have hAcc : acc = n := hExit.2.2
    subst hBlock
    subst hI
    exact wpOutcome_det_done_eq (step := toyStep) (out := acc) rfl hAcc

/-- The fuel-free specification yields a step budget for every `n`, which is
the `∃ fuel` shape of a fuel-bounded convergence predicate. -/
theorem countDownToy_spec_exists_fuel (n : Nat) :
    ∃ fuel, wpOutcomeFuel (ops := toyOps) (fun out => out = n)
      (fun _ => False) fuel { block := 0, i := n, acc := 0 } :=
  wpOutcome_det_iff_exists_fuel.mp (countDownToy_spec n)

/-- The toy specification is not vacuous: the machine cannot return anything
but `n`. -/
theorem countDownToy_spec_exact (n m : Nat)
    (h : wpStateOk (ops := toyOps) (fun out => out = m)
      { block := 0, i := n, acc := 0 }) : m = n := by
  have hBoth := wpOutcome_conj (ops := toyOps)
    (MirWpOps.ofDetStep_conjunctive toyStep (fun s => some s.block))
    (countDownToy_spec n) h
  cases Nat.decEq m n with
  | isTrue hEq => exact hEq
  | isFalse hNe =>
    refine False.elim
      (wpOutcome_not_false (ops := toyOps)
        (MirWpOps.ofDetStep_strict toyStep (fun s => some s.block))
        (wpOutcome_mono (ops := toyOps) (fun out hOut => ?_)
          (fun _ hf => hf.1) hBoth))
    exact hNe (hOut.2.symm.trans hOut.1)

/-- Fault propagation is not vacuous: a toy state at an unknown block faults,
so no fault-free specification holds for it. -/
theorem toy_fault_not_wpStateOk (block i acc : Nat) (post : Nat → Prop) :
    ¬ wpStateOk (ops := toyOps) post
      { block := block + 2, i := i, acc := acc } :=
  fun h =>
    wpOutcome_det_fault_inv (step := toyStep) (onFault := fun _ => False)
      (err := ()) rfl h

/-- The same faulting state is accepted once the fault is allowed, so the
fault predicate is what decides the previous theorem. -/
theorem toy_fault_wpOutcome (block i acc : Nat) (post : Nat → Prop) :
    wpOutcome (ops := toyOps) post (fun err => err = ())
      { block := block + 2, i := i, acc := acc } :=
  wpOutcome_det_fault_eq (step := toyStep) (err := ()) rfl rfl

/-- Outcome type for a dot-notation and early-return regression canary. -/
inductive ToyOutcome where
  /-- Normal loop completion returning `v`. -/
  | normal (v : Nat) : ToyOutcome
  /-- Early return from inside the loop returning `v`. -/
  | early (v : Nat) : ToyOutcome

/-- One step of a two-exit countdown machine: if `i = 0` it returns `.normal acc`,
if `acc = 5` it takes an early return `.early acc`, otherwise it decrements `i`
and increments `acc`. -/
def earlyToyStep (s : ToyState) : StepOutcome ToyState ToyOutcome Unit :=
  match s.block with
  | 0 =>
    match s.i with
    | 0 => .done (.normal s.acc)
    | _ + 1 =>
      match Nat.beq s.acc 5 with
      | true => .step { block := 2, i := s.i, acc := s.acc }
      | false => .step { block := 1, i := s.i, acc := s.acc }
  | 1 => .step { block := 0, i := Nat.pred s.i, acc := s.acc + 1 }
  | 2 => .done (.early s.acc)
  | _ => .fault ()

section EarlyToyCanary

/-- Non-reducible local `MirWpOps` instance verifying that `outParam` resolves
constructor dot-notation (`.normal` / `.early`) without any wrapper. -/
local instance earlyToyOpsInst : MirWpOps ToyState ToyOutcome Unit :=
  MirWpOps.ofDetStep earlyToyStep (fun s => some s.block)

/-- Regression canary exercising `wpLoop_early_return` and constructor
dot-notation on the `outParam` `Out`. The outcome is exact for every `n`: a
count of at most `5` (including the zero-trip loop `n = 0`) finishes normally
with `n`, and every larger count takes the early return with `5`. The
postcondition is not a bare disjunction, so a machine that took the wrong exit
would not satisfy it. -/
theorem earlyToy_spec (n : Nat) :
    wpStateOk
      (fun out => (n ≤ 5 ∧ out = .normal n) ∨ (5 < n ∧ out = .early 5))
      ({ block := 0, i := n, acc := 0 } : ToyState) := by
  refine wpLoop_early_return (r := fun a b : Nat => a < b) Nat.lt_wfRel.wf
    (Inv := fun k s => s.block = 0 ∧ s.i = k ∧ s.acc + k = n ∧ s.acc ≤ 5)
    (normalExit := fun s => s.block = 0 ∧ s.i = 0 ∧ s.acc = n ∧ n ≤ 5)
    (earlyClean := fun s => s.block = 2 ∧ s.acc = 5 ∧ 5 < n)
    ?_ ?_ ?_ n ({ block := 0, i := n, acc := 0 } : ToyState)
    ⟨rfl, rfl, Nat.zero_add n, Nat.zero_le 5⟩
  · intro k s hInv
    cases s with
    | mk block i acc =>
      have hB : block = 0 := hInv.1
      have hI : i = k := hInv.2.1
      have hSum : acc + k = n := hInv.2.2.1
      have hLe : acc ≤ 5 := hInv.2.2.2
      subst hB
      subst hI
      cases i with
      | zero =>
        have hAcc : acc = n := hSum
        refine Or.inl ⟨rfl, rfl, hAcc, ?_⟩
        rw [← hAcc]
        exact hLe
      | succ j =>
        refine Or.inr (Or.inr ?_)
        cases hEq : Nat.beq acc 5 with
        | true =>
          have hAcc5 : acc = 5 := Nat.eq_of_beq_eq_true hEq
          have hStep : earlyToyStep { block := 0, i := j + 1, acc := acc } =
              .step { block := 2, i := j + 1, acc := acc } := by
            unfold earlyToyStep
            change (match Nat.beq acc 5 with
              | true =>
                (StepOutcome.step { block := 2, i := j + 1, acc := acc } :
                  StepOutcome ToyState ToyOutcome Unit)
              | false =>
                StepOutcome.step { block := 1, i := j + 1, acc := acc }) = _
            rw [hEq]
          have hLt : 5 < n := by
            rw [← hSum, hAcc5]
            exact Nat.lt_add_of_pos_right (Nat.succ_pos j)
          exact wpUntil_det_step_eq (step := earlyToyStep) hStep
            (wpUntil_here (Or.inr (Or.inl ⟨rfl, hAcc5, hLt⟩)))
        | false =>
          have hStep1 : earlyToyStep { block := 0, i := j + 1, acc := acc } =
              .step { block := 1, i := j + 1, acc := acc } := by
            unfold earlyToyStep
            change (match Nat.beq acc 5 with
              | true =>
                (StepOutcome.step { block := 2, i := j + 1, acc := acc } :
                  StepOutcome ToyState ToyOutcome Unit)
              | false =>
                StepOutcome.step { block := 1, i := j + 1, acc := acc }) = _
            rw [hEq]
          have hLe' : acc + 1 ≤ 5 :=
            Nat.lt_of_le_of_ne hLe (Nat.ne_of_beq_eq_false hEq)
          have hSum' : acc + 1 + j = n := by
            rw [Nat.add_assoc, Nat.add_comm 1 j]
            exact hSum
          exact wpUntil_det_step_eq (step := earlyToyStep) hStep1
            (wpUntil_det_step_eq (step := earlyToyStep)
              (s' := { block := 0, i := j, acc := acc + 1 }) rfl
              (wpUntil_here (Or.inr (Or.inr
                ⟨j, Nat.lt_succ_self j, rfl, rfl, hSum', hLe'⟩))))
  · intro s hN
    cases s with
    | mk block i acc =>
      have hB : block = 0 := hN.1
      have hI : i = 0 := hN.2.1
      have hA : acc = n := hN.2.2.1
      subst hB
      subst hI
      exact wpOutcome_det_done_eq (step := earlyToyStep)
        (out := .normal acc) rfl
        (Or.inl ⟨hN.2.2.2, congrArg ToyOutcome.normal hA⟩)
  · intro s hE
    cases s with
    | mk block i acc =>
      have hB : block = 2 := hE.1
      have hA : acc = 5 := hE.2.1
      subst hB
      exact wpOutcome_det_done_eq (step := earlyToyStep)
        (out := .early acc) rfl
        (Or.inr ⟨hE.2.2, congrArg ToyOutcome.early hA⟩)

/-- The two exits of the canary machine are distinguished by the exact
outcome: the zero-trip loop and a three-trip loop finish normally, and a
seven-trip loop takes the early return after five trips. -/
theorem earlyToy_exits_canary :
    wpStateOk (fun out => out = .normal 0)
      ({ block := 0, i := 0, acc := 0 } : ToyState) ∧
    wpStateOk (fun out => out = .normal 3)
      ({ block := 0, i := 3, acc := 0 } : ToyState) ∧
    wpStateOk (fun out => out = .early 5)
      ({ block := 0, i := 7, acc := 0 } : ToyState) :=
  ⟨wpOutcome_mono
      (fun _ h => h.elim (fun hN => hN.2)
        (fun hE => absurd hE.1 (Nat.not_lt_zero 5)))
      (fun _ hf => hf) (earlyToy_spec 0),
    wpOutcome_mono
      (fun _ h => h.elim (fun hN => hN.2)
        (fun hE => absurd hE.1 (by decide)))
      (fun _ hf => hf) (earlyToy_spec 3),
    wpOutcome_mono
      (fun _ h => h.elim (fun hN => absurd hN.1 (by decide))
        (fun hE => hE.2))
      (fun _ hf => hf) (earlyToy_spec 7)⟩

end EarlyToyCanary

end Anneal.ParametricCore
