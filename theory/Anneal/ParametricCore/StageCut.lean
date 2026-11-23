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
import Anneal.ParametricCore.LoopInv
import Anneal.ParametricCore.BlockTree

universe u v w x

namespace Anneal.ParametricCore

/-!
# Zero-`Prop`-Argument Stage Cuts and Compositional WP Rules
(`Anneal.ParametricCore.StageCut`)

This module restates the cutpoint barriers of `Anneal.Core.StageCut` (`#4069`)
over the step interface `MirWpOps` of `Anneal.ParametricCore.LoopInv` and the
lookup tables of `Anneal.ParametricCore.BlockTree`, with no MIR model.

1. **`StepStageCut` (`@[irreducible]`):** `s₀` reaches `s₁` within `fuel`
   steps of a deterministic step function, without terminating or faulting.
   Its arguments are the step function, the budget and the two states, so `rw`
   and `simp` have no proposition to descend into. It composes
   (`StepStageCut.trans`), weakens (`StepStageCut.fuel_mono`), is produced by
   kernel evaluation (`stepStageCut_of_runToCut_cut`,
   `stageCut_of_evalBlockTreeToCut`), moves between `BlockTree`-backed and
   list-backed lookup (`stageCut_of_blockTree`), and prepends onto `wpUntil`
   and `wpOutcome` proofs.
2. **`BoolCertCut` (`@[irreducible]`):** a reflective certificate barrier
   sealing `check cert = true`.
3. **`StageCut` and `DetStageCut` (`@[irreducible]`):** fuel-free stages over
   any `MirWpOps` interface, from an entry predicate to a cutpoint predicate,
   with reflexivity, single steps, sequential composition, weakening, diamond
   joins, a loop rule and the frame rule `stageCut_frame`.
4. **`wlpOutcome` and `wpOutcome_conj_of_wlp`:** a two-pass split that proves
   termination and safety once and adds functional postconditions through a
   weakest liberal precondition.
5. **Self-test:** a two-stage diamond control-flow graph, evaluated through a
   `BlockTree`, framed and composed into a whole-execution specification.

Why the barriers carry no `Prop` argument: `rw` (`kabstract` and `congrArg`)
and `simp` (`congrArgs`) descend into explicit arguments even beneath an
`@[irreducible]` head constant, so wrapping a large proposition as an argument
does not hide it. A barrier whose arguments are only data and predicates keeps
the sealed obligation out of reach of tactic traversal, and every seal and
unseal lemma stays linear-time.
-/

/-! ## Part I: Deterministic Fuel-Bounded Stage Cuts (`StepStageCut`) -/

section StepStage

variable {S : Type u} {Out : Type v} {Fault : Type w}

/-- Underlying bounded `.step`-reachability relation of `StepStageCut`: `s₀`
reaches `s₁` within `fuel` steps, and no step on the way terminates or
faults. -/
def reachStepIn (step : S → StepOutcome S Out Fault) (fuel : Nat)
    (s₀ s₁ : S) : Prop :=
  execUntilFuel step (fun st => st = s₁) (fun _ => False) (fun _ => False)
    fuel s₀

/-- Unfold `reachStepIn` at fuel `0`. -/
theorem reachStepIn_zero_iff {step : S → StepOutcome S Out Fault}
    {s₀ s₁ : S} : reachStepIn step 0 s₀ s₁ ↔ s₀ = s₁ :=
  Iff.rfl

/-- Unfold `reachStepIn` at fuel `fuel + 1`. -/
theorem reachStepIn_succ_iff {step : S → StepOutcome S Out Fault}
    {fuel : Nat} {s₀ s₁ : S} :
    reachStepIn step (fuel + 1) s₀ s₁ ↔
      (s₀ = s₁ ∨
        (step s₀).wp (fun st' => reachStepIn step fuel st' s₁)
          (fun _ => False) (fun _ => False)) :=
  Iff.rfl

/-- Zero-`Prop`-argument stage-cut barrier: `s₀` reaches `s₁` within `fuel`
steps of `step` without faulting or terminating on the way. It is sealed
`@[irreducible]` after its introduction, composition and bridge laws, so
downstream `rw` and `simp` cannot unfold it into the symbolic intermediate
states; they can only apply those laws. -/
def StepStageCut (step : S → StepOutcome S Out Fault) (fuel : Nat)
    (s₀ s₁ : S) : Prop :=
  reachStepIn step fuel s₀ s₁

/-- Seal a `reachStepIn` derivation as a `StepStageCut`, and unseal it. -/
theorem stepStageCut_iff_reachStepIn {step : S → StepOutcome S Out Fault}
    {fuel : Nat} {s₀ s₁ : S} :
    StepStageCut step fuel s₀ s₁ ↔ reachStepIn step fuel s₀ s₁ :=
  Iff.rfl

/-- A `StepStageCut` is a bounded reachability proof of the deterministic
interface of `step`, for any block tag. -/
theorem stepStageCut_iff_wpUntilFuel {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {fuel : Nat} {s₀ s₁ : S} :
    StepStageCut step fuel s₀ s₁ ↔
      wpUntilFuel (ops := MirWpOps.ofDetStep step tag) (fun s => s = s₁)
        (fun _ => False) (fun _ => False) fuel s₀ :=
  Iff.rfl

/-- Zero-step reflexivity at any budget. -/
theorem StepStageCut.refl (step : S → StepOutcome S Out Fault) (fuel : Nat)
    (s : S) : StepStageCut step fuel s s := by
  cases fuel with
  | zero => exact reachStepIn_zero_iff.mpr rfl
  | succ fuel => exact reachStepIn_succ_iff.mpr (Or.inl rfl)

/-- Prepend a single `.step` transition onto a `StepStageCut`. -/
theorem StepStageCut.step {step : S → StepOutcome S Out Fault} {fuel : Nat}
    {s₀ s₁ s₂ : S} (hStep : step s₀ = .step s₁)
    (hRest : StepStageCut step fuel s₁ s₂) :
    StepStageCut step (fuel + 1) s₀ s₂ := by
  refine reachStepIn_succ_iff.mpr (Or.inr ?_)
  rw [hStep]
  exact hRest

/-- A single `.step` transition is a one-step stage. -/
theorem StepStageCut.single {step : S → StepOutcome S Out Fault}
    {s₀ s₁ : S} (hStep : step s₀ = .step s₁) : StepStageCut step 1 s₀ s₁ :=
  StepStageCut.step hStep (StepStageCut.refl step 0 s₁)

/-- Fuel weakening `f₁ ≤ f₂` for `StepStageCut`. -/
theorem StepStageCut.fuel_mono {step : S → StepOutcome S Out Fault}
    {f₁ f₂ : Nat} {s₀ s₁ : S} (hLe : f₁ ≤ f₂)
    (h : StepStageCut step f₁ s₀ s₁) : StepStageCut step f₂ s₀ s₁ :=
  (stepStageCut_iff_wpUntilFuel (tag := fun _ => none)).mpr
    (wpUntilFuel_mono (ops := MirWpOps.ofDetStep step) hLe
      ((stepStageCut_iff_wpUntilFuel (tag := fun _ => none)).mp h))

/-- Sequential composition of `StepStageCut` segments: a stage `s₀ ↝ s₁` at
`f₁` and a stage `s₁ ↝ s₂` at `f₂` give a stage `s₀ ↝ s₂` at `f₁ + f₂`. -/
theorem StepStageCut.trans {step : S → StepOutcome S Out Fault}
    {f₁ f₂ : Nat} {s₀ s₁ s₂ : S} (h₁ : StepStageCut step f₁ s₀ s₁)
    (h₂ : StepStageCut step f₂ s₁ s₂) :
    StepStageCut step (f₁ + f₂) s₀ s₂ := by
  refine (stepStageCut_iff_wpUntilFuel (tag := fun _ => none)).mpr
    (wpUntilFuel_bind (ops := MirWpOps.ofDetStep step)
      ((stepStageCut_iff_wpUntilFuel (tag := fun _ => none)).mp h₁) ?_)
  intro s' hs
  have hEq : s' = s₁ := hs
  rw [hEq]
  exact (stepStageCut_iff_wpUntilFuel (tag := fun _ => none)).mp h₂

private theorem stepStageCut_imp_of_step_eq
    {step₁ step₂ : S → StepOutcome S Out Fault}
    (hEq : ∀ s : S, step₁ s = step₂ s) {fuel : Nat} {s₀ s₁ : S}
    (h : StepStageCut step₁ fuel s₀ s₁) : StepStageCut step₂ fuel s₀ s₁ := by
  induction fuel generalizing s₀ with
  | zero => exact h
  | succ fuel ih =>
    cases reachStepIn_succ_iff.mp h with
    | inl hSame => exact reachStepIn_succ_iff.mpr (Or.inl hSame)
    | inr hSt =>
      refine reachStepIn_succ_iff.mpr (Or.inr ?_)
      rw [← hEq s₀]
      exact StepOutcome.wp_mono (fun _ h' => ih h') (fun _ hf => hf)
        (fun _ hf => hf) hSt

/-- Pointwise transition congruence for `StepStageCut`. -/
theorem StepStageCut.congr_step {step₁ step₂ : S → StepOutcome S Out Fault}
    (hEq : ∀ s : S, step₁ s = step₂ s) {fuel : Nat} {s₀ s₁ : S} :
    StepStageCut step₁ fuel s₀ s₁ ↔ StepStageCut step₂ fuel s₀ s₁ :=
  ⟨stepStageCut_imp_of_step_eq hEq,
   stepStageCut_imp_of_step_eq (fun s => (hEq s).symm)⟩

/-- Stage frame for a step invariant: if every `.step` transition preserves
`F`, then `F` holds at the end of a stage that starts in `F`. -/
theorem StepStageCut.frame {step : S → StepOutcome S Out Fault}
    {F : S → Prop}
    (hFrame : ∀ s s', F s → step s = .step s' → F s')
    {fuel : Nat} {s₀ s₁ : S} (hCut : StepStageCut step fuel s₀ s₁)
    (hF : F s₀) : F s₁ := by
  induction fuel generalizing s₀ with
  | zero =>
    have hEq : s₀ = s₁ := reachStepIn_zero_iff.mp hCut
    rw [← hEq]
    exact hF
  | succ fuel ih =>
    cases reachStepIn_succ_iff.mp hCut with
    | inl hEq =>
      rw [← hEq]
      exact hF
    | inr hSt =>
      cases hStep : step s₀ with
      | step st' =>
        rw [hStep] at hSt
        exact ih hSt (hFrame s₀ st' hF hStep)
      | done o =>
        rw [hStep] at hSt
        exact False.elim hSt
      | fault e =>
        rw [hStep] at hSt
        exact False.elim hSt

/-- Stage frame for a projection: if no `.step` transition changes `proj`,
then `proj` has the same value at both ends of a stage. -/
theorem StepStageCut.frame_proj {step : S → StepOutcome S Out Fault}
    {V : Sort x} {proj : S → V}
    (hFrame : ∀ s s', step s = .step s' → proj s' = proj s)
    {fuel : Nat} {s₀ s₁ : S} (hCut : StepStageCut step fuel s₀ s₁) :
    proj s₁ = proj s₀ :=
  StepStageCut.frame (F := fun s => proj s = proj s₀)
    (fun s s' hF hStep => (hFrame s s' hStep).trans hF) hCut rfl

/-- A `StepStageCut` is a fuel-free reachability proof. -/
theorem StepStageCut.to_wpReach {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {fuel : Nat} {s₀ s₁ : S}
    (hCut : StepStageCut step fuel s₀ s₁) :
    wpReach (ops := MirWpOps.ofDetStep step tag) (fun s => s = s₁) s₀ :=
  wpUntil_of_wpUntilFuel (ops := MirWpOps.ofDetStep step tag)
    (stepStageCut_iff_wpUntilFuel.mp hCut)

/-- Prepend a `StepStageCut` prefix onto a fuel-free checkpoint proof. -/
theorem StepStageCut.to_wpUntil {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {fuel : Nat} {s₀ s₁ : S} {stop : S → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : StepStageCut step fuel s₀ s₁)
    (h : wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault
      s₁) :
    wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault s₀ := by
  refine wpUntil_bind (ops := MirWpOps.ofDetStep step tag)
    (wpUntil_mono (ops := MirWpOps.ofDetStep step tag) (fun _ hs => hs)
      (fun _ hf => False.elim hf) (fun _ hf => False.elim hf)
      (StepStageCut.to_wpReach (tag := tag) hCut)) ?_
  intro s' hs
  have hEq : s' = s₁ := hs
  rw [hEq]
  exact h

/-- A `StepStageCut` that ends in a checkpoint state is a checkpoint proof. -/
theorem StepStageCut.to_wpUntil_here {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {fuel : Nat} {s₀ s₁ : S} {stop : S → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : StepStageCut step fuel s₀ s₁) (hStop : stop s₁) :
    wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault s₀ :=
  StepStageCut.to_wpUntil hCut
    (wpUntil_here (ops := MirWpOps.ofDetStep step tag) hStop)

/-- Prepend a `StepStageCut` prefix onto a fuel-free whole-execution proof. -/
theorem StepStageCut.to_wpOutcome {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {fuel : Nat} {s₀ s₁ : S}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : StepStageCut step fuel s₀ s₁)
    (h : wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s₁) :
    wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s₀ :=
  StepStageCut.to_wpUntil hCut h

/-- Prepend a `StepStageCut` prefix onto a bounded whole-execution proof:
budgets add. -/
theorem StepStageCut.to_wpOutcomeFuel {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {f₁ f₂ : Nat} {s₀ s₁ : S}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : StepStageCut step f₁ s₀ s₁)
    (h : wpOutcomeFuel (ops := MirWpOps.ofDetStep step tag) onDone onFault
      f₂ s₁) :
    wpOutcomeFuel (ops := MirWpOps.ofDetStep step tag) onDone onFault
      (f₁ + f₂) s₀ := by
  refine wpUntilFuel_to_wpOutcomeFuel (ops := MirWpOps.ofDetStep step tag)
    (wpUntilFuel_weaken (ops := MirWpOps.ofDetStep step tag)
      (fun _ hs => hs) (fun _ hf => False.elim hf)
      (fun _ hf => False.elim hf)
      ((stepStageCut_iff_wpUntilFuel (tag := tag)).mp hCut)) ?_
  intro s' hs
  have hEq : s' = s₁ := hs
  rw [hEq]
  exact h

/-- Lift a `StepStageCut` into any `MirWpOps` interface (for example a
coalgebraic `ITree` step or a `valid`-quantified interface) that simulates
every `.step` transition of `step`. -/
theorem StepStageCut.to_wpReach_of_step {ops : MirWpOps S Out Fault}
    {step : S → StepOutcome S Out Fault}
    (hSim : ∀ s s' (P : S → Prop) (Q : Out → Prop) (R : Fault → Prop),
      step s = .step s' → P s' → ops.stepWp s P Q R)
    {fuel : Nat} {s₀ s₁ : S} (hCut : StepStageCut step fuel s₀ s₁) :
    wpReach (ops := ops) (fun s => s = s₁) s₀ := by
  induction fuel generalizing s₀ with
  | zero => exact .here (reachStepIn_zero_iff.mp hCut)
  | succ fuel ih =>
    cases reachStepIn_succ_iff.mp hCut with
    | inl hEq => exact .here hEq
    | inr hSt =>
      cases hEv : step s₀ with
      | step st' =>
        rw [hEv] at hSt
        exact wpUntil_step (ops := ops)
          (hSim s₀ st' _ (fun _ => False) (fun _ => False) hEv (ih hSt))
      | done _ =>
        rw [hEv] at hSt
        exact False.elim hSt
      | fault _ =>
        rw [hEv] at hSt
        exact False.elim hSt

/-- Prepend a `StepStageCut` onto a checkpoint proof of any simulating
`MirWpOps` interface. -/
theorem StepStageCut.to_wpUntil_of_step {ops : MirWpOps S Out Fault}
    {step : S → StepOutcome S Out Fault}
    (hSim : ∀ s s' (P : S → Prop) (Q : Out → Prop) (R : Fault → Prop),
      step s = .step s' → P s' → ops.stepWp s P Q R)
    {fuel : Nat} {s₀ s₁ : S} {stop : S → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} (hCut : StepStageCut step fuel s₀ s₁)
    (h : wpUntil (ops := ops) stop onDone onFault s₁) :
    wpUntil (ops := ops) stop onDone onFault s₀ :=
  wpReach_bind (ops := ops) (StepStageCut.to_wpReach_of_step hSim hCut)
    (fun s' hs => by
      have hEq : s' = s₁ := hs
      rw [hEq]
      exact h)

/-- Prepend a `StepStageCut` onto a whole-execution proof of any simulating
`MirWpOps` interface. -/
theorem StepStageCut.to_wpOutcome_of_step {ops : MirWpOps S Out Fault}
    {step : S → StepOutcome S Out Fault}
    (hSim : ∀ s s' (P : S → Prop) (Q : Out → Prop) (R : Fault → Prop),
      step s = .step s' → P s' → ops.stepWp s P Q R)
    {fuel : Nat} {s₀ s₁ : S} {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : StepStageCut step fuel s₀ s₁)
    (h : wpOutcome (ops := ops) onDone onFault s₁) :
    wpOutcome (ops := ops) onDone onFault s₀ :=
  StepStageCut.to_wpUntil_of_step hSim hCut h

/-- Kernel evaluation yields a `StepStageCut`: if `runToCut` over the
successor function of `step` stops at the cutpoint state `s₁`, then `s₀`
reaches `s₁` within the same budget. The hypothesis is closed by `rfl` on a
state whose steps reduce. -/
theorem stepStageCut_of_runToCut_cut {step : S → StepOutcome S Out Fault}
    {isCut : S → Bool} {fuel : Nat} {s₀ s₁ : S}
    (h : runToCut step StepOutcome.next? isCut fuel s₀ = .cut s₁) :
    StepStageCut step fuel s₀ s₁ := by
  induction fuel generalizing s₀ with
  | zero =>
    cases hCut : isCut s₀ with
    | true =>
      rw [runToCut_of_isCut hCut 0] at h
      exact reachStepIn_zero_iff.mpr (CutRun.cut.inj h)
    | false =>
      rw [runToCut_zero_of_not_isCut hCut] at h
      cases h
  | succ fuel ih =>
    cases hCut : isCut s₀ with
    | true =>
      rw [runToCut_of_isCut hCut (fuel + 1)] at h
      exact reachStepIn_succ_iff.mpr (Or.inl (CutRun.cut.inj h))
    | false =>
      cases hNext : (step s₀).next? with
      | none =>
        rw [runToCut_succ_of_halt hCut hNext fuel] at h
        cases h
      | some st' =>
        rw [runToCut_succ_of_next hCut hNext fuel] at h
        exact StepStageCut.step (StepOutcome.next?_eq_some_iff.mp hNext)
          (ih h)

/-- Kernel evaluation yields a `StepStageCut` from a run that uses up its
budget: if `runToCut` times out at `s₁`, then `s₀` reaches `s₁` within the
budget. With `isCut := fun _ => false` this runs exactly `fuel` steps. -/
theorem stepStageCut_of_runToCut_timeout
    {step : S → StepOutcome S Out Fault} {isCut : S → Bool} {fuel : Nat}
    {s₀ s₁ : S}
    (h : runToCut step StepOutcome.next? isCut fuel s₀ = .timeout s₁) :
    StepStageCut step fuel s₀ s₁ := by
  induction fuel generalizing s₀ with
  | zero =>
    cases hCut : isCut s₀ with
    | true =>
      rw [runToCut_of_isCut hCut 0] at h
      cases h
    | false =>
      rw [runToCut_zero_of_not_isCut hCut] at h
      exact reachStepIn_zero_iff.mpr (CutRun.timeout.inj h)
  | succ fuel ih =>
    cases hCut : isCut s₀ with
    | true =>
      rw [runToCut_of_isCut hCut (fuel + 1)] at h
      cases h
    | false =>
      cases hNext : (step s₀).next? with
      | none =>
        rw [runToCut_succ_of_halt hCut hNext fuel] at h
        cases h
      | some st' =>
        rw [runToCut_succ_of_next hCut hNext fuel] at h
        exact StepStageCut.step (StepOutcome.next?_eq_some_iff.mp hNext)
          (ih h)

/-- Kernel evaluation yields a `StepStageCut` from a stage starting at a
cutpoint: if `runFromCut` stops at `s₁` within `fuel` remaining steps after its
first mandatory step, then `s₀` reaches `s₁` within `fuel + 1` steps. -/
theorem stepStageCut_of_runFromCut_cut {step : S → StepOutcome S Out Fault}
    {isCut : S → Bool} {fuel : Nat} {s₀ s₁ : S}
    (h : runFromCut step StepOutcome.next? isCut fuel s₀ = .cut s₁) :
    StepStageCut step (fuel + 1) s₀ s₁ := by
  cases hNext : (step s₀).next? with
  | none =>
    rw [runFromCut_of_halt hNext fuel] at h
    cases h
  | some st' =>
    rw [runFromCut_of_next hNext fuel] at h
    exact StepStageCut.step (StepOutcome.next?_eq_some_iff.mp hNext)
      (stepStageCut_of_runToCut_cut h)

/-- Constructive equivalence between bounded deterministic reachability
(`wpUntilFuel` with `onDone := False`, `onFault := False`) and existential
witness reachability over `StepStageCut` (`#4069`'s
`wpUntilCutStep_iff_exists_stepStageCut`, `0` axioms). -/
theorem wpUntilFuel_det_iff_exists_stepStageCut
    {step : S → StepOutcome S Out Fault} {tag : S → Option Nat}
    {cut : S → Prop} :
    ∀ {fuel : Nat} {s₀ : S},
      wpUntilFuel (ops := MirWpOps.ofDetStep step tag) cut
        (fun _ => False) (fun _ => False) fuel s₀ ↔
      ∃ s₁ : S, StepStageCut step fuel s₀ s₁ ∧ cut s₁
  | 0, s₀ =>
    ⟨fun h => ⟨s₀, StepStageCut.refl step 0 s₀, h⟩,
     fun h => by
       let ⟨s₁, hCut, hC⟩ := h
       have hEq : s₀ = s₁ := reachStepIn_zero_iff.mp hCut
       rw [hEq]
       exact hC⟩
  | fuel + 1, s₀ => by
    constructor
    · intro h
      cases (wpUntilFuel_succ_iff (ops := MirWpOps.ofDetStep step tag)).mp h
          with
      | inl hC => exact ⟨s₀, StepStageCut.refl step (fuel + 1) s₀, hC⟩
      | inr hSt =>
        have hWp : (step s₀).wp
            (wpUntilFuel (ops := MirWpOps.ofDetStep step tag) cut
              (fun _ => False) (fun _ => False) fuel)
            (fun _ => False) (fun _ => False) := hSt
        cases hEv : step s₀ with
        | step st' =>
          rw [hEv] at hWp
          let ⟨s₁, hCut, hC⟩ :=
            (wpUntilFuel_det_iff_exists_stepStageCut (tag := tag)
              (fuel := fuel)).mp hWp
          exact ⟨s₁, StepStageCut.step hEv hCut, hC⟩
        | done _ =>
          rw [hEv] at hWp
          exact False.elim hWp
        | fault _ =>
          rw [hEv] at hWp
          exact False.elim hWp
    · intro hEx
      let ⟨s₁, hCut, hC⟩ := hEx
      cases reachStepIn_succ_iff.mp hCut with
      | inl hEq =>
        rw [hEq]
        exact wpUntilFuel_here (ops := MirWpOps.ofDetStep step tag) hC
      | inr hSt =>
        refine wpUntilFuel_step (ops := MirWpOps.ofDetStep step tag) ?_
        change (step s₀).wp _ (fun _ => False) (fun _ => False)
        cases hEv : step s₀ with
        | step st' =>
          rw [hEv] at hSt
          exact (wpUntilFuel_det_iff_exists_stepStageCut (tag := tag)
            (fuel := fuel)).mpr ⟨s₁, hSt, hC⟩
        | done _ =>
          rw [hEv] at hSt
          exact False.elim hSt
        | fault _ =>
          rw [hEv] at hSt
          exact False.elim hSt

/-- Move a stage from `BlockTree`-backed block lookup to list-backed lookup:
a stage of a block-indexed step function evaluated over
`BlockTree.ofList blocks` is a stage of the same step function over
`listGet? blocks`, which is the lookup a list-backed `MirWpOps` instance
uses. -/
theorem stageCut_of_blockTree {BB : Type x} (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {fuel : Nat} {s₀ s₁ : S}
    (hCut : StepStageCut (stepWith (BlockTree.ofList blocks).lookup?) fuel
      s₀ s₁) :
    StepStageCut (stepWith (listGet? blocks)) fuel s₀ s₁ :=
  (StepStageCut.congr_step (stepWith_blockTree_eq stepWith blocks)).mp hCut

/-- `0 Quot.sound` pointwise form of `stageCut_of_blockTree`. -/
theorem stageCut_of_blockTree_of_pointwise {BB : Type x} (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    (hPointwise : ∀ (f g : Nat → Option BB) (s : S),
      (∀ i, f i = g i) → stepWith f s = stepWith g s)
    {fuel : Nat} {s₀ s₁ : S}
    (hCut : StepStageCut (stepWith (BlockTree.ofList blocks).lookup?) fuel
      s₀ s₁) :
    StepStageCut (stepWith (listGet? blocks)) fuel s₀ s₁ :=
  (StepStageCut.congr_step
    (stepWith_blockTree_eq_of_pointwise stepWith hPointwise blocks)).mp hCut

/-- Move a stage from `Chunk8BlockTree`-backed block lookup to list-backed
lookup. -/
theorem stageCut_of_chunk8BlockTree {BB : Type x} (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {fuel : Nat} {s₀ s₁ : S}
    (hCut : StepStageCut (stepWith (Chunk8BlockTree.ofList blocks).lookup?)
      fuel s₀ s₁) :
    StepStageCut (stepWith (listGet? blocks)) fuel s₀ s₁ :=
  (StepStageCut.congr_step
    (stepWith_chunk8BlockTree_eq stepWith blocks)).mp hCut

/-- Move a stage from the index-forcing `BlockTree` lookup to list-backed
lookup. The forcing lookup is the one that evaluates by `rfl` on a state with
symbolic fields. -/
theorem stageCut_of_blockTree_forced {BB : Type x} (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {fuel : Nat} {s₀ s₁ : S}
    (hCut : StepStageCut (stepWith (BlockTree.ofList blocks).lookupForced?)
      fuel s₀ s₁) :
    StepStageCut (stepWith (listGet? blocks)) fuel s₀ s₁ :=
  (StepStageCut.congr_step
    (stepWith_blockTree_forced_eq stepWith blocks)).mp hCut

/-- `0 Quot.sound` pointwise form of `stageCut_of_blockTree_forced`. -/
theorem stageCut_of_blockTree_forced_of_pointwise {BB : Type x}
    (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    (hPointwise : ∀ (f g : Nat → Option BB) (s : S),
      (∀ i, f i = g i) → stepWith f s = stepWith g s)
    {fuel : Nat} {s₀ s₁ : S}
    (hCut : StepStageCut (stepWith (BlockTree.ofList blocks).lookupForced?)
      fuel s₀ s₁) :
    StepStageCut (stepWith (listGet? blocks)) fuel s₀ s₁ :=
  (StepStageCut.congr_step
    (fun st => hPointwise _ _ st (fun i =>
      ((BlockTree.ofList blocks).lookupForced?_eq i).trans
        (BlockTree.ofList_lookup_eq blocks i)))).mp hCut

/-- Move a stage from the index-forcing `Chunk8BlockTree` lookup to
list-backed lookup. -/
theorem stageCut_of_chunk8BlockTree_forced {BB : Type x} (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {fuel : Nat} {s₀ s₁ : S}
    (hCut : StepStageCut
      (stepWith (Chunk8BlockTree.ofList blocks).lookupForced?) fuel s₀ s₁) :
    StepStageCut (stepWith (listGet? blocks)) fuel s₀ s₁ :=
  (StepStageCut.congr_step
    (stepWith_chunk8BlockTree_forced_eq stepWith blocks)).mp hCut

/-- Stage cut of a block-indexed step function evaluated over
`BlockTree.ofList blocks` with the index-forcing lookup, so each `.step` of
the stage is discharged by `rfl` through the trie, also on a state with
symbolic fields. -/
abbrev BlockTreeStageCut {BB : Type x}
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    (blocks : List BB) (fuel : Nat) (s₀ s₁ : S) : Prop :=
  StepStageCut (stepWith (BlockTree.ofList blocks).lookupForced?) fuel s₀ s₁

/-- A `BlockTreeStageCut` is a stage of the list-backed step function. -/
theorem BlockTreeStageCut.to_stepStageCut {BB : Type x}
    {stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault}
    {blocks : List BB} {fuel : Nat} {s₀ s₁ : S}
    (hCut : BlockTreeStageCut stepWith blocks fuel s₀ s₁) :
    StepStageCut (stepWith (listGet? blocks)) fuel s₀ s₁ :=
  stageCut_of_blockTree_forced blocks stepWith hCut

/-- A stage of the list-backed step function is a `BlockTreeStageCut`. -/
theorem BlockTreeStageCut.of_stepStageCut {BB : Type x}
    {stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault}
    {blocks : List BB} {fuel : Nat} {s₀ s₁ : S}
    (hCut : StepStageCut (stepWith (listGet? blocks)) fuel s₀ s₁) :
    BlockTreeStageCut stepWith blocks fuel s₀ s₁ :=
  (StepStageCut.congr_step
    (stepWith_blockTree_forced_eq stepWith blocks)).mpr hCut

/-- A `BlockTreeStageCut` prepends onto a checkpoint proof of the list-backed
deterministic interface. -/
theorem BlockTreeStageCut.to_wpUntil {BB : Type x}
    {stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault}
    {blocks : List BB} {tag : S → Option Nat} {fuel : Nat} {s₀ s₁ : S}
    {stop : S → Prop} {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : BlockTreeStageCut stepWith blocks fuel s₀ s₁)
    (h : wpUntil
      (ops := MirWpOps.ofDetStep (stepWith (listGet? blocks)) tag) stop
      onDone onFault s₁) :
    wpUntil (ops := MirWpOps.ofDetStep (stepWith (listGet? blocks)) tag)
      stop onDone onFault s₀ :=
  StepStageCut.to_wpUntil (BlockTreeStageCut.to_stepStageCut hCut) h

/-- Evaluate a stage on `BlockTree.ofList blocks` and obtain it for the
list-backed step function: if `evalBlockTreeToCut` stops at the cutpoint state
`s₁`, then `s₀` reaches `s₁` under `stepWith (listGet? blocks)`. The
hypothesis is closed by `rfl`, and each evaluated step costs one trie lookup
instead of a list traversal. -/
theorem stageCut_of_evalBlockTreeToCut {BB : Type x} (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {blockOf : S → Nat} {cuts : MaskTree} {fuel : Nat} {s₀ s₁ : S}
    (h : evalBlockTreeToCut (BlockTree.ofList blocks) stepWith
      StepOutcome.next? blockOf cuts fuel s₀ = .cut s₁) :
    StepStageCut (stepWith (listGet? blocks)) fuel s₀ s₁ :=
  stageCut_of_blockTree_forced blocks stepWith
    (stepStageCut_of_runToCut_cut h)

/-- `0 Quot.sound` pointwise form of `stageCut_of_evalBlockTreeToCut`. -/
theorem stageCut_of_evalBlockTreeToCut_of_pointwise {BB : Type x}
    (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    (hPointwise : ∀ (f g : Nat → Option BB) (s : S),
      (∀ i, f i = g i) → stepWith f s = stepWith g s)
    {blockOf : S → Nat} {cuts : MaskTree} {fuel : Nat} {s₀ s₁ : S}
    (h : evalBlockTreeToCut (BlockTree.ofList blocks) stepWith
      StepOutcome.next? blockOf cuts fuel s₀ = .cut s₁) :
    StepStageCut (stepWith (listGet? blocks)) fuel s₀ s₁ :=
  stageCut_of_blockTree_forced_of_pointwise blocks stepWith hPointwise
    (stepStageCut_of_runToCut_cut h)

/-- Evaluate a stage starting at a cutpoint on `BlockTree.ofList blocks` via
`evalBlockTreeFromCut` and lift it directly to the list-backed step function
at budget `fuel + 1`. -/
theorem stageCut_of_evalBlockTreeFromCut {BB : Type x} (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {blockOf : S → Nat} {cuts : MaskTree} {fuel : Nat} {s₀ s₁ : S}
    (h : evalBlockTreeFromCut (BlockTree.ofList blocks) stepWith
      StepOutcome.next? blockOf cuts fuel s₀ = .cut s₁) :
    StepStageCut (stepWith (listGet? blocks)) (fuel + 1) s₀ s₁ :=
  stageCut_of_blockTree_forced blocks stepWith
    (stepStageCut_of_runFromCut_cut h)

/-- `0 Quot.sound` pointwise form of `stageCut_of_evalBlockTreeFromCut`. -/
theorem stageCut_of_evalBlockTreeFromCut_of_pointwise {BB : Type x}
    (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    (hPointwise : ∀ (f g : Nat → Option BB) (s : S),
      (∀ i, f i = g i) → stepWith f s = stepWith g s)
    {blockOf : S → Nat} {cuts : MaskTree} {fuel : Nat} {s₀ s₁ : S}
    (h : evalBlockTreeFromCut (BlockTree.ofList blocks) stepWith
      StepOutcome.next? blockOf cuts fuel s₀ = .cut s₁) :
    StepStageCut (stepWith (listGet? blocks)) (fuel + 1) s₀ s₁ :=
  stageCut_of_blockTree_forced_of_pointwise blocks stepWith hPointwise
    (stepStageCut_of_runFromCut_cut h)

/-- Evaluate a stage on `Chunk8BlockTree.ofList blocks` and obtain it for the
list-backed step function. -/
theorem stageCut_of_evalChunk8BlockTreeToCut {BB : Type x} (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {blockOf : S → Nat} {cuts : MaskTree} {fuel : Nat} {s₀ s₁ : S}
    (h : evalChunk8BlockTreeToCut (Chunk8BlockTree.ofList blocks) stepWith
      StepOutcome.next? blockOf cuts fuel s₀ = .cut s₁) :
    StepStageCut (stepWith (listGet? blocks)) fuel s₀ s₁ :=
  stageCut_of_chunk8BlockTree_forced blocks stepWith
    (stepStageCut_of_runToCut_cut h)

/-- Evaluate a stage starting at a cutpoint on `Chunk8BlockTree.ofList blocks`
and obtain it for the list-backed step function at budget `fuel + 1`. -/
theorem stageCut_of_evalChunk8BlockTreeFromCut {BB : Type x}
    (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {blockOf : S → Nat} {cuts : MaskTree} {fuel : Nat} {s₀ s₁ : S}
    (h : evalChunk8BlockTreeFromCut (Chunk8BlockTree.ofList blocks) stepWith
      StepOutcome.next? blockOf cuts fuel s₀ = .cut s₁) :
    StepStageCut (stepWith (listGet? blocks)) (fuel + 1) s₀ s₁ :=
  stageCut_of_chunk8BlockTree_forced blocks stepWith
    (stepStageCut_of_runFromCut_cut h)

/-- Bridge a `BlockTree`-evaluated stage directly into a checkpoint proof of
the list-backed deterministic interface. -/
theorem wpUntil_of_evalBlockTreeToCut {BB : Type x} (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {tag : S → Option Nat} {blockOf : S → Nat} {cuts : MaskTree}
    {fuel : Nat} {s₀ s₁ : S} {stop : S → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop}
    (h : evalBlockTreeToCut (BlockTree.ofList blocks) stepWith
      StepOutcome.next? blockOf cuts fuel s₀ = .cut s₁)
    (hRest : wpUntil
      (ops := MirWpOps.ofDetStep (stepWith (listGet? blocks)) tag) stop
      onDone onFault s₁) :
    wpUntil (ops := MirWpOps.ofDetStep (stepWith (listGet? blocks)) tag)
      stop onDone onFault s₀ :=
  StepStageCut.to_wpUntil (stageCut_of_evalBlockTreeToCut blocks stepWith h)
    hRest

end StepStage

attribute [irreducible] StepStageCut

/-! ## Part II: Zero-`Prop`-Argument Reflective Barrier (`BoolCertCut`) -/

/-- Zero-`Prop`-argument reflective certificate barrier asserting that the
computable checker `check : Code → Bool` accepts the certificate
`cert : Code`. It is sealed `@[irreducible]` after its seal, unseal and
pairing laws. Parameterizing it by computational data only keeps the sealed
proposition opaque to downstream rewriting while supporting axiom-free
reflective proofs. -/
def BoolCertCut {Code : Type u} (check : Code → Bool) (cert : Code) : Prop :=
  check cert = true

/-- Seals a `check cert = true` witness behind `BoolCertCut`. -/
theorem BoolCertCut.seal {Code : Type u} (check : Code → Bool) (cert : Code)
    (h : check cert = true) : BoolCertCut check cert :=
  h

/-- Unseals `BoolCertCut check cert` back to `check cert = true`. -/
theorem BoolCertCut.unseal {Code : Type u} {check : Code → Bool}
    {cert : Code} (h : BoolCertCut check cert) : check cert = true :=
  h

/-- Applies a pointwise soundness implication to a sealed `BoolCertCut`
witness without exposing the definition to downstream tactics. -/
theorem BoolCertCut.elim {Code : Type u} {check : Code → Bool} {cert : Code}
    {P : Prop} (hSound : check cert = true → P)
    (hCut : BoolCertCut check cert) : P :=
  hSound hCut

/-- Soundness combinator: applies a universal checker soundness theorem
`∀ c, check c = true → interp c` to a sealed `BoolCertCut check cert`. -/
theorem BoolCertCut.sound {Code : Type u} {check : Code → Bool}
    {interp : Code → Prop}
    (hSound : ∀ c : Code, check c = true → interp c)
    {cert : Code} (hCut : BoolCertCut check cert) : interp cert :=
  hSound cert hCut

/-- Pointwise checker congruence for `BoolCertCut`. -/
theorem BoolCertCut.congr_check {Code : Type u}
    {check₁ check₂ : Code → Bool}
    (hEq : ∀ c : Code, check₁ c = check₂ c) {cert : Code} :
    BoolCertCut check₁ cert ↔ BoolCertCut check₂ cert := by
  unfold BoolCertCut
  rw [hEq cert]

/-- Conjoins two `BoolCertCut` witnesses into a single paired certificate
checker without introducing any `Prop` argument. -/
theorem BoolCertCut.pair {C₁ : Type u} {C₂ : Type v}
    {check₁ : C₁ → Bool} {check₂ : C₂ → Bool} {c₁ : C₁} {c₂ : C₂}
    (h₁ : BoolCertCut check₁ c₁) (h₂ : BoolCertCut check₂ c₂) :
    BoolCertCut (fun p : C₁ × C₂ => check₁ p.1 && check₂ p.2) (c₁, c₂) := by
  unfold BoolCertCut at h₁ h₂
  unfold BoolCertCut
  dsimp only
  rw [h₁, h₂]
  rfl

/-- Extracts the left `BoolCertCut` component from a paired certificate. -/
theorem BoolCertCut.fst {C₁ : Type u} {C₂ : Type v}
    {check₁ : C₁ → Bool} {check₂ : C₂ → Bool} {c₁ : C₁} {c₂ : C₂}
    (h : BoolCertCut (fun p : C₁ × C₂ => check₁ p.1 && check₂ p.2)
      (c₁, c₂)) :
    BoolCertCut check₁ c₁ := by
  unfold BoolCertCut at h
  unfold BoolCertCut
  dsimp only at h
  cases h1 : check₁ c₁ with
  | true => rfl
  | false =>
    rw [h1] at h
    cases h

/-- Extracts the right `BoolCertCut` component from a paired certificate. -/
theorem BoolCertCut.snd {C₁ : Type u} {C₂ : Type v}
    {check₁ : C₁ → Bool} {check₂ : C₂ → Bool} {c₁ : C₁} {c₂ : C₂}
    (h : BoolCertCut (fun p : C₁ × C₂ => check₁ p.1 && check₂ p.2)
      (c₁, c₂)) :
    BoolCertCut check₂ c₂ := by
  unfold BoolCertCut at h
  unfold BoolCertCut
  dsimp only at h
  cases h1 : check₁ c₁ with
  | false =>
    rw [h1] at h
    cases h
  | true =>
    rw [h1, Bool.true_and] at h
    exact h

attribute [irreducible] BoolCertCut

/-- Canary: sealing, pairing and discharging through `BoolCertCut.sound` keep
`BoolCertCut` opaque after sealing. Two sealed `Nat.beq` certificates over
symbolic numbers are paired, split again, and turned into equalities. -/
theorem boolCertCut_roundtrip_canary (a b c d : Nat)
    (hab : Nat.beq a b = true) (hcd : Nat.beq c d = true) :
    a = b ∧ c = d := by
  let check : Nat × Nat → Bool := fun p => Nat.beq p.1 p.2
  have h1 : BoolCertCut check (a, b) := BoolCertCut.seal check (a, b) hab
  have h2 : BoolCertCut check (c, d) := BoolCertCut.seal check (c, d) hcd
  have hPair :
      BoolCertCut
        (fun p : (Nat × Nat) × (Nat × Nat) => check p.1 && check p.2)
        ((a, b), (c, d)) :=
    BoolCertCut.pair h1 h2
  have hSound : ∀ p : Nat × Nat, check p = true → p.1 = p.2 :=
    fun p h => Nat.eq_of_beq_eq_true h
  exact ⟨BoolCertCut.sound hSound (BoolCertCut.fst hPair),
         BoolCertCut.sound hSound (BoolCertCut.snd hPair)⟩

/-! ## Part III: Region Restriction and Step Frames -/

namespace MirWpOps

variable {State : Type u} {Out : Type v} {Fault : Type w}

/-- Restriction of a step interface to a region `A`: a step is only allowed
from a state in `A`. A checkpoint proof over `ops.within A` is a checkpoint
proof over `ops` all of whose stepped states lie in `A`, which is the shape a
frame rule for one stage needs. -/
@[reducible] def within (ops : MirWpOps State Out Fault) (A : State → Prop) :
    MirWpOps State Out Fault where
  stepWp s onStep onDone onFault := A s ∧ ops.stepWp s onStep onDone onFault
  stepWp_mono := fun hP hQ hR h => ⟨h.1, ops.stepWp_mono hP hQ hR h.2⟩
  blockTag? := ops.blockTag?

/-- `F` is preserved by every step that `ops` takes from a state in the region
`A`: a step from an `A` state that satisfies `F` leads only to states that
satisfy `F`. -/
def StepFrameOn (ops : MirWpOps State Out Fault) (A F : State → Prop) :
    Prop :=
  ∀ (s : State) (K : State → Prop) (Q : Out → Prop)
    (R : Fault → Prop),
    A s → F s → ops.stepWp s K Q R →
    ops.stepWp s (fun s' => K s' ∧ F s') Q R

/-- `F` is preserved by every step of `ops`. -/
def StepFrame (ops : MirWpOps State Out Fault) (F : State → Prop) : Prop :=
  ops.StepFrameOn (fun _ => True) F

/-- A frame on a region is a frame on every smaller region. -/
theorem StepFrameOn.mono_region {ops : MirWpOps State Out Fault}
    {A A' F : State → Prop} (h : ops.StepFrameOn A F)
    (hSub : ∀ s, A' s → A s) : ops.StepFrameOn A' F :=
  fun s K Q R hA hF hStep => h s K Q R (hSub s hA) hF hStep

/-- Frames on the same region combine. -/
theorem StepFrameOn.and {ops : MirWpOps State Out Fault}
    {A F₁ F₂ : State → Prop} (h₁ : ops.StepFrameOn A F₁)
    (h₂ : ops.StepFrameOn A F₂) :
    ops.StepFrameOn A (fun s => F₁ s ∧ F₂ s) := by
  intro s K Q R hA hF hStep
  have hBoth := h₂ s (fun s' => K s' ∧ F₁ s') Q R hA hF.2
    (h₁ s K Q R hA hF.1 hStep)
  exact ops.stepWp_mono (fun _ hk => ⟨hk.1.1, hk.1.2, hk.2⟩)
    (fun _ hq => hq) (fun _ hr => hr) hBoth

/-- Frame of a deterministic interface: it suffices that every `.step`
transition from a region state preserves `F`. -/
theorem stepFrameOn_ofDetStep
    {step : State → StepOutcome State Out Fault} {tag : State → Option Nat}
    {A F : State → Prop}
    (hFrame : ∀ s s', A s → F s → step s = .step s' → F s') :
    (ofDetStep step tag).StepFrameOn A F := by
  intro s K Q R hA hF hStep
  have hWp : (step s).wp K Q R := hStep
  change (step s).wp (fun s' => K s' ∧ F s') Q R
  cases hS : step s with
  | step s' =>
    rw [hS] at hWp
    exact ⟨hWp, hFrame s s' hA hF hS⟩
  | done o =>
    rw [hS] at hWp
    exact hWp
  | fault e =>
    rw [hS] at hWp
    exact hWp

/-- Projection frame of a deterministic interface: if no `.step` transition
from a region state changes `proj`, then `proj s = v` is framed. -/
theorem stepFrameOn_ofDetStep_proj
    {step : State → StepOutcome State Out Fault} {tag : State → Option Nat}
    {A : State → Prop} {V : Sort x} {proj : State → V}
    (hFrame : ∀ s s', A s → step s = .step s' → proj s' = proj s) (v : V) :
    (ofDetStep step tag).StepFrameOn A (fun s => proj s = v) :=
  stepFrameOn_ofDetStep
    (fun s s' hA hF hS => (hFrame s s' hA hS).trans hF)

end MirWpOps

section Within

variable {State : Type u} {Out : Type v} {Fault : Type w}
  [ops : MirWpOps State Out Fault]

/-- Forget the region: a checkpoint proof within `A` is a checkpoint proof. -/
theorem wpUntil_of_within {A : State → Prop} {stop : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop} {s : State}
    (h : wpUntil (ops := ops.within A) stop onDone onFault s) :
    wpUntil (ops := ops) stop onDone onFault s := by
  induction h with
  | here hs => exact wpUntil.here (ops := ops) hs
  | step mid hStep _ ih => exact wpUntil.step (ops := ops) mid hStep.2 ih

/-- A checkpoint proof is within any region that contains every state. -/
theorem wpUntil_within_of_forall {A : State → Prop} (hA : ∀ s, A s)
    {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State}
    (h : wpUntil (ops := ops) stop onDone onFault s) :
    wpUntil (ops := ops.within A) stop onDone onFault s := by
  induction h with
  | here hs => exact wpUntil.here (ops := ops.within A) hs
  | step mid hStep _ ih =>
    exact wpUntil.step (ops := ops.within A) mid ⟨hA _, hStep⟩ ih

/-- Enlarge the region of a checkpoint proof. -/
theorem wpUntil_within_mono {A A' : State → Prop} (hSub : ∀ s, A s → A' s)
    {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State}
    (h : wpUntil (ops := ops.within A) stop onDone onFault s) :
    wpUntil (ops := ops.within A') stop onDone onFault s := by
  induction h with
  | here hs => exact wpUntil.here (ops := ops.within A') hs
  | step mid hStep _ ih =>
    exact wpUntil.step (ops := ops.within A') mid
      ⟨hSub _ hStep.1, hStep.2⟩ ih

/-- Region-preserving frame rule for checkpoints: carries `F` from entry to
checkpoint while retaining `ops.within A`, so multiple frames can be stacked
and composed inside `A` before forgetting the region. -/
theorem wpUntil_frame_within_keep {A F : State → Prop}
    (hFrame : ops.StepFrameOn A F)
    {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} (hF : F s)
    (h : wpUntil (ops := ops.within A) stop onDone onFault s) :
    wpUntil (ops := ops.within A) (fun s' => stop s' ∧ F s') onDone onFault
      s := by
  induction h with
  | here hs => exact wpUntil.here (ops := ops.within A) ⟨hs, hF⟩
  | step mid hStep _ ih =>
    exact wpUntil.step (ops := ops.within A) (fun s' => mid s' ∧ F s')
      ⟨hStep.1, hFrame _ mid onDone onFault hStep.1 hF hStep.2⟩
      (fun s' hs' => ih s' hs'.1 hs'.2)

/-- Frame rule for checkpoints: a checkpoint proof within the region `A`
carries every `A`-frame `F` from its start to its checkpoint. `F` is
established once at the start and never re-proved, however the execution
branches and joins in between. -/
theorem wpUntil_frame_within {A F : State → Prop}
    (hFrame : ops.StepFrameOn A F)
    {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} (hF : F s)
    (h : wpUntil (ops := ops.within A) stop onDone onFault s) :
    wpUntil (ops := ops) (fun s' => stop s' ∧ F s') onDone onFault s :=
  wpUntil_of_within (wpUntil_frame_within_keep hFrame hF h)

/-- Frame rule for checkpoints and a global step invariant. -/
theorem wpUntil_frame {F : State → Prop} (hFrame : ops.StepFrame F)
    {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} (hF : F s)
    (h : wpUntil (ops := ops) stop onDone onFault s) :
    wpUntil (ops := ops) (fun s' => stop s' ∧ F s') onDone onFault s :=
  wpUntil_frame_within hFrame hF
    (wpUntil_within_of_forall (fun _ => True.intro) h)

end Within

section GuardedRun

variable {S : Type u} {Out : Type v} {Fault : Type w}

/-- Region-guarded step for kernel evaluation: `none` outside the region. -/
def guardStep (region : S → Bool) (step : S → StepOutcome S Out Fault)
    (s : S) : Option (StepOutcome S Out Fault) :=
  match region s with
  | true => some (step s)
  | false => none

/-- Successor state of a region-guarded step result. -/
def guardNext? (r : Option (StepOutcome S Out Fault)) : Option S :=
  match r with
  | some o => o.next?
  | none => none

/-- A guarded step has a successor only inside the region, and then it is the
successor of the unguarded step. -/
theorem guardNext?_guardStep_eq_some {region : S → Bool}
    {step : S → StepOutcome S Out Fault} {s s' : S}
    (h : guardNext? (guardStep region step s) = some s') :
    region s = true ∧ step s = .step s' := by
  unfold guardStep at h
  cases hR : region s with
  | false =>
    rw [hR] at h
    cases h
  | true =>
    rw [hR] at h
    exact ⟨rfl, StepOutcome.next?_eq_some_iff.mp h⟩

/-- Kernel evaluation yields a stage within a region: if `runToCut` over the
region-guarded step function stops at the cutpoint state `s₁`, then `s₀`
reaches `s₁` within the budget and every stepped state lies in the region. -/
theorem wpUntilFuel_within_of_runToCut {region : S → Bool}
    {step : S → StepOutcome S Out Fault} {tag : S → Option Nat}
    {isCut : S → Bool} {fuel : Nat} {s₀ s₁ : S}
    (h : runToCut (guardStep region step) guardNext? isCut fuel s₀ =
      .cut s₁) :
    wpUntilFuel
      (ops := (MirWpOps.ofDetStep step tag).within
        (fun s => region s = true))
      (fun s => s = s₁) (fun _ => False) (fun _ => False) fuel s₀ := by
  induction fuel generalizing s₀ with
  | zero =>
    cases hCut : isCut s₀ with
    | true =>
      rw [runToCut_of_isCut hCut 0] at h
      exact CutRun.cut.inj h
    | false =>
      rw [runToCut_zero_of_not_isCut hCut] at h
      cases h
  | succ fuel ih =>
    cases hCut : isCut s₀ with
    | true =>
      rw [runToCut_of_isCut hCut (fuel + 1)] at h
      exact Or.inl (CutRun.cut.inj h)
    | false =>
      cases hNext : guardNext? (guardStep region step s₀) with
      | none =>
        rw [runToCut_succ_of_halt hCut hNext fuel] at h
        cases h
      | some st' =>
        rw [runToCut_succ_of_next hCut hNext fuel] at h
        have hInfo := guardNext?_guardStep_eq_some hNext
        refine Or.inr ⟨hInfo.1, ?_⟩
        change (step s₀).wp _ (fun _ => False) (fun _ => False)
        rw [hInfo.2]
        exact ih h

/-- Fuel-free form of `wpUntilFuel_within_of_runToCut`. -/
theorem wpReach_within_of_runToCut {region : S → Bool}
    {step : S → StepOutcome S Out Fault} {tag : S → Option Nat}
    {isCut : S → Bool} {fuel : Nat} {s₀ s₁ : S}
    (h : runToCut (guardStep region step) guardNext? isCut fuel s₀ =
      .cut s₁) :
    wpReach
      (ops := (MirWpOps.ofDetStep step tag).within
        (fun s => region s = true))
      (fun s => s = s₁) s₀ :=
  wpUntil_of_wpUntilFuel
    (ops := (MirWpOps.ofDetStep step tag).within (fun s => region s = true))
    (wpUntilFuel_within_of_runToCut h)

/-- `BlockTree`-accelerated region-guarded cut evaluation lifted directly into
`wpReach` over `(MirWpOps.ofDetStep (stepWith (listGet? blocks)) tag).within`,
so stages evaluated by `rfl` through `BlockTree.ofList blocks` can be framed
directly with `stageCut_frame` without falling back to list lookup. -/
theorem wpReach_within_of_evalBlockTreeToCut {BB : Type x} (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {region : S → Bool} {tag : S → Option Nat} {blockOf : S → Nat}
    {cuts : MaskTree} {fuel : Nat} {s₀ s₁ : S}
    (h : evalBlockTreeToCut (BlockTree.ofList blocks)
      (fun look => guardStep region (stepWith look)) guardNext? blockOf cuts
      fuel s₀ = .cut s₁) :
    wpReach
      (ops := (MirWpOps.ofDetStep (stepWith (listGet? blocks)) tag).within
        (fun s => region s = true))
      (fun s => s = s₁) s₀ := by
  have hList :
      runToCut (guardStep region (stepWith (listGet? blocks))) guardNext?
        (fun st => cuts.get (blockOf st)) fuel s₀ = .cut s₁ := by
    rw [← evalBlockTreeToCut_ofList_eq blocks
      (fun look => guardStep region (stepWith look)) guardNext? blockOf cuts
      fuel s₀]
    exact h
  exact wpReach_within_of_runToCut hList

/-- Kernel evaluation from a cutpoint yields a bounded stage within a region:
if `runFromCut` over the region-guarded step stops at `s₁`, then `s₀` reaches
`s₁` in `fuel + 1` steps and every stepped state lies in the region. -/
theorem wpUntilFuel_within_of_runFromCut {region : S → Bool}
    {step : S → StepOutcome S Out Fault} {tag : S → Option Nat}
    {isCut : S → Bool} {fuel : Nat} {s₀ s₁ : S}
    (h : runFromCut (guardStep region step) guardNext? isCut fuel s₀ =
      .cut s₁) :
    wpUntilFuel
      (ops := (MirWpOps.ofDetStep step tag).within
        (fun s => region s = true))
      (fun s => s = s₁) (fun _ => False) (fun _ => False) (fuel + 1) s₀ := by
  cases hNext : guardNext? (guardStep region step s₀) with
  | none =>
    rw [runFromCut_of_halt hNext fuel] at h
    cases h
  | some st' =>
    rw [runFromCut_of_next hNext fuel] at h
    have hInfo := guardNext?_guardStep_eq_some hNext
    refine Or.inr ⟨hInfo.1, ?_⟩
    change (step s₀).wp _ (fun _ => False) (fun _ => False)
    rw [hInfo.2]
    exact wpUntilFuel_within_of_runToCut h

/-- Fuel-free form of `wpUntilFuel_within_of_runFromCut`. -/
theorem wpReach_within_of_runFromCut {region : S → Bool}
    {step : S → StepOutcome S Out Fault} {tag : S → Option Nat}
    {isCut : S → Bool} {fuel : Nat} {s₀ s₁ : S}
    (h : runFromCut (guardStep region step) guardNext? isCut fuel s₀ =
      .cut s₁) :
    wpReach
      (ops := (MirWpOps.ofDetStep step tag).within
        (fun s => region s = true))
      (fun s => s = s₁) s₀ :=
  wpUntil_of_wpUntilFuel
    (ops := (MirWpOps.ofDetStep step tag).within (fun s => region s = true))
    (wpUntilFuel_within_of_runFromCut h)

/-- `BlockTree`-accelerated region-guarded stage evaluation starting at a
cutpoint (`evalBlockTreeFromCut`), lifted directly into `wpReach` over
`ops.within`. -/
theorem wpReach_within_of_evalBlockTreeFromCut {BB : Type x} (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {region : S → Bool} {tag : S → Option Nat} {blockOf : S → Nat}
    {cuts : MaskTree} {fuel : Nat} {s₀ s₁ : S}
    (h : evalBlockTreeFromCut (BlockTree.ofList blocks)
      (fun look => guardStep region (stepWith look)) guardNext? blockOf cuts
      fuel s₀ = .cut s₁) :
    wpReach
      (ops := (MirWpOps.ofDetStep (stepWith (listGet? blocks)) tag).within
        (fun s => region s = true))
      (fun s => s = s₁) s₀ := by
  have hList :
      runFromCut (guardStep region (stepWith (listGet? blocks))) guardNext?
        (fun st => cuts.get (blockOf st)) fuel s₀ = .cut s₁ := by
    rw [← evalBlockTreeFromCut_ofList_eq blocks
      (fun look => guardStep region (stepWith look)) guardNext? blockOf cuts
      fuel s₀]
    exact h
  exact wpReach_within_of_runFromCut hList

/-- `Chunk8BlockTree`-accelerated region-guarded stage evaluation lifted
directly into `wpReach` over `ops.within`. -/
theorem wpReach_within_of_evalChunk8BlockTreeToCut {BB : Type x}
    (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {region : S → Bool} {tag : S → Option Nat} {blockOf : S → Nat}
    {cuts : MaskTree} {fuel : Nat} {s₀ s₁ : S}
    (h : evalChunk8BlockTreeToCut (Chunk8BlockTree.ofList blocks)
      (fun look => guardStep region (stepWith look)) guardNext? blockOf cuts
      fuel s₀ = .cut s₁) :
    wpReach
      (ops := (MirWpOps.ofDetStep (stepWith (listGet? blocks)) tag).within
        (fun s => region s = true))
      (fun s => s = s₁) s₀ := by
  have hList :
      runToCut (guardStep region (stepWith (listGet? blocks))) guardNext?
        (fun st => cuts.get (blockOf st)) fuel s₀ = .cut s₁ := by
    rw [← evalChunk8BlockTreeToCut_ofList_eq blocks
      (fun look => guardStep region (stepWith look)) guardNext? blockOf cuts
      fuel s₀]
    exact h
  exact wpReach_within_of_runToCut hList

/-- `Chunk8BlockTree`-accelerated region-guarded stage evaluation starting at a
cutpoint (`evalChunk8BlockTreeFromCut`), lifted directly into `wpReach` over
`ops.within`. -/
theorem wpReach_within_of_evalChunk8BlockTreeFromCut {BB : Type x}
    (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {region : S → Bool} {tag : S → Option Nat} {blockOf : S → Nat}
    {cuts : MaskTree} {fuel : Nat} {s₀ s₁ : S}
    (h : evalChunk8BlockTreeFromCut (Chunk8BlockTree.ofList blocks)
      (fun look => guardStep region (stepWith look)) guardNext? blockOf cuts
      fuel s₀ = .cut s₁) :
    wpReach
      (ops := (MirWpOps.ofDetStep (stepWith (listGet? blocks)) tag).within
        (fun s => region s = true))
      (fun s => s = s₁) s₀ := by
  have hList :
      runFromCut (guardStep region (stepWith (listGet? blocks))) guardNext?
        (fun st => cuts.get (blockOf st)) fuel s₀ = .cut s₁ := by
    rw [← evalChunk8BlockTreeFromCut_ofList_eq blocks
      (fun look => guardStep region (stepWith look)) guardNext? blockOf cuts
      fuel s₀]
    exact h
  exact wpReach_within_of_runFromCut hList

end GuardedRun

/-! ## Part IV: Fuel-Free Stage Cuts over `MirWpOps` (`StageCut`) -/

/-- Fuel-free stage cut over a step interface: from every state satisfying
`entry`, every execution reaches a state satisfying `cut`, unless it first
terminates with an outcome satisfying `onDone` or faults with an error
satisfying `onFault`.

`StageCut` carries the entry/cut/outcome/fault predicate interface and seals
the underlying `wpUntil` derivation (and all intermediate symbolic states)
behind `@[irreducible]`; when a completely data-only barrier with zero `Prop`
or predicate arguments is required, use `StepStageCut`, `BoolCertCut`, or
`DetStageCut`. -/
def StageCut {State : Type u} {Out : Type v} {Fault : Type w}
    [ops : MirWpOps State Out Fault]
    (entry cut : State → Prop) (onDone : Out → Prop)
    (onFault : Fault → Prop) : Prop :=
  ∀ s, entry s → wpUntil cut onDone onFault s

section StageCutLaws

variable {State : Type u} {Out : Type v} {Fault : Type w}
  [ops : MirWpOps State Out Fault]

/-- Seal a family of checkpoint proofs as a `StageCut`. -/
theorem StageCut.intro {entry cut : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop}
    (h : ∀ s, entry s → wpUntil cut onDone onFault s) :
    StageCut entry cut onDone onFault :=
  h

/-- Unseal a `StageCut` at an entry state. -/
theorem StageCut.elim {entry cut : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} (h : StageCut entry cut onDone onFault)
    {s : State} (hs : entry s) : wpUntil cut onDone onFault s :=
  h s hs

/-- A stage whose entry states are already cutpoint states. -/
theorem stageCut_of_imp {entry cut : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} (hImp : ∀ s, entry s → cut s) :
    StageCut entry cut onDone onFault :=
  fun s hs => .here (hImp s hs)

/-- Reflexivity: the empty stage from a predicate to itself. -/
theorem stageCut_refl (entry : State → Prop) (onDone : Out → Prop)
    (onFault : Fault → Prop) : StageCut entry entry onDone onFault :=
  stageCut_of_imp (fun _ hs => hs)

/-- A single step is a stage. -/
theorem stageCut_step {entry cut : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop}
    (hStep : ∀ s, entry s → ops.stepWp s cut onDone onFault) :
    StageCut entry cut onDone onFault :=
  fun s hs => .step cut (hStep s hs) (fun _ h' => .here h')

/-- Prepend a single step onto a stage. -/
theorem stageCut_step_compose {entry mid cut : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hStep : ∀ s, entry s → ops.stepWp s mid onDone onFault)
    (hRest : StageCut mid cut onDone onFault) :
    StageCut entry cut onDone onFault :=
  fun s hs => .step mid (hStep s hs) hRest

/-- Fuel-free sequential composition of stages: a stage from `entry` to `mid`
and a stage from `mid` to `cut` give a stage from `entry` to `cut`. There is
no budget to add, and the first stage may reach `mid` along any number of
branches. -/
theorem stageCut_compose {entry mid cut : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (h₁ : StageCut entry mid onDone onFault)
    (h₂ : StageCut mid cut onDone onFault) :
    StageCut entry cut onDone onFault :=
  fun s hs => wpUntil_bind (h₁ s hs) h₂

/-- Rule of consequence for stages: strengthen the entry predicate and weaken
the cutpoint, terminal and fault predicates. -/
theorem stageCut_weaken {entry entry' cut cut' : State → Prop}
    {onDone onDone' : Out → Prop} {onFault onFault' : Fault → Prop}
    (hEntry : ∀ s, entry' s → entry s) (hCut : ∀ s, cut s → cut' s)
    (hDone : ∀ o, onDone o → onDone' o)
    (hFault : ∀ f, onFault f → onFault' f)
    (h : StageCut entry cut onDone onFault) :
    StageCut entry' cut' onDone' onFault' :=
  fun s hs => wpUntil_mono hCut hDone hFault (h s (hEntry s hs))

/-- Diamond join: stages from two entry predicates to the same cutpoint give a
stage from their disjunction. -/
theorem stageCut_join {entry₁ entry₂ cut : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (h₁ : StageCut entry₁ cut onDone onFault)
    (h₂ : StageCut entry₂ cut onDone onFault) :
    StageCut (fun s => entry₁ s ∨ entry₂ s) cut onDone onFault := by
  intro s hs
  cases hs with
  | inl hs₁ => exact h₁ s hs₁
  | inr hs₂ => exact h₂ s hs₂

/-- Case split at a stage entry: if every entry state satisfies one of two
predicates and each has a stage to the cutpoint, so does the entry. -/
theorem stageCut_cases {entry entry₁ entry₂ cut : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hSplit : ∀ s, entry s → entry₁ s ∨ entry₂ s)
    (h₁ : StageCut entry₁ cut onDone onFault)
    (h₂ : StageCut entry₂ cut onDone onFault) :
    StageCut entry cut onDone onFault :=
  stageCut_weaken hSplit (fun _ hc => hc) (fun _ hq => hq) (fun _ hr => hr)
    (stageCut_join h₁ h₂)

/-- A stage for every member of a family of entry predicates is a stage for
their union. This carries ghost values (for example the value of a variable
that the stage does not touch) across the stage. -/
theorem stageCut_exists {ι : Sort x} {entry : ι → State → Prop}
    {cut : ι → State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop}
    (h : ∀ i, StageCut (entry i) (cut i) onDone onFault) :
    StageCut (fun s => ∃ i, entry i s) (fun s => ∃ i, cut i s) onDone
      onFault := by
  intro s hs
  let ⟨i, hi⟩ := hs
  exact wpUntil_mono_stop (fun _ hc => ⟨i, hc⟩) (h i s hi)

/-- Region-preserving frame rule for stages: frames `F` across a stage while
retaining `ops.within A`, so additional frames or stages inside `A` can be
composed before dropping `within A`. -/
theorem stageCut_frame_within {A F : State → Prop}
    (hFrame : ops.StepFrameOn A F)
    {entry cut : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop}
    (h : StageCut (ops := ops.within A) entry cut onDone onFault) :
    StageCut (ops := ops.within A) (fun s => entry s ∧ F s)
      (fun s => cut s ∧ F s) onDone onFault :=
  fun s hs => wpUntil_frame_within_keep hFrame hs.2 (h s hs.1)

/-- Frame rule for stages: a stage within the region `A` carries every
`A`-frame `F` from the stage entry to the stage cutpoint, so `P ∧ F` at entry
becomes `Q ∧ F` at the cutpoint without re-proving `F` along the branches and
joins of the stage. -/
theorem stageCut_frame {A F : State → Prop} (hFrame : ops.StepFrameOn A F)
    {entry cut : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop}
    (h : StageCut (ops := ops.within A) entry cut onDone onFault) :
    StageCut (ops := ops) (fun s => entry s ∧ F s) (fun s => cut s ∧ F s)
      onDone onFault :=
  fun s hs => wpUntil_frame_within hFrame hs.2 (h s hs.1)

/-- Frame rule for stages and a global step invariant. -/
theorem stageCut_frame_global {F : State → Prop} (hFrame : ops.StepFrame F)
    {entry cut : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop}
    (h : StageCut (ops := ops) entry cut onDone onFault) :
    StageCut (ops := ops) (fun s => entry s ∧ F s) (fun s => cut s ∧ F s)
      onDone onFault :=
  fun s hs => wpUntil_frame hFrame hs.2 (h s hs.1)

/-- Forget the region of a stage. -/
theorem stageCut_of_within {A : State → Prop} {entry cut : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (h : StageCut (ops := ops.within A) entry cut onDone onFault) :
    StageCut (ops := ops) entry cut onDone onFault :=
  fun s hs => wpUntil_of_within (h s hs)

/-- Hand a stage over to a whole-execution proof: if every cutpoint state
terminates as required, so does every entry state. -/
theorem stageCut_to_wpOutcome {entry cut : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (h : StageCut entry cut onDone onFault)
    (hK : ∀ s, cut s → wpOutcome onDone onFault s)
    {s : State} (hs : entry s) : wpOutcome onDone onFault s :=
  wpUntil_to_wpOutcome (h s hs) hK

/-- Loop rule at the level of stages: if every iteration is a stage from
`Inv a` to `exit` or to `Inv a'` with `r a' a`, then the loop is a stage from
`Inv a` to `exit`. -/
theorem stageCut_loop {α : Sort x} {r : α → α → Prop} (hWf : WellFounded r)
    {Inv : α → State → Prop} {exit : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hIter : ∀ a, StageCut (Inv a)
      (fun s' => exit s' ∨ ∃ a', r a' a ∧ Inv a' s') onDone onFault)
    (a : α) : StageCut (Inv a) exit onDone onFault :=
  fun s hs => wpLoop_inv hWf (fun a' s' h' => Or.inr (hIter a' s' h')) a s hs

end StageCutLaws

section DetStage

variable {S : Type u} {Out : Type v} {Fault : Type w}

/-- A `StepStageCut` is a `StageCut` of the deterministic interface from its
start state to its end state. -/
theorem StageCut.of_stepStageCut {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {fuel : Nat} {s₀ s₁ : S}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : StepStageCut step fuel s₀ s₁) :
    StageCut (ops := MirWpOps.ofDetStep step tag) (fun s => s = s₀)
      (fun s => s = s₁) onDone onFault := by
  intro s hs
  have hEq : s = s₀ := hs
  rw [hEq]
  exact StepStageCut.to_wpUntil_here hCut rfl

/-- A family of `StepStageCut`s indexed by ghost values is one `StageCut`
between the corresponding families of states. A constraint `P i` on the ghost
value holds at the cutpoint because it holds at the entry. -/
theorem StageCut.of_stepStageCut_family {ι : Sort x}
    {step : S → StepOutcome S Out Fault} {tag : S → Option Nat}
    {P : ι → Prop} {fuel : ι → Nat} {src dst : ι → S}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : ∀ i, P i → StepStageCut step (fuel i) (src i) (dst i)) :
    StageCut (ops := MirWpOps.ofDetStep step tag)
      (fun s => ∃ i, P i ∧ s = src i) (fun s => ∃ i, P i ∧ s = dst i)
      onDone onFault := by
  intro s hs
  let ⟨i, hP, hEq⟩ := hs
  rw [hEq]
  exact StepStageCut.to_wpUntil_here (hCut i hP) ⟨i, hP, rfl⟩

/-- Lift a `StageCut` along a same-state step-interface refinement. -/
theorem StageCut.of_refines {ops₁ ops₂ : MirWpOps S Out Fault}
    (hRef : ops₁.Refines ops₂) {entry cut : S → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop}
    (h : StageCut (ops := ops₁) entry cut onDone onFault) :
    StageCut (ops := ops₂) entry cut onDone onFault :=
  fun s hs => wpUntil_of_refines hRef (h s hs)

/-- A `StepStageCut` is a `StageCut` of any `MirWpOps` interface that
simulates every `.step` transition of `step`. -/
theorem StageCut.of_stepStageCut_of_step {ops : MirWpOps S Out Fault}
    {step : S → StepOutcome S Out Fault}
    (hSim : ∀ s s' (P : S → Prop) (Q : Out → Prop) (R : Fault → Prop),
      step s = .step s' → P s' → ops.stepWp s P Q R)
    {fuel : Nat} {s₀ s₁ : S} {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : StepStageCut step fuel s₀ s₁) :
    StageCut (ops := ops) (fun s => s = s₀) (fun s => s = s₁) onDone
      onFault := by
  intro s hs
  have hEq : s = s₀ := hs
  rw [hEq]
  exact StepStageCut.to_wpUntil_of_step hSim hCut
    (wpUntil_here (ops := ops) rfl)

end DetStage

attribute [irreducible] StageCut

/-- Fuel-free deterministic stage cut: `s₀` reaches `s₁` under `step` within
some budget. Like `StepStageCut` it takes only the step function and the two
states; it is sealed `@[irreducible]` after its laws. -/
def DetStageCut {S : Type u} {Out : Type v} {Fault : Type w}
    (step : S → StepOutcome S Out Fault) (s₀ s₁ : S) : Prop :=
  ∃ fuel, StepStageCut step fuel s₀ s₁

section DetStageCutLaws

variable {S : Type u} {Out : Type v} {Fault : Type w}

/-- Forget the budget of a `StepStageCut`. -/
theorem DetStageCut.of_stepStageCut {step : S → StepOutcome S Out Fault}
    {fuel : Nat} {s₀ s₁ : S} (h : StepStageCut step fuel s₀ s₁) :
    DetStageCut step s₀ s₁ :=
  ⟨fuel, h⟩

/-- A `DetStageCut` has a budget. -/
theorem DetStageCut.exists_fuel {step : S → StepOutcome S Out Fault}
    {s₀ s₁ : S} (h : DetStageCut step s₀ s₁) :
    ∃ fuel, StepStageCut step fuel s₀ s₁ :=
  h

/-- Reflexivity of `DetStageCut`. -/
theorem DetStageCut.refl (step : S → StepOutcome S Out Fault) (s : S) :
    DetStageCut step s s :=
  ⟨0, StepStageCut.refl step 0 s⟩

/-- Prepend a single `.step` transition onto a `DetStageCut`. -/
theorem DetStageCut.step {step : S → StepOutcome S Out Fault}
    {s₀ s₁ s₂ : S} (hStep : step s₀ = .step s₁)
    (hRest : DetStageCut step s₁ s₂) : DetStageCut step s₀ s₂ := by
  let ⟨fuel, h⟩ := hRest
  exact ⟨fuel + 1, StepStageCut.step hStep h⟩

/-- Fuel-free sequential composition of deterministic stages. -/
theorem DetStageCut.trans {step : S → StepOutcome S Out Fault}
    {s₀ s₁ s₂ : S} (h₁ : DetStageCut step s₀ s₁)
    (h₂ : DetStageCut step s₁ s₂) : DetStageCut step s₀ s₂ := by
  let ⟨f₁, h₁'⟩ := h₁
  let ⟨f₂, h₂'⟩ := h₂
  exact ⟨f₁ + f₂, StepStageCut.trans h₁' h₂'⟩

/-- Pointwise transition congruence for `DetStageCut`. -/
theorem DetStageCut.congr_step {step₁ step₂ : S → StepOutcome S Out Fault}
    (hEq : ∀ s : S, step₁ s = step₂ s) {s₀ s₁ : S} :
    DetStageCut step₁ s₀ s₁ ↔ DetStageCut step₂ s₀ s₁ := by
  constructor
  · intro h
    let ⟨fuel, h'⟩ := h
    exact ⟨fuel, (StepStageCut.congr_step hEq).mp h'⟩
  · intro h
    let ⟨fuel, h'⟩ := h
    exact ⟨fuel, (StepStageCut.congr_step hEq).mpr h'⟩

/-- A `DetStageCut` is exactly a fuel-free reachability proof of the
deterministic interface. -/
theorem detStageCut_iff_wpReach {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {s₀ s₁ : S} :
    DetStageCut step s₀ s₁ ↔
      wpReach (ops := MirWpOps.ofDetStep step tag) (fun s => s = s₁) s₀ := by
  constructor
  · intro h
    let ⟨_, h'⟩ := h
    exact StepStageCut.to_wpReach h'
  · intro h
    let ⟨fuel, hFuel⟩ :=
      (wpUntil_det_iff_exists_fuel (step := step) (tag := tag)).mp h
    exact ⟨fuel, stepStageCut_iff_wpUntilFuel.mpr hFuel⟩

/-- Fuel-free constructive equivalence between predicate-level deterministic
reachability and existential `DetStageCut` reachability. -/
theorem wpReach_det_iff_exists_detStageCut
    {step : S → StepOutcome S Out Fault} {tag : S → Option Nat}
    {cut : S → Prop} {s₀ : S} :
    wpReach (ops := MirWpOps.ofDetStep step tag) cut s₀ ↔
      ∃ s₁ : S, DetStageCut step s₀ s₁ ∧ cut s₁ := by
  constructor
  · intro h
    let ⟨fuel, hFuel⟩ :=
      (wpUntil_det_iff_exists_fuel (step := step) (tag := tag)).mp h
    let ⟨s₁, hCut, hC⟩ :=
      (wpUntilFuel_det_iff_exists_stepStageCut (tag := tag)).mp hFuel
    exact ⟨s₁, ⟨fuel, hCut⟩, hC⟩
  · intro h
    let ⟨s₁, ⟨fuel, hCut⟩, hC⟩ := h
    exact StepStageCut.to_wpUntil_here hCut hC

/-- Stage frame for a fuel-free `DetStageCut`. -/
theorem DetStageCut.frame {step : S → StepOutcome S Out Fault}
    {F : S → Prop}
    (hFrame : ∀ s s', F s → step s = .step s' → F s')
    {s₀ s₁ : S} (hCut : DetStageCut step s₀ s₁) (hF : F s₀) : F s₁ := by
  let ⟨_, h'⟩ := hCut
  exact StepStageCut.frame hFrame h' hF

/-- Projection frame for a fuel-free `DetStageCut`. -/
theorem DetStageCut.frame_proj {step : S → StepOutcome S Out Fault}
    {V : Sort x} {proj : S → V}
    (hFrame : ∀ s s', step s = .step s' → proj s' = proj s)
    {s₀ s₁ : S} (hCut : DetStageCut step s₀ s₁) : proj s₁ = proj s₀ := by
  let ⟨_, h'⟩ := hCut
  exact StepStageCut.frame_proj hFrame h'

/-- Prepend a `DetStageCut` prefix onto a fuel-free checkpoint proof. -/
theorem DetStageCut.to_wpUntil {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {s₀ s₁ : S} {stop : S → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : DetStageCut step s₀ s₁)
    (h : wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault
      s₁) :
    wpUntil (ops := MirWpOps.ofDetStep step tag) stop onDone onFault s₀ := by
  let ⟨_, h'⟩ := hCut
  exact StepStageCut.to_wpUntil h' h

/-- Prepend a `DetStageCut` prefix onto a fuel-free whole-execution proof. -/
theorem DetStageCut.to_wpOutcome {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {s₀ s₁ : S}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : DetStageCut step s₀ s₁)
    (h : wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s₁) :
    wpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s₀ :=
  DetStageCut.to_wpUntil hCut h

/-- A `DetStageCut` is a `StageCut` of the deterministic interface. -/
theorem DetStageCut.to_stageCut {step : S → StepOutcome S Out Fault}
    {tag : S → Option Nat} {s₀ s₁ : S}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : DetStageCut step s₀ s₁) :
    StageCut (ops := MirWpOps.ofDetStep step tag) (fun s => s = s₀)
      (fun s => s = s₁) onDone onFault := by
  let ⟨_, h'⟩ := hCut
  exact StageCut.of_stepStageCut h'

/-- A `BlockTree`-backed deterministic stage is a list-backed one. -/
theorem DetStageCut.of_blockTree {BB : Type x} (blocks : List BB)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    {s₀ s₁ : S}
    (hCut : DetStageCut (stepWith (BlockTree.ofList blocks).lookup?) s₀
      s₁) :
    DetStageCut (stepWith (listGet? blocks)) s₀ s₁ :=
  (DetStageCut.congr_step (stepWith_blockTree_eq stepWith blocks)).mp hCut

/-- Lift a `DetStageCut` into any simulating `MirWpOps` interface. -/
theorem DetStageCut.to_wpReach_of_step {ops : MirWpOps S Out Fault}
    {step : S → StepOutcome S Out Fault}
    (hSim : ∀ s s' (P : S → Prop) (Q : Out → Prop) (R : Fault → Prop),
      step s = .step s' → P s' → ops.stepWp s P Q R)
    {s₀ s₁ : S} (hCut : DetStageCut step s₀ s₁) :
    wpReach (ops := ops) (fun s => s = s₁) s₀ := by
  let ⟨_, h'⟩ := hCut
  exact StepStageCut.to_wpReach_of_step hSim h'

/-- Prepend a `DetStageCut` onto a checkpoint proof of any simulating
`MirWpOps` interface. -/
theorem DetStageCut.to_wpUntil_of_step {ops : MirWpOps S Out Fault}
    {step : S → StepOutcome S Out Fault}
    (hSim : ∀ s s' (P : S → Prop) (Q : Out → Prop) (R : Fault → Prop),
      step s = .step s' → P s' → ops.stepWp s P Q R)
    {s₀ s₁ : S} {stop : S → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} (hCut : DetStageCut step s₀ s₁)
    (h : wpUntil (ops := ops) stop onDone onFault s₁) :
    wpUntil (ops := ops) stop onDone onFault s₀ := by
  let ⟨_, h'⟩ := hCut
  exact StepStageCut.to_wpUntil_of_step hSim h' h

/-- Prepend a `DetStageCut` onto a whole-execution proof of any simulating
`MirWpOps` interface. -/
theorem DetStageCut.to_wpOutcome_of_step {ops : MirWpOps S Out Fault}
    {step : S → StepOutcome S Out Fault}
    (hSim : ∀ s s' (P : S → Prop) (Q : Out → Prop) (R : Fault → Prop),
      step s = .step s' → P s' → ops.stepWp s P Q R)
    {s₀ s₁ : S} {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : DetStageCut step s₀ s₁)
    (h : wpOutcome (ops := ops) onDone onFault s₁) :
    wpOutcome (ops := ops) onDone onFault s₀ :=
  DetStageCut.to_wpUntil_of_step hSim hCut h

/-- A `DetStageCut` is a `StageCut` of any simulating `MirWpOps`
interface. -/
theorem DetStageCut.to_stageCut_of_step {ops : MirWpOps S Out Fault}
    {step : S → StepOutcome S Out Fault}
    (hSim : ∀ s s' (P : S → Prop) (Q : Out → Prop) (R : Fault → Prop),
      step s = .step s' → P s' → ops.stepWp s P Q R)
    {s₀ s₁ : S} {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : DetStageCut step s₀ s₁) :
    StageCut (ops := ops) (fun s => s = s₀) (fun s => s = s₁) onDone
      onFault := by
  let ⟨_, h'⟩ := hCut
  exact StageCut.of_stepStageCut_of_step hSim h'

end DetStageCutLaws

attribute [irreducible] DetStageCut

/-! ## Part V: Two-Pass Safety / Functional-Spec Split (`wlpOutcome`) -/

section Liberal

variable {State : Type u} {Out : Type v} {Fault : Type w}
  [ops : MirWpOps State Out Fault]

/-- Fuel-free weakest liberal precondition of a whole execution: every
terminating path satisfies `onDone` and every faulting path satisfies
`onFault`, while divergence is allowed. It is the greatest predicate closed
under one step, given by an invariant `I` that holds at `s` and is preserved
by `stepWp`. -/
def wlpOutcome (onDone : Out → Prop) (onFault : Fault → Prop)
    (s : State) : Prop :=
  ∃ I : State → Prop, I s ∧ ∀ s', I s' → ops.stepWp s' I onDone onFault

/-- Coinduction principle for `wlpOutcome`: any step-closed invariant is
contained in it. -/
theorem wlpOutcome_of_invariant {onDone : Out → Prop}
    {onFault : Fault → Prop} (I : State → Prop)
    (hClosed : ∀ s', I s' → ops.stepWp s' I onDone onFault)
    {s : State} (hs : I s) : wlpOutcome onDone onFault s :=
  ⟨I, hs, hClosed⟩

/-- Unfold `wlpOutcome` by one step. -/
theorem wlpOutcome_unfold_iff {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State} :
    wlpOutcome onDone onFault s ↔
      ops.stepWp s (wlpOutcome onDone onFault) onDone onFault := by
  have hFwd : ∀ t, wlpOutcome onDone onFault t →
      ops.stepWp t (wlpOutcome onDone onFault) onDone onFault := by
    intro t h
    let ⟨I, hI, hClosed⟩ := h
    exact ops.stepWp_mono (fun s' hs' => ⟨I, hs', hClosed⟩)
      (fun _ hq => hq) (fun _ hr => hr) (hClosed t hI)
  constructor
  · exact hFwd s
  · intro h
    refine ⟨fun t =>
      ops.stepWp t (wlpOutcome onDone onFault) onDone onFault, h, ?_⟩
    intro s' hs'
    exact ops.stepWp_mono hFwd (fun _ hq => hq) (fun _ hr => hr) hs'

/-- Rule of consequence for `wlpOutcome`. -/
theorem wlpOutcome_mono {onDone₁ onDone₂ : Out → Prop}
    {onFault₁ onFault₂ : Fault → Prop}
    (hDone : ∀ o, onDone₁ o → onDone₂ o)
    (hFault : ∀ f, onFault₁ f → onFault₂ f)
    {s : State} (h : wlpOutcome onDone₁ onFault₁ s) :
    wlpOutcome onDone₂ onFault₂ s := by
  let ⟨I, hI, hClosed⟩ := h
  exact ⟨I, hI, fun s' hs' =>
    ops.stepWp_mono (fun _ hi => hi) hDone hFault (hClosed s' hs')⟩

/-- Total correctness implies partial correctness. -/
theorem wlpOutcome_of_wpOutcome {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State}
    (h : wpOutcome onDone onFault s) : wlpOutcome onDone onFault s :=
  ⟨wpOutcome onDone onFault, h, fun _ hs' => wpOutcome_unfold_iff.mp hs'⟩

/-- Prepend a checkpoint derivation onto a partial-correctness proof: if every
execution reaches `stop` (or terminates/faults as accepted) and every `stop`
state satisfies `wlpOutcome`, then the start state satisfies `wlpOutcome`. -/
theorem wlpOutcome_of_wpUntil {stop : State → Prop} {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State}
    (h : wpUntil stop onDone onFault s)
    (hK : ∀ s', stop s' → wlpOutcome onDone onFault s') :
    wlpOutcome onDone onFault s :=
  wpUntil_induction hK (fun _ hStep => wlpOutcome_unfold_iff.mpr hStep) h

/-- Prepend a `StageCut` onto a `wlpOutcome` continuation. -/
theorem StageCut.to_wlpOutcome {entry cut : State → Prop}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : StageCut entry cut onDone onFault)
    (hK : ∀ s, cut s → wlpOutcome onDone onFault s)
    {s : State} (hs : entry s) : wlpOutcome onDone onFault s :=
  wlpOutcome_of_wpUntil (StageCut.elim hCut hs) hK

omit ops in
/-- Prepend a `StepStageCut` onto a `wlpOutcome` continuation. -/
theorem StepStageCut.to_wlpOutcome {step : State → StepOutcome State Out Fault}
    {tag : State → Option Nat} {fuel : Nat} {s₀ s₁ : State}
    {onDone : Out → Prop} {onFault : Fault → Prop}
    (hCut : StepStageCut step fuel s₀ s₁)
    (h : wlpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s₁) :
    wlpOutcome (ops := MirWpOps.ofDetStep step tag) onDone onFault s₀ :=
  wlpOutcome_of_wpUntil (ops := MirWpOps.ofDetStep step tag)
    (StepStageCut.to_wpUntil_here (stop := fun s => s = s₁) hCut rfl)
    (fun s' hs => by
      have hEq : s' = s₁ := hs
      rw [hEq]
      exact h)

/-- Conjunctive split: total termination and safety (`wpOutcome`) combined
with partial functional correctness (`wlpOutcome`) give conjunctive total
correctness, without re-proving termination or fault absence. -/
theorem wpOutcome_conj_of_wlp (hConj : ops.Conjunctive)
    {onDone₁ onDone₂ : Out → Prop}
    {onFault₁ onFault₂ : Fault → Prop} {s : State}
    (hSafe : wpOutcome onDone₁ onFault₁ s)
    (hWlp : wlpOutcome onDone₂ onFault₂ s) :
    wpOutcome (fun o => onDone₁ o ∧ onDone₂ o)
      (fun f => onFault₁ f ∧ onFault₂ f) s := by
  induction hSafe with
  | here hf => exact False.elim hf
  | step mid hStep _ ih =>
    have hBoth := hConj _ _ _ _ _ _ _ hStep (wlpOutcome_unfold_iff.mp hWlp)
    exact .step (fun s' => mid s' ∧ wlpOutcome onDone₂ onFault₂ s') hBoth
      (fun s' hs' => ih s' hs'.1 hs'.2)

/-- Two-pass combination: a fault-free termination proof with an arbitrary
outcome and a liberal proof of `post` give a fault-free proof of `post`. -/
theorem wpStateOk_of_wlp_and_safety (hConj : ops.Conjunctive)
    {post : Out → Prop} {s : State}
    (hSafe : wpStateOk (ops := ops) (fun _ => True) s)
    (hWlp : wlpOutcome post (fun _ => True) s) :
    wpStateOk post s :=
  wpOutcome_mono (fun _ hp => hp.2) (fun _ hf => hf.1)
    (wpOutcome_conj_of_wlp hConj hSafe hWlp)

/-- Fuel-bounded weakest liberal precondition: running out of fuel is
accepted, while every path that terminates or faults within `fuel` steps must
satisfy `onDone` or `onFault`. -/
def wlpOutcomeFuel (onDone : Out → Prop) (onFault : Fault → Prop)
    (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => True)
    (fun _ ih st => ops.stepWp st ih onDone onFault)
    fuel s

/-- Unfold `wlpOutcomeFuel` at fuel `fuel + 1`. -/
theorem wlpOutcomeFuel_succ_iff {onDone : Out → Prop}
    {onFault : Fault → Prop} {fuel : Nat} {s : State} :
    wlpOutcomeFuel onDone onFault (fuel + 1) s ↔
      ops.stepWp s (wlpOutcomeFuel onDone onFault fuel) onDone onFault :=
  Iff.rfl

/-- A fuel-free liberal proof is a liberal proof at every budget. -/
theorem wlpOutcomeFuel_of_wlpOutcome {onDone : Out → Prop}
    {onFault : Fault → Prop} {s : State}
    (h : wlpOutcome onDone onFault s) (fuel : Nat) :
    wlpOutcomeFuel onDone onFault fuel s := by
  induction fuel generalizing s with
  | zero => exact True.intro
  | succ fuel ih =>
    exact wlpOutcomeFuel_succ_iff.mpr
      (ops.stepWp_mono (fun _ h' => ih h') (fun _ hq => hq)
        (fun _ hr => hr) (wlpOutcome_unfold_iff.mp h))

/-- Fuel-bounded conjunctive split at a common budget. -/
theorem wpOutcomeFuel_conj_of_wlpFuel (hConj : ops.Conjunctive)
    {onDone₁ onDone₂ : Out → Prop}
    {onFault₁ onFault₂ : Fault → Prop} {fuel : Nat} {s : State}
    (hSafe : wpOutcomeFuel onDone₁ onFault₁ fuel s)
    (hWlp : wlpOutcomeFuel onDone₂ onFault₂ fuel s) :
    wpOutcomeFuel (fun o => onDone₁ o ∧ onDone₂ o)
      (fun f => onFault₁ f ∧ onFault₂ f) fuel s := by
  induction fuel generalizing s with
  | zero => exact False.elim (wpOutcomeFuel_zero_elim hSafe)
  | succ fuel ih =>
    have hBoth := hConj _ _ _ _ _ _ _ (wpOutcomeFuel_succ_iff.mp hSafe)
      (wlpOutcomeFuel_succ_iff.mp hWlp)
    exact wpOutcomeFuel_succ_iff.mpr
      (ops.stepWp_mono (fun _ hs' => ih hs'.1 hs'.2) (fun _ hq => hq)
        (fun _ hr => hr) hBoth)

end Liberal

/-! ## Part VI: Non-Vacuity Self-Test on a Two-Stage Diamond CFG

A seven-block machine with two diamonds separated by the cutpoint block `3`
checks that `BlockTree` evaluation, stage cuts, the frame rule and stage
composition fit together.

* Stage 1 (blocks `0`, `1`, `2`): branch on `x = 0` and set `y` to `10` or
  `20`; both arms join at block `3`. This stage never writes `z`.
* Stage 2 (blocks `3`, `4`, `5`, `6`): branch on `x = 0` again; the zero arm
  adds `y` to `z`, the other arm first resets `y` to `1`; both arms join at
  block `4` and return `z` from block `6`. -/

/-- Basic blocks of the toy diamond machine. -/
inductive DiamondBlock where
  /-- Jump to `ifZero` when `x = 0` and to `ifPos` otherwise. -/
  | branch (ifZero ifPos : Nat) : DiamondBlock
  /-- Set `y := v` and jump to `next`. -/
  | setY (v next : Nat) : DiamondBlock
  /-- Set `z := z + y` and jump to `next`. -/
  | addZ (next : Nat) : DiamondBlock
  /-- Return `z`. -/
  | ret : DiamondBlock

/-- State of the toy diamond machine. -/
structure DiamondState where
  /-- Current basic block. -/
  block : Nat
  /-- Branch condition. -/
  x : Nat
  /-- Scratch variable. -/
  y : Nat
  /-- Accumulator. -/
  z : Nat

/-- One step of the toy diamond machine over a block lookup function. A
missing block faults. -/
def diamondStepWith (look : Nat → Option DiamondBlock) (s : DiamondState) :
    StepOutcome DiamondState Nat Unit :=
  match look s.block with
  | none => .fault ()
  | some (.branch ifZero ifPos) =>
    match s.x with
    | 0 => .step { block := ifZero, x := s.x, y := s.y, z := s.z }
    | _ + 1 => .step { block := ifPos, x := s.x, y := s.y, z := s.z }
  | some (.setY v next) => .step { block := next, x := s.x, y := v, z := s.z }
  | some (.addZ next) =>
    .step { block := next, x := s.x, y := s.y, z := s.z + s.y }
  | some .ret => .done s.z

/-- The two-diamond program. -/
def diamondBlocks : List DiamondBlock :=
  [.branch 1 2, .setY 10 3, .setY 20 3, .branch 4 5, .addZ 6, .setY 1 4,
   .ret]

/-- List-backed step function of the diamond program. -/
abbrev diamondStep : DiamondState → StepOutcome DiamondState Nat Unit :=
  diamondStepWith (listGet? diamondBlocks)

/-- List-backed deterministic interface of the diamond program. -/
@[reducible] def diamondOps : MirWpOps DiamondState Nat Unit :=
  MirWpOps.ofDetStep diamondStep (fun s => some s.block)

/-- Cutpoint blocks of the diamond program: the join block `3` and the return
block `6`. -/
def diamondCuts : MaskTree :=
  MaskTree.ofList [false, false, false, true, false, false, true]

/-- Stage 1, zero arm, evaluated through the `BlockTree` by `rfl` on a state
whose `y` and `z` are symbolic. -/
theorem diamond_stage1_zero (y z : Nat) :
    StepStageCut diamondStep 2 { block := 0, x := 0, y := y, z := z }
      { block := 3, x := 0, y := 10, z := z } :=
  stageCut_of_evalBlockTreeToCut diamondBlocks diamondStepWith
    (blockOf := fun s => s.block) (cuts := diamondCuts) rfl

/-- Stage 1, positive arm. -/
theorem diamond_stage1_pos (n y z : Nat) :
    StepStageCut diamondStep 2 { block := 0, x := n + 1, y := y, z := z }
      { block := 3, x := n + 1, y := 20, z := z } :=
  stageCut_of_evalBlockTreeToCut diamondBlocks diamondStepWith
    (blockOf := fun s => s.block) (cuts := diamondCuts) rfl

/-- Stage 2, zero arm: from the join block to the return block, evaluated
directly through `evalBlockTreeFromCut` by `rfl`. -/
theorem diamond_stage2_zero (y z : Nat) :
    StepStageCut diamondStep 3 { block := 3, x := 0, y := y, z := z }
      { block := 6, x := 0, y := y, z := z + y } :=
  stageCut_of_evalBlockTreeFromCut diamondBlocks diamondStepWith
    (blockOf := fun s => s.block) (cuts := diamondCuts) (fuel := 2) rfl

/-- Stage 2, positive arm, evaluated directly through `evalBlockTreeFromCut`
by `rfl`. -/
theorem diamond_stage2_pos (n y z : Nat) :
    StepStageCut diamondStep 3 { block := 3, x := n + 1, y := y, z := z }
      { block := 6, x := n + 1, y := 1, z := z + 1 } :=
  stageCut_of_evalBlockTreeFromCut diamondBlocks diamondStepWith
    (blockOf := fun s => s.block) (cuts := diamondCuts) (fuel := 2) rfl

/-- Amount the diamond program adds to `z`. -/
def diamondDelta (x : Nat) : Nat :=
  match x with
  | 0 => 10
  | _ + 1 => 1

/-- Value of `y` at the join block. -/
def diamondJoinY (x : Nat) : Nat :=
  match x with
  | 0 => 10
  | _ + 1 => 20

/-- Stage 1 as a fuel-free `StageCut` from the entry block to the join block,
for every branch condition: the two arms are joined by a case split on `x`. -/
theorem diamond_stage1 (x : Nat) :
    StageCut (ops := diamondOps) (fun s => s.block = 0 ∧ s.x = x)
      (fun s => s.block = 3 ∧ s.x = x ∧ s.y = diamondJoinY x)
      (fun _ => False) (fun _ => False) := by
  refine StageCut.intro (ops := diamondOps) ?_
  intro s hs
  cases s with
  | mk block sx y z =>
    have hBlock : block = 0 := hs.1
    have hX : sx = x := hs.2
    subst hBlock
    subst hX
    cases sx with
    | zero =>
      exact StepStageCut.to_wpUntil_here (diamond_stage1_zero y z)
        ⟨rfl, rfl, rfl⟩
    | succ n =>
      exact StepStageCut.to_wpUntil_here (diamond_stage1_pos n y z)
        ⟨rfl, rfl, rfl⟩

/-- Stage 2 as a fuel-free `StageCut` from the join block to the return
block. -/
theorem diamond_stage2 (x z₀ : Nat) :
    StageCut (ops := diamondOps)
      (fun s => (s.block = 3 ∧ s.x = x ∧ s.y = diamondJoinY x) ∧ s.z = z₀)
      (fun s => s.block = 6 ∧ s.z = z₀ + diamondDelta x)
      (fun _ => False) (fun _ => False) := by
  refine StageCut.intro (ops := diamondOps) ?_
  intro s hs
  cases s with
  | mk block sx y z =>
    have hBlock : block = 3 := hs.1.1
    have hX : sx = x := hs.1.2.1
    have hY : y = diamondJoinY x := hs.1.2.2
    have hZ : z = z₀ := hs.2
    subst hBlock
    subst hX
    subst hZ
    cases sx with
    | zero =>
      refine StepStageCut.to_wpUntil_here (diamond_stage2_zero y z) ⟨rfl, ?_⟩
      have hY' : y = 10 := hY
      rw [hY']
      rfl
    | succ n =>
      exact StepStageCut.to_wpUntil_here (diamond_stage2_pos n y z)
        ⟨rfl, rfl⟩

/-- Stage 1 stays inside blocks `0`, `1` and `2`: evaluated through the
`BlockTree` with the region-guarded step function, both arms reach the join
block without leaving the region. -/
theorem diamond_stage1_within (x : Nat) :
    StageCut
      (ops := diamondOps.within (fun s => Nat.blt s.block 3 = true))
      (fun s => s.block = 0 ∧ s.x = x)
      (fun s => s.block = 3 ∧ s.x = x ∧ s.y = diamondJoinY x)
      (fun _ => False) (fun _ => False) := by
  refine StageCut.intro
    (ops := diamondOps.within (fun s => Nat.blt s.block 3 = true)) ?_
  intro s hs
  cases s with
  | mk block sx y z =>
    have hBlock : block = 0 := hs.1
    have hX : sx = x := hs.2
    subst hBlock
    subst hX
    cases sx with
    | zero =>
      refine wpUntil_mono_stop
        (ops := diamondOps.within (fun s => Nat.blt s.block 3 = true)) ?_
        (wpReach_within_of_evalBlockTreeToCut diamondBlocks diamondStepWith
          (region := fun s => Nat.blt s.block 3)
          (tag := fun s => some s.block) (blockOf := fun s => s.block)
          (cuts := diamondCuts) (fuel := 2)
          (s₁ := { block := 3, x := 0, y := 10, z := z }) rfl)
      intro s' hs'
      have hEq : s' = { block := 3, x := 0, y := 10, z := z } := hs'
      rw [hEq]
      exact ⟨rfl, rfl, rfl⟩
    | succ n =>
      refine wpUntil_mono_stop
        (ops := diamondOps.within (fun s => Nat.blt s.block 3 = true)) ?_
        (wpReach_within_of_evalBlockTreeToCut diamondBlocks diamondStepWith
          (region := fun s => Nat.blt s.block 3)
          (tag := fun s => some s.block) (blockOf := fun s => s.block)
          (cuts := diamondCuts) (fuel := 2)
          (s₁ := { block := 3, x := n + 1, y := 20, z := z }) rfl)
      intro s' hs'
      have hEq : s' = { block := 3, x := n + 1, y := 20, z := z } := hs'
      rw [hEq]
      exact ⟨rfl, rfl, rfl⟩

/-- No step from blocks `0`, `1` or `2` writes `z`. -/
theorem diamond_stage1_frame (z₀ : Nat) :
    diamondOps.StepFrameOn (fun s => Nat.blt s.block 3 = true)
      (fun s => s.z = z₀) := by
  refine MirWpOps.stepFrameOn_ofDetStep_proj
    (proj := fun s : DiamondState => s.z) ?_ z₀
  intro s s' hRegion hStep
  cases s with
  | mk block sx y z =>
    cases block with
    | zero =>
      cases sx with
      | zero =>
        injection hStep with hEq
        rw [← hEq]
      | succ n =>
        injection hStep with hEq
        rw [← hEq]
    | succ b1 =>
      cases b1 with
      | zero =>
        injection hStep with hEq
        rw [← hEq]
      | succ b2 =>
        cases b2 with
        | zero =>
          injection hStep with hEq
          rw [← hEq]
        | succ b3 => cases hRegion

/-- Stage 1 framed: `z` keeps its entry value across the first diamond. The
frame is obtained from `stageCut_frame`, not by tracking `z` through the two
arms. -/
theorem diamond_stage1_framed (x z₀ : Nat) :
    StageCut (ops := diamondOps)
      (fun s => (s.block = 0 ∧ s.x = x) ∧ s.z = z₀)
      (fun s => (s.block = 3 ∧ s.x = x ∧ s.y = diamondJoinY x) ∧ s.z = z₀)
      (fun _ => False) (fun _ => False) :=
  stageCut_frame (ops := diamondOps) (diamond_stage1_frame z₀)
    (diamond_stage1_within x)

/-- Both stages composed: a `StageCut` from the entry block to the return
block. -/
theorem diamond_stages (x z₀ : Nat) :
    StageCut (ops := diamondOps)
      (fun s => (s.block = 0 ∧ s.x = x) ∧ s.z = z₀)
      (fun s => s.block = 6 ∧ s.z = z₀ + diamondDelta x)
      (fun _ => False) (fun _ => False) :=
  stageCut_compose (ops := diamondOps) (diamond_stage1_framed x z₀)
    (diamond_stage2 x z₀)

/-- Whole-execution specification of the two-diamond program: for every
branch condition `x`, scratch value `y` and accumulator `z`, it terminates
without faulting and returns `z + diamondDelta x`. -/
theorem diamond_spec (x y z : Nat) :
    wpStateOk (ops := diamondOps) (fun out => out = z + diamondDelta x)
      { block := 0, x := x, y := y, z := z } := by
  refine stageCut_to_wpOutcome (ops := diamondOps)
    (stageCut_weaken (ops := diamondOps) (fun _ hs => hs) (fun _ hc => hc)
      (fun _ hf => False.elim hf) (fun _ hf => False.elim hf)
      (diamond_stages x z)) ?_
    (s := { block := 0, x := x, y := y, z := z }) ⟨⟨rfl, rfl⟩, rfl⟩
  intro s hs
  cases s with
  | mk block sx sy sz =>
    have hBlock : block = 6 := hs.1
    have hZ : sz = z + diamondDelta x := hs.2
    subst hBlock
    exact wpOutcome_det_done_eq (step := diamondStep) (out := sz) rfl hZ

/-- The same specification through deterministic stage cuts only: the two
stages compose with `StepStageCut.trans` at budget `2 + 3`. -/
theorem diamond_stepStageCut_zero (y z : Nat) :
    StepStageCut diamondStep (2 + 3) { block := 0, x := 0, y := y, z := z }
      { block := 6, x := 0, y := 10, z := z + 10 } :=
  StepStageCut.trans (diamond_stage1_zero y z) (diamond_stage2_zero 10 z)

/-- The diamond specification is not vacuous: with `x = 0` the program does
not return `z + 1`, the result of the other arm. -/
theorem diamond_spec_zero_exact (y z : Nat) :
    ¬ wpStateOk (ops := diamondOps) (fun out => out = z + 1)
      { block := 0, x := 0, y := y, z := z } := by
  intro h
  have hBoth := wpOutcome_conj (ops := diamondOps)
    (MirWpOps.ofDetStep_conjunctive diamondStep (fun s => some s.block))
    (diamond_spec 0 y z) h
  refine wpOutcome_not_false (ops := diamondOps)
    (MirWpOps.ofDetStep_strict diamondStep (fun s => some s.block))
    (wpOutcome_mono (ops := diamondOps) (fun out hOut => ?_)
      (fun _ hf => hf.1) hBoth)
  have hEq : z + 10 = z + 1 := hOut.1.symm.trans hOut.2
  have hNum : (10 : Nat) = 1 := Nat.add_left_cancel hEq
  cases hNum

/-- Two-pass canary exercising `wlpOutcome_of_invariant` and
`wpStateOk_of_wlp_and_safety`: pass 1 proves safety/termination once with a
trivial postcondition (`fun _ => True`), pass 2 proves the functional
postcondition via a coinductive invariant, and `wpStateOk_of_wlp_and_safety`
combines them into exact total correctness. -/
theorem diamond_spec_two_pass_canary (x y z : Nat) :
    wpStateOk (ops := diamondOps) (fun out => out = z + diamondDelta x)
      { block := 0, x := x, y := y, z := z } := by
  have hSafe :
      wpStateOk (ops := diamondOps) (fun _ => True)
        { block := 0, x := x, y := y, z := z } :=
    wpOutcome_mono (ops := diamondOps) (fun _ _ => True.intro)
      (fun _ hf => hf) (diamond_spec x y z)
  let I : DiamondState → Prop := fun s =>
    s.x = x ∧
    ((s.block = 0 ∧ s.z = z) ∨
     (s.block = 1 ∧ s.x = 0 ∧ s.z = z) ∨
     (s.block = 2 ∧ 0 < s.x ∧ s.z = z) ∨
     (s.block = 3 ∧ s.y = diamondJoinY x ∧ s.z = z) ∨
     (s.block = 4 ∧ s.y = diamondDelta x ∧ s.z = z) ∨
     (s.block = 5 ∧ 0 < s.x ∧ s.z = z) ∨
     (s.block = 6 ∧ s.z = z + diamondDelta x))
  have hWlp :
      wlpOutcome (ops := diamondOps) (fun out => out = z + diamondDelta x)
        (fun _ => True) { block := 0, x := x, y := y, z := z } := by
    refine wlpOutcome_of_invariant (ops := diamondOps) I ?_
      ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    intro s hI
    cases s with
    | mk blk sx sy sz =>
      have hX : sx = x := hI.1
      subst hX
      cases hI.2 with
      | inl h0 =>
        have hB : blk = 0 := h0.1
        have hZ : sz = z := h0.2
        subst hB; subst hZ
        cases sx with
        | zero => exact ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
        | succ n =>
          exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, Nat.succ_pos n, rfl⟩))⟩
      | inr h1 =>
        cases h1 with
        | inl hB1 =>
          have hB : blk = 1 := hB1.1
          have hX0 : sx = 0 := hB1.2.1
          have hZ : sz = z := hB1.2.2
          subst hB; subst hX0; subst hZ
          exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))⟩
        | inr h2 =>
          cases h2 with
          | inl hB2 =>
            have hB : blk = 2 := hB2.1
            have hZ : sz = z := hB2.2.2
            subst hB; subst hZ
            cases sx with
            | zero => exact False.elim (Nat.lt_irrefl 0 hB2.2.1)
            | succ _ =>
              exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))⟩
          | inr h3 =>
            cases h3 with
            | inl hB3 =>
              have hB : blk = 3 := hB3.1
              have hY : sy = diamondJoinY sx := hB3.2.1
              have hZ : sz = z := hB3.2.2
              subst hB; subst hZ
              cases sx with
              | zero =>
                exact ⟨rfl,
                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hY, rfl⟩))))⟩
              | succ n =>
                exact ⟨rfl,
                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨rfl, Nat.succ_pos n, rfl⟩)))))⟩
            | inr h4 =>
              cases h4 with
              | inl hB4 =>
                have hB : blk = 4 := hB4.1
                have hY : sy = diamondDelta sx := hB4.2.1
                have hZ : sz = z := hB4.2.2
                subst hB; subst hZ
                refine ⟨rfl,
                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    ⟨rfl, ?_⟩)))))⟩
                change sz + sy = sz + diamondDelta sx
                rw [hY]
              | inr h5 =>
                cases h5 with
                | inl hB5 =>
                  have hB : blk = 5 := hB5.1
                  have hZ : sz = z := hB5.2.2
                  subst hB; subst hZ
                  cases sx with
                  | zero => exact False.elim (Nat.lt_irrefl 0 hB5.2.1)
                  | succ _ =>
                    exact ⟨rfl,
                      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                        ⟨rfl, rfl, rfl⟩))))⟩
                | inr hB6 =>
                  have hB : blk = 6 := hB6.1
                  subst hB
                  exact hB6.2
  exact wpStateOk_of_wlp_and_safety (ops := diamondOps)
    (MirWpOps.ofDetStep_conjunctive diamondStep (fun s => some s.block))
    hSafe hWlp

end Anneal.ParametricCore
