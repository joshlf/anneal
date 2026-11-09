/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.ProjLM2_2
import LeanMiriSpec.Correspondence.EnumLM2_3
import LeanMiriSpec.Correspondence.UnionLM2_4
import LeanMiriSpec.Correspondence.RefLM3_2
import LeanMiriSpec.Correspondence.CallLM4_1

/-!
# `LM-4.3`: Whole-Program Safety Equivalence and Multi-Step `RunLoop` Simulation

This module composes the one-step correspondences of `LM-1` … `LM-4.2` into
whole-program statements relating

* Anneal's interaction-tree semantics `mirTree body s` (`ITree.cofix
  (stepMirState body) (.running s)`, `MirSemantics/Machine.lean`), judged by
  `Trusted.ITree.TreeSafe` (`MirNoUBTree`), `Trusted.ITree.ReachesRet`, and
  reachable faults (`Trusted.ITree.FaultNow`); and
* `lean-miri`'s scheduler loop `Miri.Interpreter.RunLoop.iteration` over
  concrete single-threaded `RunLoopHooks` (`annealRunLoopHooks`), packaged as a
  `Miri.OperationalSafety.System` (`miriSystem`).

## Contents

1. Reachability of coalgebraic trees: `CoStep` / `CoReach`; `treeSafe_cofix_iff`
   and `reachesRet_cofix_iff` characterize `TreeSafe` and `ReachesRet` of every
   `ITree.cofix` by its reachable coalgebra states.
2. `miriSystem H`: one transition is one `RunLoop.iteration` (through
   `RunLoop.stepCurrentThread` and `RunLoop.runOnStackEmpty`, `miriIter_eq`)
   that succeeds and leaves a nonempty stack. An iteration failing with `e` is
   terminal with `classifyError e`: `.undefinedBehavior` exactly when
   `RunLoop.reportsUB e`, `.unsupported` for unsupported operations, and
   `.blocked` otherwise. An iteration that pops the root frame is terminal with
   `.returned v` for the return operand `v` that `ControlHooks.returnOperand`
   reads from `_0`.
3. The step-closed simulation engine. `Lockstep` relates one Anneal step and one
   `lean-miri` core step relative to an invariant `Inv` and a return relation
   `RetRel` (both continue into `Inv`; both return with `RetRel`-related values;
   or both fail, agreeing on undefined behavior). `StepClosedSim` asks every
   `Inv` pair to take a `Lockstep` step. From a `StepClosedSim` and one related
   pair: `step_universal_simulation` (master small-step theorem),
   `runLoop_universal_simulation` (master multi-step theorem over fuel),
   `treeSafe_iff_miriSafe` (with `treeSafe_imp_miriSafe`,
   `miriSafe_imp_treeSafe`, `mirNoUBTree_iff_miriSafe`),
   `treeSafe_imp_noUndefinedBehavior`, `reachesUB_iff_miriReachesUB` and
   `runLoop_ub_iff` (finite-step undefined-behavior reachability in both
   directions), `partialCorrect_iff_annealPostcondition`, and
   `infiniteRun_iff_anneal_forever`.
4. Run certificates (`MiriPath`, `AnnealPath`, `runLoopFuel` and
   `runAnnealBounded` observations, lassos, `wholeProgram_returns`,
   `wholeProgram_ub`) that turn concrete executions into whole-program facts.
5. The unconditional closed fragment `InSafeScalarFragment` (`LM-1.1`
   `WellTypedBody`): `scalarFragment_stepClosedSim` holds with no per-step
   hypothesis, and `scalarFragment_entry` relates the entry states
   `initMachineState body []` and `miriEntryState body` of every body, so the
   whole-program theorems hold from entry for every fragment body, including
   diverging loops (`scalarFragment_infiniteRun_iff`).
6. Bridges from `StepObsRel`, `StepRelLM2_2`, `StepRelLM2_3`, `StepRelLM2_4`,
   `StepRelLM3_1`, `StepRelLM3_2`, and `StepRelMultiFrame` (and through them
   `StateRel`, `StateRelLM2_2` … `MultiFrameStateRel`) to `Lockstep`, with
   `stepClosedSim_of_stepRelLM2_3`, `stepClosedSim_of_stepRelLM3_1`, and
   `stepClosedSim_of_stepRelMultiFrame` lifting any step-closed fragment of
   those relations to the whole-program theorems.

## Correspondence Scope & Divergence Ledger

Agreed fragments (kernel-certified per step, lifted here):

* `LM-1.1` scalar statements and `Goto` / `Return` / `Unreachable`, closed and
  unconditional (`InSafeScalarFragment`); `LM-1.2` comparisons, `IntToInt`
  casts, and `SwitchInt` (`StepObsRel`); `LM-1.3` checked arithmetic and
  `Assert` with `UnwindAction::Unreachable`; `LM-1.4` storage, moves, and
  `PlaceMention`.
* `LM-2.1` arrays (`Index`, `ConstantIndex`, `Len`, `Repeat`); `LM-2.2` structs
  and tuples with padding; `LM-2.3` multi-variant enums (`Downcast`,
  `SetDiscriminant`, `Discriminant`, `SwitchInt`); `LM-2.4` unions (initialized
  prefixes, uninitialized bytes).
* `LM-3.1` raw pointers (`&raw`, `*ptr`, `Offset`, `StorageDead`
  use-after-free); `LM-3.2` references and the Tree Borrows hierarchy; `LM-3.3`
  6-state Tree Borrows (`I-10`, `I-11`, protectors) at the level of
  `Tree.NormalTreeState.performAccess`.
* `LM-4.1` multi-frame `Call` / `Return` with `CallId` protectors and
  `GlobalState.endCall`; `LM-4.2` intrinsics (`Assume`, `exact_div`,
  `write_bytes`, `CopyNonOverlapping`, `arith_offset`, bit and saturating
  integer intrinsics).

Kernel-certified divergences (outside every agreed fragment):

* `C2` (`cex_end_of_call_foreign_unique_frozen_divergence`): `lean-miri`'s
  end-of-call protector release performs an implicit read that freezes a
  foreign `Unique` sibling, which Anneal's `Return` leaves `Unique`.
* `H4` (`wit_lm4_1_unscoped_borrow_cross_frame_divergence`): Anneal's
  `BorrowEntry.targetLocal` is not scoped by frame, so a callee borrow survives
  the return and aliases caller locals, whereas `Stack.cleanupStackFrame`
  deallocates the callee's locals.
* `H3` (`canonical_drop_no_glue_preserves_local_divergence`): Anneal's `Drop`
  deinitializes the dropped local; canonical `lean-miri` treats `Drop` without
  glue as `goToBlock` and keeps the value.
* `H1` (`wit_lm4_1_zst_unit_return_simulation`): a zero-sized `_0` returns as
  `.init .unit` in Anneal and as `.live (.immediate .uninit)` in `lean-miri`
  (`RemoveZsts`), a representation difference the relations absorb.
* `LM-4.2`: `CopyNonOverlapping` from an uninitialized source and through a
  frozen borrow (`step_intrinsic_copyNonOverlapping_uninit_src_divergence`,
  `step_intrinsic_copyNonOverlapping_perm_divergence`), `write_bytes` through a
  frozen borrow (`call_intrinsic_write_bytes_perm_divergence`), and
  `rotate_left` / `rotate_right` shift widths
  (`wit_lm4_2_rotate_left_divergence`, `wit_lm4_2_rotate_right_divergence`).
* `LM-4.3` (`MiriDiffWitnesses.w1_assert_continue_divergence`): a failing
  `Assert` with `UnwindAction::Continue` panics in Anneal (a defined outcome,
  so `TreeSafe` holds) while `annealTerminatorHooks.assertPanic` reports
  undefined behavior; unwinding `Assert`s are therefore excluded from the closed
  fragments.
* Entry states: Anneal's `initLocalsAux` starts every non-argument local dead
  and `miriEntryState` mirrors it, whereas Miri starts locals without storage
  markers live.
* The eight open `known_anneal_bug` ratchets of
  `tests/miri-diff/manifest.toml`: `ub_transmute_invalid_bool_through_ptr`,
  `pass_ptr_offset_within_array`, `ub_ptr_offset_oob_read`,
  `ub_ptr_offset_oob_write`, `ub_ptr_offset_negative_before_start`,
  `ub_unaligned_ptr_read_u32`, `pass_direct_fn_call`, and
  `panic_explicit_macro`.

The multi-frame witnesses instantiate `annealStepHooksLM4_1` at the body of the
active `lean-miri` frame (`MiriDiffWitnesses.callHooks`), a function of the
`lean-miri` state alone; the `LM-4.1` per-step theorems instantiate it at
Anneal's `activeMirBody`.
-/

namespace LeanMiriSpec.Correspondence.Safety

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ## 1. Reachability of coalgebraic interaction trees (`ITree.cofix`) -/

section Coalgebra

universe u

variable {E : Effect.{u}} {R S : Type u} [FaultEffect E]

/-- One transition of the coalgebra `step`: a silent `.tau`, or a non-fault
visible request answered by any `o`. These are exactly the edges along which
`Trusted.ITree.Reaches` explores `ITree.cofix step`. -/
inductive CoStep (step : S → ITreeF E R S) : S → S → Prop where
  | tau {x y : S} : step x = .tau y → CoStep step x y
  | vis {x : S} {i : E.I} {k : E.O i → S} :
      step x = .vis i k → ¬ FaultEffect.isFault i → (o : E.O i) → CoStep step x (k o)

/-- Finite reachability under `CoStep`. -/
inductive CoReach (step : S → ITreeF E R S) : S → S → Prop where
  | refl (x : S) : CoReach step x x
  | head {x y z : S} : CoStep step x y → CoReach step y z → CoReach step x z

/-- A node that immediately emits a fault request. -/
def IsFaultNode (n : ITreeF E R S) : Prop :=
  ∃ i k, n = .vis i k ∧ FaultEffect.isFault i

namespace CoReach

variable {step : S → ITreeF E R S}

theorem tail {x y z : S} (h : CoReach step x y) (hs : CoStep step y z) : CoReach step x z := by
  induction h with
  | refl x => exact .head hs (.refl z)
  | head h₁ _ ih => exact .head h₁ (ih hs)

theorem trans {x y z : S} (h₁ : CoReach step x y) (h₂ : CoReach step y z) : CoReach step x z := by
  induction h₁ with
  | refl _ => exact h₂
  | head h _ ih => exact .head h (ih h₂)

end CoReach

omit [FaultEffect E] in
theorem observe_cofix_eq (step : S → ITreeF E R S) (x : S) :
    (ITree.cofix step x).observe = (step x).map (ITree.cofix step) :=
  ITree.observe_cofix step x

/-- Every residual reachable from `ITree.cofix step x` is the unfolding of a
`CoReach`-reachable coalgebra state. -/
theorem reaches_cofix_inv {step : S → ITreeF E R S} {x : S} {tr : List (Event E)}
    {u : ITree E R} (h : Reaches (ITree.cofix step x) tr u) :
    ∃ y, CoReach step x y ∧ u = ITree.cofix step y := by
  generalize ht : ITree.cofix step x = t at h
  induction h generalizing x with
  | refl t => exact ⟨x, .refl x, ht.symm⟩
  | tau hobs _ ih =>
    subst ht
    rw [observe_cofix_eq] at hobs
    cases hx : step x with
    | ret r => rw [hx] at hobs; cases hobs
    | tau y =>
      rw [hx] at hobs
      injection hobs with hobs
      obtain ⟨z, hz, rfl⟩ := ih hobs
      exact ⟨z, .head (.tau hx) hz, rfl⟩
    | vis i k => rw [hx] at hobs; cases hobs
  | vis hobs hnf o _ ih =>
    subst ht
    rw [observe_cofix_eq] at hobs
    cases hx : step x with
    | ret r => rw [hx] at hobs; cases hobs
    | tau y => rw [hx] at hobs; cases hobs
    | vis i' k' =>
      rw [hx] at hobs
      cases hobs
      obtain ⟨z, hz, rfl⟩ := ih rfl
      exact ⟨z, .head (.vis hx hnf o) hz, rfl⟩

/-- Silent prefixes of `ITree.cofix step y` are unfoldings of `CoReach`-reachable states. -/
theorem tauStar_cofix_inv {step : S → ITreeF E R S} {y : S} {t' : ITree E R}
    (h : TauStar (ITree.cofix step y) t') :
    ∃ y', CoReach step y y' ∧ t' = ITree.cofix step y' := by
  generalize ht : ITree.cofix step y = t at h
  induction h generalizing y with
  | refl t => exact ⟨y, .refl y, ht.symm⟩
  | step hobs _ ih =>
    subst ht
    rw [observe_cofix_eq] at hobs
    cases hx : step y with
    | ret r => rw [hx] at hobs; cases hobs
    | tau y₁ =>
      rw [hx] at hobs
      injection hobs with hobs
      obtain ⟨z, hz, rfl⟩ := ih hobs
      exact ⟨z, .head (.tau hx) hz, rfl⟩
    | vis i k => rw [hx] at hobs; cases hobs

/-- Every `CoReach`-reachable coalgebra state unfolds to a residual reachable
from `ITree.cofix step x` along some trace. -/
theorem reaches_cofix_of_coReach {step : S → ITreeF E R S} {x y : S}
    (h : CoReach step x y) : ∃ tr, Reaches (ITree.cofix step x) tr (ITree.cofix step y) := by
  induction h with
  | refl x => exact ⟨[], .refl _⟩
  | head hs _ ih =>
    obtain ⟨tr, htr⟩ := ih
    cases hs with
    | tau hx =>
      exact ⟨tr, .tau (by rw [observe_cofix_eq, hx]; rfl) htr⟩
    | vis hx hnf o =>
      exact ⟨⟨_, o⟩ :: tr, .vis (by rw [observe_cofix_eq, hx]; rfl) hnf o htr⟩

/-- `TreeSafe` of a coalgebraic tree is exactly the absence of reachable fault nodes. -/
theorem treeSafe_cofix_iff {step : S → ITreeF E R S} {x : S} :
    TreeSafe (ITree.cofix step x) ↔ ∀ y, CoReach step x y → ¬ IsFaultNode (step y) := by
  constructor
  · rintro hsafe y hy ⟨i, k, hyk, hf⟩
    obtain ⟨tr, htr⟩ := reaches_cofix_of_coReach hy
    exact hsafe tr _ htr
      ⟨ITree.cofix step y, i, fun o => ITree.cofix step (k o), .refl _,
        by rw [observe_cofix_eq, hyk]; rfl, hf⟩
  · rintro h tr u hr ⟨t', i, k, hts, hobs, hf⟩
    obtain ⟨y, hy, rfl⟩ := reaches_cofix_inv hr
    obtain ⟨y', hy', rfl⟩ := tauStar_cofix_inv hts
    rw [observe_cofix_eq] at hobs
    cases hx : step y' with
    | ret r => rw [hx] at hobs; cases hobs
    | tau z => rw [hx] at hobs; cases hobs
    | vis i' k' =>
      rw [hx] at hobs
      cases hobs
      exact h y' (hy.trans hy') ⟨_, _, hx, hf⟩

/-- A coalgebraic tree reaches `.ret r` iff some reachable state returns `r`. -/
theorem reachesRet_cofix_iff {step : S → ITreeF E R S} {x : S} {r : R} :
    (∃ tr, ReachesRet (ITree.cofix step x) tr r) ↔ ∃ y, CoReach step x y ∧ step y = .ret r := by
  constructor
  · rintro ⟨tr, u, hr, hobs⟩
    obtain ⟨y, hy, rfl⟩ := reaches_cofix_inv hr
    rw [observe_cofix_eq] at hobs
    cases hx : step y with
    | ret r' =>
      rw [hx] at hobs
      injection hobs with hobs
      subst hobs
      exact ⟨y, hy, hx⟩
    | tau z => rw [hx] at hobs; cases hobs
    | vis i k => rw [hx] at hobs; cases hobs
  · rintro ⟨y, hy, hret⟩
    obtain ⟨tr, htr⟩ := reaches_cofix_of_coReach hy
    exact ⟨tr, _, htr, by rw [observe_cofix_eq, hret]; rfl⟩

end Coalgebra

/-! ## 2. `lean-miri` whole-program semantics over `RunLoop` (`miriSystem`) -/

/-- An Anneal-instantiated `lean-miri` interpreter: one `Step.step` driver
iteration (`coreStep`) and the root frame's return-operand read
(`ControlHooks.returnOperand`, which `ControlFlow.returnFromCurrentFrame` performs
before popping a frame). -/
structure AnnealMiriHooks : Type where
  coreStep : Unit → AnnealStepState → Miri.Interpreter.StepResult AnnealStepState Bool
  returnOperand : Unit → AnnealStepState →
    Miri.Interpreter.StepResult AnnealStepState (Miri.Interpreter.Operand AnnealProv)

/-- Package `StepHooks` and `ControlHooks` as an `AnnealMiriHooks` interpreter. -/
def AnnealMiriHooks.ofHooks {PV : Type}
    (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine
      Unit PV)
    (control : Miri.Interpreter.ControlHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.Operand AnnealProv)) : AnnealMiriHooks where
  coreStep := Miri.Interpreter.Step.step hooks
  returnOperand := control.returnOperand

/-- The `LM-1` / `LM-3` / `LM-4.2` interpreter (`annealStepHooks`, `annealControlHooks`). -/
def annealMiriHooks (body : CapturedMir) : AnnealMiriHooks :=
  .ofHooks (annealStepHooks body.localDecls body.layouts) annealControlHooks

/-- `RunLoopHooks` of Anneal's single-threaded machine around `H.coreStep`.

The machine has one thread and no I/O: it is never interrupted, the scheduler
always executes a step, and nothing sleeps or polls. When the active stack is
empty the main thread has no pending callback (`StackEmptyPoll.ready`), and
terminating it stops the program with `TerminationInfo.exit 0 true`. -/
def annealRunLoopHooks (H : AnnealMiriHooks) :
    Miri.Interpreter.RunLoopHooks AnnealStepState Unit Unit where
  coreStep := H.coreStep
  takeStackEmptyCallback := fun s => (s, .ok ())
  invokeStackEmptyCallback := fun _ _ s => (s, .ok .ready)
  restoreStackEmptyCallback := fun _ s => (s, .ok ())
  terminateActiveThread := fun _ _ s => (s, .error (.termination (.exit 0 true)))
  interrupted := fun _ => false
  handleAbnormalTermination := fun s => s
  schedule := fun _ s => (s, .ok .executeStep)
  communicate := fun _ => false
  pollAndUnblock := fun _ _ s => (s, .ok ())
  sleep := fun _ _ s => (s, .ok ())

/-- One `RunLoop.iteration` of `lean-miri`'s scheduler on Anneal's machine. -/
def miriIter (H : AnnealMiriHooks) (m : AnnealStepState) :
    Miri.Interpreter.StepResult AnnealStepState Unit :=
  Miri.Interpreter.RunLoop.iteration (annealRunLoopHooks H) () m

/-- The result of `RunLoop.stepCurrentThread` as a function of the core step's result. -/
def stepToIteration :
    Miri.Interpreter.StepResult AnnealStepState Bool →
      Miri.Interpreter.StepResult AnnealStepState Unit
  | (m', .ok true) => (m', .ok ())
  | (m', .ok false) => (m', .error (.termination (.exit 0 true)))
  | (m', .error e) => (m', .error e)

/-- `RunLoop.iteration` (through `RunLoop.stepCurrentThread` and
`RunLoop.runOnStackEmpty`) of `annealRunLoopHooks H`. -/
theorem miriIter_eq (H : AnnealMiriHooks) (m : AnnealStepState) :
    miriIter H m = stepToIteration (H.coreStep () m) := by
  obtain ⟨core, ret⟩ := H
  unfold miriIter Miri.Interpreter.RunLoop.iteration Miri.Interpreter.RunLoop.stepCurrentThread
    Miri.Interpreter.RunLoop.runOnStackEmpty
  dsimp only [annealRunLoopHooks]
  rcases core () m with ⟨m', (e | (_ | _))⟩ <;> rfl

/-- `lean-miri` errors that report an unsupported operation. -/
def isUnsupportedError : Miri.Interpreter.StepError → Bool
  | .unsupported _ => true
  | .termination (.unsupportedInIsolation _) => true
  | .termination (.unsupportedForeignItem _) => true
  | _ => false

/-- Terminal outcomes of `miriSystem`: the root frame's return operand, the
undefined-behavior error, or the unsupported / blocked error. -/
abbrev MiriSafetyOutcome : Type :=
  Miri.OperationalSafety.Outcome (Miri.Interpreter.Operand AnnealProv) Miri.Interpreter.StepError
    Miri.Interpreter.StepError

/-- Classification of a `lean-miri` error: undefined behavior exactly when
`RunLoop.reportsUB` holds, unsupported for `isUnsupportedError`, and blocked
otherwise. -/
def classifyError (e : Miri.Interpreter.StepError) : MiriSafetyOutcome :=
  if Miri.Interpreter.RunLoop.reportsUB e = true then .undefinedBehavior e
  else if isUnsupportedError e = true then .unsupported e
  else .blocked e

theorem classifyError_not_isReturn (e : Miri.Interpreter.StepError) :
    ¬ (classifyError e).isReturn := by
  unfold classifyError
  split
  · exact id
  · split <;> exact id

theorem classifyError_ne_returned (e : Miri.Interpreter.StepError)
    (v : Miri.Interpreter.Operand AnnealProv) : classifyError e ≠ .returned v := by
  intro h
  have := classifyError_not_isReturn e
  rw [h] at this
  exact this trivial

theorem classifyError_eq_ub_iff {e e' : Miri.Interpreter.StepError} :
    classifyError e = .undefinedBehavior e' ↔
      Miri.Interpreter.RunLoop.reportsUB e = true ∧ e' = e := by
  unfold classifyError
  split
  · next h => exact ⟨fun h' => ⟨h, by injection h' with h'; exact h'.symm⟩,
      fun ⟨_, h'⟩ => by rw [h']⟩
  · next h =>
    constructor
    · intro h'; split at h' <;> cases h'
    · intro ⟨h', _⟩; exact absurd h' h

/-- Whole-program `Miri.OperationalSafety.System` of `lean-miri`'s interpreter on
Anneal's machine.

* A transition is one `RunLoop.iteration` that succeeds and leaves a nonempty
  call stack.
* An iteration that fails with `e` is terminal with outcome `classifyError e`.
* An iteration that succeeds and empties the call stack popped the root frame:
  it is terminal with outcome `.returned v`, where `v` is the return operand
  `ControlHooks.returnOperand` read from the root frame's `_0`. -/
def miriSystem (H : AnnealMiriHooks) :
    Miri.OperationalSafety.System AnnealStepState (Miri.Interpreter.Operand AnnealProv)
      Miri.Interpreter.StepError Miri.Interpreter.StepError where
  step m m' := miriIter H m = (m', .ok ()) ∧ m'.stack.frames ≠ #[]
  terminal m o :=
    (∃ e, (miriIter H m).2 = .error e ∧ o = classifyError e) ∨
    (∃ v, (miriIter H m).2 = .ok () ∧ (miriIter H m).1.stack.frames = #[] ∧
      (H.returnOperand () m).2 = .ok v ∧ o = .returned v)

section MiriSystemFacts

variable {H : AnnealMiriHooks}

theorem miriSystem_step_iff {m m' : AnnealStepState} :
    (miriSystem H).step m m' ↔ miriIter H m = (m', .ok ()) ∧ m'.stack.frames ≠ #[] :=
  Iff.rfl

theorem miriSystem_step_det {m m₁ m₂ : AnnealStepState}
    (h₁ : (miriSystem H).step m m₁) (h₂ : (miriSystem H).step m m₂) : m₁ = m₂ := by
  have := h₁.1.symm.trans h₂.1
  injection this

theorem miriSystem_not_terminal_of_ok_nonempty {m m' : AnnealStepState}
    (hm : miriIter H m = (m', .ok ())) (hne : m'.stack.frames ≠ #[]) (o : MiriSafetyOutcome) :
    ¬ (miriSystem H).terminal m o := by
  rintro (⟨e, he, _⟩ | ⟨v, _, hemp, _, _⟩)
  · rw [hm] at he; cases he
  · rw [hm] at hemp; exact hne hemp

theorem miriSystem_terminal_of_ok_empty {m m' : AnnealStepState}
    (hm : miriIter H m = (m', .ok ())) (hemp : m'.stack.frames = #[]) (o : MiriSafetyOutcome) :
    (miriSystem H).terminal m o ↔ ∃ v, (H.returnOperand () m).2 = .ok v ∧ o = .returned v := by
  constructor
  · rintro (⟨e, he, _⟩ | ⟨v, _, _, hv, ho⟩)
    · rw [hm] at he; cases he
    · exact ⟨v, hv, ho⟩
  · rintro ⟨v, hv, ho⟩
    exact Or.inr ⟨v, by rw [hm], by rw [hm]; exact hemp, hv, ho⟩

theorem miriSystem_terminal_of_error {m m' : AnnealStepState} {e : Miri.Interpreter.StepError}
    (hm : miriIter H m = (m', .error e)) (o : MiriSafetyOutcome) :
    (miriSystem H).terminal m o ↔ o = classifyError e := by
  constructor
  · rintro (⟨e', he', ho⟩ | ⟨v, hv, _, _, _⟩)
    · rw [hm] at he'; injection he' with he'; subst he'; exact ho
    · rw [hm] at hv; cases hv
  · intro ho
    exact Or.inl ⟨e, by rw [hm], ho⟩

theorem miriSystem_not_step_of_error {m m' m'' : AnnealStepState} {e : Miri.Interpreter.StepError}
    (hm : miriIter H m = (m', .error e)) : ¬ (miriSystem H).step m m'' := by
  rintro ⟨h, _⟩
  rw [hm] at h; cases h

theorem miriSystem_not_step_of_ok_empty {m m' m'' : AnnealStepState}
    (hm : miriIter H m = (m', .ok ())) (hemp : m'.stack.frames = #[]) :
    ¬ (miriSystem H).step m m'' := by
  rintro ⟨h, hne⟩
  rw [hm] at h
  injection h with h
  subst h
  exact hne hemp

/-- `System.Reaches` composed with a leading transition. -/
theorem miriSystem_reaches_head {a b c : AnnealStepState} (hab : (miriSystem H).step a b)
    (hbc : (miriSystem H).Reaches b c) : (miriSystem H).Reaches a c := by
  induction hbc with
  | refl => exact .step (.refl a) hab
  | step _ hs ih => exact .step ih hs

/-- In the deterministic `miriSystem`, every state reachable from `a` is `a`
itself or reachable from `a`'s unique successor. -/
theorem miriSystem_reaches_cases {a b c : AnnealStepState} (hab : (miriSystem H).step a b)
    (hac : (miriSystem H).Reaches a c) : c = a ∨ (miriSystem H).Reaches b c := by
  induction hac with
  | refl => exact Or.inl rfl
  | step hr hs ih =>
    rcases ih with rfl | hbr
    · exact Or.inr (by rw [miriSystem_step_det hs hab]; exact .refl _)
    · exact Or.inr (.step hbr hs)

/-- A state without a successor reaches only itself. -/
theorem miriSystem_reaches_of_no_step {a c : AnnealStepState}
    (hno : ∀ b, ¬ (miriSystem H).step a b) (hac : (miriSystem H).Reaches a c) : c = a := by
  induction hac with
  | refl => rfl
  | step _ hs ih => subst ih; exact absurd hs (hno _)

end MiriSystemFacts

/-! ## 3. Anneal's MIR coalgebra (`stepMirState`) -/

/-- Some finitely reachable residual of `t` immediately emits the
undefined-behavior fault `FailureKind.ub`. -/
def MirReachesUB (t : ITree MirEffect MirOutcome) : Prop :=
  ∃ tr u k, Reaches t tr u ∧ u.observe = .vis (.inl (.fail .ub)) k

theorem mir_isFault_inl (e : MirFailE.I) :
    FaultEffect.isFault (E := MirEffect) (.inl e) := trivial

theorem mir_not_isFault_inr (e : (SumE MirObsE MirCallE).I) :
    ¬ FaultEffect.isFault (E := MirEffect) (.inr e) := by
  rcases e with e | e <;> exact id

theorem isFaultNode_fail (k : FailureKind) :
    IsFaultNode (MirStepNode.fail k) :=
  ⟨.inl (.fail k), PEmpty.elim, rfl, mir_isFault_inl _⟩

theorem not_isFaultNode_emitStep (obs : MirObs) (s' : MachineState) :
    ¬ IsFaultNode (MirStepNode.emitStep obs s') := by
  rintro ⟨i, k, h, hf⟩
  cases obs with
  | silent => cases h
  | event tag =>
    simp only [MirStepNode.emitStep] at h
    cases h
    exact mir_not_isFault_inr _ hf

theorem not_isFaultNode_retNormal (v : Value) (mem : Memory) :
    ¬ IsFaultNode (MirStepNode.retNormal v mem) := by
  rintro ⟨i, k, h, _⟩
  cases h

theorem mirTree_eq_cofix (body : CapturedMir) (s : MachineState) :
    mirTree body s = ITree.cofix (stepMirState body) (.running s) := rfl

section NodeShapes

variable {body : CapturedMir} {s : MachineState}

theorem coStep_of_emitStep {obs : MirObs} {s' : MachineState}
    (hs : stepMirFn body s = .emitStep obs s') :
    CoStep (stepMirState body) (.running s) (.running s') := by
  cases obs with
  | silent => exact .tau hs
  | event tag =>
    have h : stepMirState body (.running s) =
        .vis (.inr (.inl (.emit (.event tag)))) (fun _ => .running s') := hs
    exact .vis h (mir_not_isFault_inr _) PUnit.unit

theorem coStep_emitStep_inv {obs : MirObs} {s' : MachineState} {y : MirExecState}
    (hs : stepMirFn body s = .emitStep obs s')
    (hy : CoStep (stepMirState body) (.running s) y) : y = .running s' := by
  cases hy with
  | tau h =>
    change stepMirFn body s = _ at h
    rw [hs] at h
    cases obs with
    | silent => injection h with h; exact h.symm
    | event tag => simp only [MirStepNode.emitStep] at h; cases h
  | vis h _ o =>
    change stepMirFn body s = _ at h
    rw [hs] at h
    cases obs with
    | silent => cases h
    | event tag =>
      simp only [MirStepNode.emitStep] at h
      cases h
      rfl

theorem not_coStep_retNormal {v : Value} {mem : Memory} {y : MirExecState}
    (hs : stepMirFn body s = .retNormal v mem) :
    ¬ CoStep (stepMirState body) (.running s) y := by
  intro hy
  cases hy with
  | tau h => change stepMirFn body s = _ at h; rw [hs] at h; cases h
  | vis h _ _ => change stepMirFn body s = _ at h; rw [hs] at h; cases h

theorem not_coStep_fail {k : FailureKind} {y : MirExecState}
    (hs : stepMirFn body s = .fail k) :
    ¬ CoStep (stepMirState body) (.running s) y := by
  intro hy
  cases hy with
  | tau h => change stepMirFn body s = _ at h; rw [hs] at h; cases h
  | vis h hnf _ =>
    change stepMirFn body s = _ at h
    rw [hs] at h
    cases h
    exact hnf (mir_isFault_inl _)

end NodeShapes

/-! ## 4. Step-closed simulation engine (`StepClosedSim`) -/

/-- Anneal's fault kind and `lean-miri`'s error agree on undefined behavior. -/
def FaultAgrees (k : FailureKind) (e : Miri.Interpreter.StepError) : Prop :=
  (k = .ub ↔ Miri.Interpreter.RunLoop.reportsUB e = true)

/-- One-step lockstep correspondence, relative to a state invariant `Inv` and a
return-value relation `RetRel`, between Anneal's `stepMirFn` result and
`lean-miri`'s core-step result from `m`:

* both continue within the program, Anneal emitting `obs`, to an
  `Inv`-related pair with a nonempty `lean-miri` stack;
* Anneal returns normally from the root frame while `lean-miri` pops it, with
  `RetRel`-related return value and return operand; or
* both fail, agreeing on whether the failure is undefined behavior. -/
inductive Lockstep (H : AnnealMiriHooks) (Inv : MachineState → AnnealStepState → Prop)
    (RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop) (m : AnnealStepState) :
    MirStepNode → Miri.Interpreter.StepResult AnnealStepState Bool → Prop where
  | emitStep (obs : MirObs) (s' : MachineState) (m' : AnnealStepState) :
      Inv s' m' → m'.stack.frames ≠ #[] →
      Lockstep H Inv RetRel m (MirStepNode.emitStep obs s') (m', .ok true)
  | retRoot (retVal : Value) (mem' : Memory) (m' : AnnealStepState)
      (v : Miri.Interpreter.Operand AnnealProv) :
      m'.stack.frames = #[] → (H.returnOperand () m).2 = .ok v → RetRel retVal v →
      Lockstep H Inv RetRel m (MirStepNode.retNormal retVal mem') (m', .ok true)
  | fault (k : FailureKind) (m' : AnnealStepState) (e : Miri.Interpreter.StepError) :
      FaultAgrees k e →
      Lockstep H Inv RetRel m (MirStepNode.fail k) (m', .error e)

/-- `Inv` is closed under single-step lockstep simulation of `stepMirFn body`
and `H.coreStep`: from every `Inv`-related pair, the two machines take one
`Lockstep`-related step. -/
structure StepClosedSim (body : CapturedMir) (H : AnnealMiriHooks)
    (Inv : MachineState → AnnealStepState → Prop)
    (RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop) : Prop where
  lockstep : ∀ s m, Inv s m → Lockstep H Inv RetRel m (stepMirFn body s) (H.coreStep () m)

section Engine

variable {body : CapturedMir} {H : AnnealMiriHooks}
  {Inv : MachineState → AnnealStepState → Prop}
  {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}

/-- The three lockstep shapes, read off through `RunLoop.iteration`. -/
theorem lockstep_shapes (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) :
    (∃ obs s' m', stepMirFn body s = .emitStep obs s' ∧ miriIter H m = (m', .ok ()) ∧
      m'.stack.frames ≠ #[] ∧ Inv s' m') ∨
    (∃ retVal mem m' v, stepMirFn body s = .retNormal retVal mem ∧
      miriIter H m = (m', .ok ()) ∧ m'.stack.frames = #[] ∧
      (H.returnOperand () m).2 = .ok v ∧ RetRel retVal v) ∨
    (∃ k m' e, stepMirFn body s = .fail k ∧ miriIter H m = (m', .error e) ∧ FaultAgrees k e) := by
  have h := hsim.lockstep s m hinv
  generalize ha : stepMirFn body s = aRes at h
  generalize hc : H.coreStep () m = mRes at h
  cases h with
  | emitStep obs s' m' hinv' hne =>
    exact Or.inl ⟨obs, s', m', rfl, by rw [miriIter_eq, hc]; rfl, hne, hinv'⟩
  | retRoot retVal mem m' v hemp hop hrel =>
    exact Or.inr (Or.inl ⟨retVal, mem, m', v, rfl, by rw [miriIter_eq, hc]; rfl, hemp, hop, hrel⟩)
  | fault k m' e hag =>
    exact Or.inr (Or.inr ⟨k, m', e, rfl, by rw [miriIter_eq, hc]; rfl, hag⟩)

/-- Forward simulation: every Anneal coalgebra transition from an `Inv`-related
pair is matched by a `miriSystem` transition to an `Inv`-related pair. -/
theorem forward_step (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) {y : MirExecState}
    (hy : CoStep (stepMirState body) (.running s) y) :
    ∃ s' m', y = .running s' ∧ Inv s' m' ∧ (miriSystem H).step m m' := by
  rcases lockstep_shapes hsim hinv with
    ⟨obs, s', m', ha, hm, hne, hinv'⟩ | ⟨_, _, _, _, ha, _⟩ | ⟨_, _, _, ha, _⟩
  · exact ⟨s', m', coStep_emitStep_inv ha hy, hinv', hm, hne⟩
  · exact absurd hy (not_coStep_retNormal ha)
  · exact absurd hy (not_coStep_fail ha)

/-- Backward simulation: every `miriSystem` transition from an `Inv`-related
pair is matched by an Anneal coalgebra transition to an `Inv`-related pair. -/
theorem backward_step (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m m' : AnnealStepState} (hinv : Inv s m) (hm : (miriSystem H).step m m') :
    ∃ s', CoStep (stepMirState body) (.running s) (.running s') ∧ Inv s' m' := by
  rcases lockstep_shapes hsim hinv with
    ⟨obs, s', m'', ha, hm', _, hinv'⟩ | ⟨_, _, _, _, _, hm', hemp, _⟩ | ⟨_, _, _, _, hm', _⟩
  · have : m'' = m' := by
      have := hm'.symm.trans hm.1
      injection this
    subst this
    exact ⟨s', coStep_of_emitStep ha, hinv'⟩
  · exact absurd hm (miriSystem_not_step_of_ok_empty hm' hemp)
  · exact absurd hm (miriSystem_not_step_of_error hm')

/-- Every Anneal state reachable from an `Inv`-related pair is a running state
`Inv`-related to a `miriSystem`-reachable state. -/
theorem coReach_to_miri (hsim : StepClosedSim body H Inv RetRel) {x y : MirExecState}
    (h : CoReach (stepMirState body) x y) :
    ∀ {s m}, x = .running s → Inv s m →
      ∃ s' m', y = .running s' ∧ Inv s' m' ∧ (miriSystem H).Reaches m m' := by
  induction h with
  | refl x => intro s m hx hinv; exact ⟨s, m, hx, hinv, .refl m⟩
  | head hs _ ih =>
    intro s m hx hinv
    subst hx
    obtain ⟨s₁, m₁, rfl, hinv₁, hstep₁⟩ := forward_step hsim hinv hs
    obtain ⟨s', m', hy, hinv', hr⟩ := ih rfl hinv₁
    exact ⟨s', m', hy, hinv', miriSystem_reaches_head hstep₁ hr⟩

/-- Every `miriSystem` state reachable from an `Inv`-related pair is
`Inv`-related to an Anneal state reachable from the running Anneal state. -/
theorem miri_to_coReach (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m m' : AnnealStepState} (hinv : Inv s m) (h : (miriSystem H).Reaches m m') :
    ∃ s', CoReach (stepMirState body) (.running s) (.running s') ∧ Inv s' m' := by
  induction h with
  | refl => exact ⟨s, .refl _, hinv⟩
  | step _ hstep ih =>
    obtain ⟨s₁, hco, hinv₁⟩ := ih
    obtain ⟨s', hs', hinv'⟩ := backward_step hsim hinv₁ hstep
    exact ⟨s', hco.tail hs', hinv'⟩

/-- **Master small-step theorem.** From an `Inv`-related pair `(s, m)`:

1. every Anneal coalgebra transition is matched by a `miriSystem` transition
   (one `RunLoop.iteration`) to an `Inv`-related pair, and conversely;
2. Anneal faults iff `lean-miri` reaches a non-return terminal outcome;
3. Anneal faults with undefined behavior iff `lean-miri` reports undefined
   behavior (`RunLoop.reportsUB`);
4. Anneal returns normally iff `lean-miri` pops the root frame with a
   `RetRel`-related return operand. -/
theorem step_universal_simulation (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) :
    (∀ y, CoStep (stepMirState body) (.running s) y →
      ∃ s' m', y = .running s' ∧ Inv s' m' ∧ (miriSystem H).step m m') ∧
    (∀ m', (miriSystem H).step m m' →
      ∃ s', CoStep (stepMirState body) (.running s) (.running s') ∧ Inv s' m') ∧
    ((∃ k, stepMirFn body s = .fail k) ↔
      ∃ o, (miriSystem H).terminal m o ∧ ¬ o.isReturn) ∧
    (stepMirFn body s = .fail .ub ↔
      ∃ e, (miriSystem H).terminal m (.undefinedBehavior e)) ∧
    ((∃ retVal mem, stepMirFn body s = .retNormal retVal mem) ↔
      ∃ v, (miriSystem H).terminal m (.returned v)) ∧
    (∀ v, (miriSystem H).terminal m (.returned v) →
      ∃ retVal mem, stepMirFn body s = .retNormal retVal mem ∧ RetRel retVal v) := by
  refine ⟨fun y hy => forward_step hsim hinv hy, fun m' hm => backward_step hsim hinv hm,
    ?_, ?_, ?_, ?_⟩
  · rcases lockstep_shapes hsim hinv with
      ⟨obs, s', m', ha, hm, hne, _⟩ | ⟨retVal, mem, m', v, ha, hm, hemp, hop, _⟩ |
        ⟨k, m', e, ha, hm, _⟩
    · refine ⟨fun ⟨k, hk⟩ => ?_, fun ⟨o, ho, _⟩ => ?_⟩
      · rw [ha] at hk; cases obs <;> cases hk
      · exact absurd ho (miriSystem_not_terminal_of_ok_nonempty hm hne o)
    · refine ⟨fun ⟨k, hk⟩ => ?_, fun ⟨o, ho, hnr⟩ => ?_⟩
      · rw [ha] at hk; cases hk
      · obtain ⟨v', _, rfl⟩ := (miriSystem_terminal_of_ok_empty hm hemp o).1 ho
        exact absurd trivial hnr
    · exact ⟨fun _ => ⟨classifyError e, (miriSystem_terminal_of_error hm _).2 rfl,
        classifyError_not_isReturn e⟩, fun _ => ⟨k, ha⟩⟩
  · rcases lockstep_shapes hsim hinv with
      ⟨obs, s', m', ha, hm, hne, _⟩ | ⟨retVal, mem, m', v, ha, hm, hemp, hop, _⟩ |
        ⟨k, m', e, ha, hm, hag⟩
    · refine ⟨fun hk => ?_, fun ⟨e, he⟩ => ?_⟩
      · rw [ha] at hk; cases obs <;> cases hk
      · exact absurd he (miriSystem_not_terminal_of_ok_nonempty hm hne _)
    · refine ⟨fun hk => ?_, fun ⟨e, he⟩ => ?_⟩
      · rw [ha] at hk; cases hk
      · obtain ⟨v', _, h⟩ := (miriSystem_terminal_of_ok_empty hm hemp _).1 he
        cases h
    · rw [ha]
      constructor
      · intro hk
        injection hk with hk
        injection hk with hk
        injection hk with hk
        have hub : Miri.Interpreter.RunLoop.reportsUB e = true := hag.1 hk
        exact ⟨e, (miriSystem_terminal_of_error hm _).2
          (classifyError_eq_ub_iff.2 ⟨hub, rfl⟩).symm⟩
      · rintro ⟨e', he'⟩
        have h := (miriSystem_terminal_of_error hm _).1 he'
        have := (classifyError_eq_ub_iff.1 h.symm).1
        rw [hag.2 this]
  · rcases lockstep_shapes hsim hinv with
      ⟨obs, s', m', ha, hm, hne, _⟩ | ⟨retVal, mem, m', v, ha, hm, hemp, hop, _⟩ |
        ⟨k, m', e, ha, hm, _⟩
    · refine ⟨fun ⟨_, _, hk⟩ => ?_, fun ⟨v, hv⟩ => ?_⟩
      · rw [ha] at hk; cases obs <;> cases hk
      · exact absurd hv (miriSystem_not_terminal_of_ok_nonempty hm hne _)
    · exact ⟨fun _ => ⟨v, (miriSystem_terminal_of_ok_empty hm hemp _).2 ⟨v, hop, rfl⟩⟩,
        fun _ => ⟨retVal, mem, ha⟩⟩
    · refine ⟨fun ⟨_, _, hk⟩ => ?_, fun ⟨v, hv⟩ => ?_⟩
      · rw [ha] at hk; cases hk
      · exact absurd ((miriSystem_terminal_of_error hm _).1 hv).symm (classifyError_ne_returned e v)
  · intro v hv
    rcases lockstep_shapes hsim hinv with
      ⟨obs, s', m', ha, hm, hne, _⟩ | ⟨retVal, mem, m', v', ha, hm, hemp, hop, hrel⟩ |
        ⟨k, m', e, ha, hm, _⟩
    · exact absurd hv (miriSystem_not_terminal_of_ok_nonempty hm hne _)
    · obtain ⟨v'', hv'', h⟩ := (miriSystem_terminal_of_ok_empty hm hemp _).1 hv
      injection h with h
      subst h
      rw [hop] at hv''
      injection hv'' with hv''
      subst hv''
      exact ⟨retVal, mem, ha, hrel⟩
    · exact absurd ((miriSystem_terminal_of_error hm _).1 hv).symm (classifyError_ne_returned e v)

end Engine

/-! ## 5. Whole-program equivalence: `TreeSafe ↔ System.Safe`, UB, partial correctness -/

section WholeProgram

variable {body : CapturedMir} {H : AnnealMiriHooks}
  {Inv : MachineState → AnnealStepState → Prop}
  {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}

/-- Anneal tree safety implies `lean-miri` whole-program safety. -/
theorem treeSafe_imp_miriSafe (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) (hsafe : TreeSafe (mirTree body s)) :
    (miriSystem H).Safe m := by
  rw [mirTree_eq_cofix, treeSafe_cofix_iff] at hsafe
  refine ⟨fun m' hr => ?_, fun o ⟨final, hr, hterm⟩ => ?_⟩
  · obtain ⟨s', hco, hinv'⟩ := miri_to_coReach hsim hinv hr
    rcases lockstep_shapes hsim hinv' with
      ⟨_, _, m'', _, hm, hne, _⟩ | ⟨_, _, _, v, _, hm, hemp, hop, _⟩ | ⟨k, _, _, ha, _, _⟩
    · exact Or.inl ⟨m'', hm, hne⟩
    · exact Or.inr ⟨.returned v, (miriSystem_terminal_of_ok_empty hm hemp _).2 ⟨v, hop, rfl⟩⟩
    · exact absurd (show IsFaultNode (stepMirState body (.running s')) by
        change IsFaultNode (stepMirFn body s'); rw [ha]; exact isFaultNode_fail k) (hsafe _ hco)
  · obtain ⟨s', hco, hinv'⟩ := miri_to_coReach hsim hinv hr
    rcases lockstep_shapes hsim hinv' with
      ⟨_, _, _, _, hm, hne, _⟩ | ⟨_, _, _, _, _, hm, hemp, _, _⟩ | ⟨k, _, _, ha, _, _⟩
    · exact absurd hterm (miriSystem_not_terminal_of_ok_nonempty hm hne _)
    · obtain ⟨v, _, rfl⟩ := (miriSystem_terminal_of_ok_empty hm hemp _).1 hterm
      trivial
    · exact absurd (show IsFaultNode (stepMirState body (.running s')) by
        change IsFaultNode (stepMirFn body s'); rw [ha]; exact isFaultNode_fail k) (hsafe _ hco)

/-- `lean-miri` whole-program safety implies Anneal tree safety. -/
theorem miriSafe_imp_treeSafe (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) (hsafe : (miriSystem H).Safe m) :
    TreeSafe (mirTree body s) := by
  rw [mirTree_eq_cofix, treeSafe_cofix_iff]
  intro y hy hfault
  obtain ⟨s', m', rfl, hinv', hr⟩ := coReach_to_miri hsim hy rfl hinv
  rcases lockstep_shapes hsim hinv' with
    ⟨obs, s'', _, ha, _, _, _⟩ | ⟨retVal, mem, _, _, ha, _⟩ | ⟨_, _, e, _, hm, _⟩
  · exact not_isFaultNode_emitStep obs s'' (ha ▸ hfault)
  · exact not_isFaultNode_retNormal retVal mem (ha ▸ hfault)
  · exact classifyError_not_isReturn e
      (hsafe.2 _ ⟨m', hr, (miriSystem_terminal_of_error hm _).2 rfl⟩)

/-- **Whole-program safety equivalence.** Under a step-closed simulation,
Anneal's all-prefix UB-freedom of `mirTree body s` (`TreeSafe`, i.e.
`MirNoUBTree`) holds iff `lean-miri`'s `RunLoop` semantics is
`Miri.OperationalSafety.System.Safe` from the related state `m`. -/
theorem treeSafe_iff_miriSafe (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) :
    TreeSafe (mirTree body s) ↔ (miriSystem H).Safe m :=
  ⟨treeSafe_imp_miriSafe hsim hinv, miriSafe_imp_treeSafe hsim hinv⟩

/-- `MirNoUBTree` form of `treeSafe_iff_miriSafe`. -/
theorem mirNoUBTree_iff_miriSafe (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) :
    MirNoUBTree (mirTree body s) ↔ (miriSystem H).Safe m :=
  treeSafe_iff_miriSafe hsim hinv

/-- Anneal tree safety implies `lean-miri`'s UB freedom. -/
theorem treeSafe_imp_noUndefinedBehavior (hsim : StepClosedSim body H Inv RetRel)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m)
    (hsafe : TreeSafe (mirTree body s)) : (miriSystem H).NoUndefinedBehavior m :=
  Miri.OperationalSafety.System.noUndefinedBehavior_of_safe _
    (treeSafe_imp_miriSafe hsim hinv hsafe)

/-- **Bidirectional finite-step UB reachability.** Some finitely reachable
residual of `mirTree body s` emits Anneal's undefined-behavior fault iff
`lean-miri` reaches an undefined-behavior outcome. -/
theorem reachesUB_iff_miriReachesUB (hsim : StepClosedSim body H Inv RetRel)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m) :
    MirReachesUB (mirTree body s) ↔ ∃ e, (miriSystem H).ReachesOutcome m (.undefinedBehavior e) := by
  rw [mirTree_eq_cofix]
  constructor
  · rintro ⟨tr, u, k, hr, hobs⟩
    obtain ⟨y, hy, rfl⟩ := reaches_cofix_inv hr
    obtain ⟨s', m', rfl, hinv', hreach⟩ := coReach_to_miri hsim hy rfl hinv
    rw [observe_cofix_eq] at hobs
    rcases lockstep_shapes hsim hinv' with
      ⟨obs, _, _, ha, _⟩ | ⟨_, _, _, _, ha, _⟩ | ⟨k', _, e, ha, hm, hag⟩
    · change (stepMirFn body s').map _ = _ at hobs
      rw [ha] at hobs
      cases obs with
      | silent => cases hobs
      | event tag => simp only [MirStepNode.emitStep, ITreeF.map] at hobs; cases hobs
    · change (stepMirFn body s').map _ = _ at hobs
      rw [ha] at hobs; cases hobs
    · change (stepMirFn body s').map _ = _ at hobs
      rw [ha] at hobs
      simp only [MirStepNode.fail, ITreeF.map] at hobs
      cases hobs
      have hub : Miri.Interpreter.RunLoop.reportsUB e = true := hag.1 rfl
      exact ⟨e, m', hreach, (miriSystem_terminal_of_error hm _).2
        (classifyError_eq_ub_iff.2 ⟨hub, rfl⟩).symm⟩
  · rintro ⟨e, final, hr, hterm⟩
    obtain ⟨s', hco, hinv'⟩ := miri_to_coReach hsim hinv hr
    rcases lockstep_shapes hsim hinv' with
      ⟨_, _, _, _, hm, hne, _⟩ | ⟨_, _, _, _, _, hm, hemp, _, _⟩ | ⟨k, _, e', ha, hm, hag⟩
    · exact absurd hterm (miriSystem_not_terminal_of_ok_nonempty hm hne _)
    · obtain ⟨_, _, h⟩ := (miriSystem_terminal_of_ok_empty hm hemp _).1 hterm
      cases h
    · have h := (miriSystem_terminal_of_error hm _).1 hterm
      have hk : k = .ub := hag.2 (classifyError_eq_ub_iff.1 h.symm).1
      subst hk
      obtain ⟨tr, htr⟩ := reaches_cofix_of_coReach hco
      have hobs : (ITree.cofix (stepMirState body) (.running s')).observe =
          .vis (.inl (.fail .ub)) (fun o => ITree.cofix (stepMirState body) (PEmpty.elim o)) := by
        rw [observe_cofix_eq]
        change (stepMirFn body s').map _ = _
        rw [ha]
        rfl
      exact ⟨tr, _, _, htr, hobs⟩

/-- Anneal tree safety excludes reachable Anneal undefined behavior. -/
theorem not_reachesUB_of_treeSafe {t : ITree MirEffect MirOutcome} (h : TreeSafe t) :
    ¬ MirReachesUB t := by
  rintro ⟨tr, u, k, hr, hobs⟩
  exact h tr u hr ⟨u, _, k, .refl u, hobs, mir_isFault_inl _⟩

/-- **Partial-correctness equivalence.** For postconditions `postA` on Anneal
return values and `postM` on `lean-miri` return operands that agree along
`RetRel`, `lean-miri`'s `System.PartialCorrect` holds iff every Anneal
`ReachesRet` normal return satisfies `postA`. -/
theorem partialCorrect_iff_annealPostcondition (hsim : StepClosedSim body H Inv RetRel)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m)
    (postA : Value → Prop) (postM : Miri.Interpreter.Operand AnnealProv → Prop)
    (hpost : ∀ retVal v, RetRel retVal v → (postA retVal ↔ postM v)) :
    (miriSystem H).PartialCorrect m postM ↔
      ∀ tr retVal mem, ReachesRet (mirTree body s) tr (.normal (retVal, mem)) → postA retVal := by
  constructor
  · intro hpc tr retVal mem hrr
    obtain ⟨y, hy, hret⟩ := reachesRet_cofix_iff.1 ⟨tr, hrr⟩
    obtain ⟨s', m', rfl, hinv', hreach⟩ := coReach_to_miri hsim hy rfl hinv
    change stepMirFn body s' = _ at hret
    rcases lockstep_shapes hsim hinv' with
      ⟨obs, _, _, ha, _⟩ | ⟨retVal', mem', _, v, ha, hm, hemp, hop, hrel⟩ | ⟨_, _, _, ha, _⟩
    · rw [ha] at hret; cases obs <;> cases hret
    · rw [ha] at hret
      injection hret with hret
      injection hret with hret
      injection hret with hrv _
      subst hrv
      exact (hpost retVal' v hrel).2
        (hpc v ⟨m', hreach, (miriSystem_terminal_of_ok_empty hm hemp _).2 ⟨v, hop, rfl⟩⟩)
    · rw [ha] at hret; cases hret
  · intro hA v ⟨final, hr, hterm⟩
    obtain ⟨s', hco, hinv'⟩ := miri_to_coReach hsim hinv hr
    rcases lockstep_shapes hsim hinv' with
      ⟨_, _, _, _, hm, hne, _⟩ | ⟨retVal, mem, _, v₀, ha, hm, hemp, hop, hrel⟩ |
        ⟨_, _, e, _, hm, _⟩
    · exact absurd hterm (miriSystem_not_terminal_of_ok_nonempty hm hne _)
    · obtain ⟨v', hv', h⟩ := (miriSystem_terminal_of_ok_empty hm hemp _).1 hterm
      injection h with h
      subst h
      rw [hop] at hv'
      injection hv' with hv'
      subst hv'
      obtain ⟨tr, htr⟩ := reachesRet_cofix_iff.2 ⟨MirExecState.running s', hco, ha⟩
      exact (hpost retVal v₀ hrel).1 (hA tr retVal mem (by rw [mirTree_eq_cofix]; exact htr))
    · exact absurd ((miriSystem_terminal_of_error hm _).1 hterm).symm
        (classifyError_ne_returned e v)

end WholeProgram

/-! ## 6. Fuel-indexed multi-step `RunLoop` simulation -/

/-- Outcome of running `lean-miri`'s `RunLoop.iteration` for at most `fuel` iterations. -/
inductive MiriRunLoopOutcome : Type where
  /-- Still running after the iterations performed. -/
  | running (state : AnnealStepState)
  /-- An iteration popped the root frame; `retOperand` is the root's return operand. -/
  | returned (state : AnnealStepState)
      (retOperand : Except Miri.Interpreter.StepError (Miri.Interpreter.Operand AnnealProv))
  /-- An iteration stopped with error `err`. -/
  | stopped (state : AnnealStepState) (err : Miri.Interpreter.StepError)

/-- Fuel-bounded execution of `lean-miri`'s scheduler loop (`RunLoop.iteration`). -/
def runLoopFuel (H : AnnealMiriHooks) : Nat → AnnealStepState → MiriRunLoopOutcome
  | 0, m => .running m
  | fuel + 1, m =>
    match miriIter H m with
    | (m', .ok _) =>
      if m'.stack.frames.isEmpty then .returned m' (H.returnOperand () m).2
      else runLoopFuel H fuel m'
    | (m', .error e) => .stopped m' e

/-- Multi-step lockstep relation between `runAnnealBounded` and `runLoopFuel`. -/
inductive RunLoopRel (Inv : MachineState → AnnealStepState → Prop)
    (RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop) :
    AnnealRunOutcome → MiriRunLoopOutcome → Prop where
  | running (s : MachineState) (m : AnnealStepState) :
      Inv s m → RunLoopRel Inv RetRel (.running s) (.running m)
  | returned (retVal : Value) (mem : Memory) (m : AnnealStepState)
      (v : Miri.Interpreter.Operand AnnealProv) :
      RetRel retVal v → RunLoopRel Inv RetRel (.returned retVal mem) (.returned m (.ok v))
  | fault (k : FailureKind) (m : AnnealStepState) (e : Miri.Interpreter.StepError) :
      FaultAgrees k e → RunLoopRel Inv RetRel (.faulted k) (.stopped m e)

theorem array_isEmpty_eq_false {α : Type} {a : Array α} (h : a ≠ #[]) : a.isEmpty = false := by
  rcases a with ⟨l⟩
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem array_isEmpty_eq_true {α : Type} {a : Array α} (h : a = #[]) : a.isEmpty = true := by
  subst h; rfl

section RunLoopSim

variable {body : CapturedMir} {H : AnnealMiriHooks}
  {Inv : MachineState → AnnealStepState → Prop}
  {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}

/-- **Master multi-step theorem.** Under a step-closed simulation, after any
number `fuel` of steps, Anneal's `runAnnealBounded` and `lean-miri`'s
`RunLoop.iteration` loop (`runLoopFuel`) are both running in `Inv`-related
states, both returned with `RetRel`-related values, or both failed agreeing on
undefined behavior. -/
theorem runLoop_universal_simulation (hsim : StepClosedSim body H Inv RetRel) (fuel : Nat)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m) :
    RunLoopRel Inv RetRel (runAnnealBounded body fuel s) (runLoopFuel H fuel m) := by
  induction fuel generalizing s m with
  | zero => exact .running s m hinv
  | succ fuel ih =>
    rcases lockstep_shapes hsim hinv with
      ⟨obs, s', m', ha, hm, hne, hinv'⟩ | ⟨retVal, mem, m', v, ha, hm, hemp, hop, hrel⟩ |
        ⟨k, m', e, ha, hm, hag⟩
    · rw [runAnnealBounded_emitStep body fuel s s' obs ha]
      unfold runLoopFuel
      rw [hm]
      simp only [array_isEmpty_eq_false hne, Bool.false_eq_true, ↓reduceIte]
      exact ih hinv'
    · have hA : runAnnealBounded body (fuel + 1) s = .returned retVal mem := by
        unfold runAnnealBounded; rw [ha]; rfl
      rw [hA]
      unfold runLoopFuel
      rw [hm]
      simp only [array_isEmpty_eq_true hemp, ↓reduceIte, hop]
      exact .returned retVal mem m' v hrel
    · have hA : runAnnealBounded body (fuel + 1) s = .faulted k := by
        unfold runAnnealBounded; rw [ha]; rfl
      rw [hA]
      unfold runLoopFuel
      rw [hm]
      exact .fault k m' e hag

/-- Fuel-indexed form of bidirectional UB reachability. -/
theorem runLoop_ub_iff (hsim : StepClosedSim body H Inv RetRel) (fuel : Nat)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m) :
    runAnnealBounded body fuel s = .faulted .ub ↔
      ∃ m' e, runLoopFuel H fuel m = .stopped m' e ∧ Miri.Interpreter.RunLoop.reportsUB e = true := by
  have h := runLoop_universal_simulation hsim fuel hinv
  generalize runAnnealBounded body fuel s = aOut at h
  generalize runLoopFuel H fuel m = mOut at h
  cases h with
  | running => exact ⟨fun h => (by cases h), fun ⟨_, _, h, _⟩ => (by cases h)⟩
  | returned => exact ⟨fun h => (by cases h), fun ⟨_, _, h, _⟩ => (by cases h)⟩
  | fault k m' e hag =>
    constructor
    · intro h
      injection h with h
      exact ⟨m', e, rfl, hag.1 h⟩
    · rintro ⟨_, _, h, hub⟩
      injection h with h₁ h₂
      subst h₁ h₂
      rw [hag.2 hub]

/-- Fuel-indexed normal-return correspondence. -/
theorem runLoop_returned_iff (hsim : StepClosedSim body H Inv RetRel) (fuel : Nat)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m) :
    (∃ retVal mem, runAnnealBounded body fuel s = .returned retVal mem) ↔
      ∃ m' v, runLoopFuel H fuel m = .returned m' (.ok v) := by
  have h := runLoop_universal_simulation hsim fuel hinv
  generalize runAnnealBounded body fuel s = aOut at h
  generalize runLoopFuel H fuel m = mOut at h
  cases h with
  | running => exact ⟨fun ⟨_, _, h⟩ => (by cases h), fun ⟨_, _, h⟩ => (by cases h)⟩
  | returned retVal mem m' v _ => exact ⟨fun _ => ⟨m', v, rfl⟩, fun _ => ⟨retVal, mem, rfl⟩⟩
  | fault => exact ⟨fun ⟨_, _, h⟩ => (by cases h), fun ⟨_, _, h⟩ => (by cases h)⟩

end RunLoopSim

/-! ## 7. Run certificates for concrete whole-program witnesses -/

theorem array_eq_empty_of_isEmpty {α : Type} {a : Array α} (h : a.isEmpty = true) : a = #[] := by
  rcases a with ⟨l⟩
  cases l with
  | nil => rfl
  | cons _ _ => cases h

theorem array_ne_empty_of_isEmpty {α : Type} {a : Array α} (h : a.isEmpty = false) :
    a ≠ #[] := by
  intro h'
  subst h'
  cases h

section MiriCertificates

variable {H : AnnealMiriHooks}

/-- Continue a `runLoopFuel` outcome that is still running. -/
def MiriRunLoopOutcome.andThen (o : MiriRunLoopOutcome)
    (f : AnnealStepState → MiriRunLoopOutcome) : MiriRunLoopOutcome :=
  match o with
  | .running m => f m
  | o => o

theorem runLoopFuel_succ (H : AnnealMiriHooks) (n : Nat) (m : AnnealStepState) :
    runLoopFuel H (n + 1) m =
      match miriIter H m with
      | (m', .ok _) =>
        if m'.stack.frames.isEmpty then .returned m' (H.returnOperand () m).2
        else runLoopFuel H n m'
      | (m', .error e) => .stopped m' e := rfl

theorem runLoopFuel_add (H : AnnealMiriHooks) (n k : Nat) (m : AnnealStepState) :
    runLoopFuel H (n + k) m = (runLoopFuel H n m).andThen (runLoopFuel H k) := by
  induction n generalizing m with
  | zero => rw [Nat.zero_add]; rfl
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega, runLoopFuel_succ, runLoopFuel_succ]
    rcases miriIter H m with ⟨m', (e | _)⟩
    · rfl
    · dsimp only
      cases hemp : m'.stack.frames.isEmpty
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih m'
      · rfl

theorem runLoopFuel_running_of_le {n N : Nat} {m m' : AnnealStepState}
    (h : runLoopFuel H N m = .running m') (hle : n ≤ N) :
    ∃ x, runLoopFuel H n m = .running x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [runLoopFuel_add] at h
  cases hn : runLoopFuel H n m with
  | running x => exact ⟨x, rfl⟩
  | returned _ _ => rw [hn] at h; cases h
  | stopped _ _ => rw [hn] at h; cases h

/-- Leading `RunLoop` transition of a `runLoopFuel` run. -/
theorem runLoopFuel_of_step {n : Nat} {m m₁ : AnnealStepState}
    (h : H.coreStep () m = (m₁, .ok true)) (hne : m₁.stack.frames ≠ #[]) :
    runLoopFuel H (n + 1) m = runLoopFuel H n m₁ := by
  rw [runLoopFuel_succ, miriIter_eq, h]
  simp only [stepToIteration, array_isEmpty_eq_false hne, Bool.false_eq_true, ↓reduceIte]

/-- A `RunLoop` run that pops the root frame with return operand `v` is
`System.Safe`, reaches `.returned v`, and reaches no other outcome. -/
theorem miri_safe_of_runLoopFuel_returned {N : Nat} {m m' : AnnealStepState}
    {v : Miri.Interpreter.Operand AnnealProv} (h : runLoopFuel H N m = .returned m' (.ok v)) :
    (miriSystem H).Safe m ∧ (miriSystem H).ReachesOutcome m (.returned v) ∧
      ∀ o, (miriSystem H).ReachesOutcome m o → o = .returned v := by
  induction N generalizing m with
  | zero => cases h
  | succ N ih =>
    rw [runLoopFuel_succ] at h
    rcases hm : miriIter H m with ⟨m₁, (e | u)⟩
    · rw [hm] at h; cases h
    · cases u
      rw [hm] at h
      dsimp only at h
      cases hemp : m₁.stack.frames.isEmpty
      · rw [hemp] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        have hne := array_ne_empty_of_isEmpty hemp
        have hstep : (miriSystem H).step m m₁ := ⟨hm, hne⟩
        obtain ⟨hsafe, hreach, huniq⟩ := ih h
        have hcases : ∀ c, (miriSystem H).Reaches m c → c = m ∨ (miriSystem H).Reaches m₁ c :=
          fun c hc => miriSystem_reaches_cases hstep hc
        refine ⟨⟨fun c hc => ?_, fun o ⟨f, hf, ht⟩ => ?_⟩, ?_, fun o ⟨f, hf, ht⟩ => ?_⟩
        · rcases hcases c hc with rfl | hc'
          · exact Or.inl ⟨m₁, hstep⟩
          · exact hsafe.1 c hc'
        · rcases hcases f hf with rfl | hf'
          · exact absurd ht (miriSystem_not_terminal_of_ok_nonempty hm hne o)
          · exact hsafe.2 o ⟨f, hf', ht⟩
        · obtain ⟨f, hf, ht⟩ := hreach
          exact ⟨f, miriSystem_reaches_head hstep hf, ht⟩
        · rcases hcases f hf with rfl | hf'
          · exact absurd ht (miriSystem_not_terminal_of_ok_nonempty hm hne o)
          · exact huniq o ⟨f, hf', ht⟩
      · rw [hemp] at h
        simp only [↓reduceIte] at h
        injection h with _ hv
        have hemp' := array_eq_empty_of_isEmpty hemp
        have hno : ∀ b, ¬ (miriSystem H).step m b := fun b => miriSystem_not_step_of_ok_empty hm hemp'
        have hterm : ∀ o, (miriSystem H).terminal m o ↔ o = .returned v := by
          intro o
          rw [miriSystem_terminal_of_ok_empty hm hemp' o]
          exact ⟨fun ⟨v', hv', ho⟩ => by rw [hv] at hv'; injection hv' with hv'; rw [ho, hv'],
            fun ho => ⟨v, hv, ho⟩⟩
        refine ⟨⟨fun c hc => ?_, fun o ⟨f, hf, ht⟩ => ?_⟩, ⟨m, .refl m, (hterm _).2 rfl⟩,
          fun o ⟨f, hf, ht⟩ => ?_⟩
        · rw [miriSystem_reaches_of_no_step hno hc]
          exact Or.inr ⟨.returned v, (hterm _).2 rfl⟩
        · rw [miriSystem_reaches_of_no_step hno hf] at ht
          rw [(hterm o).1 ht]
          trivial
        · rw [miriSystem_reaches_of_no_step hno hf] at ht
          exact (hterm o).1 ht

/-- A `RunLoop` run that stops with error `e` reaches `classifyError e` and is not safe. -/
theorem miri_outcome_of_runLoopFuel_stopped {N : Nat} {m m' : AnnealStepState}
    {e : Miri.Interpreter.StepError} (h : runLoopFuel H N m = .stopped m' e) :
    (miriSystem H).ReachesOutcome m (classifyError e) ∧ ¬ (miriSystem H).Safe m := by
  have hreach : (miriSystem H).ReachesOutcome m (classifyError e) := by
    induction N generalizing m with
    | zero => cases h
    | succ N ih =>
      rw [runLoopFuel_succ] at h
      rcases hm : miriIter H m with ⟨m₁, (e' | u)⟩
      · rw [hm] at h
        injection h with _ he
        subst he
        exact ⟨m, .refl m, (miriSystem_terminal_of_error hm _).2 rfl⟩
      · cases u
        rw [hm] at h
        dsimp only at h
        cases hemp : m₁.stack.frames.isEmpty
        · rw [hemp] at h
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨f, hf, ht⟩ := ih h
          exact ⟨f, miriSystem_reaches_head ⟨hm, array_ne_empty_of_isEmpty hemp⟩ hf, ht⟩
        · rw [hemp] at h; cases h
  exact ⟨hreach, fun hsafe => classifyError_not_isReturn e (hsafe.2 _ hreach)⟩

/-- A `RunLoop` loop that keeps running forever has an infinite run, is
`System.Safe`, and reaches no terminal outcome. -/
theorem miri_infinite_of_forall_running {m : AnnealStepState}
    (h : ∀ n, ∃ m', runLoopFuel H n m = .running m') :
    Miri.OperationalSafety.InfiniteRun (miriSystem H) m ∧ (miriSystem H).Safe m ∧
      ∀ o, ¬ (miriSystem H).ReachesOutcome m o := by
  let run : Nat → AnnealStepState := fun n =>
    match runLoopFuel H n m with
    | .running x => x
    | _ => m
  have hrun : ∀ n, runLoopFuel H n m = .running (run n) := by
    intro n
    obtain ⟨x, hx⟩ := h n
    simp only [run, hx]
  have hstep : ∀ n, (miriSystem H).step (run n) (run (n + 1)) := by
    intro n
    have h1 := hrun (n + 1)
    rw [runLoopFuel_add, hrun n] at h1
    change runLoopFuel H 1 (run n) = _ at h1
    rw [runLoopFuel_succ] at h1
    rcases hm : miriIter H (run n) with ⟨x, (e | u)⟩
    · rw [hm] at h1; cases h1
    · cases u
      rw [hm] at h1
      dsimp only at h1
      cases hemp : x.stack.frames.isEmpty
      · rw [hemp] at h1
        simp only [Bool.false_eq_true, ↓reduceIte] at h1
        change MiriRunLoopOutcome.running x = _ at h1
        injection h1 with h1
        subst h1
        exact ⟨hm, array_ne_empty_of_isEmpty hemp⟩
      · rw [hemp] at h1; cases h1
  have h0 : run 0 = m := rfl
  have hreach : ∀ c, (miriSystem H).Reaches m c → ∃ n, c = run n := by
    intro c hc
    induction hc with
    | refl => exact ⟨0, h0.symm⟩
    | step _ hs ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n + 1, miriSystem_step_det hs (hstep n)⟩
  have hnoterm : ∀ n o, ¬ (miriSystem H).terminal (run n) o :=
    fun n o => miriSystem_not_terminal_of_ok_nonempty (hstep n).1 (hstep n).2 o
  refine ⟨⟨run, h0, hstep⟩, ⟨fun c hc => ?_, fun o ⟨f, hf, ht⟩ => ?_⟩, fun o ⟨f, hf, ht⟩ => ?_⟩
  · obtain ⟨n, rfl⟩ := hreach c hc
    exact Or.inl ⟨_, hstep n⟩
  · obtain ⟨n, rfl⟩ := hreach f hf
    exact absurd ht (hnoterm n o)
  · obtain ⟨n, rfl⟩ := hreach f hf
    exact hnoterm n o ht

/-- Lasso certificate: a run prefix reaching `mp` followed by a nonempty cycle
`mp → … → mp` runs forever. -/
theorem forall_running_of_lasso {p c : Nat} {m mp : AnnealStepState}
    (hp : runLoopFuel H p m = .running mp) (hc : runLoopFuel H (c + 1) mp = .running mp) :
    ∀ n, ∃ m', runLoopFuel H n m = .running m' := by
  have hcyc : ∀ q, ∃ x, runLoopFuel H q mp = .running x := by
    intro q
    induction q using Nat.strongRecOn with
    | ind q ih =>
      by_cases hq : q ≤ c + 1
      · exact runLoopFuel_running_of_le hc hq
      · obtain ⟨q', rfl⟩ : ∃ q', q = (c + 1) + q' := ⟨q - (c + 1), by omega⟩
        rw [runLoopFuel_add, hc]
        exact ih q' (by omega)
  intro n
  by_cases hn : n ≤ p
  · exact runLoopFuel_running_of_le hp hn
  · obtain ⟨q, rfl⟩ : ∃ q, n = p + q := ⟨n - p, by omega⟩
    rw [runLoopFuel_add, hp]
    exact hcyc q


/-! ### Decidable observations of `runLoopFuel` -/

/-- Unsigned bits of an immediate scalar return operand of `sizeBytes` bytes. -/
def operandScalarBits? (sizeBytes : Nat) : Miri.Interpreter.Operand AnnealProv → Option Nat
  | .immediate (.scalar s) =>
    match s.toScalarInt with
    | .ok sc =>
      if sc.size == Miri.ABI.Size.ofBytes (UInt64.ofNat sizeBytes) then some sc.data.toNat
      else none
    | .error _ => none
  | _ => none

/-- The return operand of a `runLoopFuel` outcome that popped the root frame. -/
def MiriRunLoopOutcome.returnedOperand? :
    MiriRunLoopOutcome → Option (Miri.Interpreter.Operand AnnealProv)
  | .returned _ (.ok v) => some v
  | _ => none

/-- The error of a `runLoopFuel` outcome that stopped. -/
def MiriRunLoopOutcome.stoppedError? : MiriRunLoopOutcome → Option Miri.Interpreter.StepError
  | .stopped _ e => some e
  | _ => none

/-- Whether a `runLoopFuel` outcome is still running. -/
def MiriRunLoopOutcome.isRunning : MiriRunLoopOutcome → Bool
  | .running _ => true
  | _ => false

theorem MiriRunLoopOutcome.returnedOperand?_spec {o : MiriRunLoopOutcome}
    {v : Miri.Interpreter.Operand AnnealProv} (h : o.returnedOperand? = some v) :
    ∃ m', o = .returned m' (.ok v) := by
  cases o with
  | running _ => cases h
  | returned m' r =>
    cases r with
    | ok v' => injection h with h; subst h; exact ⟨m', rfl⟩
    | error _ => cases h
  | stopped _ _ => cases h

theorem MiriRunLoopOutcome.stoppedError?_spec {o : MiriRunLoopOutcome}
    {e : Miri.Interpreter.StepError} (h : o.stoppedError? = some e) :
    ∃ m', o = .stopped m' e := by
  cases o with
  | running _ => cases h
  | returned _ _ => cases h
  | stopped m' e' => injection h with h; subst h; exact ⟨m', rfl⟩

theorem MiriRunLoopOutcome.isRunning_spec {o : MiriRunLoopOutcome} (h : o.isRunning = true) :
    ∃ m', o = .running m' := by
  cases o with
  | running m' => exact ⟨m', rfl⟩
  | returned _ _ => cases h
  | stopped _ _ => cases h

/-- Whole-program certificate from a decidable observation of a returning run. -/
theorem miri_returns_of_observation {H : AnnealMiriHooks} {N : Nat} {m : AnnealStepState}
    {post : Miri.Interpreter.Operand AnnealProv → Prop}
    (h : ∃ v, (runLoopFuel H N m).returnedOperand? = some v ∧ post v) :
    (miriSystem H).Safe m ∧ (miriSystem H).PartialCorrect m post ∧
      ∃ v, (miriSystem H).ReachesOutcome m (.returned v) ∧ post v := by
  obtain ⟨v, hv, hpost⟩ := h
  obtain ⟨m', hm'⟩ := MiriRunLoopOutcome.returnedOperand?_spec hv
  obtain ⟨hsafe, hreach, huniq⟩ := miri_safe_of_runLoopFuel_returned hm'
  refine ⟨hsafe, fun v' hv' => ?_, v, hreach, hpost⟩
  have := huniq _ hv'
  injection this with this
  rw [this]
  exact hpost

/-- Whole-program certificate from a decidable observation of an undefined-behavior stop. -/
theorem miri_ub_of_observation {H : AnnealMiriHooks} {N : Nat} {m : AnnealStepState}
    {e : Miri.Interpreter.StepError} (h : (runLoopFuel H N m).stoppedError? = some e)
    (hub : Miri.Interpreter.RunLoop.reportsUB e = true) :
    (miriSystem H).ReachesOutcome m (.undefinedBehavior e) ∧ ¬ (miriSystem H).Safe m := by
  obtain ⟨m', hm'⟩ := MiriRunLoopOutcome.stoppedError?_spec h
  have h' := miri_outcome_of_runLoopFuel_stopped hm'
  rw [classifyError_eq_ub_iff.2 ⟨hub, rfl⟩] at h'
  exact h'

/-- A `Step.step` iteration that continues (`.ok true`) started from a nonempty stack. -/
theorem frames_ne_of_step_ok_true {PV : Type}
    {hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine
      Unit PV}
    {m m' : AnnealStepState} (h : Miri.Interpreter.Step.step hooks () m = (m', .ok true)) :
    m.stack.frames ≠ #[] := by
  intro hemp
  have hcur : m.stack.currentFrame? = none := by
    unfold Miri.Interpreter.Stack.currentFrame?
    rw [hemp]
    rfl
  unfold Miri.Interpreter.Step.step at h
  rw [hcur] at h
  cases h

/-- A finite `lean-miri` execution path of core steps that keep a nonempty stack. -/
inductive MiriPath (H : AnnealMiriHooks) : AnnealStepState → AnnealStepState → Prop where
  | refl (m : AnnealStepState) : MiriPath H m m
  | step {m m₁ m₂ : AnnealStepState} :
      H.coreStep () m = (m₁, .ok true) → m₁.stack.frames ≠ #[] → MiriPath H m₁ m₂ →
      MiriPath H m m₂

theorem MiriPath.run_shift {m m' : AnnealStepState} (h : MiriPath H m m') :
    ∃ n, ∀ k, runLoopFuel H (n + k) m = runLoopFuel H k m' := by
  induction h with
  | refl m => exact ⟨0, fun k => by rw [Nat.zero_add]⟩
  | step hc hne _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, fun k => by rw [show n + 1 + k = (n + k) + 1 by omega, runLoopFuel_of_step hc hne, hn]⟩

theorem runLoopFuel_one_returned {m m' : AnnealStepState}
    {v : Miri.Interpreter.Operand AnnealProv} (hret : H.coreStep () m = (m', .ok true))
    (hemp : m'.stack.frames = #[]) (hop : (H.returnOperand () m).2 = .ok v) :
    runLoopFuel H 1 m = .returned m' (.ok v) := by
  rw [runLoopFuel_succ, miriIter_eq, hret]
  simp only [stepToIteration, array_isEmpty_eq_true hemp, ↓reduceIte, hop]

theorem runLoopFuel_one_stopped {m m' : AnnealStepState} {e : Miri.Interpreter.StepError}
    (herr : H.coreStep () m = (m', .error e)) : runLoopFuel H 1 m = .stopped m' e := by
  rw [runLoopFuel_succ, miriIter_eq, herr]
  rfl

theorem MiriPath.trans {a b c : AnnealStepState} (h₁ : MiriPath H a b) (h₂ : MiriPath H b c) :
    MiriPath H a c := by
  induction h₁ with
  | refl _ => exact h₂
  | step hc hne _ ih => exact .step hc hne (ih h₂)

/-- A running `runLoopFuel` prefix is a `MiriPath`. -/
theorem MiriPath.of_runLoopFuel {n : Nat} {m m' : AnnealStepState}
    (h : runLoopFuel H n m = .running m') : MiriPath H m m' := by
  induction n generalizing m with
  | zero => cases h; exact .refl _
  | succ n ih =>
    rw [runLoopFuel_succ, miriIter_eq] at h
    rcases hc : H.coreStep () m with ⟨m₁, (e | (_ | _))⟩ <;> rw [hc] at h
    · cases h
    · cases h
    · simp only [stepToIteration] at h
      cases hemp : m₁.stack.frames.isEmpty
      · rw [hemp] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact .step hc (array_ne_empty_of_isEmpty hemp) (ih h)
      · rw [hemp] at h; cases h

/-- Whole-program certificate: a path to a root-frame return with operand `v`. -/
theorem miri_safe_of_path_return {m mₙ m' : AnnealStepState}
    {v : Miri.Interpreter.Operand AnnealProv} (hpath : MiriPath H m mₙ)
    (hret : H.coreStep () mₙ = (m', .ok true)) (hemp : m'.stack.frames = #[])
    (hop : (H.returnOperand () mₙ).2 = .ok v) :
    (miriSystem H).Safe m ∧ (miriSystem H).ReachesOutcome m (.returned v) ∧
      ∀ o, (miriSystem H).ReachesOutcome m o → o = .returned v := by
  obtain ⟨n, hn⟩ := hpath.run_shift
  apply miri_safe_of_runLoopFuel_returned (N := n + 1) (m' := m')
  rw [hn 1, runLoopFuel_succ, miriIter_eq, hret]
  simp only [stepToIteration, array_isEmpty_eq_true hemp, ↓reduceIte, hop]

/-- Whole-program certificate: a path to a core step failing with `e`. -/
theorem miri_outcome_of_path_error {m mₙ m' : AnnealStepState} {e : Miri.Interpreter.StepError}
    (hpath : MiriPath H m mₙ) (herr : H.coreStep () mₙ = (m', .error e)) :
    (miriSystem H).ReachesOutcome m (classifyError e) ∧ ¬ (miriSystem H).Safe m := by
  obtain ⟨n, hn⟩ := hpath.run_shift
  apply miri_outcome_of_runLoopFuel_stopped (N := n + 1) (m' := m')
  rw [hn 1, runLoopFuel_succ, miriIter_eq, herr]
  rfl

end MiriCertificates

section AnnealCertificates

variable {body : CapturedMir}

/-- A finite Anneal execution path through `emitStep` transitions. -/
inductive AnnealPath (body : CapturedMir) : MachineState → MachineState → Prop where
  | refl (s : MachineState) : AnnealPath body s s
  | step {s s₁ s₂ : MachineState} (obs : MirObs) :
      stepMirFn body s = .emitStep obs s₁ → AnnealPath body s₁ s₂ → AnnealPath body s s₂

theorem AnnealPath.coReach {s s' : MachineState} (h : AnnealPath body s s') :
    CoReach (stepMirState body) (.running s) (.running s') := by
  induction h with
  | refl s => exact .refl _
  | step obs hs _ ih => exact .head (coStep_of_emitStep hs) ih

/-- An Anneal path to a normal root-frame return is tree-safe and returns exactly that value. -/
theorem anneal_safe_of_path_return {s sₙ : MachineState} {retVal : Value} {mem : Memory}
    (hpath : AnnealPath body s sₙ) (hret : stepMirFn body sₙ = .retNormal retVal mem) :
    TreeSafe (mirTree body s) ∧ (∃ tr, ReachesRet (mirTree body s) tr (.normal (retVal, mem))) ∧
      ∀ tr r, ReachesRet (mirTree body s) tr r → r = .normal (retVal, mem) := by
  have hend : ∀ y, CoReach (stepMirState body) (.running sₙ) y → y = .running sₙ := by
    intro y hy
    cases hy with
    | refl _ => rfl
    | head hst _ => exact absurd hst (not_coStep_retNormal hret)
  have hpathStates : ∀ y, CoReach (stepMirState body) (.running s) y →
      ∃ s', y = .running s' ∧ ((∃ obs s'', stepMirFn body s' = .emitStep obs s'') ∨ s' = sₙ) := by
    intro y hy
    induction hpath generalizing y with
    | refl s => exact ⟨s, hend y hy, Or.inr rfl⟩
    | @step s s₁ s₂ obs hs hrest ih =>
      have hret' := hret
      cases hy with
      | refl _ => exact ⟨s, rfl, Or.inl ⟨obs, s₁, hs⟩⟩
      | head hst hy' =>
        rw [coStep_emitStep_inv hs hst] at hy'
        exact ih hret' hend y hy'
  rw [mirTree_eq_cofix]
  refine ⟨treeSafe_cofix_iff.2 fun y hy hf => ?_, reachesRet_cofix_iff.2 ⟨_, hpath.coReach, hret⟩,
    fun tr r hr => ?_⟩
  · obtain ⟨s', rfl, ⟨obs, s'', hs'⟩ | rfl⟩ := hpathStates y hy
    · exact not_isFaultNode_emitStep obs s'' (hs' ▸ hf)
    · exact not_isFaultNode_retNormal retVal mem (hret ▸ hf)
  · obtain ⟨y, hy, hyr⟩ := reachesRet_cofix_iff.1 ⟨tr, hr⟩
    obtain ⟨s', rfl, ⟨obs, s'', hs'⟩ | rfl⟩ := hpathStates y hy
    · change stepMirFn body s' = _ at hyr
      rw [hs'] at hyr
      cases obs <;> cases hyr
    · change stepMirFn body s' = _ at hyr
      rw [hret] at hyr
      injection hyr with hyr
      exact hyr.symm

/-- An Anneal path to a fault is not tree-safe; an undefined-behavior fault is
reachable undefined behavior. -/
theorem anneal_fault_of_path {s sₙ : MachineState} {k : FailureKind}
    (hpath : AnnealPath body s sₙ) (hfail : stepMirFn body sₙ = .fail k) :
    ¬ TreeSafe (mirTree body s) ∧ (k = .ub → MirReachesUB (mirTree body s)) := by
  rw [mirTree_eq_cofix]
  refine ⟨fun hsafe => ?_, fun hk => ?_⟩
  · exact treeSafe_cofix_iff.1 hsafe _ hpath.coReach
      (show IsFaultNode (stepMirFn body sₙ) by rw [hfail]; exact isFaultNode_fail k)
  · subst hk
    obtain ⟨tr, htr⟩ := reaches_cofix_of_coReach hpath.coReach
    have hobs : (ITree.cofix (stepMirState body) (.running sₙ)).observe =
        .vis (.inl (.fail .ub)) (fun o => ITree.cofix (stepMirState body) (PEmpty.elim o)) := by
      rw [observe_cofix_eq]
      change (stepMirFn body sₙ).map _ = _
      rw [hfail]
      rfl
    exact ⟨tr, _, _, htr, hobs⟩

/-- Invariant certificate for Anneal loops: if a set of states is closed under
`emitStep` transitions, every run from it is tree-safe and never returns. -/
theorem anneal_safe_of_closed {P : MachineState → Prop} {s : MachineState} (hs : P s)
    (hclosed : ∀ x, P x → ∃ obs x', stepMirFn body x = .emitStep obs x' ∧ P x') :
    TreeSafe (mirTree body s) ∧ ∀ tr r, ¬ ReachesRet (mirTree body s) tr r := by
  have hinv : ∀ y, CoReach (stepMirState body) (.running s) y → ∃ x, y = .running x ∧ P x := by
    intro y hy
    generalize hx : (MirExecState.running s) = x₀ at hy
    induction hy generalizing s with
    | refl _ => exact ⟨s, hx.symm, hs⟩
    | head hst _ ih =>
      subst hx
      obtain ⟨obs, x', hx', hPx'⟩ := hclosed s hs
      have hy_eq := coStep_emitStep_inv hx' hst
      subst hy_eq
      exact ih hPx' rfl
  rw [mirTree_eq_cofix]
  refine ⟨treeSafe_cofix_iff.2 fun y hy hf => ?_, fun tr r hr => ?_⟩
  · obtain ⟨x, rfl, hPx⟩ := hinv y hy
    obtain ⟨obs, x', hx', _⟩ := hclosed x hPx
    exact not_isFaultNode_emitStep obs x' (hx' ▸ hf)
  · obtain ⟨y, hy, hyr⟩ := reachesRet_cofix_iff.1 ⟨tr, hr⟩
    obtain ⟨x, rfl, hPx⟩ := hinv y hy
    obtain ⟨obs, x', hx', _⟩ := hclosed x hPx
    change stepMirFn body x = _ at hyr
    rw [hx'] at hyr
    cases obs <;> cases hyr


/-! ### `runAnnealBounded` certificates -/

/-- Anneal's bounded-run result for a terminal outcome. -/
def annealHaltOutcome : MirOutcome → AnnealRunOutcome
  | .normal (retVal, mem) => .returned retVal mem
  | out => .haltedOther out

theorem CoStep.not_fault_not_ret {E : Effect.{0}} {R S : Type} [FaultEffect E]
    {step : S → ITreeF E R S} {x y : S} (h : CoStep step x y) :
    ¬ IsFaultNode (step x) ∧ ∀ r, step x ≠ .ret r := by
  cases h with
  | tau h' =>
    refine ⟨fun ⟨_, _, hik, _⟩ => ?_, fun r hr => ?_⟩
    · rw [h'] at hik; cases hik
    · rw [h'] at hr; cases hr
  | vis h' hnf _ =>
    refine ⟨fun ⟨_, _, hik, hf⟩ => ?_, fun r hr => ?_⟩
    · rw [h'] at hik; cases hik; exact hnf hf
    · rw [h'] at hr; cases hr

theorem halted_coReach {body : CapturedMir} {out : MirOutcome} {y : MirExecState}
    (hy : CoReach (stepMirState body) (.halted out) y) : y = .halted out := by
  cases hy with
  | refl _ => rfl
  | head h _ =>
    cases h with
    | tau h => cases h
    | vis h _ _ => cases h

theorem halted_node (body : CapturedMir) (out : MirOutcome) :
    ¬ IsFaultNode (stepMirState body (.halted out)) ∧
      ∀ r, stepMirState body (.halted out) = .ret r → r = out := by
  refine ⟨fun ⟨_, _, h, _⟩ => ?_, fun r hr => ?_⟩
  · cases h
  · injection hr with hr; exact hr.symm

/-- Behaviour of one Anneal step from `.running s`, as seen by `runAnnealBounded`
and by the coalgebra reachability of `mirTree`. -/
theorem anneal_step_classify (body : CapturedMir) (s : MachineState) :
    (∃ s', (∀ n, runAnnealBounded body (n + 1) s = runAnnealBounded body n s') ∧
      ∀ y, CoStep (stepMirState body) (.running s) y ↔ y = .running s') ∨
    (∃ out, (∀ n, runAnnealBounded body (n + 1) s = annealHaltOutcome out) ∧
      (∀ y, CoReach (stepMirState body) (.running s) y →
        ¬ IsFaultNode (stepMirState body y) ∧ ∀ r, stepMirState body y = .ret r → r = out) ∧
      ∃ y, CoReach (stepMirState body) (.running s) y ∧ stepMirState body y = .ret out) ∨
    (∃ k, (∀ n, runAnnealBounded body (n + 1) s = .faulted k) ∧
      ∃ y, CoReach (stepMirState body) (.running s) y ∧
        ∃ f, stepMirState body y = .vis (.inl (.fail k)) f) ∨
    (∀ n, runAnnealBounded body (n + 1) s = .blocked) := by
  have hs : stepMirState body (.running s) = stepMirFn body s := rfl
  -- A unique halted successor yields a terminating, fault-free reachable set.
  have halted_succ : ∀ out, (∀ y, CoStep (stepMirState body) (.running s) y ↔ y = .halted out) →
      (∀ y, CoReach (stepMirState body) (.running s) y →
        ¬ IsFaultNode (stepMirState body y) ∧ ∀ r, stepMirState body y = .ret r → r = out) ∧
      ∃ y, CoReach (stepMirState body) (.running s) y ∧ stepMirState body y = .ret out := by
    intro out hsucc
    have hnode := ((hsucc _).2 rfl).not_fault_not_ret
    refine ⟨fun y hy => ?_, .halted out, .head ((hsucc _).2 rfl) (.refl _), rfl⟩
    cases hy with
    | refl _ => exact ⟨hnode.1, fun r hr => absurd hr (hnode.2 r)⟩
    | head h hy' =>
      rw [(hsucc _).1 h] at hy'
      rw [halted_coReach hy']
      exact halted_node body out
  match hst : stepMirFn body s with
  | .ret r =>
    refine Or.inr (Or.inl ⟨r, fun n => ?_, fun y hy => ?_, .running s, .refl _, by rw [hs, hst]⟩)
    · simp only [runAnnealBounded, hst]
      rcases r with ⟨retVal, mem⟩ | _ | _ <;> rfl
    · cases hy with
      | refl _ =>
        rw [hs, hst]
        refine ⟨fun ⟨_, _, h, _⟩ => ?_, fun r' hr' => ?_⟩
        · cases h
        · injection hr' with hr'; exact hr'.symm
      | head h _ =>
        cases h with
        | tau h => rw [hs, hst] at h; cases h
        | vis h _ _ => rw [hs, hst] at h; cases h
  | .tau (.running s') =>
    refine Or.inl ⟨s', fun n => by simp only [runAnnealBounded, hst], fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
    · cases h with
      | tau h => rw [hs, hst] at h; injection h with h; exact h.symm
      | vis h _ _ => rw [hs, hst] at h; cases h
    · subst h; exact .tau (by rw [hs, hst])
  | .tau (.halted out) =>
    refine Or.inr (Or.inl ⟨out, fun n => ?_, halted_succ out fun y => ⟨fun h => ?_, fun h => ?_⟩⟩)
    · simp only [runAnnealBounded, hst]
      rcases out with ⟨retVal, mem⟩ | _ | _ <;> rfl
    · cases h with
      | tau h => rw [hs, hst] at h; injection h with h; exact h.symm
      | vis h _ _ => rw [hs, hst] at h; cases h
    · subst h; exact .tau (by rw [hs, hst])
  | .tau (.faulted k) =>
    exact Or.inr (Or.inr (Or.inl ⟨k, fun n => by simp only [runAnnealBounded, hst], .faulted k,
      .head (.tau (by rw [hs, hst])) (.refl _), PEmpty.elim, rfl⟩))
  | .vis (.inl (.fail k)) f =>
    exact Or.inr (Or.inr (Or.inl ⟨k, fun n => by simp only [runAnnealBounded, hst], .running s, .refl _, f,
      by rw [hs, hst]⟩))
  | .vis (.inr (.inl (.emit ev))) f =>
    have hsucc : ∀ y, CoStep (stepMirState body) (.running s) y ↔ y = f PUnit.unit := by
      intro y
      constructor
      · intro h
        cases h with
        | tau h => rw [hs, hst] at h; cases h
        | vis h _ o =>
          rw [hs, hst] at h
          cases h
          cases o
          rfl
      · intro h
        subst h
        have hv : stepMirState body (.running s) = .vis (.inr (.inl (.emit ev))) f := by
          rw [hs, hst]
        exact .vis hv (mir_not_isFault_inr _) PUnit.unit
    match hk : f PUnit.unit with
    | .running s' =>
      refine Or.inl ⟨s', fun n => ?_, fun y => by rw [hsucc, hk]⟩
      simp only [runAnnealBounded, hst, hk]
    | .halted out =>
      refine Or.inr (Or.inl ⟨out, fun n => ?_, halted_succ out fun y => by rw [hsucc, hk]⟩)
      simp only [runAnnealBounded, hst, hk]
      rcases out with ⟨retVal, mem⟩ | _ | _ <;> rfl
    | .faulted k =>
      refine Or.inr (Or.inr (Or.inl ⟨k, fun n => ?_, .faulted k,
        .head ((hsucc _).2 hk.symm) (.refl _), PEmpty.elim, rfl⟩))
      simp only [runAnnealBounded, hst, hk]
  | .vis (.inr (.inr (.call req))) f =>
    exact Or.inr (Or.inr (Or.inr fun n => by simp only [runAnnealBounded, hst]))

/-- An Anneal bounded run that returns normally certifies tree safety and the return value. -/
theorem anneal_safe_of_runAnnealBounded_returned {body : CapturedMir} {N : Nat}
    {s : MachineState} {retVal : Value} {mem : Memory}
    (h : runAnnealBounded body N s = .returned retVal mem) :
    TreeSafe (mirTree body s) ∧ (∃ tr, ReachesRet (mirTree body s) tr (.normal (retVal, mem))) ∧
      ∀ tr r, ReachesRet (mirTree body s) tr r → r = .normal (retVal, mem) := by
  suffices hreach : (∀ y, CoReach (stepMirState body) (.running s) y →
      ¬ IsFaultNode (stepMirState body y) ∧
        ∀ r, stepMirState body y = .ret r → r = .normal (retVal, mem)) ∧
      ∃ y, CoReach (stepMirState body) (.running s) y ∧
        stepMirState body y = .ret (.normal (retVal, mem)) by
    rw [mirTree_eq_cofix]
    refine ⟨treeSafe_cofix_iff.2 fun y hy => (hreach.1 y hy).1, reachesRet_cofix_iff.2 hreach.2,
      fun tr r hr => ?_⟩
    obtain ⟨y, hy, hyr⟩ := reachesRet_cofix_iff.1 ⟨tr, hr⟩
    exact (hreach.1 y hy).2 r hyr
  induction N generalizing s with
  | zero => cases h
  | succ N ih =>
    rcases anneal_step_classify body s with
      ⟨s', hrun, hsucc⟩ | ⟨out, hrun, hall, hex⟩ | ⟨k, hrun, _⟩ | hrun
    · rw [hrun] at h
      obtain ⟨hall, hex⟩ := ih h
      have hnode := ((hsucc _).2 rfl).not_fault_not_ret
      refine ⟨fun y hy => ?_, ?_⟩
      · cases hy with
        | refl _ => exact ⟨hnode.1, fun r hr => absurd hr (hnode.2 r)⟩
        | head hst hy' =>
          rw [(hsucc _).1 hst] at hy'
          exact hall y hy'
      · obtain ⟨y, hy, hyr⟩ := hex
        exact ⟨y, .head ((hsucc _).2 rfl) hy, hyr⟩
    · rw [hrun] at h
      have hout : out = .normal (retVal, mem) := by
        rcases out with ⟨rv, mm⟩ | _ | _
        · injection h with h₁ h₂; subst h₁ h₂; rfl
        · cases h
        · cases h
      subst hout
      exact ⟨hall, hex⟩
    · rw [hrun] at h; cases h
    · rw [hrun] at h; cases h

/-- An Anneal bounded run that faults certifies the absence of tree safety, and
an undefined-behavior fault certifies reachable undefined behavior. -/
theorem anneal_fault_of_runAnnealBounded_faulted {body : CapturedMir} {N : Nat}
    {s : MachineState} {k : FailureKind} (h : runAnnealBounded body N s = .faulted k) :
    ¬ TreeSafe (mirTree body s) ∧ (k = .ub → MirReachesUB (mirTree body s)) := by
  suffices hreach : ∃ y, CoReach (stepMirState body) (.running s) y ∧
      ∃ f, stepMirState body y = .vis (.inl (.fail k)) f by
    obtain ⟨y, hy, f, hf⟩ := hreach
    rw [mirTree_eq_cofix]
    refine ⟨fun hsafe => treeSafe_cofix_iff.1 hsafe y hy ⟨_, f, hf, mir_isFault_inl _⟩,
      fun hk => ?_⟩
    subst hk
    obtain ⟨tr, htr⟩ := reaches_cofix_of_coReach hy
    exact ⟨tr, _, _, htr, by rw [observe_cofix_eq, hf]; rfl⟩
  induction N generalizing s with
  | zero => cases h
  | succ N ih =>
    rcases anneal_step_classify body s with
      ⟨s', hrun, hsucc⟩ | ⟨out, hrun, _, _⟩ | ⟨k', hrun, hex⟩ | hrun
    · rw [hrun] at h
      obtain ⟨y, hy, hf⟩ := ih h
      exact ⟨y, .head ((hsucc _).2 rfl) hy, hf⟩
    · rw [hrun] at h
      rcases out with ⟨rv, mm⟩ | _ | _ <;> cases h
    · rw [hrun] at h
      injection h with h
      subst h
      exact hex
    · rw [hrun] at h; cases h

/-- An Anneal execution that keeps running for every bound is tree-safe and never returns. -/
theorem anneal_safe_of_forall_running {body : CapturedMir} {s : MachineState}
    (h : ∀ n, ∃ s', runAnnealBounded body n s = .running s') :
    TreeSafe (mirTree body s) ∧ ∀ tr r, ¬ ReachesRet (mirTree body s) tr r := by
  -- Every reachable state is a running state from which every bounded run keeps running.
  have hinv : ∀ y, CoReach (stepMirState body) (.running s) y →
      ∃ x, y = .running x ∧ ∀ n, ∃ s', runAnnealBounded body n x = .running s' := by
    intro y hy
    generalize hx : (MirExecState.running s) = x₀ at hy
    induction hy generalizing s with
    | refl _ => exact ⟨s, hx.symm, h⟩
    | head hst _ ih =>
      subst hx
      rcases anneal_step_classify body s with
        ⟨s', hrun, hsucc⟩ | ⟨out, hrun, _, _⟩ | ⟨k, hrun, _⟩ | hrun
      · have hy_eq := (hsucc _).1 hst
        subst hy_eq
        exact ih (fun n => by obtain ⟨x, hx⟩ := h (n + 1); rw [hrun] at hx; exact ⟨x, hx⟩) rfl
      · obtain ⟨x, hx⟩ := h 1
        rw [hrun] at hx
        rcases out with ⟨rv, mm⟩ | _ | _ <;> cases hx
      · obtain ⟨x, hx⟩ := h 1; rw [hrun] at hx; cases hx
      · obtain ⟨x, hx⟩ := h 1; rw [hrun] at hx; cases hx
  have hnode : ∀ x, (∀ n, ∃ s', runAnnealBounded body n x = .running s') →
      ¬ IsFaultNode (stepMirFn body x) ∧ ∀ r, stepMirFn body x ≠ .ret r := by
    intro x hx
    rcases anneal_step_classify body x with
      ⟨s', _, hsucc⟩ | ⟨out, hrun, _, _⟩ | ⟨k, hrun, _⟩ | hrun
    · exact ((hsucc _).2 rfl).not_fault_not_ret
    · obtain ⟨y, hy⟩ := hx 1
      rw [hrun] at hy
      rcases out with ⟨rv, mm⟩ | _ | _ <;> cases hy
    · obtain ⟨y, hy⟩ := hx 1; rw [hrun] at hy; cases hy
    · obtain ⟨y, hy⟩ := hx 1; rw [hrun] at hy; cases hy
  rw [mirTree_eq_cofix]
  refine ⟨treeSafe_cofix_iff.2 fun y hy => ?_, fun tr r hr => ?_⟩
  · obtain ⟨x, rfl, hx⟩ := hinv y hy
    exact (hnode x hx).1
  · obtain ⟨y, hy, hyr⟩ := reachesRet_cofix_iff.1 ⟨tr, hr⟩
    obtain ⟨x, rfl, hx⟩ := hinv y hy
    exact (hnode x hx).2 r hyr

/-- `runAnnealBounded` composes along running prefixes. -/
theorem runAnnealBounded_add (body : CapturedMir) (n k : Nat) (x : MachineState) :
    runAnnealBounded body (n + k) x =
      match runAnnealBounded body n x with
      | .running x' => runAnnealBounded body k x'
      | o => o := by
  induction n generalizing x with
  | zero => rw [Nat.zero_add]; rfl
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega]
    rcases anneal_step_classify body x with
      ⟨x', hrun, _⟩ | ⟨out, hrun, _, _⟩ | ⟨k', hrun, _⟩ | hrun
    · rw [hrun, hrun, ih x']
    · rw [hrun, hrun]; rcases out with ⟨rv, mm⟩ | _ | _ <;> rfl
    · rw [hrun, hrun]
    · rw [hrun, hrun]

theorem AnnealPath.run_shift {body : CapturedMir} {s s' : MachineState}
    (h : AnnealPath body s s') :
    ∃ n, ∀ k, runAnnealBounded body (n + k) s = runAnnealBounded body k s' := by
  induction h with
  | refl s => exact ⟨0, fun k => by rw [Nat.zero_add]⟩
  | step obs hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, fun k => by
      rw [show n + 1 + k = (n + k) + 1 by omega, runAnnealBounded_emitStep _ _ _ _ obs hs, hn]⟩

theorem runAnnealBounded_one_retNormal {body : CapturedMir} {s : MachineState} {v : Value}
    {mem : Memory} (h : stepMirFn body s = .retNormal v mem) :
    runAnnealBounded body 1 s = .returned v mem := by
  unfold runAnnealBounded; rw [h]; rfl

theorem runAnnealBounded_one_fail {body : CapturedMir} {s : MachineState} {k : FailureKind}
    (h : stepMirFn body s = .fail k) : runAnnealBounded body 1 s = .faulted k := by
  unfold runAnnealBounded; rw [h]; rfl

/-- Lasso certificate for Anneal: a prefix reaching `sp` followed by a nonempty
cycle `sp → … → sp` runs forever. -/
theorem anneal_forall_running_of_lasso {body : CapturedMir} {p c : Nat} {s sp : MachineState}
    (hp : runAnnealBounded body p s = .running sp)
    (hc : runAnnealBounded body (c + 1) sp = .running sp) :
    ∀ n, ∃ s', runAnnealBounded body n s = .running s' := by
  have hadd := runAnnealBounded_add body
  have hle : ∀ {N n : Nat} {x x' : MachineState}, runAnnealBounded body N x = .running x' →
      n ≤ N → ∃ y, runAnnealBounded body n x = .running y := by
    intro N n x x' hN hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [hadd] at hN
    cases hx : runAnnealBounded body n x with
    | running y => exact ⟨y, rfl⟩
    | returned _ _ => rw [hx] at hN; cases hN
    | faulted _ => rw [hx] at hN; cases hN
    | haltedOther _ => rw [hx] at hN; cases hN
    | blocked => rw [hx] at hN; cases hN
  have hcyc : ∀ q, ∃ x, runAnnealBounded body q sp = .running x := by
    intro q
    induction q using Nat.strongRecOn with
    | ind q ih =>
      by_cases hq : q ≤ c + 1
      · exact hle hc hq
      · obtain ⟨q', rfl⟩ : ∃ q', q = (c + 1) + q' := ⟨q - (c + 1), by omega⟩
        rw [hadd, hc]
        exact ih q' (by omega)
  intro n
  by_cases hn : n ≤ p
  · exact hle hp hn
  · obtain ⟨q, rfl⟩ : ∃ q, n = p + q := ⟨n - p, by omega⟩
    rw [hadd, hp]
    exact hcyc q

/-! ### Two-machine whole-program certificates -/

/-- **Whole-program return agreement.** A running prefix of both machines
followed by explicit paths ending in a normal root return certifies Anneal's
`TreeSafe` and unique `ReachesRet`, and `lean-miri`'s `System.Safe` with the
unique outcome `.returned v`. -/
theorem wholeProgram_returns {body : CapturedMir} {H : AnnealMiriHooks}
    {entryA preA sₙ : MachineState} {entryM preM mₙ m' : AnnealStepState} {p : Nat}
    {retVal : Value} {mem : Memory} {v : Miri.Interpreter.Operand AnnealProv}
    (hpa : runAnnealBounded body p entryA = .running preA)
    (hpm : runLoopFuel H p entryM = .running preM)
    (hA : AnnealPath body preA sₙ) (hAr : stepMirFn body sₙ = .retNormal retVal mem)
    (hM : MiriPath H preM mₙ) (hMr : H.coreStep () mₙ = (m', .ok true))
    (hemp : m'.stack.frames = #[]) (hop : (H.returnOperand () mₙ).2 = .ok v) :
    (TreeSafe (mirTree body entryA) ∧
      (∃ tr, ReachesRet (mirTree body entryA) tr (.normal (retVal, mem))) ∧
      ∀ tr r, ReachesRet (mirTree body entryA) tr r → r = .normal (retVal, mem)) ∧
    ((miriSystem H).Safe entryM ∧ (miriSystem H).ReachesOutcome entryM (.returned v) ∧
      ∀ o, (miriSystem H).ReachesOutcome entryM o → o = .returned v) := by
  refine ⟨?_, miri_safe_of_path_return ((MiriPath.of_runLoopFuel hpm).trans hM) hMr hemp hop⟩
  obtain ⟨n, hn⟩ := hA.run_shift
  apply anneal_safe_of_runAnnealBounded_returned (N := p + (n + 1))
  rw [runAnnealBounded_add, hpa]
  dsimp only
  rw [hn 1, runAnnealBounded_one_retNormal hAr]

/-- **Whole-program undefined-behavior agreement.** A running prefix of both
machines followed by explicit paths ending in Anneal's `.fail .ub` and a
`lean-miri` error that `RunLoop.reportsUB` certifies reachable undefined
behavior on both sides. -/
theorem wholeProgram_ub {body : CapturedMir} {H : AnnealMiriHooks}
    {entryA preA sₙ : MachineState} {entryM preM mₙ m' : AnnealStepState} {p : Nat}
    {e : Miri.Interpreter.StepError}
    (hpa : runAnnealBounded body p entryA = .running preA)
    (hpm : runLoopFuel H p entryM = .running preM)
    (hA : AnnealPath body preA sₙ) (hAf : stepMirFn body sₙ = .fail .ub)
    (hM : MiriPath H preM mₙ) (hMe : H.coreStep () mₙ = (m', .error e))
    (hub : Miri.Interpreter.RunLoop.reportsUB e = true) :
    (MirReachesUB (mirTree body entryA) ∧ ¬ TreeSafe (mirTree body entryA)) ∧
    ((miriSystem H).ReachesOutcome entryM (.undefinedBehavior e) ∧
      ¬ (miriSystem H).Safe entryM) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn⟩ := hA.run_shift
    have h : runAnnealBounded body (p + (n + 1)) entryA = .faulted .ub := by
      rw [runAnnealBounded_add, hpa]
      dsimp only
      rw [hn 1, runAnnealBounded_one_fail hAf]
    obtain ⟨hns, hreach⟩ := anneal_fault_of_runAnnealBounded_faulted h
    exact ⟨hreach rfl, hns⟩
  · have h := miri_outcome_of_path_error ((MiriPath.of_runLoopFuel hpm).trans hM) hMe
    rw [classifyError_eq_ub_iff.2 ⟨hub, rfl⟩] at h
    exact h

end AnnealCertificates

/-! ## 8. Infinite runs under a step-closed simulation -/

section InfiniteRuns

variable {body : CapturedMir} {H : AnnealMiriHooks}
  {Inv : MachineState → AnnealStepState → Prop}
  {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}

/-- `lean-miri` runs forever iff Anneal runs forever (under a step-closed simulation). -/
theorem runLoop_forever_iff (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) :
    (∀ n, ∃ m', runLoopFuel H n m = .running m') ↔
      ∀ n, ∃ s', runAnnealBounded body n s = .running s' := by
  constructor
  · intro h n
    have hrel := runLoop_universal_simulation hsim n hinv
    obtain ⟨m', hm'⟩ := h n
    rw [hm'] at hrel
    generalize runAnnealBounded body n s = a at hrel
    cases hrel with
    | running s' _ _ => exact ⟨s', rfl⟩
  · intro h n
    have hrel := runLoop_universal_simulation hsim n hinv
    obtain ⟨s', hs'⟩ := h n
    rw [hs'] at hrel
    generalize runLoopFuel H n m = o at hrel
    cases hrel with
    | running _ m' _ => exact ⟨m', rfl⟩

/-- Under a step-closed simulation, an Anneal execution that never stops
gives `lean-miri` an infinite safe run with no terminal outcome. -/
theorem miri_infiniteRun_of_anneal_forever (hsim : StepClosedSim body H Inv RetRel)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m)
    (h : ∀ n, ∃ s', runAnnealBounded body n s = .running s') :
    Miri.OperationalSafety.InfiniteRun (miriSystem H) m ∧ (miriSystem H).Safe m ∧
      ∀ o, ¬ (miriSystem H).ReachesOutcome m o :=
  miri_infinite_of_forall_running ((runLoop_forever_iff hsim hinv).2 h)

end InfiniteRuns

theorem forall_running_of_infiniteRun {H : AnnealMiriHooks} {m : AnnealStepState}
    (h : Miri.OperationalSafety.InfiniteRun (miriSystem H) m) :
    ∀ n, ∃ m', runLoopFuel H n m = .running m' := by
  obtain ⟨run, h0, hstep⟩ := h
  have hrun : ∀ n k, runLoopFuel H n (run k) = .running (run (k + n)) := by
    intro n
    induction n with
    | zero => intro k; rfl
    | succ n ih =>
      intro k
      rw [runLoopFuel_succ, (hstep k).1]
      dsimp only
      rw [array_isEmpty_eq_false (hstep k).2]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih (k + 1), show k + 1 + n = k + (n + 1) by omega]
  intro n
  exact ⟨run n, by rw [← h0, hrun n 0, Nat.zero_add]⟩

/-- Under a step-closed simulation, `lean-miri` has an infinite run iff Anneal never stops. -/
theorem infiniteRun_iff_anneal_forever {body : CapturedMir} {H : AnnealMiriHooks}
    {Inv : MachineState → AnnealStepState → Prop}
    {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}
    (hsim : StepClosedSim body H Inv RetRel) {s : MachineState} {m : AnnealStepState}
    (hinv : Inv s m) :
    Miri.OperationalSafety.InfiniteRun (miriSystem H) m ↔
      ∀ n, ∃ s', runAnnealBounded body n s = .running s' :=
  ⟨fun h => (runLoop_forever_iff hsim hinv).1 (forall_running_of_infiniteRun h),
    fun h => (miri_infiniteRun_of_anneal_forever hsim hinv h).1⟩

/-! ## 9. Unconditional closed fragment: `InSafeScalarFragment` -/

/-- `lean-miri`'s locals on entry to a body with `n` locals and no arguments:
the return place `_0` is live and uninitialized and every other local is dead,
as in Anneal's `initLocalsAux`. -/
def miriEntryLocals (n : Nat) :
    Array (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :=
  ((List.range n).map fun i =>
    if i = 0 then { value := .live (.immediate .uninit), layout := none }
    else { value := .dead, layout := none }).toArray

/-- Layout recorded in the root frame's return place. -/
def entryReturnLayout (body : CapturedMir) : Miri.Interpreter.LocalLayout :=
  match body.localDecls with
  | d :: _ => translateTy d.ty body.layouts
  | [] => translateTy { kind := .tuple [], layoutIdx := 0 } body.layouts

/-- `lean-miri`'s root frame on entry to `body`. -/
def miriEntryFrame (body : CapturedMir) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody body
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (entryReturnLayout body) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := miriEntryLocals body.localDecls.length
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- `lean-miri`'s single-threaded state on entry to `body`. -/
def miriEntryState (body : CapturedMir) : AnnealStepState :=
  { stack := ⟨#[miriEntryFrame body]⟩, machine := AnnealMachine.empty }

theorem miriEntryLocals_getElem? (n i : Nat) :
    (miriEntryLocals n)[i]? =
      if i < n then
        some (if i = 0 then { value := .live (.immediate .uninit), layout := none }
          else { value := .dead, layout := none })
      else none := by
  unfold miriEntryLocals
  rw [List.getElem?_toArray, List.getElem?_map]
  by_cases h : i < n
  · have hr : (List.range n)[i]? = some i := by
      rw [List.getElem?_eq_getElem (by simpa using h)]
      simp
    rw [hr]
    simp [h]
  · have hr : (List.range n)[i]? = none := List.getElem?_eq_none (by simpa using h)
    rw [hr]
    simp [h]

theorem miriEntryLocals_size (n : Nat) : (miriEntryLocals n).size = n := by
  simp [miriEntryLocals]

theorem initLocalsAux_succ_nil (k : Nat) (ds : List LocalDecl) (i : Nat) :
    get? (initLocalsAux (k + 1) ds []) i = if i < ds.length then some .dead else none := by
  induction ds generalizing k i with
  | nil => simp [initLocalsAux, get?]
  | cons d ds ih =>
    cases i with
    | zero => simp [initLocalsAux, get?]
    | succ i =>
      show get? (initLocalsAux (k + 1) ds []) i = _
      rw [ih k i]
      by_cases hi : i < ds.length <;> simp [hi]

theorem initLocalsAux_succ_nil_length (k : Nat) (ds : List LocalDecl) :
    (initLocalsAux (k + 1) ds []).length = ds.length := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih =>
    show (initLocalsAux (k + 1) ds []).length + 1 = ds.length + 1
    rw [ih k]

theorem entry_locals_get (body : CapturedMir) (i : Nat) :
    get? (initMachineState body []).frame.locals i =
      if i < body.localDecls.length then some (if i = 0 then LocalSlot.uninit else .dead)
      else none := by
  change get? (initLocalsAux 0 body.localDecls []) i = _
  cases hd : body.localDecls with
  | nil => simp [initLocalsAux, get?]
  | cons d ds =>
    cases i with
    | zero => simp [initLocalsAux, get?]
    | succ i =>
      show get? (initLocalsAux (0 + 1) ds []) i = _
      rw [initLocalsAux_succ_nil 0 ds i]
      by_cases hi : i < ds.length <;> simp [hi]

theorem entry_locals_length (body : CapturedMir) :
    (initMachineState body []).frame.locals.length = body.localDecls.length := by
  change (initLocalsAux 0 body.localDecls []).length = _
  cases body.localDecls with
  | nil => rfl
  | cons d ds =>
    show (initLocalsAux (0 + 1) ds []).length + 1 = ds.length + 1
    rw [initLocalsAux_succ_nil_length 0 ds]

/-- The entry states of Anneal (`initMachineState body []`) and `lean-miri`
(`miriEntryState body`) are `StateRel`-related for every body. -/
theorem stateRel_entry (body : CapturedMir) :
    StateRel body (initMachineState body []) (miriEntryState body) := by
  refine StateRel.mk (miriEntryFrame body) rfl rfl ⟨_, rfl⟩ ?_ rfl rfl rfl rfl rfl ?_
  · refine
      { body_eq := rfl
        location_eq := rfl
        af_locals_len := entry_locals_length body
        mf_locals_size := miriEntryLocals_size _
        locals_rel := ?_ }
    intro i decl slot mls hdecl hslot hmls
    have hi : i < body.localDecls.length := by
      rw [get?_eq_getElem?] at hdecl
      exact (List.getElem?_eq_some_iff.1 hdecl).1
    rw [entry_locals_get] at hslot
    change (miriEntryLocals body.localDecls.length)[i]? = some mls at hmls
    rw [miriEntryLocals_getElem?] at hmls
    simp only [hi, ↓reduceIte] at hslot hmls
    by_cases h0 : i = 0
    · simp only [h0, ↓reduceIte] at hslot hmls
      injection hslot with hslot
      injection hmls with hmls
      subst hslot hmls
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · simp only [h0, ↓reduceIte] at hslot hmls
      injection hslot with hslot
      injection hmls with hmls
      subst hslot hmls
      exact .dead none (fun _ h => nomatch h)
  · apply MemoryAllocDisjoint.of_no_indirect
    intro k x hx mp hmp
    change (miriEntryLocals body.localDecls.length)[k]? = some x at hx
    rw [miriEntryLocals_getElem?] at hx
    split at hx
    · split at hx <;> (injection hx with hx; subst hx; cases hmp)
    · cases hx

theorem entry_immediate (body : CapturedMir) (nonAddrTaken : Nat → Prop) :
    NonAddrTakenImmediate body nonAddrTaken (miriEntryState body) := by
  intro tf htf idx _ _ _ mls hmls mp hmp
  have htf' : tf = miriEntryFrame body := by
    injection htf with h; injection h with h; exact h.symm
  subst htf'
  change (miriEntryLocals body.localDecls.length)[idx]? = some mls at hmls
  rw [miriEntryLocals_getElem?] at hmls
  split at hmls
  · split at hmls <;> (injection hmls with hmls; subst hmls; cases hmp)
  · cases hmls

/-- The `LM-1.1` closed invariant: `StateRel`, an in-bounds program counter, and
immediate representation of every non-address-taken local. -/
def ScalarFragmentInv (body : CapturedMir) (nonAddrTaken : Nat → Prop)
    (s : MachineState) (m : AnnealStepState) : Prop :=
  StateRel body s m ∧ ValidFrameLocation body s.frame ∧ NonAddrTakenImmediate body nonAddrTaken m

/-- Return-value relation of the `LM-1` fragments: the operand is an immediate
`ImmediateRel`-related at the type of `_0`. -/
def ImmediateRetRel (body : CapturedMir) (retVal : Value)
    (v : Miri.Interpreter.Operand AnnealProv) : Prop :=
  ∃ decl0 imm0, get? body.localDecls 0 = some decl0 ∧ v = .immediate imm0 ∧
    ImmediateRel decl0.ty body.layouts retVal imm0

/-- Lift an `LM-1` `StepRel` (with `Inv` holding at every related post-state)
to `Lockstep` over the `annealMiriHooks` interpreter. -/
theorem StepRel.toLockstep {body : CapturedMir} {Inv : MachineState → AnnealStepState → Prop}
    {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRel body m aRes mRes)
    (hinv : ∀ s' m', aRes = .step s' → mRes = (m', .ok true) → StateRel body s' m' → Inv s' m') :
    Lockstep (annealMiriHooks body) Inv (ImmediateRetRel body) m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    have hne : m'.stack.frames ≠ #[] := by
      obtain ⟨tf, hf, _⟩ := id hrel
      rw [hf]; intro h; cases h
    exact .emitStep .silent s' m' (hinv s' m' rfl rfl hrel) hne
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (by
      change (annealControlHooks.returnOperand () m).2 = _; rw [hop])
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) ⟨fun _ => rfl, fun _ => rfl⟩

/-- **Unconditional closed-fragment instance.** For every body in the syntactic
`LM-1.1` scalar fragment (`WellTypedBody`: multi-block `Goto` control flow
including loops, `Return`, `Unreachable`, `StorageLive` / `StorageDead`, and
assignments of constants, copies, unary operators, and wrapping, checked
(`(T, bool)` pair), comparison, bitwise, and shift binary operators),
`ScalarFragmentInv` is step-closed with no per-step hypotheses. -/
theorem scalarFragment_stepClosedSim {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    (hbody : WellTypedBody body nonAddrTaken) :
    StepClosedSim body (annealMiriHooks body) (ScalarFragmentInv body nonAddrTaken)
      (ImmediateRetRel body) := by
  refine ⟨fun s m ⟨hstate, hloc, himm⟩ => ?_⟩
  have hstep := step_wellTypedBody_simulation hbody hstate hloc himm
  have hloc' := fun s' (hs : stepMirFn body s = .step s') =>
    ValidFrameLocation.preserved hbody hstate hloc hs
  have himm' := NonAddrTakenImmediate.preserved hbody hstate hloc himm
  refine StepRel.toLockstep hstep fun s' m' ha hm hrel => ⟨hrel, hloc' s' ha, ?_⟩
  change Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
    (m', .ok true) at hm
  have h := himm' (by rw [hm])
  rw [hm] at h
  exact h

/-- `InSafeScalarFragment body`: the syntactic, unconditional `LM-1.1` scalar
fragment with every local immediate, over a nonempty body. -/
structure InSafeScalarFragment (body : CapturedMir) : Prop where
  wellTyped : WellTypedBody body
  blocks_ne : body.basicBlocks ≠ []

/-- The entry states satisfy the closed invariant. -/
theorem scalarFragment_entry {body : CapturedMir} (hfrag : InSafeScalarFragment body) :
    ScalarFragmentInv body (fun _ => True) (initMachineState body []) (miriEntryState body) := by
  refine ⟨stateRel_entry body, ?_, entry_immediate body _⟩
  cases hb : body.basicBlocks with
  | nil => exact absurd hb hfrag.blocks_ne
  | cons bb bbs => exact ⟨bb, by rw [hb]; rfl, Nat.zero_le _⟩

section ScalarFragment

variable {body : CapturedMir} (hfrag : InSafeScalarFragment body)
include hfrag

/-- `TreeSafe (mirCallTree body []) ↔ System.Safe` for the unconditional fragment. -/
theorem scalarFragment_treeSafe_iff_miriSafe :
    TreeSafe (mirCallTree body []) ↔
      (miriSystem (annealMiriHooks body)).Safe (miriEntryState body) :=
  treeSafe_iff_miriSafe (scalarFragment_stepClosedSim hfrag.wellTyped) (scalarFragment_entry hfrag)

/-- Bidirectional finite-step UB reachability for the unconditional fragment. -/
theorem scalarFragment_reachesUB_iff :
    MirReachesUB (mirCallTree body []) ↔
      ∃ e, (miriSystem (annealMiriHooks body)).ReachesOutcome (miriEntryState body)
        (.undefinedBehavior e) :=
  reachesUB_iff_miriReachesUB (scalarFragment_stepClosedSim hfrag.wellTyped)
    (scalarFragment_entry hfrag)

/-- Partial-correctness equivalence for the unconditional fragment. -/
theorem scalarFragment_partialCorrect_iff (postA : Value → Prop)
    (postM : Miri.Interpreter.Operand AnnealProv → Prop)
    (hpost : ∀ retVal v, ImmediateRetRel body retVal v → (postA retVal ↔ postM v)) :
    (miriSystem (annealMiriHooks body)).PartialCorrect (miriEntryState body) postM ↔
      ∀ tr retVal mem, ReachesRet (mirCallTree body []) tr (.normal (retVal, mem)) →
        postA retVal :=
  partialCorrect_iff_annealPostcondition (scalarFragment_stepClosedSim hfrag.wellTyped)
    (scalarFragment_entry hfrag) postA postM hpost

/-- Multi-step `RunLoop` simulation for the unconditional fragment, for every fuel. -/
theorem scalarFragment_runLoop_simulation (fuel : Nat) :
    RunLoopRel (ScalarFragmentInv body (fun _ => True)) (ImmediateRetRel body)
      (runAnnealBounded body fuel (initMachineState body []))
      (runLoopFuel (annealMiriHooks body) fuel (miriEntryState body)) :=
  runLoop_universal_simulation (scalarFragment_stepClosedSim hfrag.wellTyped) fuel
    (scalarFragment_entry hfrag)

/-- Divergence correspondence for the unconditional fragment. -/
theorem scalarFragment_infiniteRun_iff :
    Miri.OperationalSafety.InfiniteRun (miriSystem (annealMiriHooks body)) (miriEntryState body) ↔
      ∀ n, ∃ s', runAnnealBounded body n (initMachineState body []) = .running s' :=
  infiniteRun_iff_anneal_forever (scalarFragment_stepClosedSim hfrag.wellTyped)
    (scalarFragment_entry hfrag)

end ScalarFragment

/-! ## 10. Bridges from the `LM-1` … `LM-4.2` step relations -/

section Bridges

variable {core : Unit → AnnealStepState → Miri.Interpreter.StepResult AnnealStepState Bool}

/-- An interpreter whose root-frame return reads `_0` through `annealControlHooks`
(the `LM-1`, `LM-2`, `LM-3`, and `LM-4.2` interpreters). -/
def rootHooks (core : Unit → AnnealStepState → Miri.Interpreter.StepResult AnnealStepState Bool) :
    AnnealMiriHooks :=
  ⟨core, annealControlHooks.returnOperand⟩

theorem frames_ne_of_eq_singleton {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : m.stack.frames = #[tf]) : m.stack.frames ≠ #[] := by
  rw [h]; intro h'; cases h'

theorem retRoot_operand {m : AnnealStepState} {imm0 : Miri.Interpreter.Immediate AnnealProv}
    (hop : annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0))) :
    ((rootHooks core).returnOperand () m).2 = .ok (.immediate imm0) := by
  change (annealControlHooks.returnOperand () m).2 = _
  rw [hop]

theorem ub_faultAgrees (msg : String) :
    FaultAgrees .ub (.undefinedBehavior msg) := ⟨fun _ => rfl, fun _ => rfl⟩

/-- `LM-1.2` `StepObsRel` (`SwitchInt` branch observations) as `Lockstep`. -/
theorem StepObsRel.toLockstep {body : CapturedMir} {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop} (h : StepObsRel body m aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRel body s' m' → Inv s' m') :
    Lockstep (rootHooks core) Inv (ImmediateRetRel body) m aRes mRes := by
  cases h with
  | emitStep obs s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep obs s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-2.2` `StepRelLM2_2` (struct / tuple projections) as `Lockstep`. -/
theorem StepRelLM2_2.toLockstep {body : CapturedMir} {env : StructTypeEnv}
    {stEnv' : LM2_2StaticEnv} {b' : Nat} {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}
    (h : StepRelLM2_2 body env stEnv' b' m aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM2_2 body env stEnv' b' s' m' → Inv s' m') :
    Lockstep (rootHooks core) Inv RetRel m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-2.3` `StepRelLM2_3` (multi-variant enums, `Downcast`, `SwitchInt`) as `Lockstep`. -/
theorem StepRelLM2_3.toLockstep {body : CapturedMir} {env : EnumTypeEnv} {b' : Nat}
    {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepRelLM2_3 body env b' m aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM2_3 body env b' s' m' → Inv s' m') :
    Lockstep (rootHooks core) Inv (ImmediateRetRel body) m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | emitStep obs s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep obs s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-2.4` `StepRelLM2_4` (unions) as `Lockstep`. -/
theorem StepRelLM2_4.toLockstep {body : CapturedMir} {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}
    (h : StepRelLM2_4 body m aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM2_4 body s' m' → Inv s' m') :
    Lockstep (rootHooks core) Inv RetRel m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-3.1` / `LM-4.2` `StepRelLM3_1` (raw pointers, intrinsics) as `Lockstep`. -/
theorem StepRelLM3_1.toLockstep {body : CapturedMir} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepRelLM3_1 body m allocMap aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM3_1 body s' m' allocMap → Inv s' m') :
    Lockstep (rootHooks core) Inv (ImmediateRetRel body) m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- Return relation of `LM-3.2`: an immediate `ImmediateRelLM3_2`-related at `_0`'s type. -/
def RefRetRel (body : CapturedMir) (allocMap : List AllocMapEntry) (retVal : Value)
    (v : Miri.Interpreter.Operand AnnealProv) : Prop :=
  ∃ decl0 imm0, get? body.localDecls 0 = some decl0 ∧ v = .immediate imm0 ∧
    ImmediateRelLM3_2 allocMap decl0.ty body.layouts retVal imm0

/-- `LM-3.2` `StepRelLM3_2` (safe references, Tree Borrows hierarchy) as `Lockstep`. -/
theorem StepRelLM3_2.toLockstep {body : CapturedMir} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepRelLM3_2 body m allocMap aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM3_2 body s' m' allocMap → Inv s' m') :
    Lockstep (rootHooks core) Inv (RefRetRel body allocMap) m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- The `LM-4.1` multi-frame interpreter (`annealControlHooksLM4_1` reads `_0`). -/
def multiFrameHooks (rootBody : CapturedMir)
    (core : Unit → AnnealStepState → Miri.Interpreter.StepResult AnnealStepState Bool) :
    AnnealMiriHooks :=
  ⟨core, (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).returnOperand⟩

/-- Return relation of `LM-4.1`: an immediate or memory-backed `_0`. -/
def MultiFrameRetRel (rootBody : CapturedMir) (retVal : Value)
    (v : Miri.Interpreter.Operand AnnealProv) : Prop :=
  ∃ decl0, get? rootBody.localDecls 0 = some decl0 ∧
    ((∃ imm0, v = .immediate imm0 ∧ ImmediateRel decl0.ty rootBody.layouts retVal imm0) ∨
      (∃ mach mp0, v = .indirect mp0 ∧ MemPlaceRel mach decl0.ty rootBody.layouts (some retVal) mp0))

/-- `LM-4.1` `StepRelMultiFrame` (calls, returns, `GlobalState.endCall`) as `Lockstep`. -/
theorem StepRelMultiFrame.toLockstep {rootBody : CapturedMir} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepRelMultiFrame rootBody m aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → MultiFrameStateRel rootBody s' m' → Inv s' m') :
    Lockstep (multiFrameHooks rootBody core) Inv (MultiFrameRetRel rootBody) m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) hrel.frames_ne_empty
  | retRoot decl0 retVal retOp mem' m' hdecl hop hrel hm' =>
    subst hm'
    refine .retRoot retVal mem' _ retOp rfl (by
      change ((annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).returnOperand () m).2 = _
      rw [hop]) ⟨decl0, hdecl, ?_⟩
    rcases hrel with ⟨imm0, h1, h2⟩ | ⟨mp0, h1, h2⟩
    · exact Or.inl ⟨imm0, h1, h2⟩
    · exact Or.inr ⟨m.machine, mp0, h1, h2⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- Generic multi-step lifting: an invariant whose every pair takes a
`Lockstep`-related step back into the invariant is a step-closed simulation,
so every relation above lifts to `runLoop_universal_simulation`,
`treeSafe_iff_miriSafe`, `reachesUB_iff_miriReachesUB`, and
`partialCorrect_iff_annealPostcondition` as soon as its per-step theorem is
shown on a step-closed fragment. -/
theorem stepClosedSim_of_lockstep {body : CapturedMir} {H : AnnealMiriHooks}
    {Inv : MachineState → AnnealStepState → Prop}
    {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}
    (h : ∀ s m, Inv s m → Lockstep H Inv RetRel m (stepMirFn body s) (H.coreStep () m)) :
    StepClosedSim body H Inv RetRel :=
  ⟨h⟩

/-- `LM-2.3` lifting (`StateRelLM2_3`, any stack-allocation budget). -/
theorem stepClosedSim_of_stepRelLM2_3 {body : CapturedMir} {env : EnumTypeEnv}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m b, StateRelLM2_3 body env b s m → Frag s m → ∃ b',
      StepRelLM2_3 body env b' m (stepMirFn body s) (core () m) ∧
      ∀ s' m', core () m = (m', .ok true) → StateRelLM2_3 body env b' s' m' → Frag s' m') :
    StepClosedSim body (rootHooks core) (fun s m => (∃ b, StateRelLM2_3 body env b s m) ∧ Frag s m)
      (ImmediateRetRel body) := by
  refine ⟨fun s m ⟨⟨b, hrel⟩, hfrag⟩ => ?_⟩
  obtain ⟨b', hstep, hpres⟩ := h s m b hrel hfrag
  exact StepRelLM2_3.toLockstep hstep fun s' m' hm hrel' => ⟨⟨b', hrel'⟩, hpres s' m' hm hrel'⟩

/-- `LM-3.1` / `LM-4.2` lifting (`StateRelLM3_1`, any allocation map). -/
theorem stepClosedSim_of_stepRelLM3_1 {body : CapturedMir}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m a, StateRelLM3_1 body s m a → Frag s m → ∃ a',
      StepRelLM3_1 body m a' (stepMirFn body s) (core () m) ∧
      ∀ s' m', core () m = (m', .ok true) → StateRelLM3_1 body s' m' a' → Frag s' m') :
    StepClosedSim body (rootHooks core) (fun s m => (∃ a, StateRelLM3_1 body s m a) ∧ Frag s m)
      (ImmediateRetRel body) := by
  refine ⟨fun s m ⟨⟨a, hrel⟩, hfrag⟩ => ?_⟩
  obtain ⟨a', hstep, hpres⟩ := h s m a hrel hfrag
  exact StepRelLM3_1.toLockstep hstep fun s' m' hm hrel' => ⟨⟨a', hrel'⟩, hpres s' m' hm hrel'⟩

/-- `LM-4.1` lifting (`MultiFrameStateRel`). -/
theorem stepClosedSim_of_stepRelMultiFrame {rootBody : CapturedMir}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m, MultiFrameStateRel rootBody s m → Frag s m →
      StepRelMultiFrame rootBody m (stepMirFn rootBody s) (core () m) ∧
      ∀ s' m', core () m = (m', .ok true) → MultiFrameStateRel rootBody s' m' → Frag s' m') :
    StepClosedSim rootBody (multiFrameHooks rootBody core)
      (fun s m => MultiFrameStateRel rootBody s m ∧ Frag s m) (MultiFrameRetRel rootBody) := by
  refine ⟨fun s m ⟨hrel, hfrag⟩ => ?_⟩
  obtain ⟨hstep, hpres⟩ := h s m hrel hfrag
  exact StepRelMultiFrame.toLockstep hstep fun s' m' hm hrel' => ⟨hrel', hpres s' m' hm hrel'⟩

/-- Trace lifting: a `Lockstep`-related `emitStep` advances both machines
(`AnnealPath` and `MiriPath` one step) into the invariant. -/
theorem Lockstep.emitStep_lift {body : CapturedMir} {H : AnnealMiriHooks}
    {Inv : MachineState → AnnealStepState → Prop}
    {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}
    {s s' : MachineState} {m : AnnealStepState} {obs : MirObs}
    (h : Lockstep H Inv RetRel m (stepMirFn body s) (H.coreStep () m))
    (hs : stepMirFn body s = .emitStep obs s') :
    ∃ m', H.coreStep () m = (m', .ok true) ∧ m'.stack.frames ≠ #[] ∧ Inv s' m' := by
  generalize hc : H.coreStep () m = mRes at h
  rw [hs] at h
  generalize ha : MirStepNode.emitStep obs s' = aRes at h
  cases h with
  | emitStep obs' s'' m' hinv hne =>
    have : s'' = s' := by
      cases obs <;> cases obs' <;> simp only [MirStepNode.emitStep] at ha <;>
        first | (injection ha with ha; injection ha with ha; exact ha.symm) | cases ha |
          (injection ha with h₁ h₂; cases h₁; have := congrFun h₂ PUnit.unit;
            injection this with this; exact this.symm)
    subst this
    exact ⟨m', rfl, hne, hinv⟩
  | retRoot => cases obs <;> cases ha
  | fault => cases obs <;> cases ha

end Bridges

end LeanMiriSpec.Correspondence.Safety
