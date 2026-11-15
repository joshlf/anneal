-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.MirLiftCore
import Anneal.PureLift.BlockCfg
import Anneal.PureLift.Canaries

/-!
# `PureLift.BlockCfg` ↔ `MirLiftCore` Interoperability (`MirLiftCoreInterop`)

`Anneal.PureLift` is MIR-agnostic and `Init`-only: its block-indexed CFGs
(`BlockCfg.lean`) run through the fueled evaluator `runBlockCfg` and are
verified compositionally by `modular_block_cfg_sound` (partial correctness from
per-block `LocalBlockVC`s) and `runWhileFlowSteps_cutpoint_sound` (loop
cutpoints). `Anneal.MirLiftCore` provides the fuel-free total-correctness
calculus over generic deterministic machines (`PureMirExec.Step`,
`WpConverges`, `StepsTo`, header-targeted `runToTarget`, structural
`forRangeUp` loops) and its live instance `mirStep` / `runMirToBlock` /
`LiftBlockToJoin` over trusted `CapturedMir`.

This module (kept out of the `Init`-only `PureLift` core, since it imports the
`Trusted`-backed `MirLiftCore`) connects the two:

1. **Exact machine embedding.** `blockCfgStep stepBb` embeds a PureLift block
   step function into `PureMirExec.Step` (pending `.jumpWrapped` return
   wrappers are accumulated in the machine state; symbolic `.branchJump` forks,
   which a deterministic machine cannot represent, become `.fault`).
   `evalFuel_blockCfgStep` proves `PureMirExec.evalFuel` of the embedding
   *equals* `runBlockCfg` of the fork-free CFG `forkFree stepBb` at every fuel,
   and `runBlockCfg_of_forkFree_ret` transports every fork-free return back to
   the original CFG; on CFGs without symbolic forks the embedding is complete
   (`wpConverges_blockCfgStep_iff_of_noFork`).
2. **Partial correctness transfer** (`modular_block_cfg_sound`):
   `wpConverges_blockCfgStep_postRet` strengthens any fuel-free convergence
   proof of the embedded CFG with PureLift's `PostRet`, and
   `evalFuel_blockCfgStep_ne_faulted` rules out machine faults.
3. **Fuel-free total correctness.** `StepInv` / `wpConverges_of_stepInv_rank`
   (generic over every `PureMirExec.Step` machine) and
   `wpConverges_blockCfgStep_of_rank` / `runBlockCfg_total_of_rank` turn
   per-block `LocalBlockVC`s plus a ranking function into `WpConverges`, hence
   into an actual `runBlockCfg` return.
4. **Header-targeted segments** (`runToTarget`, the generic core of
   `runMirToBlock`): `runToTarget_of_stepInv` (generic) and
   `runBlockCfgToBlock_sound` (PureLift) propagate per-block VCs along
   segments, and `runMirToBlock_of_stepInv` instantiates the same rule for live
   MIR.
5. **Loops** (`runWhileFlowSteps_cutpoint_sound`, `forRangeUp`):
   `stepsTo_whileExit_of_runWhileFlowSteps` simulates every terminating
   structured `while` run by a fuel-free `StepsTo` segment of the 3-block loop
   CFG of `cfg_certificate_while_sound`; `while_cutpoint_wpConverges` composes it
   with `runWhileFlowSteps_cutpoint_sound`, and
   `whileLoop_stepsTo_forRangeUp` drives the same CFG with MirLiftCore's
   structural `stepsTo_forRangeUp` rule.
6. **Refinement into live MIR** (`runMirToBlock`, `LiftBlockToJoin`):
   `wpConverges_of_forwardSim` transports convergence of any machine along a
   forward simulation; `mirWpConverges_of_blockCfg_forwardSim` and
   `liftBlockToJoin_of_blockCfg_segment` instantiate it for live MIR, so a
   verified PureLift CFG plus per-step MIR simulation obligations (each
   dischargeable by `stepsTo_of_runMirToBlock_reached`) yields
   `MirWpConverges` / `LiftBlockToJoin` for the MIR body.
7. **Adequacy bridge** (`Adapter.pure_lift_sound`): `stepOperationalAdapter`
   realizes PureLift's `OperationalAdapter` by exact `k`-step paths
   (`StepPath`, interconvertible with `StepsTo`) of any MirLiftCore machine,
   and `pure_lift_stepsTo` / `pure_lift_mirWpConverges` turn
   `pure_lift_sound` into a fuel-free segment / live `MirWpConverges`.

All results are exercised non-vacuously at the end of the file on concrete
PureLift CFGs with symbolic data (`testCfgStep` countdown, and the `S6`
count-up loop over `StdVal` with symbolic bounds) and on the live two-block
`CapturedMir` body `liveInteropMirBody`.
-/

namespace Anneal.PureLift.MirLiftCoreInterop

open Anneal.PureLift
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## Generic Invariant Rules for `PureMirExec.Step` Machines -/

section Generic

variable {σ α : Type}

/-- `StepInv step I Post`: `I` is an inductive invariant of the deterministic
machine `step` under which `step` never faults and every halting value
satisfies `Post`. -/
def StepInv (step : σ → PureMirExec.Step σ α) (I : σ → Prop) (Post : α → Prop) :
    Prop :=
  ∀ s, I s →
    match step s with
    | .cont s' => I s'
    | .done v => Post v
    | .fault => False

/-- Under a `StepInv`, every bounded evaluation from an invariant state halts in
`Post` or runs out of fuel; it never faults. -/
theorem evalFuel_of_stepInv {step : σ → PureMirExec.Step σ α} {I : σ → Prop}
    {Post : α → Prop} (hInv : StepInv step I Post) :
    ∀ (k : Nat) (s : σ), I s →
      match PureMirExec.evalFuel step k s with
      | .halted v => Post v
      | .faulted => False
      | .outOfFuel => True
  | 0, _, _ => trivial
  | k + 1, s, hs => by
    have h := hInv s hs
    unfold PureMirExec.evalFuel
    cases hst : step s with
    | cont s' =>
      rw [hst] at h
      exact evalFuel_of_stepInv hInv k s' h
    | done v =>
      rw [hst] at h
      exact h
    | fault =>
      rw [hst] at h
      exact h

/-- `StepInv` along a `StepsTo` segment: every segment from an invariant state
ends in an invariant state. -/
theorem StepsTo.exists_of_stepInv {step : σ → PureMirExec.Step σ α}
    {I : σ → Prop} {Post : α → Prop} (hInv : StepInv step I Post)
    {s : σ} {mid : σ → Prop} (h : PureMirExec.StepsTo step s mid) (hs : I s) :
    Exists fun s' => mid s' ∧ I s' := by
  induction h with
  | refl hm => exact ⟨_, hm, hs⟩
  | @step s₀ s₁ _ hstep _ ih =>
    have h := hInv s₀ hs
    rw [hstep] at h
    exact ih h

/-- Header-targeted search (`runUntilTarget`) under a `StepInv`. -/
theorem runUntilTarget_of_stepInv {step : σ → PureMirExec.Step σ α}
    {atTarget : σ → Bool} {I : σ → Prop} {Post : α → Prop}
    (hInv : StepInv step I Post) :
    ∀ (bound : Nat) (s : σ), I s →
      match PureMirExec.runUntilTarget step atTarget bound s with
      | .reached s' => I s' ∧ atTarget s' = true
      | .halted v => Post v
      | .stuck => False
      | .outOfFuel => True
  | 0, s, hs => by
    unfold PureMirExec.runUntilTarget
    cases hT : atTarget s with
    | true => exact ⟨hs, hT⟩
    | false => trivial
  | bound + 1, s, hs => by
    unfold PureMirExec.runUntilTarget
    cases hT : atTarget s with
    | true => exact ⟨hs, hT⟩
    | false =>
      have h := hInv s hs
      cases hst : step s with
      | cont s' =>
        rw [hst] at h
        exact runUntilTarget_of_stepInv hInv bound s' h
      | done v =>
        rw [hst] at h
        exact h
      | fault =>
        rw [hst] at h
        exact h

/-- **Header-targeted segments preserve invariants** (`runToTarget`, the
generic core of `PureMirExec.runMirToBlock`): under a `StepInv`, a run from an
invariant state reaches an invariant target state, halts in `Post`, or runs out
of its step ceiling; it is never `.stuck`. -/
theorem runToTarget_of_stepInv {step : σ → PureMirExec.Step σ α}
    {atTarget : σ → Bool} {I : σ → Prop} {Post : α → Prop}
    (hInv : StepInv step I Post) (bound : Nat) (s : σ) (hs : I s) :
    match PureMirExec.runToTarget step atTarget bound s with
    | .reached s' => I s' ∧ atTarget s' = true
    | .halted v => Post v
    | .stuck => False
    | .outOfFuel => True := by
  have h := hInv s hs
  unfold PureMirExec.runToTarget
  cases hst : step s with
  | cont s' =>
    rw [hst] at h
    exact runUntilTarget_of_stepInv hInv bound s' h
  | done v =>
    rw [hst] at h
    exact h
  | fault =>
    rw [hst] at h
    exact h

/-- **Fuel-free total correctness from an invariant and a ranking function**:
if `rank` strictly decreases on every transition between invariant states, every
invariant state converges (`PureMirExec.WpConverges`) to `Post`. -/
theorem wpConverges_of_stepInv_rank {step : σ → PureMirExec.Step σ α}
    {I : σ → Prop} {Post : α → Prop} (hInv : StepInv step I Post)
    (rank : σ → Nat)
    (hRank : ∀ s s', I s → step s = .cont s' → rank s' < rank s) :
    ∀ s, I s → PureMirExec.WpConverges step s Post := by
  suffices hAll : ∀ (n : Nat) (s : σ), rank s < n → I s →
      PureMirExec.WpConverges step s Post from
    fun s hs => hAll (rank s + 1) s (Nat.lt_succ_self _) hs
  intro n
  induction n with
  | zero =>
    intro s hlt _
    exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro s hlt hs
    have h := hInv s hs
    cases hst : step s with
    | cont s' =>
      rw [hst] at h
      have hDec := hRank s s' hs hst
      exact PureMirExec.WpConverges.of_cont hst
        (ih s' (Nat.lt_of_lt_of_le hDec (Nat.le_of_lt_succ hlt)) h)
    | done v =>
      rw [hst] at h
      exact PureMirExec.WpConverges.of_done hst h
    | fault =>
      rw [hst] at h
      exact h.elim

end Generic

/-! ## Forward Simulation Between `PureMirExec.Step` Machines -/

section Simulation

variable {σ α τ β : Type}

/-- `ForwardSim stepA stepB R RetRel`: every transition of the source machine
`stepA` from an `R`-related state is matched by a (possibly empty) `StepsTo`
segment of the target machine `stepB` into a related state, and every halt of
`stepA` by convergence of `stepB` to a `RetRel`-related result. -/
def ForwardSim (stepA : σ → PureMirExec.Step σ α)
    (stepB : τ → PureMirExec.Step τ β) (R : σ → τ → Prop)
    (RetRel : α → β → Prop) : Prop :=
  ∀ s t, R s t →
    match stepA s with
    | .cont s' => PureMirExec.StepsTo stepB t (R s')
    | .done v => PureMirExec.WpConverges stepB t (RetRel v)
    | .fault => True

/-- **Convergence transfers along a forward simulation**: segments are glued
with MirLiftCore's fuel-free `StepsTo.bind_wp`, so no step count of the target
machine is ever mentioned. -/
theorem wpConverges_of_forwardSim {stepA : σ → PureMirExec.Step σ α}
    {stepB : τ → PureMirExec.Step τ β} {R : σ → τ → Prop}
    {RetRel : α → β → Prop} (hSim : ForwardSim stepA stepB R RetRel)
    {P : α → Prop} {s : σ} (h : PureMirExec.WpConverges stepA s P) :
    ∀ t, R s t →
      PureMirExec.WpConverges stepB t (fun o => Exists fun v => P v ∧ RetRel v o) := by
  obtain ⟨k, v, hk, hp⟩ := h
  induction k generalizing s with
  | zero => exact nomatch hk
  | succ k ih =>
    intro t hR
    have hS := hSim s t hR
    unfold PureMirExec.evalFuel at hk
    cases hst : stepA s with
    | cont s' =>
      rw [hst] at hS hk
      exact hS.bind_wp (fun t' hR' => ih hk t' hR')
    | done v' =>
      rw [hst] at hS hk
      injection hk with hv
      subst hv
      exact PureMirExec.WpConverges.mono (fun o ho => ⟨v', hp, ho⟩) hS
    | fault =>
      rw [hst] at hk
      exact nomatch hk

/-- `SegmentSim stepA stepB R`: every transition of `stepA` from an `R`-related
state is matched by a `StepsTo` segment of `stepB` into a related state. -/
def SegmentSim (stepA : σ → PureMirExec.Step σ α)
    (stepB : τ → PureMirExec.Step τ β) (R : σ → τ → Prop) : Prop :=
  ∀ s t s', R s t → stepA s = .cont s' → PureMirExec.StepsTo stepB t (R s')

/-- Segments transfer along a `SegmentSim`: a source segment to `mid` is matched
by a target segment to a state related to some `mid` state. -/
theorem stepsTo_of_segmentSim {stepA : σ → PureMirExec.Step σ α}
    {stepB : τ → PureMirExec.Step τ β} {R : σ → τ → Prop}
    (hSim : SegmentSim stepA stepB R) {s : σ} {mid : σ → Prop}
    (h : PureMirExec.StepsTo stepA s mid) :
    ∀ t, R s t →
      PureMirExec.StepsTo stepB t (fun t' => Exists fun s' => mid s' ∧ R s' t') := by
  induction h with
  | refl hm =>
    intro t hR
    exact PureMirExec.StepsTo.refl ⟨_, hm, hR⟩
  | @step s₀ s₁ _ hstep _ ih =>
    intro t hR
    exact (hSim s₀ t s₁ hR hstep).trans (fun t' hR' => ih t' hR')

/-- A `ForwardSim` restricted to transitions is a `SegmentSim`. -/
theorem ForwardSim.segmentSim {stepA : σ → PureMirExec.Step σ α}
    {stepB : τ → PureMirExec.Step τ β} {R : σ → τ → Prop}
    {RetRel : α → β → Prop} (hSim : ForwardSim stepA stepB R RetRel) :
    SegmentSim stepA stepB R := by
  intro s t s' hR hst
  have h := hSim s t hR
  rw [hst] at h
  exact h

end Simulation

/-! ## Embedding PureLift Block CFGs into `PureMirExec.Step` -/

section BlockMachine

variable {State Ret : Type}

/-- Machine state of the embedding: the return-value wrapper accumulated from
`.jumpWrapped` transitions, the current block, and the block-entry state. -/
structure BlockMachineState (State Ret : Type) where
  wrap : Ret → Ret
  bb : Nat
  st : State

/-- Deterministic embedding of a PureLift block step function into
MirLiftCore's generic machine. `.jumpWrapped` composes its wrapper into the
pending wrapper, `.ret` halts with the wrapped value, and a symbolic
`.branchJump` fork (two successor runs merged afterwards, which no
deterministic machine can represent) becomes `.fault`, just as `mirStep` maps
external calls to `.fault`. -/
def blockCfgStep (stepBb : Nat → State → BlockStepResult State Ret)
    (s : BlockMachineState State Ret) :
    PureMirExec.Step (BlockMachineState State Ret) Ret :=
  match stepBb s.bb s.st with
  | .jump nextBb st' => .cont ⟨s.wrap, nextBb, st'⟩
  | .jumpWrapped wrapRet nextBb st' =>
    .cont ⟨fun v => s.wrap (wrapRet v), nextBb, st'⟩
  | .branchJump _ _ _ _ => .fault
  | .ret v => .done (s.wrap v)
  | .fault => .fault

/-- `stepBb` with every symbolic `.branchJump` fork replaced by `.fault`. -/
def forkFree (stepBb : Nat → State → BlockStepResult State Ret) :
    Nat → State → BlockStepResult State Ret :=
  fun bb st =>
    match stepBb bb st with
    | .jump nextBb st' => .jump nextBb st'
    | .jumpWrapped wrapRet nextBb st' => .jumpWrapped wrapRet nextBb st'
    | .branchJump _ _ _ _ => .fault
    | .ret v => .ret v
    | .fault => .fault

/-- `BlockCfgOutcome` as a `PureMirExec.FuelResult`, after applying the pending
wrapper `wrap` to a returned value. -/
def outcomeToFuel (wrap : Ret → Ret) : BlockCfgOutcome Ret → PureMirExec.FuelResult Ret
  | .ret v => .halted (wrap v)
  | .diverged => .outOfFuel
  | .fault => .faulted

/-- **Exact embedding**: at every fuel, MirLiftCore's `evalFuel` of the
embedded machine is `runBlockCfg` of the fork-free CFG (fuel exhaustion is
`.outOfFuel`, never a fault or a halt). -/
theorem evalFuel_blockCfgStep (stepBb : Nat → State → BlockStepResult State Ret) :
    ∀ (k : Nat) (s : BlockMachineState State Ret),
      PureMirExec.evalFuel (blockCfgStep stepBb) k s =
        outcomeToFuel s.wrap (runBlockCfg (forkFree stepBb) s.bb s.st k)
  | 0, _ => rfl
  | k + 1, ⟨wrap, bb, st⟩ => by
    rw [runBlockCfg_succ]
    unfold PureMirExec.evalFuel
    dsimp only [blockCfgStep, forkFree]
    cases stepBb bb st with
    | jump nextBb st' =>
      exact evalFuel_blockCfgStep stepBb k ⟨wrap, nextBb, st'⟩
    | jumpWrapped wrapRet nextBb st' =>
      dsimp only
      rw [evalFuel_blockCfgStep stepBb k ⟨fun v => wrap (wrapRet v), nextBb, st'⟩]
      cases runBlockCfg (forkFree stepBb) nextBb st' k <;> rfl
    | branchJump _ _ _ _ => rfl
    | ret v => rfl
    | fault => rfl

/-- Every return of the fork-free CFG is a return of the original CFG, with the
same value and fuel. -/
theorem runBlockCfg_of_forkFree_ret
    (stepBb : Nat → State → BlockStepResult State Ret) :
    ∀ (k : Nat) (bb : Nat) (st : State) (v : Ret),
      runBlockCfg (forkFree stepBb) bb st k = .ret v →
      runBlockCfg stepBb bb st k = .ret v
  | 0, _, _, _, h => nomatch h
  | k + 1, bb, st, v, h => by
    rw [runBlockCfg_succ] at h ⊢
    dsimp only [forkFree] at h
    cases hst : stepBb bb st with
    | jump nextBb st' =>
      rw [hst] at h
      exact runBlockCfg_of_forkFree_ret stepBb k nextBb st' v h
    | jumpWrapped wrapRet nextBb st' =>
      rw [hst] at h
      dsimp only at h ⊢
      cases hRun : runBlockCfg (forkFree stepBb) nextBb st' k with
      | ret v' =>
        rw [hRun] at h
        rw [runBlockCfg_of_forkFree_ret stepBb k nextBb st' v' hRun]
        exact h
      | diverged =>
        rw [hRun] at h
        exact nomatch h
      | fault =>
        rw [hRun] at h
        exact nomatch h
    | branchJump _ _ _ _ =>
      rw [hst] at h
      exact nomatch h
    | ret v' =>
      rw [hst] at h
      exact h
    | fault =>
      rw [hst] at h
      exact nomatch h

/-- A per-block VC that excludes symbolic forks on invariant states carries over
to the fork-free CFG. -/
theorem localBlockVC_forkFree (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC stepBb BlockInv PostRet)
    (hNoFork : ∀ bb st, BlockInv bb st →
      ∀ mergeRet thenBb elseBb st',
        stepBb bb st ≠ .branchJump mergeRet thenBb elseBb st') :
    LocalBlockVC (forkFree stepBb) BlockInv PostRet := by
  intro bb st hInv
  have hVC := hLocal bb st hInv
  dsimp only [forkFree]
  cases hst : stepBb bb st with
  | jump nextBb st' =>
    rw [hst] at hVC
    exact hVC
  | jumpWrapped wrapRet nextBb st' =>
    rw [hst] at hVC
    exact hVC
  | branchJump mergeRet thenBb elseBb st' =>
    exact hNoFork bb st hInv mergeRet thenBb elseBb st' hst
  | ret v =>
    rw [hst] at hVC
    exact hVC
  | fault =>
    rw [hst] at hVC
    exact hVC

/-- A converged run of the embedded machine (with the identity wrapper) is an
actual `runBlockCfg` return of the original CFG. -/
theorem runBlockCfg_of_wpConverges
    (stepBb : Nat → State → BlockStepResult State Ret) {bb : Nat} {st : State}
    {P : Ret → Prop}
    (h : PureMirExec.WpConverges (blockCfgStep stepBb) ⟨fun v => v, bb, st⟩ P) :
    Exists fun k => Exists fun v => runBlockCfg stepBb bb st k = .ret v ∧ P v := by
  obtain ⟨k, v, hk, hp⟩ := h
  rw [evalFuel_blockCfgStep] at hk
  dsimp only at hk
  cases hRun : runBlockCfg (forkFree stepBb) bb st k with
  | ret v' =>
    rw [hRun] at hk
    injection hk with hv
    subst hv
    exact ⟨k, v', runBlockCfg_of_forkFree_ret stepBb k bb st v' hRun, hp⟩
  | diverged =>
    rw [hRun] at hk
    exact nomatch hk
  | fault =>
    rw [hRun] at hk
    exact nomatch hk

/-- **Partial correctness transfer** (`modular_block_cfg_sound`): any fuel-free
convergence proof for the embedded CFG from a `BlockInv` state is strengthened
with PureLift's `PostRet` for free. -/
theorem wpConverges_blockCfgStep_postRet
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC stepBb BlockInv PostRet) {bb : Nat} {st : State}
    (hInv : BlockInv bb st) {Q : Ret → Prop}
    (h : PureMirExec.WpConverges (blockCfgStep stepBb) ⟨fun v => v, bb, st⟩ Q) :
    PureMirExec.WpConverges (blockCfgStep stepBb) ⟨fun v => v, bb, st⟩
      (fun v => Q v ∧ PostRet v) := by
  obtain ⟨k, v, hk, hq⟩ := h
  refine ⟨k, v, hk, hq, ?_⟩
  obtain ⟨k', v', hRun, hEq⟩ :=
    runBlockCfg_of_wpConverges stepBb (P := (· = v)) ⟨k, v, hk, rfl⟩
  subst hEq
  have hSpec :=
    modular_block_cfg_sound stepBb BlockInv PostRet hLocal k' bb st hInv
  rw [hRun] at hSpec
  exact hSpec

/-- **No machine faults** (`modular_block_cfg_sound` on the fork-free CFG):
from an invariant state the embedded machine never faults at any fuel. -/
theorem evalFuel_blockCfgStep_ne_faulted
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC (forkFree stepBb) BlockInv PostRet)
    (s : BlockMachineState State Ret) (hInv : BlockInv s.bb s.st) (k : Nat) :
    PureMirExec.evalFuel (blockCfgStep stepBb) k s ≠ .faulted := by
  rw [evalFuel_blockCfgStep]
  have hSpec :=
    modular_block_cfg_sound (forkFree stepBb) BlockInv PostRet hLocal k s.bb s.st
      hInv
  cases hRun : runBlockCfg (forkFree stepBb) s.bb s.st k with
  | ret v =>
    intro hEq
    exact nomatch hEq
  | diverged =>
    intro hEq
    exact nomatch hEq
  | fault =>
    rw [hRun] at hSpec
    exact hSpec.elim

/-- Machine-level invariant induced by a per-block VC: the block invariant
holds and the pending wrapper preserves `PostRet`. -/
def MachineInv (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (s : BlockMachineState State Ret) : Prop :=
  BlockInv s.bb s.st ∧ ∀ v, PostRet v → PostRet (s.wrap v)

/-- A fork-free per-block VC is a `StepInv` of the embedded machine. -/
theorem stepInv_blockCfgStep (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC (forkFree stepBb) BlockInv PostRet) :
    StepInv (blockCfgStep stepBb) (MachineInv BlockInv PostRet) PostRet := by
  intro s hs
  obtain ⟨hInv, hWrap⟩ := hs
  have hVC := hLocal s.bb s.st hInv
  dsimp only [forkFree] at hVC
  dsimp only [blockCfgStep]
  cases hst : stepBb s.bb s.st with
  | jump nextBb st' =>
    rw [hst] at hVC
    exact ⟨hVC, hWrap⟩
  | jumpWrapped wrapRet nextBb st' =>
    rw [hst] at hVC
    exact ⟨hVC.1, fun v hv => hWrap _ (hVC.2 v hv)⟩
  | branchJump _ _ _ _ =>
    rw [hst] at hVC
    exact hVC
  | ret v =>
    rw [hst] at hVC
    exact hWrap v hVC
  | fault =>
    rw [hst] at hVC
    exact hVC

/-- Header-targeted stepping of a PureLift CFG: one mandatory block step, then
stop at the first entry of block `target` (MirLiftCore's `runToTarget`, as in
`PureMirExec.runMirToBlock`). -/
def runBlockCfgToBlock (stepBb : Nat → State → BlockStepResult State Ret)
    (target bound : Nat) (s : BlockMachineState State Ret) :
    PureMirExec.TargetOutcome (BlockMachineState State Ret) Ret :=
  PureMirExec.runToTarget (blockCfgStep stepBb) (fun t => t.bb == target) bound s

/-- **Per-block VCs compose along header-targeted segments**: from an invariant
machine state, `runBlockCfgToBlock` reaches block `target` in an invariant state,
or returns a `PostRet` value, or exhausts its ceiling; it is never `.stuck`. -/
theorem runBlockCfgToBlock_sound (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC (forkFree stepBb) BlockInv PostRet)
    (target bound : Nat) (s : BlockMachineState State Ret)
    (hs : MachineInv BlockInv PostRet s) :
    match runBlockCfgToBlock stepBb target bound s with
    | .reached s' => s'.bb = target ∧ MachineInv BlockInv PostRet s'
    | .halted v => PostRet v
    | .stuck => False
    | .outOfFuel => True := by
  have h := runToTarget_of_stepInv (atTarget := fun t => t.bb == target)
    (stepInv_blockCfgStep stepBb BlockInv PostRet hLocal) bound s hs
  unfold runBlockCfgToBlock
  cases hRun : PureMirExec.runToTarget (blockCfgStep stepBb)
      (fun t => t.bb == target) bound s with
  | reached s' =>
    rw [hRun] at h
    exact ⟨beq_iff_eq.mp h.2, h.1⟩
  | halted v =>
    rw [hRun] at h
    exact h
  | stuck =>
    rw [hRun] at h
    exact h
  | outOfFuel => trivial

/-- **Fuel-free total correctness of PureLift CFGs**: a fork-free per-block VC
and a ranking function that decreases along every `.jump` / `.jumpWrapped`
edge between invariant states make every invariant machine state converge
(`PureMirExec.WpConverges`) to `PostRet`. -/
theorem wpConverges_blockCfgStep_of_rank
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC (forkFree stepBb) BlockInv PostRet)
    (rank : Nat → State → Nat)
    (hRankJump : ∀ bb st nextBb st', BlockInv bb st →
      stepBb bb st = .jump nextBb st' → rank nextBb st' < rank bb st)
    (hRankWrapped : ∀ bb st wrapRet nextBb st', BlockInv bb st →
      stepBb bb st = .jumpWrapped wrapRet nextBb st' →
      rank nextBb st' < rank bb st) :
    ∀ s, MachineInv BlockInv PostRet s →
      PureMirExec.WpConverges (blockCfgStep stepBb) s PostRet := by
  refine wpConverges_of_stepInv_rank
    (stepInv_blockCfgStep stepBb BlockInv PostRet hLocal)
    (fun s => rank s.bb s.st) ?_
  intro s s' hs hCont
  dsimp only [blockCfgStep] at hCont
  cases hst : stepBb s.bb s.st with
  | jump nextBb st' =>
    rw [hst] at hCont
    injection hCont with hEq
    subst hEq
    exact hRankJump s.bb s.st nextBb st' hs.1 hst
  | jumpWrapped wrapRet nextBb st' =>
    rw [hst] at hCont
    injection hCont with hEq
    subst hEq
    exact hRankWrapped s.bb s.st wrapRet nextBb st' hs.1 hst
  | branchJump _ _ _ _ =>
    rw [hst] at hCont
    exact nomatch hCont
  | ret _ =>
    rw [hst] at hCont
    exact nomatch hCont
  | fault =>
    rw [hst] at hCont
    exact nomatch hCont

/-- **Total correctness of `runBlockCfg`** derived through MirLiftCore's
fuel-free calculus: some fuel makes the CFG return a `PostRet` value. -/
theorem runBlockCfg_total_of_rank
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC (forkFree stepBb) BlockInv PostRet)
    (rank : Nat → State → Nat)
    (hRankJump : ∀ bb st nextBb st', BlockInv bb st →
      stepBb bb st = .jump nextBb st' → rank nextBb st' < rank bb st)
    (hRankWrapped : ∀ bb st wrapRet nextBb st', BlockInv bb st →
      stepBb bb st = .jumpWrapped wrapRet nextBb st' →
      rank nextBb st' < rank bb st)
    (bb : Nat) (st : State) (hInv : BlockInv bb st) :
    Exists fun k => Exists fun v => runBlockCfg stepBb bb st k = .ret v ∧ PostRet v :=
  runBlockCfg_of_wpConverges stepBb
    (wpConverges_blockCfgStep_of_rank stepBb BlockInv PostRet hLocal rank
      hRankJump hRankWrapped ⟨fun v => v, bb, st⟩ ⟨hInv, fun _ hv => hv⟩)

/-- A CFG without symbolic forks is its own fork-free CFG. -/
theorem forkFree_eq_of_noFork (stepBb : Nat → State → BlockStepResult State Ret)
    (hNoFork : ∀ bb st mergeRet thenBb elseBb st',
      stepBb bb st ≠ .branchJump mergeRet thenBb elseBb st') :
    forkFree stepBb = stepBb := by
  funext bb st
  dsimp only [forkFree]
  cases h : stepBb bb st with
  | jump _ _ => rfl
  | jumpWrapped _ _ _ => rfl
  | branchJump mergeRet thenBb elseBb st' =>
    exact absurd h (hNoFork bb st mergeRet thenBb elseBb st')
  | ret _ => rfl
  | fault => rfl

/-- **Completeness for fork-free CFGs**: on a CFG without symbolic forks, the
embedded machine converges exactly when `runBlockCfg` returns at some fuel, so
`runBlockCfg_of_wpConverges` is an equivalence. -/
theorem wpConverges_blockCfgStep_iff_of_noFork
    (stepBb : Nat → State → BlockStepResult State Ret)
    (hNoFork : ∀ bb st mergeRet thenBb elseBb st',
      stepBb bb st ≠ .branchJump mergeRet thenBb elseBb st')
    (bb : Nat) (st : State) (P : Ret → Prop) :
    PureMirExec.WpConverges (blockCfgStep stepBb) ⟨fun v => v, bb, st⟩ P ↔
      Exists fun k => Exists fun v => runBlockCfg stepBb bb st k = .ret v ∧ P v := by
  refine ⟨runBlockCfg_of_wpConverges stepBb, ?_⟩
  intro h
  obtain ⟨k, v, hRun, hP⟩ := h
  refine ⟨k, v, ?_, hP⟩
  rw [evalFuel_blockCfgStep, forkFree_eq_of_noFork stepBb hNoFork]
  dsimp only
  rw [hRun]
  rfl

end BlockMachine

/-! ## Loops: `runWhileFlowSteps_cutpoint_sound` and `forRangeUp` -/

section Loops

variable {Val : Type}

/-- The 3-block loop CFG of `cfg_certificate_while_sound`: header block `0`
branches on `cond` to body block `1` (which jumps back to `0`) or to exit block
`2` (which returns `retExpr`). -/
def whileLoopBlocks (cond : RvalOp Val) (body : FlowPlan Val)
    (retExpr : RvalOp Val) : List (BasicBlock Val) :=
  [⟨.skip, .branch cond 1 2⟩, ⟨body, .goto 0⟩, ⟨.skip, .ret retExpr⟩]

/-- Header step on a concretely `true` condition. -/
theorem blockCfgStep_whileHeader_true (alg : ValAlgebra Val) (cond : RvalOp Val)
    (body : FlowPlan Val) (retExpr : RvalOp Val)
    (wrap : FuncOut Val → FuncOut Val) (st : SymState Val) (cv : Val)
    (hCond : evalRval alg cond st = some cv) (hBool : alg.asBool cv = some true) :
    blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr))
      ⟨wrap, 0, st⟩ = .cont ⟨wrap, 1, st⟩ := by
  dsimp only [blockCfgStep, stepBasicBlock, whileLoopBlocks, listGetOpt,
    evalPlan, evalPlanOps, stepPlanOp, FlowPlan.skip, List.foldr]
  rw [hCond]
  dsimp only
  rw [hBool]

/-- Header step on a concretely `false` condition. -/
theorem blockCfgStep_whileHeader_false (alg : ValAlgebra Val) (cond : RvalOp Val)
    (body : FlowPlan Val) (retExpr : RvalOp Val)
    (wrap : FuncOut Val → FuncOut Val) (st : SymState Val) (cv : Val)
    (hCond : evalRval alg cond st = some cv) (hBool : alg.asBool cv = some false) :
    blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr))
      ⟨wrap, 0, st⟩ = .cont ⟨wrap, 2, st⟩ := by
  dsimp only [blockCfgStep, stepBasicBlock, whileLoopBlocks, listGetOpt,
    evalPlan, evalPlanOps, stepPlanOp, FlowPlan.skip, List.foldr]
  rw [hCond]
  dsimp only
  rw [hBool]

/-- Body step when the body falls through. -/
theorem blockCfgStep_whileBody (alg : ValAlgebra Val) (cond : RvalOp Val)
    (body : FlowPlan Val) (retExpr : RvalOp Val)
    (wrap : FuncOut Val → FuncOut Val) (st st' : SymState Val)
    (hBody : evalPlan alg body st = .ok (.continuing st')) :
    blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr))
      ⟨wrap, 1, st⟩ = .cont ⟨wrap, 0, st'⟩ := by
  dsimp only [blockCfgStep, stepBasicBlock, whileLoopBlocks, listGetOpt,
    List.foldr]
  rw [hBody]

/-- Exit step from a clean, handle-free state. -/
theorem blockCfgStep_whileExit (alg : ValAlgebra Val) (cond : RvalOp Val)
    (body : FlowPlan Val) (retExpr : RvalOp Val)
    (wrap : FuncOut Val → FuncOut Val) (st : SymState Val) (rv : Val)
    (hClean : stateCleanAtReturn st = true)
    (hRet : evalRval alg retExpr st = some rv)
    (hFree : handleFreeOut alg ⟨rv, collectRootMutVals st.loans⟩ = true) :
    blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr))
      ⟨wrap, 2, st⟩ = .done (wrap ⟨rv, collectRootMutVals st.loans⟩) := by
  dsimp only [blockCfgStep, stepBasicBlock, whileLoopBlocks, listGetOpt,
    evalPlan, evalPlanOps, stepPlanOp, FlowPlan.skip, List.foldr]
  rw [hClean]
  dsimp
  rw [hRet]
  dsimp
  rw [hFree]
  rfl

/-- **Structured loops are fuel-free CFG segments**: every structured run of
`runWhileFlowSteps` that falls through to `stFinal` is simulated by a
MirLiftCore `StepsTo` segment of the embedded 3-block loop CFG from header
block `0` to exit block `2`, at the same final state and with the pending
wrapper unchanged. -/
theorem stepsTo_whileExit_of_runWhileFlowSteps (alg : ValAlgebra Val)
    (cond : RvalOp Val) (body : FlowPlan Val) (retExpr : RvalOp Val) :
    ∀ (fuel : Nat) (wrap : FuncOut Val → FuncOut Val) (st stFinal : SymState Val),
      runWhileFlowSteps alg cond (evalPlan alg body) fuel st =
        .ok (.continuing stFinal) →
      PureMirExec.StepsTo
        (blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr)))
        ⟨wrap, 0, st⟩ (· = ⟨wrap, 2, stFinal⟩)
  | 0, wrap, st, stFinal, hWhile => by
    rw [runWhileFlowSteps_zero] at hWhile
    revert hWhile
    cases hCond : evalRval alg cond st with
    | none =>
      intro hFalse
      exact nomatch hFalse
    | some cv =>
      dsimp only
      cases hBool : alg.asBool cv with
      | none =>
        intro hFalse
        exact nomatch hFalse
      | some b =>
        cases b with
        | true =>
          intro hFalse
          exact nomatch hFalse
        | false =>
          intro hEq
          injection hEq with hFlow
          injection hFlow with hSt
          subst hSt
          exact PureMirExec.StepsTo.step
            (blockCfgStep_whileHeader_false alg cond body retExpr wrap st cv hCond
              hBool)
            (PureMirExec.StepsTo.refl rfl)
  | k + 1, wrap, st, stFinal, hWhile => by
    rw [runWhileFlowSteps_succ] at hWhile
    revert hWhile
    cases hCond : evalRval alg cond st with
    | none =>
      intro hFalse
      exact nomatch hFalse
    | some cv =>
      dsimp only
      cases hBool : alg.asBool cv with
      | none =>
        intro hFalse
        exact nomatch hFalse
      | some b =>
        cases b with
        | false =>
          intro hEq
          injection hEq with hFlow
          injection hFlow with hSt
          subst hSt
          exact PureMirExec.StepsTo.step
            (blockCfgStep_whileHeader_false alg cond body retExpr wrap st cv hCond
              hBool)
            (PureMirExec.StepsTo.refl rfl)
        | true =>
          dsimp only
          cases hBody : evalPlan alg body st with
          | fail =>
            intro hFalse
            exact nomatch hFalse
          | ok flow =>
            cases flow with
            | returned _ _ _ =>
              intro hFalse
              exact nomatch hFalse
            | guardedContinuing wrap1 st' c1 wrapMut1 =>
              dsimp only [prependGuardedWrap]
              cases runWhileFlowSteps alg cond (evalPlan alg body) k st' with
              | fail =>
                intro hFalse
                exact nomatch hFalse
              | ok flowRec =>
                cases flowRec <;> (intro hFalse; exact nomatch hFalse)
            | continuing st' =>
              dsimp only
              intro hRec
              exact PureMirExec.StepsTo.step
                (blockCfgStep_whileHeader_true alg cond body retExpr wrap st cv
                  hCond hBool)
                (PureMirExec.StepsTo.step
                  (blockCfgStep_whileBody alg cond body retExpr wrap st st' hBody)
                  (stepsTo_whileExit_of_runWhileFlowSteps alg cond body retExpr k
                    wrap st' stFinal hRec))

/-- **Loop cutpoints compose with fuel-free lifting**
(`runWhileFlowSteps_cutpoint_sound` + `StepsTo.bind_wp`): an inductive loop
invariant `Inv` with a ranking measure `rank` (the cutpoint hypotheses) and an
exit obligation make the embedded 3-block loop CFG converge
(`PureMirExec.WpConverges`) to `Post` from every invariant header state. -/
theorem while_cutpoint_wpConverges (alg : ValAlgebra Val) (cond : RvalOp Val)
    (body : FlowPlan Val) (retExpr : RvalOp Val)
    (Inv : SymState Val → Prop) (rank : SymState Val → Nat)
    (hStep : ∀ s, Inv s →
      Exists fun cv => evalRval alg cond s = some cv ∧
        ((alg.asBool cv = some false ∧ rank s = 0) ∨
         (alg.asBool cv = some true ∧
          Exists fun s' =>
            evalPlan alg body s = .ok (.continuing s') ∧
            Inv s' ∧ rank s = rank s' + 1)))
    (Post : FuncOut Val → Prop)
    (hExit : ∀ s, Inv s →
      (Exists fun cv => evalRval alg cond s = some cv ∧ alg.asBool cv = some false) →
      stateCleanAtReturn s = true ∧
        Exists fun rv => evalRval alg retExpr s = some rv ∧
          handleFreeOut alg ⟨rv, collectRootMutVals s.loans⟩ = true ∧
          Post ⟨rv, collectRootMutVals s.loans⟩)
    (st : SymState Val) (hInv : Inv st) :
    PureMirExec.WpConverges
      (blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr)))
      ⟨fun o => o, 0, st⟩ Post := by
  obtain ⟨stFinal, hRun, hInvF, hCondF⟩ :=
    runWhileFlowSteps_cutpoint_sound alg cond (evalPlan alg body) Inv rank hStep
      (rank st) st hInv rfl
  refine (stepsTo_whileExit_of_runWhileFlowSteps alg cond body retExpr (rank st)
    (fun o => o) st stFinal hRun).bind_wp ?_
  intro s₁ hs₁
  subst hs₁
  obtain ⟨hClean, rv, hRv, hFree, hPost⟩ := hExit stFinal hInvF hCondF
  exact PureMirExec.WpConverges.of_done
    (blockCfgStep_whileExit alg cond body retExpr (fun o => o) stFinal rv hClean
      hRv hFree)
    hPost

/-- **Counted loops via MirLiftCore's `forRangeUp` rule**: when each iteration
`i ∈ [lo, hi)` of the embedded 3-block loop CFG takes the body (the header
condition is concretely `true`) and falls through to a state abstracted by
`abs (i + 1) (f i _ _ a)`, `PureMirExec.stepsTo_forRangeUp` yields a fuel-free
`StepsTo` segment from the header back to the header in a state abstracted by
`abs hi (PureMirExec.forRangeUp lo hi init f)`. -/
theorem whileLoop_stepsTo_forRangeUp {α : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val) (body : FlowPlan Val) (retExpr : RvalOp Val)
    (lo hi : Nat) (init : α) (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (abs : Nat → α → SymState Val → Prop)
    (hIter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s, abs i a s →
      (Exists fun cv => evalRval alg cond s = some cv ∧ alg.asBool cv = some true) ∧
      Exists fun s' => evalPlan alg body s = .ok (.continuing s') ∧
        abs (i + 1) (f i hlo hlt a) s')
    (wrap : FuncOut Val → FuncOut Val) (s₀ : SymState Val) (hle : lo ≤ hi)
    (hInit : abs lo init s₀) :
    PureMirExec.StepsTo
      (blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr)))
      ⟨wrap, 0, s₀⟩
      (fun t => t.wrap = wrap ∧ t.bb = 0 ∧
        abs hi (PureMirExec.forRangeUp lo hi init f) t.st) := by
  refine PureMirExec.stepsTo_forRangeUp
    (blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr)))
    lo hi init f
    (fun i a t => t.wrap = wrap ∧ t.bb = 0 ∧ abs i a t.st)
    ⟨wrap, 0, s₀⟩ hle ⟨rfl, rfl, hInit⟩ ?_
  intro i hlo hlt a t ht
  obtain ⟨hWrap, hBb, hAbs⟩ := ht
  obtain ⟨⟨cv, hCond, hBool⟩, s', hBody, hAbs'⟩ := hIter i hlo hlt a t.st hAbs
  cases t with
  | mk w bb st =>
    dsimp only at hWrap hBb hCond hBody
    subst hWrap
    subst hBb
    exact PureMirExec.StepsTo.step
      (blockCfgStep_whileHeader_true alg cond body retExpr w st cv hCond hBool)
      (PureMirExec.StepsTo.step
        (blockCfgStep_whileBody alg cond body retExpr w st s' hBody)
        (PureMirExec.StepsTo.refl ⟨rfl, rfl, hAbs'⟩))

end Loops

/-! ## Refinement into Live MIR (`runMirToBlock`, `MirWpConverges`, `LiftBlockToJoin`) -/

/-! ## `OperationalAdapter` over `PureMirExec.Step` Machines (`pure_lift_sound` as a Fuel-Free Segment) -/

section AdapterBridge

variable {σ α : Type}

/-- Exact `k`-step path of a deterministic `PureMirExec.Step` machine. -/
inductive StepPath (step : σ → PureMirExec.Step σ α) : σ → Nat → σ → Prop where
  | refl (s : σ) : StepPath step s 0 s
  | cons {s s' t : σ} {k : Nat} (hStep : step s = .cont s')
      (hRest : StepPath step s' k t) : StepPath step s (k + 1) t

theorem StepPath.trans {step : σ → PureMirExec.Step σ α} :
    ∀ {s t u : σ} {k₁ k₂ : Nat},
      StepPath step s k₁ t → StepPath step t k₂ u → StepPath step s (k₁ + k₂) u
  | _, _, _, _, _, .refl _, h₂ => by
    rw [Nat.zero_add]
    exact h₂
  | _, _, _, _, k₂, .cons (k := k) hStep hRest, h₂ => by
    rw [Nat.add_right_comm k 1 k₂]
    exact .cons hStep (StepPath.trans hRest h₂)

/-- A `k`-step path is a MirLiftCore `StepsTo` segment. -/
theorem StepPath.stepsTo {step : σ → PureMirExec.Step σ α} {s t : σ} {k : Nat}
    (h : StepPath step s k t) : PureMirExec.StepsTo step s (· = t) := by
  induction h with
  | refl _ => exact .refl rfl
  | cons hStep _ ih => exact .step hStep ih

/-- Every MirLiftCore `StepsTo` segment is a `k`-step path for some `k`. -/
theorem StepsTo.exists_stepPath {step : σ → PureMirExec.Step σ α} {s : σ}
    {mid : σ → Prop} (h : PureMirExec.StepsTo step s mid) :
    Exists fun k => Exists fun t => StepPath step s k t ∧ mid t := by
  induction h with
  | refl hm => exact ⟨0, _, .refl _, hm⟩
  | step hs _ ih =>
    obtain ⟨k, t, hPath, hm⟩ := ih
    exact ⟨k + 1, t, .cons hs hPath, hm⟩

/-- PureLift `OperationalAdapter` whose `ExecutesTo` is exact `k`-step
reachability of a MirLiftCore machine (for example live MIR
`PureMirExec.mirStep body`). -/
def stepOperationalAdapter {Val : Type} (step : σ → PureMirExec.Step σ α)
    (StateRel : SymState Val → σ → Prop) (FinalLoansRel : FuncOut Val → σ → Prop) :
    OperationalAdapter σ Val where
  ExecutesTo := StepPath step
  StateRel := StateRel
  FinalLoansRel := FinalLoansRel
  exec_zero := StepPath.refl
  exec_trans := StepPath.trans

/-- **PureLift adequacy as a fuel-free segment**: `pure_lift_sound` over
`stepOperationalAdapter step` yields a MirLiftCore `StepsTo` segment from `m0`
to a machine state related to some PureLift output that satisfies `post`. -/
theorem pure_lift_stepsTo {Val : Type} (step : σ → PureMirExec.Step σ α)
    (StateRel : SymState Val → σ → Prop) (FinalLoansRel : FuncOut Val → σ → Prop)
    (alg : ValAlgebra Val) (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retExpr : RvalOp Val) (post : FuncOut Val → Prop) (m0 : σ)
    (hInit : Exists fun st0 => initFnState alg params = .ok st0 ∧ StateRel st0 m0)
    (hSpec : HoldsFnSpec (evalFnValue alg params plan retExpr) post)
    (hSim : ∀ st0 out,
      initFnState alg params = .ok st0 → StateRel st0 m0 →
      evalFnValue alg params plan retExpr = .ok out →
      Exists fun k => Exists fun mFinal =>
        StepPath step m0 k mFinal ∧ FinalLoansRel out mFinal) :
    PureMirExec.StepsTo step m0
      (fun m => Exists fun out => FinalLoansRel out m ∧ post out) := by
  obtain ⟨_, mFinal, out, hExec, hRel, hPost⟩ :=
    pure_lift_sound (stepOperationalAdapter step StateRel FinalLoansRel) alg params
      plan retExpr post m0 hInit hSpec hSim
  refine (StepPath.stepsTo hExec).mono ?_
  intro m hm
  subst hm
  exact ⟨out, hRel, hPost⟩

/-- **PureLift adequacy refines live MIR**: `pure_lift_sound` over
`stepOperationalAdapter (PureMirExec.mirStep body)` composes with any live
`MirWpConverges` proof for the related final machine states (for example one
built with MirLiftCore's `LiftBlockConverges` judgments). -/
theorem pure_lift_mirWpConverges {Val : Type} {body : CapturedMir}
    (StateRel : SymState Val → MachineState → Prop)
    (FinalLoansRel : FuncOut Val → MachineState → Prop)
    (alg : ValAlgebra Val) (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retExpr : RvalOp Val) (post : FuncOut Val → Prop) (m0 : MachineState)
    (hInit : Exists fun st0 => initFnState alg params = .ok st0 ∧ StateRel st0 m0)
    (hSpec : HoldsFnSpec (evalFnValue alg params plan retExpr) post)
    (hSim : ∀ st0 out,
      initFnState alg params = .ok st0 → StateRel st0 m0 →
      evalFnValue alg params plan retExpr = .ok out →
      Exists fun k => Exists fun mFinal =>
        StepPath (PureMirExec.mirStep body) m0 k mFinal ∧ FinalLoansRel out mFinal)
    (Post : MirOutcome → Prop)
    (hHalt : ∀ ms out, FinalLoansRel out ms → post out →
      Anneal.MirFuelFree.MirWpConverges body ms Post) :
    Anneal.MirFuelFree.MirWpConverges body m0 Post :=
  PureMirExec.mirWpConverges_of_stepsTo_bind
    (pure_lift_stepsTo (PureMirExec.mirStep body) StateRel FinalLoansRel alg params
      plan retExpr post m0 hInit hSpec hSim)
    (fun ms hms =>
      match hms with
      | ⟨out, hRel, hPost⟩ => hHalt ms out hRel hPost)

end AdapterBridge

section LiveMir

variable {State Ret : Type}

/-- Every live `runMirToBlock` arrival discharges a `StepsTo` simulation
obligation into a related MIR state. -/
theorem stepsTo_of_runMirToBlock_reached {body : CapturedMir}
    {target : BasicBlockIdx} {ms ms' : MachineState} {R : MachineState → Prop}
    (h : PureMirExec.runMirToBlock body target ms = .reached ms') (hR : R ms') :
    PureMirExec.StepsTo (PureMirExec.mirStep body) ms R :=
  (PureMirExec.stepsTo_of_runToTarget_reached h).mono
    (fun x (hEq : x = ms') => hEq ▸ hR)

/-- The generic header-targeted invariant rule specialized to live MIR
(`PureMirExec.runMirToBlock`). -/
theorem runMirToBlock_of_stepInv {body : CapturedMir} {I : MachineState → Prop}
    {Post : MirOutcome → Prop} (hInv : StepInv (PureMirExec.mirStep body) I Post)
    (target : BasicBlockIdx) (ms : MachineState) (hms : I ms) :
    match PureMirExec.runMirToBlock body target ms with
    | .reached ms' =>
      I ms' ∧ ms'.frame.blockIdx = target ∧ ms'.frame.stmtIdx = 0
    | .halted out => Post out
    | .stuck => False
    | .outOfFuel => True := by
  have h := runToTarget_of_stepInv
    (atTarget := fun ms => ms.frame.blockIdx == target && ms.frame.stmtIdx == 0)
    hInv (PureMirExec.mirSegmentBound body) ms hms
  cases hRun : PureMirExec.runMirToBlock body target ms with
  | reached ms' =>
    unfold PureMirExec.runMirToBlock at hRun
    rw [hRun] at h
    exact ⟨h.1, (PureMirExec.runMirToBlock_reached_block_and_stmt
      (by unfold PureMirExec.runMirToBlock; exact hRun))⟩
  | halted out =>
    unfold PureMirExec.runMirToBlock at hRun
    rw [hRun] at h
    exact h
  | stuck =>
    unfold PureMirExec.runMirToBlock at hRun
    rw [hRun] at h
    exact h
  | outOfFuel => trivial

/-- **A verified PureLift CFG refines live MIR**: a forward simulation from the
embedded CFG machine into `PureMirExec.mirStep body` transports PureLift
convergence to live fuel-free MIR convergence (`MirFuelFree.MirWpConverges`). -/
theorem mirWpConverges_of_blockCfg_forwardSim
    {stepBb : Nat → State → BlockStepResult State Ret} {body : CapturedMir}
    {R : BlockMachineState State Ret → MachineState → Prop}
    {RetRel : Ret → MirOutcome → Prop}
    (hSim : ForwardSim (blockCfgStep stepBb) (PureMirExec.mirStep body) R RetRel)
    {P : Ret → Prop} {s : BlockMachineState State Ret} {ms : MachineState}
    (h : PureMirExec.WpConverges (blockCfgStep stepBb) s P) (hR : R s ms) :
    Anneal.MirFuelFree.MirWpConverges body ms
      (fun o => Exists fun v => P v ∧ RetRel v o) :=
  PureMirExec.mirWpConverges_of_wpConverges (wpConverges_of_forwardSim hSim h ms hR)

/-- **PureLift segments become MirLiftCore join paths** (`LiftBlockToJoin`): a
PureLift CFG segment (for example from `runBlockCfgToBlock`, or from
`stepsTo_whileExit_of_runWhileFlowSteps`) that reaches PureLift join states
satisfying `PJoin`, a per-step simulation into live MIR, and a join
correspondence (related MIR states sit at statement `0` of `joinBb` with
`JoinInv` locals) give a `LiftBlockToJoin` path for the MIR body, so the MIR
join block is proved once for every downstream continuation. -/
theorem liftBlockToJoin_of_blockCfg_segment
    {stepBb : Nat → State → BlockStepResult State Ret} {body : CapturedMir}
    {R : BlockMachineState State Ret → MachineState → Prop}
    (hSim : SegmentSim (blockCfgStep stepBb) (PureMirExec.mirStep body) R)
    {s : BlockMachineState State Ret} {PJoin : BlockMachineState State Ret → Prop}
    (hSeg : PureMirExec.StepsTo (blockCfgStep stepBb) s PJoin)
    {bbIdx joinBb : BasicBlockIdx} {env : MirLiftCore.PureEnv}
    {JoinInv : MirLiftCore.PureEnv → Prop}
    (hR : R s (({ bb := bbIdx, stmtIdx := 0, env := env } : PureMirExec.PureState).toMachineState
      emptyMemory))
    (hJoin : ∀ s' ms', PJoin s' → R s' ms' →
      ms' = ({ bb := joinBb, stmtIdx := 0, env := ms'.frame.locals } :
        PureMirExec.PureState).toMachineState emptyMemory ∧
      JoinInv ms'.frame.locals) :
    MirLiftCore.LiftBlockToJoin body bbIdx env joinBb JoinInv := by
  intro Q hQ
  refine MirLiftCore.LiftBlockConverges.iff_pureMirConverges.mpr ?_
  refine PureMirExec.mirWpConverges_of_stepsTo_bind
    (stepsTo_of_segmentSim hSim hSeg _ hR) ?_
  intro ms' hMid
  obtain ⟨s', hPJ, hR'⟩ := hMid
  obtain ⟨hEq, hJI⟩ := hJoin s' ms' hPJ hR'
  have hConv := MirLiftCore.LiftBlockConverges.iff_pureMirConverges.mp (hQ _ hJI)
  rw [hEq]
  exact hConv

end LiveMir

/-! ## Non-Vacuity Canaries -/

section Canaries

/-! ### Countdown CFG (`testCfgStep`) from a symbolic start value -/

/-- Block invariant of the `testCfgStep` countdown: blocks `0` and `1` hold any
counter, and the exit block `2` is entered only with counter `0`. -/
def countdownInv (bb st : Nat) : Prop :=
  bb = 0 ∨ bb = 1 ∨ (bb = 2 ∧ st = 0)

/-- Ranking function of the countdown: every `.jump` strictly decreases it. -/
def countdownRank (bb st : Nat) : Nat :=
  match bb with
  | 0 => 2 * st + 1
  | 1 => 2 * st + 2
  | _ => 0

/-- The countdown satisfies a fork-free per-block VC returning `100`. -/
theorem countdown_localBlockVC :
    LocalBlockVC (forkFree testCfgStep) countdownInv (· = 100) := by
  intro bb st hInv
  rcases hInv with h0 | h1 | ⟨h2, hst⟩
  · subst h0
    cases st with
    | zero =>
      show countdownInv 2 0
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    | succ n =>
      show countdownInv 1 (n + 1 - 1)
      exact Or.inr (Or.inl rfl)
  · subst h1
    show countdownInv 0 st
    exact Or.inl rfl
  · subst h2
    subst hst
    show 0 + 100 = 100
    rfl

theorem countdown_rank_jump : ∀ bb st nextBb st', countdownInv bb st →
    testCfgStep bb st = .jump nextBb st' →
    countdownRank nextBb st' < countdownRank bb st := by
  intro bb st nextBb st' hInv hStep
  rcases hInv with h0 | h1 | ⟨h2, hst⟩
  · subst h0
    cases st with
    | zero =>
      change BlockStepResult.jump 2 0 = _ at hStep
      injection hStep with hBb hSt
      subst hBb
      subst hSt
      exact Nat.zero_lt_succ 0
    | succ n =>
      change BlockStepResult.jump 1 n = _ at hStep
      injection hStep with hBb hSt
      subst hBb
      subst hSt
      show 2 * n + 2 < 2 * (n + 1) + 1
      omega
  · subst h1
    change BlockStepResult.jump 0 st = _ at hStep
    injection hStep with hBb hSt
    subst hBb
    subst hSt
    show 2 * st + 1 < 2 * st + 2
    omega
  · subst h2
    subst hst
    change BlockStepResult.ret (0 + 100) = _ at hStep
    exact nomatch hStep

theorem countdown_rank_jumpWrapped : ∀ bb st wrapRet nextBb st', countdownInv bb st →
    testCfgStep bb st = .jumpWrapped wrapRet nextBb st' →
    countdownRank nextBb st' < countdownRank bb st := by
  intro bb st wrapRet nextBb st' hInv hStep
  rcases hInv with h0 | h1 | ⟨h2, hst⟩
  · subst h0
    cases st with
    | zero =>
      change BlockStepResult.jump 2 0 = _ at hStep
      exact nomatch hStep
    | succ n =>
      change BlockStepResult.jump 1 (n + 1 - 1) = _ at hStep
      exact nomatch hStep
  · subst h1
    change BlockStepResult.jump 0 st = _ at hStep
    exact nomatch hStep
  · subst h2
    subst hst
    change BlockStepResult.ret (0 + 100) = _ at hStep
    exact nomatch hStep

/-- **Non-vacuity of `wpConverges_blockCfgStep_of_rank`**: the countdown CFG
converges (fuel-free) to `100` from every start value `n`. -/
theorem countdown_wpConverges (n : Nat) :
    PureMirExec.WpConverges (blockCfgStep testCfgStep) ⟨fun v => v, 0, n⟩ (· = 100) :=
  wpConverges_blockCfgStep_of_rank testCfgStep countdownInv (· = 100)
    countdown_localBlockVC countdownRank countdown_rank_jump
    countdown_rank_jumpWrapped ⟨fun v => v, 0, n⟩ ⟨Or.inl rfl, fun _ hv => hv⟩

/-- **Non-vacuity of `runBlockCfg_total_of_rank`**: some fuel makes the
countdown CFG return `100` from every start value `n`. -/
theorem countdown_runBlockCfg_total (n : Nat) :
    Exists fun k => runBlockCfg testCfgStep 0 n k = .ret 100 := by
  obtain ⟨k, v, hRun, hv⟩ := runBlockCfg_total_of_rank testCfgStep countdownInv
    (· = 100) countdown_localBlockVC countdownRank countdown_rank_jump
    countdown_rank_jumpWrapped 0 n (Or.inl rfl)
  subst hv
  exact ⟨k, hRun⟩

/-- Concrete embedding canaries: header-targeted stepping reaches the exit
block, `evalFuel` agrees with `runBlockCfg` (enough fuel halts with `100`, too
little fuel is `.outOfFuel`, never a fault), and a faulting block is `.stuck`. -/
theorem countdown_embedding_canaries :
    runBlockCfgToBlock testCfgStep 2 10 ⟨fun v => v, 0, 3⟩ =
      .reached ⟨fun v => v, 2, 0⟩ ∧
    PureMirExec.evalFuel (blockCfgStep testCfgStep) 8 ⟨fun v => v, 0, 3⟩ =
      .halted 100 ∧
    PureMirExec.evalFuel (blockCfgStep testCfgStep) 2 ⟨fun v => v, 0, 3⟩ =
      .outOfFuel ∧
    runBlockCfgToBlock testCfgStep 2 5 ⟨fun v => v, 99, 0⟩ = .stuck :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A two-state countdown machine (`0` halts with `100`, `m + 1` steps to
`m`) used as a simulation target. -/
def natCountdownStep (m : Nat) : PureMirExec.Step Nat Nat :=
  match m with
  | 0 => .done 100
  | m' + 1 => .cont m'

/-- Simulation relation from the countdown CFG machine: blocks `0` and `1`
track the counter exactly, and the exit block corresponds to `0`. -/
def countdownSimRel (s : BlockMachineState Nat Nat) (m : Nat) : Prop :=
  s.wrap = (fun v => v) ∧
    ((s.bb = 0 ∧ m = s.st) ∨ (s.bb = 1 ∧ m = s.st) ∨
     (s.bb = 2 ∧ s.st = 0 ∧ m = 0))

/-- The countdown CFG machine forward-simulates into `natCountdownStep`,
including stuttering (`0`-step) segments for the `bb1 → bb0` and `bb0 → bb2`
edges. -/
theorem countdown_forwardSim :
    ForwardSim (blockCfgStep testCfgStep) natCountdownStep countdownSimRel
      (fun v o => v = o) := by
  intro s m hR
  obtain ⟨hWrap, hCase⟩ := hR
  cases s with
  | mk wrap bb st =>
    dsimp only at hWrap hCase
    subst hWrap
    rcases hCase with ⟨h0, hm⟩ | ⟨h1, hm⟩ | ⟨h2, hst, hm⟩
    · subst h0
      rw [hm]
      cases st with
      | zero =>
        show PureMirExec.StepsTo natCountdownStep 0
          (countdownSimRel ⟨fun v => v, 2, 0⟩)
        exact PureMirExec.StepsTo.refl ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
      | succ n =>
        show PureMirExec.StepsTo natCountdownStep (n + 1)
          (countdownSimRel ⟨fun v => v, 1, n + 1 - 1⟩)
        exact PureMirExec.StepsTo.step rfl
          (PureMirExec.StepsTo.refl ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
    · subst h1
      rw [hm]
      show PureMirExec.StepsTo natCountdownStep st
        (countdownSimRel ⟨fun v => v, 0, st⟩)
      exact PureMirExec.StepsTo.refl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    · subst h2
      subst hst
      rw [hm]
      show PureMirExec.WpConverges natCountdownStep 0 (fun o => 0 + 100 = o)
      exact PureMirExec.WpConverges.of_done rfl rfl

/-- **Non-vacuity of `wpConverges_of_forwardSim`**: countdown CFG convergence
transfers to the simulating machine from every start value. -/
theorem countdown_forwardSim_wpConverges (n : Nat) :
    PureMirExec.WpConverges natCountdownStep n
      (fun o => Exists fun v => v = 100 ∧ v = o) :=
  wpConverges_of_forwardSim countdown_forwardSim (countdown_wpConverges n) n
    ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

/-! ### Symbolic forks: why the embedding is fork-free -/

/-- A CFG whose entry block forks on the symbolic parameter `_0`. -/
def symForkCfg : List (BasicBlock StdVal) :=
  [ ⟨.skip, .branch (.use (.localSub 0 [])) 1 2⟩
  , ⟨.act (.assign (.localSub 1 []) (.constVal (.nat 1))),
     .ret (.use (.localSub 1 []))⟩
  , ⟨.act (.assign (.localSub 1 []) (.constVal (.nat 2))),
     .ret (.use (.localSub 1 []))⟩ ]

/-- Negative canary: `runBlockCfg` merges both arms of a symbolic fork, while
the deterministic embedding faults on it (so `runBlockCfg_of_forkFree_ret` is
strict and the fork-free precondition of the total-correctness rules is
necessary). -/
theorem symFork_runBlockCfg_merges_but_embedding_faults :
    match initFnState stdValAlg [⟨.byVal, .symBool true⟩] with
    | .ok st =>
      runBlockCfg (stepBasicBlock stdValAlg symForkCfg) 0 st 2 =
        .ret ⟨stdValAlg.zipVal (.symBool true) (.nat 1) (.nat 2), []⟩ ∧
      blockCfgStep (stepBasicBlock stdValAlg symForkCfg) ⟨fun v => v, 0, st⟩ =
        .fault ∧
      runBlockCfg (forkFree (stepBasicBlock stdValAlg symForkCfg)) 0 st 2 = .fault
    | .fail => False :=
  ⟨rfl, rfl, rfl⟩

/-! ### `S6` count-up loop (`while *x < n { *x += 1 }`) with symbolic bounds -/

/-- Loop condition of `S6`: `*_0 < _1`. -/
def countUpCond : RvalOp StdVal :=
  .binary stdLtBool (.derefSub 0 []) (.localSub 1 [])

/-- Loop body of `S6`: `*_0 += 1`. -/
def countUpBody : FlowPlan StdVal :=
  .act (.assign (.derefSub 0 []) (.unary stdInc (.derefSub 0 [])))

/-- The `S6` loop as the 3-block CFG of `cfg_certificate_while_sound`. -/
def countUpBlocks : List (BasicBlock StdVal) :=
  whileLoopBlocks countUpCond countUpBody (.constVal .unit)

/-- Symbolic loop-header state with `*_0 = i` and `_1 = n`. -/
def countUpState (n i : Nat) : SymState StdVal :=
  ⟨[⟨.refVal 0 [], .unborrowed⟩, ⟨.nat n, .unborrowed⟩],
   [⟨0, .activeMut, ⟨.nat i, .unborrowed⟩, .rootParam 0⟩], [], [], [], 0⟩

/-- `countUpState n i` is exactly the entry state of `S6` with `*x = i`. -/
theorem countUpState_eq_initFnState (n i : Nat) :
    initFnState stdValAlg [⟨.mutRef 0 [], .nat i⟩, ⟨.byVal, .nat n⟩] =
      .ok (countUpState n i) := rfl

theorem countUp_eval_cond (n i : Nat) :
    evalRval stdValAlg countUpCond (countUpState n i) =
      some (.bool (Nat.blt i n)) := rfl

theorem countUp_eval_body (n i : Nat) :
    evalPlan stdValAlg countUpBody (countUpState n i) =
      .ok (.continuing (countUpState n (i + 1))) := rfl

theorem nat_blt_self_eq_false (n : Nat) : Nat.blt n n = false := by
  cases h : Nat.blt n n with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true h) (Nat.lt_irrefl n)

/-- Natural number carried by a `StdVal.nat` leaf. -/
def stdNatVal? (v : StdVal) : Option Nat :=
  match v with
  | ⟨_, .nat k⟩ => some k
  | _ => none

/-- Loop invariant of `S6`: the header state is `countUpState n i` with
`i ≤ n`. -/
def countUpInv (n : Nat) (s : SymState StdVal) : Prop :=
  Exists fun i => i ≤ n ∧ s = countUpState n i

/-- Ranking measure of `S6`: the remaining trip count `n - *x`. -/
def countUpRank (n : Nat) (s : SymState StdVal) : Nat :=
  match s.loans with
  | e :: _ =>
    match stdNatVal? e.cell.val with
    | some i => n - i
    | none => 0
  | [] => 0

/-- The cutpoint hypotheses of `runWhileFlowSteps_cutpoint_sound` for `S6`. -/
theorem countUp_cutpoint_step (n : Nat) : ∀ s, countUpInv n s →
    Exists fun cv => evalRval stdValAlg countUpCond s = some cv ∧
      ((stdValAlg.asBool cv = some false ∧ countUpRank n s = 0) ∨
       (stdValAlg.asBool cv = some true ∧
        Exists fun s' =>
          evalPlan stdValAlg countUpBody s = .ok (.continuing s') ∧
          countUpInv n s' ∧ countUpRank n s = countUpRank n s' + 1)) := by
  intro s hs
  obtain ⟨i, hi, hEq⟩ := hs
  subst hEq
  refine ⟨.bool (Nat.blt i n), countUp_eval_cond n i, ?_⟩
  cases hb : Nat.blt i n with
  | true =>
    have hlt : i < n := Nat.le_of_ble_eq_true hb
    refine Or.inr ⟨rfl, countUpState n (i + 1), countUp_eval_body n i,
      ⟨i + 1, hlt, rfl⟩, ?_⟩
    show n - i = n - (i + 1) + 1
    omega
  | false =>
    have hge : n ≤ i := Nat.ge_of_not_lt (fun hlt =>
      Bool.noConfusion ((Nat.ble_eq_true_of_le hlt).symm.trans hb))
    have hEq : i = n := Nat.le_antisymm hi hge
    subst hEq
    exact Or.inl ⟨rfl, Nat.sub_self i⟩

/-- The exit obligation of `S6`: the exit state is clean, handle-free, and
returns `⟨(), [n]⟩`. -/
theorem countUp_cutpoint_exit (n : Nat) : ∀ s, countUpInv n s →
    (Exists fun cv => evalRval stdValAlg countUpCond s = some cv ∧
      stdValAlg.asBool cv = some false) →
    stateCleanAtReturn s = true ∧
      Exists fun rv => evalRval stdValAlg (.constVal .unit) s = some rv ∧
        handleFreeOut stdValAlg ⟨rv, collectRootMutVals s.loans⟩ = true ∧
        (⟨rv, collectRootMutVals s.loans⟩ : FuncOut StdVal) = ⟨.unit, [.nat n]⟩ := by
  intro s hs hCond
  obtain ⟨i, hi, hEq⟩ := hs
  subst hEq
  obtain ⟨cv, hcv, hb⟩ := hCond
  rw [countUp_eval_cond] at hcv
  injection hcv with hcv
  subst hcv
  change some (Nat.blt i n) = some false at hb
  injection hb with hb
  have hge : n ≤ i := Nat.ge_of_not_lt (fun hlt =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le hlt).symm.trans hb))
  have hEq : i = n := Nat.le_antisymm hi hge
  subst hEq
  exact ⟨rfl, .unit, rfl, rfl, rfl⟩

/-- **Non-vacuity of `while_cutpoint_wpConverges`**: for all symbolic bounds
`i ≤ n`, the embedded `S6` loop CFG converges (fuel-free) from the header state
to `⟨(), [n]⟩`. -/
theorem countUp_while_cutpoint_wpConverges (n i : Nat) (hi : i ≤ n) :
    PureMirExec.WpConverges (blockCfgStep (stepBasicBlock stdValAlg countUpBlocks))
      ⟨fun o => o, 0, countUpState n i⟩ (· = ⟨.unit, [.nat n]⟩) :=
  while_cutpoint_wpConverges stdValAlg countUpCond countUpBody (.constVal .unit)
    (countUpInv n) (countUpRank n) (countUp_cutpoint_step n)
    (· = ⟨.unit, [.nat n]⟩) (countUp_cutpoint_exit n) (countUpState n i)
    ⟨i, hi, rfl⟩

/-- Total correctness of the `S6` loop CFG through the embedding: some fuel
makes `runBlockCfg` return `⟨(), [n]⟩` from the entry state, for all `i ≤ n`. -/
theorem countUp_runBlockCfg_total (n i : Nat) (hi : i ≤ n) :
    Exists fun k =>
      runBlockCfg (stepBasicBlock stdValAlg countUpBlocks) 0 (countUpState n i) k =
        .ret ⟨.unit, [.nat n]⟩ := by
  obtain ⟨k, v, hRun, hv⟩ := runBlockCfg_of_wpConverges _
    (countUp_while_cutpoint_wpConverges n i hi)
  subst hv
  exact ⟨k, hRun⟩

/-- **Non-vacuity of `whileLoop_stepsTo_forRangeUp`**: the same loop is driven
by MirLiftCore's structural `forRangeUp` rule over `[i, n)`, whose accumulator
tracks the counter, and then exits with `⟨(), [n]⟩`. -/
theorem countUp_forRangeUp_wpConverges (n i : Nat) (hi : i ≤ n) :
    PureMirExec.WpConverges (blockCfgStep (stepBasicBlock stdValAlg countUpBlocks))
      ⟨fun o => o, 0, countUpState n i⟩ (· = ⟨.unit, [.nat n]⟩) := by
  refine (whileLoop_stepsTo_forRangeUp stdValAlg countUpCond countUpBody
    (.constVal .unit) i n i (fun _ _ _ a => a + 1)
    (fun j a s => a = j ∧ s = countUpState n j) ?_ (fun o => o)
    (countUpState n i) hi ⟨rfl, rfl⟩).bind_wp ?_
  · intro j _ hlt a s hs
    obtain ⟨ha, hsEq⟩ := hs
    subst ha
    subst hsEq
    have hb : Nat.blt a n = true := Nat.ble_eq_true_of_le hlt
    refine ⟨⟨.bool (Nat.blt a n), countUp_eval_cond n a, ?_⟩,
      countUpState n (a + 1), countUp_eval_body n a, rfl, rfl⟩
    rw [hb]
    rfl
  · intro t ht
    obtain ⟨hw, hbb, _, hst⟩ := ht
    cases t with
    | mk w bb st =>
      dsimp only at hw hbb hst
      subst hw
      subst hbb
      subst hst
      exact PureMirExec.WpConverges.of_cont
        (blockCfgStep_whileHeader_false stdValAlg countUpCond countUpBody
          (.constVal .unit) (fun o => o) (countUpState n n) (.bool (Nat.blt n n))
          (countUp_eval_cond n n)
          (by rw [nat_blt_self_eq_false]; rfl))
        (PureMirExec.WpConverges.of_done
          (blockCfgStep_whileExit stdValAlg countUpCond countUpBody
            (.constVal .unit) (fun o => o) (countUpState n n) .unit rfl rfl rfl)
          rfl)

/-- Concrete header-targeted canary for `S6`: from `*x = 1, n = 3` the loop
CFG reaches its exit block with `*x = 3`, and `runBlockCfgToBlock_sound`
predicts exactly this (`countUpInv` holds there). -/
theorem countUp_runToBlock_canary :
    runBlockCfgToBlock (stepBasicBlock stdValAlg countUpBlocks) 2 8
      ⟨fun o => o, 0, countUpState 3 1⟩ =
      .reached ⟨fun o => o, 2, countUpState 3 3⟩ := rfl

/-! ### Live `CapturedMir` Non-Vacuity Canaries (`runMirToBlock`, `MirWpConverges`, `LiftBlockToJoin`) -/

/-- Two-block `CapturedMir` body (`bb0: goto bb1`, `bb1: return`) used to
exercise `stepsTo_of_runMirToBlock_reached`, `runMirToBlock_of_stepInv`,
`mirWpConverges_of_blockCfg_forwardSim`, and `liftBlockToJoin_of_blockCfg_segment`
on live trusted MIR. -/
def liveInteropMirBody : CapturedMir :=
  { PureMirExec.pureAdtMultiBlockBody with
    basicBlocks := [
      { statements := []
        terminator := { kind := .goto 1, span := "interop" }
        isCleanup := false },
      { statements := []
        terminator := { kind := .return_, span := "interop" }
        isCleanup := false }
    ]
    argCount := 0 }

def liveInteropEnv : MirLiftCore.PureEnv :=
  [.init (.scalar { bits := 100, sizeBytes := 4 })]

def liveInteropMs (bb : BasicBlockIdx) : MachineState :=
  ({ bb := bb, stmtIdx := 0, env := liveInteropEnv } :
    PureMirExec.PureState).toMachineState emptyMemory

def liveInteropMirOutcome : MirOutcome :=
  .normal (Value.scalar { bits := 100, sizeBytes := 4 }, emptyMemory)

/-- Simulation relation pairing the embedded `testCfgStep` machine (from counter
`0`) with `liveInteropMirBody`. -/
def liveInteropRel (s : BlockMachineState Nat Nat) (ms : MachineState) : Prop :=
  s.wrap = (fun v => v) ∧ s.st = 0 ∧
    ((s.bb = 0 ∧ ms = liveInteropMs 0) ∨
     (s.bb = 2 ∧ ms = liveInteropMs 1))

/-- Forward simulation from `blockCfgStep testCfgStep` into
`PureMirExec.mirStep liveInteropMirBody`, discharging the `bb0 → bb1` transition
via `stepsTo_of_runMirToBlock_reached`. -/
theorem liveInterop_forwardSim :
    ForwardSim (blockCfgStep testCfgStep)
      (PureMirExec.mirStep liveInteropMirBody) liveInteropRel
      (fun v out =>
        out =
          .normal
            (Value.scalar { bits := v, sizeBytes := 4 }, emptyMemory)) := by
  intro s ms hR
  obtain ⟨hWrap, hSt, hCases⟩ := hR
  cases s with
  | mk wrap bb st =>
    dsimp only at hWrap hSt hCases
    subst hWrap
    subst hSt
    rcases hCases with ⟨hBb, hMs⟩ | ⟨hBb, hMs⟩
    · subst hBb
      subst hMs
      show PureMirExec.StepsTo (PureMirExec.mirStep liveInteropMirBody)
        (liveInteropMs 0) (liveInteropRel ⟨fun v => v, 2, 0⟩)
      exact stepsTo_of_runMirToBlock_reached
        (rfl : PureMirExec.runMirToBlock liveInteropMirBody 1
          (liveInteropMs 0) = .reached (liveInteropMs 1))
        ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
    · subst hBb
      subst hMs
      show PureMirExec.WpConverges (PureMirExec.mirStep liveInteropMirBody)
        (liveInteropMs 1)
        (fun out =>
          out =
            .normal
              (Value.scalar { bits := 0 + 100, sizeBytes := 4 }, emptyMemory))
      exact PureMirExec.WpConverges.of_done rfl rfl

/-- **Non-vacuity of `mirWpConverges_of_blockCfg_forwardSim`**: convergence of
the PureLift `testCfgStep` machine transports to fuel-free `MirWpConverges` of
`liveInteropMirBody`. -/
theorem liveInterop_mirWpConverges_canary :
    Anneal.MirFuelFree.MirWpConverges liveInteropMirBody (liveInteropMs 0)
      (fun o =>
        Exists fun v =>
          v = 100 ∧
          o =
            .normal
              (Value.scalar { bits := v, sizeBytes := 4 }, emptyMemory)) :=
  mirWpConverges_of_blockCfg_forwardSim liveInterop_forwardSim
    (countdown_wpConverges 0) ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- **Non-vacuity of `liftBlockToJoin_of_blockCfg_segment`**: a PureLift CFG
segment from block `0` to join block `2` lifts via `liveInterop_forwardSim` to
`MirLiftCore.LiftBlockToJoin liveInteropMirBody 0 liveInteropEnv 1`. -/
theorem liveInterop_liftBlockToJoin_canary :
    MirLiftCore.LiftBlockToJoin liveInteropMirBody 0 liveInteropEnv 1
      (· = liveInteropEnv) := by
  have hSeg :
      PureMirExec.StepsTo (blockCfgStep testCfgStep) ⟨fun v => v, 0, 0⟩
        (· = ⟨fun v => v, 2, 0⟩) :=
    PureMirExec.StepsTo.step rfl (PureMirExec.StepsTo.refl rfl)
  refine liftBlockToJoin_of_blockCfg_segment liveInterop_forwardSim.segmentSim
    hSeg ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩ ?_
  intro s' ms' hPJ hR'
  subst hPJ
  rcases hR'.2.2 with ⟨hBad, _⟩ | ⟨_, hMs⟩
  · exact nomatch hBad
  · subst hMs
    exact ⟨rfl, rfl⟩

/-- **Non-vacuity of `runMirToBlock_of_stepInv`**: `liveInteropMirBody` satisfies
a `StepInv` over `{liveInteropMs 0, liveInteropMs 1}`, and `runMirToBlock` from
`liveInteropMs 0` to block `1` reaches `liveInteropMs 1` with the invariant and
block/statement indices preserved. -/
theorem liveInterop_runMirToBlock_stepInv_canary :
    let I (ms : MachineState) : Prop :=
      ms = liveInteropMs 0 ∨ ms = liveInteropMs 1
    StepInv (PureMirExec.mirStep liveInteropMirBody) I
      (· = liveInteropMirOutcome) ∧
    (match PureMirExec.runMirToBlock liveInteropMirBody 1 (liveInteropMs 0) with
     | .reached ms' =>
       I ms' ∧ ms'.frame.blockIdx = 1 ∧ ms'.frame.stmtIdx = 0
     | .halted out => out = liveInteropMirOutcome
     | .stuck => False
     | .outOfFuel => True) := by
  intro I
  have hInv :
      StepInv (PureMirExec.mirStep liveInteropMirBody) I
        (· = liveInteropMirOutcome) := by
    intro ms hms
    rcases hms with rfl | rfl
    · exact Or.inr rfl
    · exact rfl
  exact ⟨hInv, runMirToBlock_of_stepInv hInv 1 (liveInteropMs 0) (Or.inl rfl)⟩

/-! ### `pure_lift_sound` on live MIR and fork-free completeness -/

/-- One live MIR step of `liveInteropMirBody`: `bb0: goto bb1`. -/
theorem liveInterop_mirStep_bb0 :
    PureMirExec.mirStep liveInteropMirBody (liveInteropMs 0) =
      .cont (liveInteropMs 1) := rfl

/-- **Non-vacuity of `pure_lift_mirWpConverges`**: PureLift's adequacy theorem
`pure_lift_sound`, instantiated with `stepOperationalAdapter` over live
`PureMirExec.mirStep liveInteropMirBody`, proves fuel-free `MirWpConverges`
of the MIR body from the PureLift evaluation of a function returning `100`. -/
theorem liveInterop_pure_lift_mirWpConverges_canary :
    Anneal.MirFuelFree.MirWpConverges liveInteropMirBody (liveInteropMs 0)
      (· = liveInteropMirOutcome) :=
  pure_lift_mirWpConverges (Val := StdVal) (body := liveInteropMirBody)
    (fun _ ms => ms = liveInteropMs 0)
    (fun out ms => ms = liveInteropMs 1 ∧ out = ⟨.nat 100, []⟩)
    stdValAlg [] .skip (.constVal (.nat 100)) (fun out => out.ret = .nat 100)
    (liveInteropMs 0) ⟨⟨[], [], [], [], [], 0⟩, rfl, rfl⟩ rfl
    (fun _ out _ _ hEval => by
      change EvalOutcome.ok ⟨StdVal.nat 100, []⟩ = .ok out at hEval
      injection hEval with hOut
      exact ⟨1, liveInteropMs 1,
        .cons liveInterop_mirStep_bb0 (.refl _), rfl, hOut.symm⟩)
    (· = liveInteropMirOutcome)
    (fun ms _ hRel _ => by
      rw [hRel.1]
      exact PureMirExec.mirWpConverges_of_wpConverges
        (PureMirExec.WpConverges.of_done rfl rfl))

/-- `testCfgStep` has no symbolic forks. -/
theorem testCfgStep_noFork : ∀ bb st mergeRet thenBb elseBb st',
    testCfgStep bb st ≠ .branchJump mergeRet thenBb elseBb st' := by
  intro bb st mergeRet thenBb elseBb st' h
  match bb, st with
  | 0, 0 => exact nomatch h
  | 0, _ + 1 => exact nomatch h
  | 1, _ => exact nomatch h
  | 2, _ => exact nomatch h
  | _ + 3, _ => exact nomatch h

/-- **Non-vacuity of `wpConverges_blockCfgStep_iff_of_noFork`**: a concrete
`runBlockCfg` return of the fork-free countdown is a fuel-free convergence of
the embedded machine. -/
theorem countdown_wpConverges_of_runBlockCfg :
    PureMirExec.WpConverges (blockCfgStep testCfgStep) ⟨fun v => v, 0, 3⟩
      (· = 100) :=
  (wpConverges_blockCfgStep_iff_of_noFork testCfgStep testCfgStep_noFork 0 3
    (· = 100)).mpr ⟨10, 100, rfl, rfl⟩

end Canaries

end Anneal.PureLift.MirLiftCoreInterop
