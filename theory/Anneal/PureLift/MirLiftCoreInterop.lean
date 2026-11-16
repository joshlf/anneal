-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.BitValidity
import Anneal.MirLiftCore
import Anneal.SepLogicLenses
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
   step function into `PureMirExec.Step`. The pending partial return wrappers
   (`Ret → Option Ret`) of `.jumpWrapped` and `.convergedJump` are composed
   Kleisli-style (`composeWrap`) in the machine state, and a returned value
   that the pending wrapper rejects (`none`) is a machine `.fault`, exactly as
   in `runBlockCfg`. The `armSteps` fuel that `runBlockCfg` charges for the arms
   of a `.convergedJump` is replayed as `armSteps` silent delay transitions
   (`BlockMachineState.wait`). Symbolic `.branchJump` forks, which a
   deterministic machine cannot represent, become `.fault`.
   `evalFuel_blockCfgStep_loop` / `evalFuel_blockCfgStep` prove
   `PureMirExec.evalFuel` of the embedding *equals* `runBlockCfgLoop` /
   `runBlockCfg` of the fork-free CFG `forkFree stepBb` at every fuel and
   delay, and `runBlockCfg_of_forkFree_ret` transports every fork-free return
   back to the original CFG. Conversely the embedding agrees with the original
   CFG up to added faults (`evalFuel_blockCfgStep_eq_or_faulted`): it never
   masks a genuine `runBlockCfg` fault, such as a rejected wrapper or merge, as
   a halt or as fuel exhaustion (`not_wpConverges_blockCfgStep_of_runBlockCfg_fault`).
   Pending wrappers only post-process the final value
   (`evalFuel_blockCfgStep_wrap`, `wpConverges_blockCfgStep_wrap_iff`). On CFGs
   without symbolic forks the embedding is complete
   (`wpConverges_blockCfgStep_iff_of_noFork`), and on CFGs that do not fork on
   the states of a per-block invariant it is complete from those states
   (`wpConverges_blockCfgStep_iff_of_blockInv`).
2. **Partial correctness transfer** (`modular_block_cfg_sound`):
   `wpConverges_blockCfgStep_postRet` strengthens any fuel-free convergence
   proof of the embedded CFG with PureLift's `PostRet`, and
   `evalFuel_blockCfgStep_ne_faulted` rules out machine faults;
   `wpConverges_of_cfgCertificate` turns a `CfgCertificate` plus a function
   specification into fuel-free convergence of its CFG.
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
   `whileLoop_stepsTo_forRangeUp` / `whileLoop_stepsTo_exit_forRangeUp` drive
   the same CFG with MirLiftCore's structural `stepsTo_forRangeUp` rule.
6. **Refinement into live MIR** (`runMirToBlock`, `LiftBlockToJoin`):
   `wpConverges_of_forwardSim` transports convergence of any machine along a
   forward simulation; `mirWpConverges_of_blockCfg_forwardSim`,
   `mirWpConverges_of_cfgCertificate`, and `liftBlockToJoin_of_blockCfg_segment`
   instantiate it for live MIR, so a verified PureLift CFG plus per-step MIR
   simulation obligations (each dischargeable by
   `stepsTo_of_runMirToBlock_reached`) yields `MirWpConverges` /
   `LiftBlockToJoin` for the MIR body; `liftBlockToJoin_of_runBlockCfgToBlock`,
   `liftBlockToJoin_of_whileCutpoint`, and `liftBlockToJoin_of_whileForRangeUp`
   derive the PureLift segment (and the join invariant) from header-targeted
   runs, loop cutpoints, and counted loops.
7. **Adequacy bridge** (`Adapter.pure_lift_sound`): `stepOperationalAdapter`
   realizes PureLift's `OperationalAdapter` by exact `k`-step paths
   (`StepPath`, interconvertible with `StepsTo`) of any MirLiftCore machine,
   and `pure_lift_stepsTo` / `pure_lift_mirWpConverges` turn
   `pure_lift_sound` into a fuel-free segment / live `MirWpConverges`.
8. **Trusted byte windows** (Episode 2 readiness): provenance-free trusted
   `AbstractByte` windows are exactly the `.uninit` / `.rawByte` spatial cells
   (`cellsOfAbstractBytes`, `abstractBytesOfCells`, with exact round trips,
   length preservation, and `hasUninitCell` ↔ `BitValidity.allBytesInitialized`),
   and `spatialCodecOfByteLensCodec` lifts any provenance-free
   `SepLogicLenses.ByteLensCodec α n` to a `SpatialCodec` over an arbitrary
   value domain that decodes only exact-width windows and never retypes an
   in-image block (exercised on MIR `Value` with the trusted little-endian
   `u32` codec and a `bool` codec rejecting invalid bit patterns), with no
   change to the PureLift core.
9. **Episode 2 compatibility** (no change to the PureLift core): the
   `V2026_06_01` bridge's `unpinFromSpatialInState` name for `main`'s
   `reabsorbFromSpatialInState`, `evalPlan_whileLoop` for `main`'s `WfPlan`,
   handle-freedom of every halt of an embedded `stepBasicBlock` CFG
   (`evalFuel_blockCfgStep_stepBasicBlock_handleFree`), and sub-identity
   partial wrappers (`SubIdWrap`, satisfied by the `handleFreeOutOpt` guard that
   `stepBasicBlock` puts on joined `.convergedJump` arms), whose halts carry the
   unwrapped return value (`evalFuel_blockCfgStep_halted_of_subIdWrap`).

All results are exercised non-vacuously at the end of the file on concrete
PureLift CFGs with symbolic data (`testCfgStep` countdown, the `S6` count-up
loop over `StdVal` with symbolic bounds, its stride-3 strong-descent variant,
and `.convergedJump` / `.jumpWrapped` / `.branchJump` CFGs with genuinely
partial wrappers and merges) and on the live two-block `CapturedMir` body
`liveInteropMirBody`.
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

/-- Kleisli composition of partial return-value wrappers (`Ret → Option Ret`):
applies `inner` first to the returned value, and passes its result (if `some`)
to `outer`. -/
def composeWrap (outer inner : Ret → Option Ret) (v : Ret) : Option Ret :=
  match inner v with
  | some v' => outer v'
  | none => none

/-- Machine state of the embedding: the partial return-value wrapper accumulated
from `.jumpWrapped` and `.convergedJump` transitions, the current block, the
block-entry state, and the remaining `armSteps` fuel delay `wait` from a
`.convergedJump` transition (default `0`). -/
structure BlockMachineState (State Ret : Type) where
  wrap : Ret → Option Ret
  bb : Nat
  st : State
  wait : Nat := 0

/-- Deterministic embedding of a PureLift block step function into
MirLiftCore's generic machine. When `s.wait = wait' + 1`, consumes one unit of
fuel for an already-evaluated converged branch arm step before executing `s.bb`.
When `s.wait = 0`, `.jumpWrapped` composes its partial wrapper into the pending
wrapper, `.convergedJump armSteps wrapRet nextBb st'` composes `wrapRet` into
the pending wrapper and sets `wait := armSteps`, `.ret` halts with `v'` when
`s.wrap v = some v'` and faults when `s.wrap v = none`, and a symbolic
`.branchJump` fork (two successor runs merged afterwards, which no
deterministic machine can represent) becomes `.fault`, just as `mirStep` maps
external calls to `.fault`. -/
def blockCfgStep (stepBb : Nat → State → BlockStepResult State Ret)
    (s : BlockMachineState State Ret) :
    PureMirExec.Step (BlockMachineState State Ret) Ret :=
  match s.wait with
  | wait' + 1 => .cont ⟨s.wrap, s.bb, s.st, wait'⟩
  | 0 =>
    match stepBb s.bb s.st with
    | .jump nextBb st' => .cont ⟨s.wrap, nextBb, st', 0⟩
    | .jumpWrapped wrapRet nextBb st' =>
      .cont ⟨composeWrap s.wrap wrapRet, nextBb, st', 0⟩
    | .convergedJump armSteps wrapRet nextBb st' =>
      .cont ⟨composeWrap s.wrap wrapRet, nextBb, st', armSteps⟩
    | .branchJump _ _ _ _ => .fault
    | .ret v =>
      match s.wrap v with
      | some v' => .done v'
      | none => .fault
    | .fault => .fault

/-- `stepBb` with every symbolic `.branchJump` fork replaced by `.fault`
(preserving `.jump`, `.jumpWrapped`, `.convergedJump`, `.ret`, and `.fault`). -/
def forkFree (stepBb : Nat → State → BlockStepResult State Ret) :
    Nat → State → BlockStepResult State Ret :=
  fun bb st =>
    match stepBb bb st with
    | .jump nextBb st' => .jump nextBb st'
    | .jumpWrapped wrapRet nextBb st' => .jumpWrapped wrapRet nextBb st'
    | .convergedJump armSteps wrapRet nextBb st' =>
      .convergedJump armSteps wrapRet nextBb st'
    | .branchJump _ _ _ _ => .fault
    | .ret v => .ret v
    | .fault => .fault

/-- `BlockCfgOutcome` as a `PureMirExec.FuelResult`, after applying the pending
partial wrapper `wrap` to a returned value (`none` maps to `.faulted`). -/
def outcomeToFuel (wrap : Ret → Option Ret) :
    BlockCfgOutcome Ret → PureMirExec.FuelResult Ret
  | .ret v =>
    match wrap v with
    | some v' => .halted v'
    | none => .faulted
  | .diverged => .outOfFuel
  | .fault => .faulted

theorem outcomeToFuel_composeWrap (outer inner : Ret → Option Ret)
    (out : BlockCfgOutcome Ret) :
    outcomeToFuel (composeWrap outer inner) out =
      outcomeToFuel outer
        (match out with
         | .ret v =>
           match inner v with
           | some v' => .ret v'
           | none => .fault
         | .diverged => .diverged
         | .fault => .fault) := by
  cases out with
  | ret v =>
    dsimp only [outcomeToFuel, composeWrap]
    cases inner v <;> rfl
  | diverged => rfl
  | fault => rfl

/-- **Exact loop embedding**: at every fuel `k` and delay `s.wait`, MirLiftCore's
`evalFuel` of the embedded machine equals `runBlockCfgLoop` of the fork-free CFG
(fuel exhaustion is `.outOfFuel`, and wrapper rejection `none` is `.faulted`). -/
theorem evalFuel_blockCfgStep_loop
    (stepBb : Nat → State → BlockStepResult State Ret) :
    ∀ (k : Nat) (s : BlockMachineState State Ret),
      PureMirExec.evalFuel (blockCfgStep stepBb) k s =
        outcomeToFuel s.wrap
          (runBlockCfgLoop (forkFree stepBb) k s.wait s.bb s.st)
  | 0, _ => rfl
  | k + 1, ⟨wrap, bb, st, wait' + 1⟩ => by
    rw [runBlockCfgLoop_succ_wait]
    exact evalFuel_blockCfgStep_loop stepBb k ⟨wrap, bb, st, wait'⟩
  | k + 1, ⟨wrap, bb, st, 0⟩ => by
    change PureMirExec.evalFuel (blockCfgStep stepBb) (k + 1) ⟨wrap, bb, st, 0⟩ =
      outcomeToFuel wrap (runBlockCfg (forkFree stepBb) bb st (k + 1))
    rw [runBlockCfg_succ]
    unfold PureMirExec.evalFuel
    dsimp only [blockCfgStep, forkFree]
    cases stepBb bb st with
    | jump nextBb st' =>
      exact evalFuel_blockCfgStep_loop stepBb k ⟨wrap, nextBb, st', 0⟩
    | jumpWrapped wrapRet nextBb st' =>
      dsimp only
      rw [evalFuel_blockCfgStep_loop stepBb k
            ⟨composeWrap wrap wrapRet, nextBb, st', 0⟩]
      exact outcomeToFuel_composeWrap wrap wrapRet
        (runBlockCfg (forkFree stepBb) nextBb st' k)
    | convergedJump armSteps wrapRet nextBb st' =>
      dsimp only
      rw [evalFuel_blockCfgStep_loop stepBb k
            ⟨composeWrap wrap wrapRet, nextBb, st', armSteps⟩]
      exact outcomeToFuel_composeWrap wrap wrapRet
        (runBlockCfgLoop (forkFree stepBb) k armSteps nextBb st')
    | branchJump _ _ _ _ => rfl
    | ret v =>
      dsimp only [outcomeToFuel]
      cases wrap v <;> rfl
    | fault => rfl

/-- **Exact embedding**: at every fuel `k` (with `wait = 0`), MirLiftCore's
`evalFuel` of the embedded machine equals `runBlockCfg` of the fork-free CFG. -/
theorem evalFuel_blockCfgStep (stepBb : Nat → State → BlockStepResult State Ret)
    (k : Nat) (wrap : Ret → Option Ret) (bb : Nat) (st : State) :
    PureMirExec.evalFuel (blockCfgStep stepBb) k ⟨wrap, bb, st, 0⟩ =
      outcomeToFuel wrap (runBlockCfg (forkFree stepBb) bb st k) :=
  evalFuel_blockCfgStep_loop stepBb k ⟨wrap, bb, st, 0⟩

/-- Every return of `runBlockCfgLoop` on the fork-free CFG is a return on the
original CFG, with the same value, wait delay, and fuel. -/
theorem runBlockCfgLoop_of_forkFree_ret
    (stepBb : Nat → State → BlockStepResult State Ret) :
    ∀ (k wait : Nat) (bb : Nat) (st : State) (v : Ret),
      runBlockCfgLoop (forkFree stepBb) k wait bb st = .ret v →
      runBlockCfgLoop stepBb k wait bb st = .ret v
  | 0, _, _, _, _, h => nomatch h
  | k + 1, wait' + 1, bb, st, v, h => by
    rw [runBlockCfgLoop_succ_wait] at h ⊢
    exact runBlockCfgLoop_of_forkFree_ret stepBb k wait' bb st v h
  | k + 1, 0, bb, st, v, h => by
    change runBlockCfg (forkFree stepBb) bb st (k + 1) = .ret v at h
    change runBlockCfg stepBb bb st (k + 1) = .ret v
    rw [runBlockCfg_succ] at h ⊢
    dsimp only [forkFree] at h
    cases hst : stepBb bb st with
    | jump nextBb st' =>
      rw [hst] at h
      exact runBlockCfgLoop_of_forkFree_ret stepBb k 0 nextBb st' v h
    | jumpWrapped wrapRet nextBb st' =>
      rw [hst] at h
      dsimp only at h ⊢
      cases hRun : runBlockCfg (forkFree stepBb) nextBb st' k with
      | ret v' =>
        rw [hRun] at h
        change runBlockCfgLoop (forkFree stepBb) k 0 nextBb st' = .ret v' at hRun
        have hOrig : runBlockCfg stepBb nextBb st' k = .ret v' :=
          runBlockCfgLoop_of_forkFree_ret stepBb k 0 nextBb st' v' hRun
        rw [hOrig]
        exact h
      | diverged =>
        rw [hRun] at h
        exact nomatch h
      | fault =>
        rw [hRun] at h
        exact nomatch h
    | convergedJump armSteps wrapRet nextBb st' =>
      rw [hst] at h
      dsimp only at h ⊢
      cases hRun : runBlockCfgLoop (forkFree stepBb) k armSteps nextBb st' with
      | ret v' =>
        rw [hRun] at h
        rw [runBlockCfgLoop_of_forkFree_ret stepBb k armSteps nextBb st' v' hRun]
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

/-- Every return of the fork-free CFG is a return of the original CFG, with the
same value and fuel. -/
theorem runBlockCfg_of_forkFree_ret
    (stepBb : Nat → State → BlockStepResult State Ret)
    (k : Nat) (bb : Nat) (st : State) (v : Ret)
    (h : runBlockCfg (forkFree stepBb) bb st k = .ret v) :
    runBlockCfg stepBb bb st k = .ret v :=
  runBlockCfgLoop_of_forkFree_ret stepBb k 0 bb st v h

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
  | convergedJump armSteps wrapRet nextBb st' =>
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

/-- A converged run of the embedded machine (with the identity wrapper `some`) is
an actual `runBlockCfg` return of the original CFG. -/
theorem runBlockCfg_of_wpConverges
    (stepBb : Nat → State → BlockStepResult State Ret) {bb : Nat} {st : State}
    {P : Ret → Prop}
    (h : PureMirExec.WpConverges (blockCfgStep stepBb) ⟨some, bb, st, 0⟩ P) :
    Exists fun k => Exists fun v => runBlockCfg stepBb bb st k = .ret v ∧ P v := by
  obtain ⟨k, v, hk, hp⟩ := h
  rw [evalFuel_blockCfgStep] at hk
  cases hRun : runBlockCfg (forkFree stepBb) bb st k with
  | ret v' =>
    rw [hRun] at hk
    dsimp only [outcomeToFuel] at hk
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
    (h : PureMirExec.WpConverges (blockCfgStep stepBb) ⟨some, bb, st, 0⟩ Q) :
    PureMirExec.WpConverges (blockCfgStep stepBb) ⟨some, bb, st, 0⟩
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

/-- Machine-level invariant induced by a per-block VC: the block invariant
holds and the pending partial wrapper accepts every `PostRet` value and
preserves `PostRet`. -/
def MachineInv (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (s : BlockMachineState State Ret) : Prop :=
  BlockInv s.bb s.st ∧
  ∀ v, PostRet v →
    match s.wrap v with
    | some v' => PostRet v'
    | none => False

/-- A fork-free per-block VC is a `StepInv` of the embedded machine. -/
theorem stepInv_blockCfgStep (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC (forkFree stepBb) BlockInv PostRet) :
    StepInv (blockCfgStep stepBb) (MachineInv BlockInv PostRet) PostRet := by
  intro s hs
  obtain ⟨hInv, hWrap⟩ := hs
  cases s with
  | mk wrap bb st wait =>
    dsimp only at hInv hWrap
    cases wait with
    | succ wait' =>
      exact ⟨hInv, hWrap⟩
    | zero =>
      have hVC := hLocal bb st hInv
      dsimp only [forkFree] at hVC
      dsimp only [blockCfgStep]
      cases hst : stepBb bb st with
      | jump nextBb st' =>
        rw [hst] at hVC
        exact ⟨hVC, hWrap⟩
      | jumpWrapped wrapRet nextBb st' =>
        rw [hst] at hVC
        refine ⟨hVC.1, fun v hv => ?_⟩
        have hInner := hVC.2 v hv
        dsimp only [composeWrap]
        cases hw : wrapRet v with
        | none =>
          rw [hw] at hInner
          exact hInner
        | some v1 =>
          rw [hw] at hInner
          exact hWrap v1 hInner
      | convergedJump armSteps wrapRet nextBb st' =>
        rw [hst] at hVC
        refine ⟨hVC.1, fun v hv => ?_⟩
        have hInner := hVC.2 v hv
        dsimp only [composeWrap]
        cases hw : wrapRet v with
        | none =>
          rw [hw] at hInner
          exact hInner
        | some v1 =>
          rw [hw] at hInner
          exact hWrap v1 hInner
      | branchJump _ _ _ _ =>
        rw [hst] at hVC
        exact hVC
      | ret v =>
        rw [hst] at hVC
        dsimp only at hVC
        have hOut := hWrap v hVC
        dsimp only
        cases hw : wrap v with
        | some v' =>
          rw [hw] at hOut
          exact hOut
        | none =>
          rw [hw] at hOut
          exact hOut
      | fault =>
        rw [hst] at hVC
        exact hVC

/-- **No machine faults** (`modular_block_cfg_loop_sound` on the fork-free CFG):
from an invariant machine state (`MachineInv BlockInv PostRet s`), the embedded
machine never faults at any fuel. -/
theorem evalFuel_blockCfgStep_ne_faulted
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC (forkFree stepBb) BlockInv PostRet)
    (s : BlockMachineState State Ret)
    (hs : MachineInv BlockInv PostRet s) (k : Nat) :
    PureMirExec.evalFuel (blockCfgStep stepBb) k s ≠ .faulted := by
  have h := evalFuel_of_stepInv
    (stepInv_blockCfgStep stepBb BlockInv PostRet hLocal) k s hs
  intro hEq
  rw [hEq] at h
  exact h

/-- Header-targeted stepping of a PureLift CFG: one mandatory step, then stop at
the first ready (`wait == 0`) entry of block `target` (MirLiftCore's
`runToTarget`, as in `PureMirExec.runMirToBlock`). -/
def runBlockCfgToBlock (stepBb : Nat → State → BlockStepResult State Ret)
    (target bound : Nat) (s : BlockMachineState State Ret) :
    PureMirExec.TargetOutcome (BlockMachineState State Ret) Ret :=
  PureMirExec.runToTarget (blockCfgStep stepBb)
    (fun t => t.bb == target && t.wait == 0) bound s

/-- **Per-block VCs compose along header-targeted segments**: from an invariant
machine state, `runBlockCfgToBlock` reaches block `target` with no pending
`.convergedJump` delay (`wait = 0`) in an invariant state, or returns a
`PostRet` value, or exhausts its ceiling; it is never `.stuck`. -/
theorem runBlockCfgToBlock_sound (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC (forkFree stepBb) BlockInv PostRet)
    (target bound : Nat) (s : BlockMachineState State Ret)
    (hs : MachineInv BlockInv PostRet s) :
    match runBlockCfgToBlock stepBb target bound s with
    | .reached s' =>
      s'.bb = target ∧ s'.wait = 0 ∧ MachineInv BlockInv PostRet s'
    | .halted v => PostRet v
    | .stuck => False
    | .outOfFuel => True := by
  have h := runToTarget_of_stepInv
    (atTarget := fun t => t.bb == target && t.wait == 0)
    (stepInv_blockCfgStep stepBb BlockInv PostRet hLocal) bound s hs
  unfold runBlockCfgToBlock
  cases hRun : PureMirExec.runToTarget (blockCfgStep stepBb)
      (fun t => t.bb == target && t.wait == 0) bound s with
  | reached s' =>
    rw [hRun] at h
    have hAnd := Bool.and_eq_true_iff.mp h.2
    exact ⟨beq_iff_eq.mp hAnd.1, beq_iff_eq.mp hAnd.2, h.1⟩
  | halted v =>
    rw [hRun] at h
    exact h
  | stuck =>
    rw [hRun] at h
    exact h
  | outOfFuel => trivial

/-- A `runBlockCfgToBlock` arrival sits at block `target` with no pending
`.convergedJump` delay (MirLiftCore's `runToTarget_reached_atTarget`). -/
theorem runBlockCfgToBlock_reached_wait_zero
    {stepBb : Nat → State → BlockStepResult State Ret}
    {target bound : Nat} {s s' : BlockMachineState State Ret}
    (hRun : runBlockCfgToBlock stepBb target bound s = .reached s') :
    s'.bb = target ∧ s'.wait = 0 := by
  have hAt := PureMirExec.runToTarget_reached_atTarget hRun
  have hAnd := Bool.and_eq_true_iff.mp hAt
  exact ⟨beq_iff_eq.mp hAnd.1, beq_iff_eq.mp hAnd.2⟩

/-- **Fuel-free total correctness of PureLift CFGs**: a fork-free per-block VC
and a ranking function that decreases along every `.jump`, `.jumpWrapped`, and
`.convergedJump` edge between invariant states make every invariant machine
state converge (`PureMirExec.WpConverges`) to `PostRet`. -/
theorem wpConverges_blockCfgStep_of_rank
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC (forkFree stepBb) BlockInv PostRet)
    (rank : Nat → State → Nat)
    (hRankJump : ∀ bb st nextBb st', BlockInv bb st →
      stepBb bb st = .jump nextBb st' → rank nextBb st' < rank bb st)
    (hRankWrapped : ∀ bb st wrapRet nextBb st', BlockInv bb st →
      stepBb bb st = .jumpWrapped wrapRet nextBb st' →
      rank nextBb st' < rank bb st)
    (hRankConverged : ∀ bb st armSteps wrapRet nextBb st', BlockInv bb st →
      stepBb bb st = .convergedJump armSteps wrapRet nextBb st' →
      rank nextBb st' < rank bb st) :
    ∀ s, MachineInv BlockInv PostRet s →
      PureMirExec.WpConverges (blockCfgStep stepBb) s PostRet := by
  have hStepInv := stepInv_blockCfgStep stepBb BlockInv PostRet hLocal
  suffices hAll : ∀ (n : Nat) (w : Nat) (s : BlockMachineState State Ret),
      s.wait = w → rank s.bb s.st < n → MachineInv BlockInv PostRet s →
      PureMirExec.WpConverges (blockCfgStep stepBb) s PostRet from
    fun s hs => hAll (rank s.bb s.st + 1) s.wait s rfl (Nat.lt_succ_self _) hs
  intro n
  induction n with
  | zero =>
    intro _ _ _ hlt _
    exact absurd hlt (Nat.not_lt_zero _)
  | succ n ihN =>
    intro w
    induction w with
    | succ w' ihW =>
      intro s hw hlt hs
      cases s with
      | mk wrap bb st wait =>
        dsimp only at hw hlt
        subst hw
        have hCont :
            blockCfgStep stepBb ⟨wrap, bb, st, w' + 1⟩ =
              .cont ⟨wrap, bb, st, w'⟩ := rfl
        exact PureMirExec.WpConverges.of_cont hCont
          (ihW ⟨wrap, bb, st, w'⟩ rfl hlt hs)
    | zero =>
      intro s hw hlt hs
      cases s with
      | mk wrap bb st wait =>
        dsimp only at hw hlt
        subst hw
        have hInvStep := hStepInv ⟨wrap, bb, st, 0⟩ hs
        dsimp only [blockCfgStep] at hInvStep
        cases hst : stepBb bb st with
        | jump nextBb st' =>
          rw [hst] at hInvStep
          have hDec := hRankJump bb st nextBb st' hs.1 hst
          have hCont :
              blockCfgStep stepBb ⟨wrap, bb, st, 0⟩ =
                .cont ⟨wrap, nextBb, st', 0⟩ := by
            dsimp only [blockCfgStep]
            rw [hst]
          exact PureMirExec.WpConverges.of_cont hCont
            (ihN 0 ⟨wrap, nextBb, st', 0⟩ rfl
              (Nat.lt_of_lt_of_le hDec (Nat.le_of_lt_succ hlt)) hInvStep)
        | jumpWrapped wrapRet nextBb st' =>
          rw [hst] at hInvStep
          have hDec := hRankWrapped bb st wrapRet nextBb st' hs.1 hst
          have hCont :
              blockCfgStep stepBb ⟨wrap, bb, st, 0⟩ =
                .cont ⟨composeWrap wrap wrapRet, nextBb, st', 0⟩ := by
            dsimp only [blockCfgStep]
            rw [hst]
          exact PureMirExec.WpConverges.of_cont hCont
            (ihN 0 ⟨composeWrap wrap wrapRet, nextBb, st', 0⟩ rfl
              (Nat.lt_of_lt_of_le hDec (Nat.le_of_lt_succ hlt)) hInvStep)
        | convergedJump armSteps wrapRet nextBb st' =>
          rw [hst] at hInvStep
          have hDec := hRankConverged bb st armSteps wrapRet nextBb st' hs.1 hst
          have hCont :
              blockCfgStep stepBb ⟨wrap, bb, st, 0⟩ =
                .cont ⟨composeWrap wrap wrapRet, nextBb, st', armSteps⟩ := by
            dsimp only [blockCfgStep]
            rw [hst]
          exact PureMirExec.WpConverges.of_cont hCont
            (ihN armSteps ⟨composeWrap wrap wrapRet, nextBb, st', armSteps⟩ rfl
              (Nat.lt_of_lt_of_le hDec (Nat.le_of_lt_succ hlt)) hInvStep)
        | branchJump _ _ _ _ =>
          rw [hst] at hInvStep
          exact hInvStep.elim
        | ret v =>
          rw [hst] at hInvStep
          dsimp only at hInvStep
          cases hw : wrap v with
          | some v' =>
            rw [hw] at hInvStep
            have hDone :
                blockCfgStep stepBb ⟨wrap, bb, st, 0⟩ = .done v' := by
              dsimp only [blockCfgStep]
              rw [hst]
              dsimp only
              rw [hw]
            exact PureMirExec.WpConverges.of_done hDone hInvStep
          | none =>
            rw [hw] at hInvStep
            exact hInvStep.elim
        | fault =>
          rw [hst] at hInvStep
          exact hInvStep.elim

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
    (hRankConverged : ∀ bb st armSteps wrapRet nextBb st', BlockInv bb st →
      stepBb bb st = .convergedJump armSteps wrapRet nextBb st' →
      rank nextBb st' < rank bb st)
    (bb : Nat) (st : State) (hInv : BlockInv bb st) :
    Exists fun k => Exists fun v => runBlockCfg stepBb bb st k = .ret v ∧ PostRet v :=
  runBlockCfg_of_wpConverges stepBb
    (wpConverges_blockCfgStep_of_rank stepBb BlockInv PostRet hLocal rank
      hRankJump hRankWrapped hRankConverged ⟨some, bb, st, 0⟩
      ⟨hInv, fun _ hv => hv⟩)

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
  | convergedJump _ _ _ _ => rfl
  | branchJump mergeRet thenBb elseBb st' =>
    exact absurd h (hNoFork bb st mergeRet thenBb elseBb st')
  | ret _ => rfl
  | fault => rfl

/-- **Completeness for fork-free CFGs**: on a CFG without symbolic forks, the
embedded machine converges from `⟨some, bb, st, 0⟩` exactly when `runBlockCfg`
returns at some fuel, so `runBlockCfg_of_wpConverges` is an equivalence. -/
theorem wpConverges_blockCfgStep_iff_of_noFork
    (stepBb : Nat → State → BlockStepResult State Ret)
    (hNoFork : ∀ bb st mergeRet thenBb elseBb st',
      stepBb bb st ≠ .branchJump mergeRet thenBb elseBb st')
    (bb : Nat) (st : State) (P : Ret → Prop) :
    PureMirExec.WpConverges (blockCfgStep stepBb) ⟨some, bb, st, 0⟩ P ↔
      Exists fun k => Exists fun v => runBlockCfg stepBb bb st k = .ret v ∧ P v := by
  refine ⟨runBlockCfg_of_wpConverges stepBb, ?_⟩
  intro h
  obtain ⟨k, v, hRun, hP⟩ := h
  refine ⟨k, v, ?_, hP⟩
  rw [evalFuel_blockCfgStep, forkFree_eq_of_noFork stepBb hNoFork]
  rw [hRun]
  rfl

/-- **Invariant-scoped fork-free loop return preservation**: requires `hNoFork`
only on states satisfying `BlockInv`. -/
theorem runBlockCfgLoop_forkFree_of_ret_inv
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC stepBb BlockInv PostRet)
    (hNoFork : ∀ bb st, BlockInv bb st →
      ∀ mergeRet thenBb elseBb st',
        stepBb bb st ≠ .branchJump mergeRet thenBb elseBb st') :
    ∀ (k wait : Nat) (bb : Nat) (st : State) (v : Ret),
      BlockInv bb st →
      runBlockCfgLoop stepBb k wait bb st = .ret v →
      runBlockCfgLoop (forkFree stepBb) k wait bb st = .ret v
  | 0, _, _, _, _, _, h => nomatch h
  | k + 1, wait' + 1, bb, st, v, hInv, h => by
    rw [runBlockCfgLoop_succ_wait] at h ⊢
    exact runBlockCfgLoop_forkFree_of_ret_inv stepBb BlockInv PostRet hLocal
      hNoFork k wait' bb st v hInv h
  | k + 1, 0, bb, st, v, hInv, h => by
    have hVC := hLocal bb st hInv
    change runBlockCfg stepBb bb st (k + 1) = .ret v at h
    change runBlockCfg (forkFree stepBb) bb st (k + 1) = .ret v
    rw [runBlockCfg_succ] at h ⊢
    dsimp only [forkFree]
    cases hst : stepBb bb st with
    | jump nextBb st' =>
      rw [hst] at h hVC
      exact runBlockCfgLoop_forkFree_of_ret_inv stepBb BlockInv PostRet hLocal
        hNoFork k 0 nextBb st' v hVC h
    | jumpWrapped wrapRet nextBb st' =>
      rw [hst] at h hVC
      dsimp only at h ⊢
      cases hRun : runBlockCfg stepBb nextBb st' k with
      | ret v' =>
        rw [hRun] at h
        change runBlockCfgLoop stepBb k 0 nextBb st' = .ret v' at hRun
        have hFF : runBlockCfg (forkFree stepBb) nextBb st' k = .ret v' :=
          runBlockCfgLoop_forkFree_of_ret_inv stepBb BlockInv PostRet hLocal
            hNoFork k 0 nextBb st' v' hVC.1 hRun
        rw [hFF]
        exact h
      | diverged =>
        rw [hRun] at h
        exact nomatch h
      | fault =>
        rw [hRun] at h
        exact nomatch h
    | convergedJump armSteps wrapRet nextBb st' =>
      rw [hst] at h hVC
      dsimp only at h ⊢
      cases hRun : runBlockCfgLoop stepBb k armSteps nextBb st' with
      | ret v' =>
        rw [hRun] at h
        rw [runBlockCfgLoop_forkFree_of_ret_inv stepBb BlockInv PostRet hLocal
              hNoFork k armSteps nextBb st' v' hVC.1 hRun]
        exact h
      | diverged =>
        rw [hRun] at h
        exact nomatch h
      | fault =>
        rw [hRun] at h
        exact nomatch h
    | branchJump mergeRet thenBb elseBb st' =>
      exact False.elim (hNoFork bb st hInv mergeRet thenBb elseBb st' hst)
    | ret v' =>
      rw [hst] at h
      exact h
    | fault =>
      rw [hst] at h
      exact nomatch h

/-- **Invariant-scoped fork-free return preservation**: unlike
`forkFree_eq_of_noFork` (which requires `stepBb` to be fork-free on *all* states,
including unreachable states where a local could hold a symbolic choice), this
lemma requires `hNoFork` only on states satisfying `BlockInv`. -/
theorem runBlockCfg_forkFree_of_ret_inv
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC stepBb BlockInv PostRet)
    (hNoFork : ∀ bb st, BlockInv bb st →
      ∀ mergeRet thenBb elseBb st',
        stepBb bb st ≠ .branchJump mergeRet thenBb elseBb st')
    (k : Nat) (bb : Nat) (st : State) (v : Ret)
    (hInv : BlockInv bb st)
    (h : runBlockCfg stepBb bb st k = .ret v) :
    runBlockCfg (forkFree stepBb) bb st k = .ret v :=
  runBlockCfgLoop_forkFree_of_ret_inv stepBb BlockInv PostRet hLocal hNoFork
    k 0 bb st v hInv h

/-- **Invariant-scoped completeness of the CFG embedding**: for any CFG satisfying
`LocalBlockVC` that does not fork on `BlockInv` states (even if `stepBb` would
emit `.branchJump` on unreachable symbolic states outside `BlockInv`), the
embedded machine converges from `⟨some, bb, st, 0⟩` iff `runBlockCfg` returns at
some fuel. -/
theorem wpConverges_blockCfgStep_iff_of_blockInv
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC stepBb BlockInv PostRet)
    (hNoFork : ∀ bb st, BlockInv bb st →
      ∀ mergeRet thenBb elseBb st',
        stepBb bb st ≠ .branchJump mergeRet thenBb elseBb st')
    (bb : Nat) (st : State) (hInv : BlockInv bb st) (P : Ret → Prop) :
    PureMirExec.WpConverges (blockCfgStep stepBb) ⟨some, bb, st, 0⟩ P ↔
      Exists fun k => Exists fun v => runBlockCfg stepBb bb st k = .ret v ∧ P v := by
  refine ⟨runBlockCfg_of_wpConverges stepBb, ?_⟩
  intro h
  obtain ⟨k, v, hRun, hP⟩ := h
  refine ⟨k, v, ?_, hP⟩
  rw [evalFuel_blockCfgStep,
      runBlockCfg_forkFree_of_ret_inv stepBb BlockInv PostRet hLocal hNoFork k
        bb st v hInv hRun]
  rfl

/-- **The fork-free CFG only adds faults**: at every fuel and delay,
`runBlockCfgLoop (forkFree stepBb)` either agrees exactly with
`runBlockCfgLoop stepBb` or faults. Replacing symbolic `.branchJump` forks by
`.fault` can turn a return or a divergence into a fault, but it never turns a
fault into a return or a divergence, and it never changes a returned value. -/
theorem runBlockCfgLoop_forkFree_eq_or_fault
    (stepBb : Nat → State → BlockStepResult State Ret) :
    ∀ (k wait : Nat) (bb : Nat) (st : State),
      runBlockCfgLoop (forkFree stepBb) k wait bb st =
          runBlockCfgLoop stepBb k wait bb st ∨
        runBlockCfgLoop (forkFree stepBb) k wait bb st = .fault
  | 0, _, _, _ => Or.inl rfl
  | k + 1, wait' + 1, bb, st => by
    rw [runBlockCfgLoop_succ_wait, runBlockCfgLoop_succ_wait]
    exact runBlockCfgLoop_forkFree_eq_or_fault stepBb k wait' bb st
  | k + 1, 0, bb, st => by
    change runBlockCfg (forkFree stepBb) bb st (k + 1) =
        runBlockCfg stepBb bb st (k + 1) ∨
      runBlockCfg (forkFree stepBb) bb st (k + 1) = .fault
    rw [runBlockCfg_succ, runBlockCfg_succ]
    dsimp only [forkFree]
    cases stepBb bb st with
    | jump nextBb st' =>
      exact runBlockCfgLoop_forkFree_eq_or_fault stepBb k 0 nextBb st'
    | jumpWrapped wrapRet nextBb st' =>
      dsimp only
      have ih : runBlockCfg (forkFree stepBb) nextBb st' k =
            runBlockCfg stepBb nextBb st' k ∨
          runBlockCfg (forkFree stepBb) nextBb st' k = .fault :=
        runBlockCfgLoop_forkFree_eq_or_fault stepBb k 0 nextBb st'
      rcases ih with h | h
      · rw [h]
        exact Or.inl rfl
      · rw [h]
        exact Or.inr rfl
    | convergedJump armSteps wrapRet nextBb st' =>
      dsimp only
      rcases runBlockCfgLoop_forkFree_eq_or_fault stepBb k armSteps nextBb st'
        with h | h
      · rw [h]
        exact Or.inl rfl
      · rw [h]
        exact Or.inr rfl
    | branchJump _ _ _ _ => exact Or.inr rfl
    | ret _ => exact Or.inl rfl
    | fault => exact Or.inl rfl

/-- Faults of the original CFG are faults of the fork-free CFG, at the same
fuel and delay. -/
theorem runBlockCfgLoop_forkFree_of_fault
    (stepBb : Nat → State → BlockStepResult State Ret)
    (k wait : Nat) (bb : Nat) (st : State)
    (h : runBlockCfgLoop stepBb k wait bb st = .fault) :
    runBlockCfgLoop (forkFree stepBb) k wait bb st = .fault := by
  rcases runBlockCfgLoop_forkFree_eq_or_fault stepBb k wait bb st with hEq | hEq
  · rw [hEq, h]
  · exact hEq

/-- **The embedding agrees with the original CFG up to added faults**: at every
fuel, the embedded machine either produces exactly the `runBlockCfgLoop`
outcome of the original CFG `stepBb` (passed through the pending wrapper) or
faults. Only symbolic `.branchJump` forks introduce the second case. -/
theorem evalFuel_blockCfgStep_eq_or_faulted
    (stepBb : Nat → State → BlockStepResult State Ret)
    (k : Nat) (s : BlockMachineState State Ret) :
    PureMirExec.evalFuel (blockCfgStep stepBb) k s =
        outcomeToFuel s.wrap (runBlockCfgLoop stepBb k s.wait s.bb s.st) ∨
      PureMirExec.evalFuel (blockCfgStep stepBb) k s = .faulted := by
  rw [evalFuel_blockCfgStep_loop]
  rcases runBlockCfgLoop_forkFree_eq_or_fault stepBb k s.wait s.bb s.st
    with h | h
  · rw [h]
    exact Or.inl rfl
  · rw [h]
    exact Or.inr rfl

/-- **Fault adequacy of the embedding**: if the original CFG faults at fuel `k`
from the machine state's block, delay, and state (for example because a
`.jumpWrapped` / `.convergedJump` wrapper or a `.branchJump` merge function
rejects its values, or a block faults), the embedded machine faults at the same
fuel, under any pending wrapper. -/
theorem evalFuel_blockCfgStep_of_runBlockCfgLoop_fault
    (stepBb : Nat → State → BlockStepResult State Ret)
    (k : Nat) (s : BlockMachineState State Ret)
    (h : runBlockCfgLoop stepBb k s.wait s.bb s.st = .fault) :
    PureMirExec.evalFuel (blockCfgStep stepBb) k s = .faulted := by
  rcases evalFuel_blockCfgStep_eq_or_faulted stepBb k s with hEq | hEq
  · rw [hEq, h]
    rfl
  · exact hEq

/-- `runBlockCfg` form of `evalFuel_blockCfgStep_of_runBlockCfgLoop_fault`. -/
theorem evalFuel_blockCfgStep_of_runBlockCfg_fault
    (stepBb : Nat → State → BlockStepResult State Ret)
    (k : Nat) (wrap : Ret → Option Ret) (bb : Nat) (st : State)
    (h : runBlockCfg stepBb bb st k = .fault) :
    PureMirExec.evalFuel (blockCfgStep stepBb) k ⟨wrap, bb, st, 0⟩ = .faulted :=
  evalFuel_blockCfgStep_of_runBlockCfgLoop_fault stepBb k ⟨wrap, bb, st, 0⟩ h

/-- **No convergence through a genuine fault**: if the original CFG faults at
some fuel, the embedded machine converges to no postcondition from the same
block and state under any pending wrapper, so a partial wrapper or merge
function that `runBlockCfg` rejects is never masked as convergence. -/
theorem not_wpConverges_blockCfgStep_of_runBlockCfg_fault
    (stepBb : Nat → State → BlockStepResult State Ret)
    {k : Nat} {wrap : Ret → Option Ret} {bb : Nat} {st : State}
    (h : runBlockCfg stepBb bb st k = .fault) (P : Ret → Prop) :
    ¬ PureMirExec.WpConverges (blockCfgStep stepBb) ⟨wrap, bb, st, 0⟩ P :=
  PureMirExec.not_wpConverges_of_faulted
    (evalFuel_blockCfgStep_of_runBlockCfg_fault stepBb k wrap bb st h)

/-- Identity-wrapper form of `evalFuel_blockCfgStep_ne_faulted`: from a state
with the identity wrapper `some` (and any delay), `BlockInv` alone rules out
machine faults. -/
theorem evalFuel_blockCfgStep_ne_faulted_of_blockInv
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC (forkFree stepBb) BlockInv PostRet)
    (bb : Nat) (st : State) (wait : Nat) (hInv : BlockInv bb st) (k : Nat) :
    PureMirExec.evalFuel (blockCfgStep stepBb) k ⟨some, bb, st, wait⟩ ≠
      .faulted :=
  evalFuel_blockCfgStep_ne_faulted stepBb BlockInv PostRet hLocal
    ⟨some, bb, st, wait⟩ ⟨hInv, fun _ hv => hv⟩ k

/-- Post-processing of a fuel result by a partial return-value wrapper: a halt
is passed through `wrap`, and a rejected value (`none`) is a fault. -/
def wrapFuelResult (wrap : Ret → Option Ret) :
    PureMirExec.FuelResult Ret → PureMirExec.FuelResult Ret
  | .halted v =>
    match wrap v with
    | some v' => .halted v'
    | none => .faulted
  | .outOfFuel => .outOfFuel
  | .faulted => .faulted

theorem outcomeToFuel_eq_wrapFuelResult (wrap : Ret → Option Ret)
    (out : BlockCfgOutcome Ret) :
    outcomeToFuel wrap out = wrapFuelResult wrap (outcomeToFuel some out) := by
  cases out with
  | ret v =>
    dsimp only [outcomeToFuel, wrapFuelResult]
  | diverged => rfl
  | fault => rfl

/-- **Pending wrappers only post-process the final value** (frame rule for
partial wrappers): running from a state with pending wrapper `wrap` is running
from the same block, state, and delay with the identity wrapper `some`, then
passing the halted value through `wrap`. -/
theorem evalFuel_blockCfgStep_wrap
    (stepBb : Nat → State → BlockStepResult State Ret) (k : Nat)
    (wrap : Ret → Option Ret) (bb : Nat) (st : State) (wait : Nat) :
    PureMirExec.evalFuel (blockCfgStep stepBb) k ⟨wrap, bb, st, wait⟩ =
      wrapFuelResult wrap
        (PureMirExec.evalFuel (blockCfgStep stepBb) k ⟨some, bb, st, wait⟩) :=
  (evalFuel_blockCfgStep_loop stepBb k ⟨wrap, bb, st, wait⟩).trans
    ((outcomeToFuel_eq_wrapFuelResult wrap
        (runBlockCfgLoop (forkFree stepBb) k wait bb st)).trans
      (congrArg (wrapFuelResult wrap)
        (evalFuel_blockCfgStep_loop stepBb k ⟨some, bb, st, wait⟩).symm))

/-- `WpConverges` form of the wrapper frame rule `evalFuel_blockCfgStep_wrap`:
a state with pending wrapper `wrap` converges to `P` iff the identity-wrapper
state converges to a value that `wrap` accepts and maps into `P`. -/
theorem wpConverges_blockCfgStep_wrap_iff
    (stepBb : Nat → State → BlockStepResult State Ret)
    (wrap : Ret → Option Ret) (bb : Nat) (st : State) (wait : Nat)
    (P : Ret → Prop) :
    PureMirExec.WpConverges (blockCfgStep stepBb) ⟨wrap, bb, st, wait⟩ P ↔
      PureMirExec.WpConverges (blockCfgStep stepBb) ⟨some, bb, st, wait⟩
        (fun v => Exists fun v' => wrap v = some v' ∧ P v') := by
  constructor
  · intro h
    obtain ⟨k, v', hk, hP⟩ := h
    rw [evalFuel_blockCfgStep_wrap] at hk
    cases hInner :
        PureMirExec.evalFuel (blockCfgStep stepBb) k ⟨some, bb, st, wait⟩ with
    | halted v =>
      rw [hInner] at hk
      dsimp only [wrapFuelResult] at hk
      cases hw : wrap v with
      | some w =>
        rw [hw] at hk
        injection hk with hEq
        subst hEq
        exact ⟨k, v, hInner, w, hw, hP⟩
      | none =>
        rw [hw] at hk
        exact nomatch hk
    | outOfFuel =>
      rw [hInner] at hk
      exact nomatch hk
    | faulted =>
      rw [hInner] at hk
      exact nomatch hk
  · intro h
    obtain ⟨k, v, hk, v', hw, hP⟩ := h
    refine ⟨k, v', ?_, hP⟩
    rw [evalFuel_blockCfgStep_wrap, hk]
    dsimp only [wrapFuelResult]
    rw [hw]

/-- A partial wrapper that never changes the value it accepts (it may only
reject), such as the identity wrapper `some` and the `handleFreeOutOpt` guard
that `stepBasicBlock` puts on the joined arms of a `.convergedJump`. -/
def SubIdWrap (wrap : Ret → Option Ret) : Prop :=
  ∀ v v', wrap v = some v' → v' = v

theorem subIdWrap_some : SubIdWrap (some : Ret → Option Ret) := by
  intro v v' h
  injection h with hEq
  exact hEq.symm

/-- Sub-identity wrappers are closed under Kleisli composition. -/
theorem subIdWrap_composeWrap {outer inner : Ret → Option Ret}
    (hOuter : SubIdWrap outer) (hInner : SubIdWrap inner) :
    SubIdWrap (composeWrap outer inner) := by
  intro v v' h
  dsimp only [composeWrap] at h
  cases hw : inner v with
  | some v1 =>
    rw [hw] at h
    exact (hOuter v1 v' h).trans (hInner v v1 hw)
  | none =>
    rw [hw] at h
    exact nomatch h

/-- Under a sub-identity pending wrapper, every halt of the embedded machine
returns exactly the value that the identity-wrapper run returns. -/
theorem evalFuel_blockCfgStep_halted_of_subIdWrap
    (stepBb : Nat → State → BlockStepResult State Ret)
    {k : Nat} {wrap : Ret → Option Ret} {bb : Nat} {st : State} {wait : Nat}
    {v : Ret} (hWrap : SubIdWrap wrap)
    (h : PureMirExec.evalFuel (blockCfgStep stepBb) k ⟨wrap, bb, st, wait⟩ =
      .halted v) :
    PureMirExec.evalFuel (blockCfgStep stepBb) k ⟨some, bb, st, wait⟩ =
      .halted v := by
  rw [evalFuel_blockCfgStep_wrap] at h
  cases hInner :
      PureMirExec.evalFuel (blockCfgStep stepBb) k ⟨some, bb, st, wait⟩ with
  | halted v0 =>
    rw [hInner] at h
    dsimp only [wrapFuelResult] at h
    cases hw : wrap v0 with
    | some v1 =>
      rw [hw] at h
      injection h with hEq
      subst hEq
      rw [hWrap v0 v1 hw]
    | none =>
      rw [hw] at h
      exact nomatch h
  | outOfFuel =>
    rw [hInner] at h
    exact nomatch h
  | faulted =>
    rw [hInner] at h
    exact nomatch h

/-- `outcomeToFuel wrap` halts exactly on the returns that `wrap` accepts. -/
theorem outcomeToFuel_eq_halted_iff (wrap : Ret → Option Ret)
    (out : BlockCfgOutcome Ret) (v' : Ret) :
    outcomeToFuel wrap out = .halted v' ↔
      Exists fun v => out = .ret v ∧ wrap v = some v' := by
  cases out with
  | ret v =>
    dsimp only [outcomeToFuel]
    constructor
    · intro h
      cases hw : wrap v with
      | some w =>
        rw [hw] at h
        injection h with hEq
        subst hEq
        exact ⟨v, rfl, hw⟩
      | none =>
        rw [hw] at h
        exact nomatch h
    · intro ⟨v0, hEq, hw⟩
      injection hEq with hEq
      subst hEq
      rw [hw]
  | diverged =>
    constructor
    · intro h
      exact nomatch h
    · intro ⟨_, hEq, _⟩
      exact nomatch hEq
  | fault =>
    constructor
    · intro h
      exact nomatch h
    · intro ⟨_, hEq, _⟩
      exact nomatch hEq

/-- **General completeness for fork-free CFGs**: from any machine state (any
pending wrapper and any pending `.convergedJump` delay), the embedded machine
converges to `P` iff the original CFG returns at some fuel (resuming the same
delay) a value that the pending wrapper accepts and maps into `P`. -/
theorem wpConverges_blockCfgStep_iff_of_noFork_loop
    (stepBb : Nat → State → BlockStepResult State Ret)
    (hNoFork : ∀ bb st mergeRet thenBb elseBb st',
      stepBb bb st ≠ .branchJump mergeRet thenBb elseBb st')
    (s : BlockMachineState State Ret) (P : Ret → Prop) :
    PureMirExec.WpConverges (blockCfgStep stepBb) s P ↔
      Exists fun k => Exists fun v =>
        runBlockCfgLoop stepBb k s.wait s.bb s.st = .ret v ∧
        Exists fun v' => s.wrap v = some v' ∧ P v' := by
  constructor
  · intro ⟨k, v', hk, hP⟩
    rw [evalFuel_blockCfgStep_loop, forkFree_eq_of_noFork stepBb hNoFork] at hk
    obtain ⟨v, hRun, hw⟩ := (outcomeToFuel_eq_halted_iff s.wrap _ v').mp hk
    exact ⟨k, v, hRun, v', hw, hP⟩
  · intro ⟨k, v, hRun, v', hw, hP⟩
    refine ⟨k, v', ?_, hP⟩
    rw [evalFuel_blockCfgStep_loop, forkFree_eq_of_noFork stepBb hNoFork]
    exact (outcomeToFuel_eq_halted_iff s.wrap _ v').mpr ⟨v, hRun, hw⟩

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
    (wrap : FuncOut Val → Option (FuncOut Val)) (st : SymState Val) (cv : Val)
    (hCond : evalRval alg cond st = some cv) (hBool : alg.asBool cv = some true) :
    blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr))
      ⟨wrap, 0, st, 0⟩ = .cont ⟨wrap, 1, st, 0⟩ := by
  dsimp only [blockCfgStep, stepBasicBlock, whileLoopBlocks, listGetOpt,
    evalPlan, evalPlanOps, stepPlanOp, FlowPlan.skip, List.foldr]
  rw [hCond]
  dsimp only
  rw [hBool]

/-- Header step on a concretely `false` condition. -/
theorem blockCfgStep_whileHeader_false (alg : ValAlgebra Val) (cond : RvalOp Val)
    (body : FlowPlan Val) (retExpr : RvalOp Val)
    (wrap : FuncOut Val → Option (FuncOut Val)) (st : SymState Val) (cv : Val)
    (hCond : evalRval alg cond st = some cv) (hBool : alg.asBool cv = some false) :
    blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr))
      ⟨wrap, 0, st, 0⟩ = .cont ⟨wrap, 2, st, 0⟩ := by
  dsimp only [blockCfgStep, stepBasicBlock, whileLoopBlocks, listGetOpt,
    evalPlan, evalPlanOps, stepPlanOp, FlowPlan.skip, List.foldr]
  rw [hCond]
  dsimp only
  rw [hBool]

/-- Body step when the body falls through. -/
theorem blockCfgStep_whileBody (alg : ValAlgebra Val) (cond : RvalOp Val)
    (body : FlowPlan Val) (retExpr : RvalOp Val)
    (wrap : FuncOut Val → Option (FuncOut Val)) (st st' : SymState Val)
    (hBody : evalPlan alg body st = .ok (.continuing st')) :
    blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr))
      ⟨wrap, 1, st, 0⟩ = .cont ⟨wrap, 0, st', 0⟩ := by
  dsimp only [blockCfgStep, stepBasicBlock, whileLoopBlocks, listGetOpt,
    List.foldr]
  rw [hBody]

/-- Exit step from a clean, handle-free state. -/
theorem blockCfgStep_whileExit (alg : ValAlgebra Val) (cond : RvalOp Val)
    (body : FlowPlan Val) (retExpr : RvalOp Val)
    (wrap : FuncOut Val → Option (FuncOut Val)) (st : SymState Val) (rv : Val)
    (out : FuncOut Val)
    (hClean : stateCleanAtReturn st = true)
    (hRet : evalRval alg retExpr st = some rv)
    (hFree : handleFreeOut alg ⟨rv, collectRootMutVals st.loans⟩ = true)
    (hWrap : wrap ⟨rv, collectRootMutVals st.loans⟩ = some out := by rfl) :
    blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr))
      ⟨wrap, 2, st, 0⟩ = .done out := by
  dsimp only [blockCfgStep, stepBasicBlock, whileLoopBlocks, listGetOpt,
    evalPlan, evalPlanOps, stepPlanOp, FlowPlan.skip, List.foldr]
  rw [hClean]
  dsimp
  rw [hRet]
  dsimp
  rw [hFree]
  dsimp
  rw [hWrap]

/-- **Structured loops are fuel-free CFG segments**: every structured run of
`runWhileFlowSteps` that falls through to `stFinal` is simulated by a
MirLiftCore `StepsTo` segment of the embedded 3-block loop CFG from header
block `0` to exit block `2`, at the same final state and with the pending
wrapper unchanged. -/
theorem stepsTo_whileExit_of_runWhileFlowSteps (alg : ValAlgebra Val)
    (cond : RvalOp Val) (body : FlowPlan Val) (retExpr : RvalOp Val) :
    ∀ (fuel : Nat) (wrap : FuncOut Val → Option (FuncOut Val))
      (st stFinal : SymState Val),
      runWhileFlowSteps alg cond (evalPlan alg body) fuel st =
        .ok (.continuing stFinal) →
      PureMirExec.StepsTo
        (blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr)))
        ⟨wrap, 0, st, 0⟩ (· = ⟨wrap, 2, stFinal, 0⟩)
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
invariant `Inv` with a strong well-founded ranking measure `rank` (`rank s' <
rank s` on taken iterations) and an exit obligation make the embedded 3-block
loop CFG converge (`PureMirExec.WpConverges`) to `Post` from every invariant
header state. -/
theorem while_cutpoint_wpConverges (alg : ValAlgebra Val) (cond : RvalOp Val)
    (body : FlowPlan Val) (retExpr : RvalOp Val)
    (Inv : SymState Val → Prop) (rank : SymState Val → Nat)
    (hStep : ∀ s, Inv s →
      Exists fun cv => evalRval alg cond s = some cv ∧
        (alg.asBool cv = some false ∨
         (alg.asBool cv = some true ∧
          Exists fun s' =>
            evalPlan alg body s = .ok (.continuing s') ∧
            Inv s' ∧ rank s' < rank s)))
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
      ⟨some, 0, st, 0⟩ Post := by
  obtain ⟨stFinal, hRun, hInvF, hCondF⟩ :=
    runWhileFlowSteps_cutpoint_sound alg cond (evalPlan alg body) Inv rank hStep
      (rank st) st hInv (Nat.le_refl (rank st))
  refine (stepsTo_whileExit_of_runWhileFlowSteps alg cond body retExpr (rank st)
    some st stFinal hRun).bind_wp ?_
  intro s₁ hs₁
  subst hs₁
  obtain ⟨hClean, rv, hRv, hFree, hPost⟩ := hExit stFinal hInvF hCondF
  exact PureMirExec.WpConverges.of_done
    (blockCfgStep_whileExit alg cond body retExpr some stFinal rv
      ⟨rv, collectRootMutVals stFinal.loans⟩ hClean hRv hFree rfl)
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
    (wrap : FuncOut Val → Option (FuncOut Val)) (s₀ : SymState Val) (hle : lo ≤ hi)
    (hInit : abs lo init s₀) :
    PureMirExec.StepsTo
      (blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr)))
      ⟨wrap, 0, s₀, 0⟩
      (fun t => t.wrap = wrap ∧ t.bb = 0 ∧ t.wait = 0 ∧
        abs hi (PureMirExec.forRangeUp lo hi init f) t.st) := by
  refine PureMirExec.stepsTo_forRangeUp
    (blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr)))
    lo hi init f
    (fun i a t => t.wrap = wrap ∧ t.bb = 0 ∧ t.wait = 0 ∧ abs i a t.st)
    ⟨wrap, 0, s₀, 0⟩ hle ⟨rfl, rfl, rfl, hInit⟩ ?_
  intro i hlo hlt a t ht
  obtain ⟨hWrap, hBb, hWait, hAbs⟩ := ht
  obtain ⟨⟨cv, hCond, hBool⟩, s', hBody, hAbs'⟩ := hIter i hlo hlt a t.st hAbs
  cases t with
  | mk w bb st wait =>
    dsimp only at hWrap hBb hWait hCond hBody
    subst hWrap
    subst hBb
    subst hWait
    exact PureMirExec.StepsTo.step
      (blockCfgStep_whileHeader_true alg cond body retExpr w st cv hCond hBool)
      (PureMirExec.StepsTo.step
        (blockCfgStep_whileBody alg cond body retExpr w st s' hBody)
        (PureMirExec.StepsTo.refl ⟨rfl, rfl, rfl, hAbs'⟩))

/-- **Counted loops to exit block `2` via `forRangeUp`**: composing
`whileLoop_stepsTo_forRangeUp` with one false-header transition reaches exit
block `2` in a state satisfying `abs hi (PureMirExec.forRangeUp lo hi init f)`. -/
theorem whileLoop_stepsTo_exit_forRangeUp {α : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val) (body : FlowPlan Val) (retExpr : RvalOp Val)
    (lo hi : Nat) (init : α) (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (abs : Nat → α → SymState Val → Prop)
    (hIter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s, abs i a s →
      (Exists fun cv => evalRval alg cond s = some cv ∧ alg.asBool cv = some true) ∧
      Exists fun s' => evalPlan alg body s = .ok (.continuing s') ∧
        abs (i + 1) (f i hlo hlt a) s')
    (hExit : ∀ s, abs hi (PureMirExec.forRangeUp lo hi init f) s →
      Exists fun cv => evalRval alg cond s = some cv ∧ alg.asBool cv = some false)
    (wrap : FuncOut Val → Option (FuncOut Val)) (s₀ : SymState Val) (hle : lo ≤ hi)
    (hInit : abs lo init s₀) :
    PureMirExec.StepsTo
      (blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond body retExpr)))
      ⟨wrap, 0, s₀, 0⟩
      (fun t => t.wrap = wrap ∧ t.bb = 2 ∧ t.wait = 0 ∧
        abs hi (PureMirExec.forRangeUp lo hi init f) t.st) := by
  refine (whileLoop_stepsTo_forRangeUp alg cond body retExpr lo hi init f abs
    hIter wrap s₀ hle hInit).trans ?_
  intro t ht
  obtain ⟨hWrap, hBb, hWait, hAbs⟩ := ht
  obtain ⟨cv, hCond, hBool⟩ := hExit t.st hAbs
  cases t with
  | mk w bb st wait =>
    dsimp only at hWrap hBb hWait hCond hAbs
    subst hWrap
    subst hBb
    subst hWait
    exact PureMirExec.StepsTo.step
      (blockCfgStep_whileHeader_false alg cond body retExpr w st cv hCond hBool)
      (PureMirExec.StepsTo.refl ⟨rfl, rfl, rfl, hAbs⟩)

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

/-! ## Episode 2 Readiness: Trusted `AbstractByte` Windows as Spatial Cells

`SpatialPin` stores frozen loans as `List (CellVal Val)`. Provenance-free
trusted bytes (`.uninit`, `.init b none`) are exactly the `.uninit` / `.rawByte`
cells, so any `SepLogicLenses.ByteLensCodec α n` with provenance-free encodings
lifts (`spatialCodecOfByteLensCodec`) to a `SpatialCodec` over an arbitrary
value domain (for example MIR `Value`) that encodes `α`'s image as its exact
`n`-byte raw window and every other value as `byteLensFallbackCells n v`, whose
width is never `n`. Since `mutateSpatialInState` preserves cell counts, a block
frozen from an in-image value decodes only through the byte codec
(`spatialCodecOfByteLensCodec_decode_in_subdomain`), so spatial byte writes can
never retype it; no change to the PureLift core is needed. -/

section ByteWindows

variable {Val : Type}

/-- A provenance-free trusted byte as a spatial cell; a byte carrying pointer
provenance has no raw-byte cell. -/
def cellOfAbstractByte : AbstractByte → Option (CellVal Val)
  | .uninit => some .uninit
  | .init b none => some (.rawByte b)
  | .init _ (some _) => none

/-- A raw-byte or uninitialized spatial cell as a trusted byte. -/
def abstractByteOfCell : CellVal Val → Option AbstractByte
  | .uninit => some .uninit
  | .rawByte b => some (.init b none)
  | .init _ => none

def cellsOfAbstractBytes (bs : List AbstractByte) : Option (List (CellVal Val)) :=
  bs.foldr
    (fun b acc =>
      match cellOfAbstractByte b, acc with
      | some c, some cs => some (c :: cs)
      | _, _ => none)
    (some [])

def abstractBytesOfCells (cs : List (CellVal Val)) : Option (List AbstractByte) :=
  cs.foldr
    (fun c acc =>
      match abstractByteOfCell c, acc with
      | some b, some bs => some (b :: bs)
      | _, _ => none)
    (some [])

/-- True iff no byte of `bs` carries pointer provenance. -/
def provenanceFree (bs : List AbstractByte) : Bool :=
  bs.all (fun b =>
    match b with
    | .init _ (some _) => false
    | _ => true)

theorem cellsOfAbstractBytes_cons (b : AbstractByte) (bs : List AbstractByte) :
    cellsOfAbstractBytes (Val := Val) (b :: bs) =
      (match cellOfAbstractByte b, cellsOfAbstractBytes bs with
       | some c, some cs => some (c :: cs)
       | _, _ => none) := rfl

theorem abstractBytesOfCells_cons (c : CellVal Val) (cs : List (CellVal Val)) :
    abstractBytesOfCells (c :: cs) =
      (match abstractByteOfCell c, abstractBytesOfCells cs with
       | some b, some bs => some (b :: bs)
       | _, _ => none) := rfl

/-- Provenance-free byte windows convert to cells. -/
theorem cellsOfAbstractBytes_isSome :
    ∀ (bs : List AbstractByte), provenanceFree bs = true →
      Exists fun cs => cellsOfAbstractBytes (Val := Val) bs = some cs
  | [], _ => ⟨[], rfl⟩
  | b :: bs, h => by
    cases b with
    | uninit =>
      have hbs : provenanceFree bs = true := h
      obtain ⟨cs, hcs⟩ := cellsOfAbstractBytes_isSome bs hbs
      rw [cellsOfAbstractBytes_cons, hcs]
      exact ⟨_, rfl⟩
    | init x p =>
      cases p with
      | none =>
        have hbs : provenanceFree bs = true := h
        obtain ⟨cs, hcs⟩ := cellsOfAbstractBytes_isSome bs hbs
        rw [cellsOfAbstractBytes_cons, hcs]
        exact ⟨_, rfl⟩
      | some _ =>
        have hF : false = true := h
        exact Bool.noConfusion hF

/-- Converting a byte window to cells and back is the identity. -/
theorem abstractBytesOfCells_cellsOfAbstractBytes :
    ∀ (bs : List AbstractByte) (cs : List (CellVal Val)),
      cellsOfAbstractBytes bs = some cs → abstractBytesOfCells cs = some bs
  | [], cs, h => by
    injection h with h
    subst h
    rfl
  | b :: bs, cs, h => by
    rw [cellsOfAbstractBytes_cons] at h
    cases hb : cellOfAbstractByte (Val := Val) b with
    | none =>
      rw [hb] at h
      exact nomatch h
    | some c =>
      cases hcs : cellsOfAbstractBytes (Val := Val) bs with
      | none =>
        rw [hb, hcs] at h
        exact nomatch h
      | some cs' =>
        rw [hb, hcs] at h
        injection h with h
        subst h
        rw [abstractBytesOfCells_cons,
          abstractBytesOfCells_cellsOfAbstractBytes bs cs' hcs]
        cases b with
        | uninit =>
          injection hb with hc
          subst hc
          rfl
        | init x p =>
          cases p with
          | none =>
            injection hb with hc
            subst hc
            rfl
          | some _ => exact nomatch hb

/-- Cells produced from bytes are never value cells. -/
theorem cellsOfAbstractBytes_ne_init :
    ∀ (bs : List AbstractByte) (cs : List (CellVal Val)) (w : Val),
      cellsOfAbstractBytes bs = some cs → cs ≠ [.init w]
  | [], _, _, h, hEq => by
    injection h with h
    subst h
    exact nomatch hEq
  | b :: bs, cs, w, h, hEq => by
    rw [cellsOfAbstractBytes_cons] at h
    cases hb : cellOfAbstractByte (Val := Val) b with
    | none =>
      rw [hb] at h
      exact nomatch h
    | some c =>
      cases hcs : cellsOfAbstractBytes (Val := Val) bs with
      | none =>
        rw [hb, hcs] at h
        exact nomatch h
      | some cs' =>
        rw [hb, hcs] at h
        injection h with h
        subst h
        injection hEq with hc _
        subst hc
        cases b with
        | uninit => exact nomatch hb
        | init x p =>
          cases p with
          | none => exact nomatch hb
          | some _ => exact nomatch hb

/-- Converting a byte window to cells preserves length. -/
theorem cellsOfAbstractBytes_length :
    ∀ (bs : List AbstractByte) (cs : List (CellVal Val)),
      cellsOfAbstractBytes bs = some cs → cs.length = bs.length
  | [], cs, h => by
    injection h with h
    subst h
    rfl
  | b :: bs, cs, h => by
    rw [cellsOfAbstractBytes_cons] at h
    cases hb : cellOfAbstractByte (Val := Val) b with
    | none =>
      rw [hb] at h
      exact nomatch h
    | some c =>
      cases hcs : cellsOfAbstractBytes (Val := Val) bs with
      | none =>
        rw [hb, hcs] at h
        exact nomatch h
      | some cs' =>
        rw [hb, hcs] at h
        injection h with h
        subst h
        exact congrArg (· + 1) (cellsOfAbstractBytes_length bs cs' hcs)

/-- Converting a cell window to bytes preserves length. -/
theorem abstractBytesOfCells_length :
    ∀ (cs : List (CellVal Val)) (bs : List AbstractByte),
      abstractBytesOfCells cs = some bs → bs.length = cs.length
  | [], bs, h => by
    injection h with h
    subst h
    rfl
  | c :: cs, bs, h => by
    rw [abstractBytesOfCells_cons] at h
    cases hc : abstractByteOfCell c with
    | none =>
      rw [hc] at h
      exact nomatch h
    | some b =>
      cases hbs : abstractBytesOfCells cs with
      | none =>
        rw [hc, hbs] at h
        exact nomatch h
      | some bs' =>
        rw [hc, hbs] at h
        injection h with h
        subst h
        exact congrArg (· + 1) (abstractBytesOfCells_length cs bs' hbs)

/-- Converting a cell window to bytes and back is the identity. -/
theorem cellsOfAbstractBytes_abstractBytesOfCells :
    ∀ (cs : List (CellVal Val)) (bs : List AbstractByte),
      abstractBytesOfCells cs = some bs →
      cellsOfAbstractBytes (Val := Val) bs = some cs
  | [], bs, h => by
    injection h with h
    subst h
    rfl
  | c :: cs, bs, h => by
    rw [abstractBytesOfCells_cons] at h
    cases hc : abstractByteOfCell c with
    | none =>
      rw [hc] at h
      exact nomatch h
    | some b =>
      cases hbs : abstractBytesOfCells cs with
      | none =>
        rw [hc, hbs] at h
        exact nomatch h
      | some bs' =>
        rw [hc, hbs] at h
        injection h with h
        subst h
        rw [cellsOfAbstractBytes_cons,
          cellsOfAbstractBytes_abstractBytesOfCells cs bs' hbs]
        cases c with
        | uninit =>
          injection hc with hb
          subst hb
          rfl
        | rawByte x =>
          injection hc with hb
          subst hb
          rfl
        | init _ => exact nomatch hc

/-- `SpatialPin.hasUninitCell` on a converted byte window is the exact negation
of `Anneal.BitValidity.allBytesInitialized`. -/
theorem hasUninitCell_cellsOfAbstractBytes :
    ∀ (bs : List AbstractByte) (cs : List (CellVal Val)),
      cellsOfAbstractBytes bs = some cs →
      hasUninitCell cs = !Anneal.BitValidity.allBytesInitialized bs
  | [], cs, h => by
    injection h with h
    subst h
    rfl
  | b :: bs, cs, h => by
    rw [cellsOfAbstractBytes_cons] at h
    cases hb : cellOfAbstractByte (Val := Val) b with
    | none =>
      rw [hb] at h
      exact nomatch h
    | some c =>
      cases hcs : cellsOfAbstractBytes (Val := Val) bs with
      | none =>
        rw [hb, hcs] at h
        exact nomatch h
      | some cs' =>
        rw [hb, hcs] at h
        injection h with h
        subst h
        cases b with
        | uninit =>
          injection hb with hc
          subst hc
          rfl
        | init x p =>
          cases p with
          | none =>
            injection hb with hc
            subst hc
            exact hasUninitCell_cellsOfAbstractBytes bs cs' hcs
          | some _ => exact nomatch hb

/-- `Anneal.BitValidity.allBytesInitialized` on a converted cell window is the
exact negation of `SpatialPin.hasUninitCell`. -/
theorem allBytesInitialized_abstractBytesOfCells :
    ∀ (cs : List (CellVal Val)) (bs : List AbstractByte),
      abstractBytesOfCells cs = some bs →
      Anneal.BitValidity.allBytesInitialized bs = !hasUninitCell cs
  | cs, bs, h => by
    have hConv := cellsOfAbstractBytes_abstractBytesOfCells cs bs h
    have hUninit := hasUninitCell_cellsOfAbstractBytes bs cs hConv
    rw [hUninit, Bool.not_not]

/-- Fallback cell encoding for values outside the subdomain of an `n`-byte
codec: uses 2 value cells `[.init v, .init v]` when `n = 1` and 1 value cell
`[.init v]` when `n ≠ 1`, so the fallback cell count is never `n` (preventing
width-1 byte codecs such as `bool` or `u8` from sharing width `1` with a
fallback `[.init w]` cell). -/
def byteLensFallbackCells (n : Nat) (v : Val) : List (CellVal Val) :=
  if Nat.beq n 1 then [.init v, .init v] else [.init v]

/-- Extract the fallback value when `cells` has the fallback shape for width `n`
(length 2 when `n = 1`, length 1 when `n ≠ 1`). -/
def decodeByteLensFallback? (n : Nat) (cells : List (CellVal Val)) : Option Val :=
  if Nat.beq n 1 then
    match cells with
    | [.init w, .init _] => some w
    | _ => none
  else
    match cells with
    | [.init w] => some w
    | _ => none

theorem decodeByteLensFallback?_fallback (n : Nat) (v : Val) :
    decodeByteLensFallback? n (byteLensFallbackCells n v) = some v := by
  unfold byteLensFallbackCells decodeByteLensFallback?
  cases Nat.beq n 1 <;> rfl

theorem decodeByteLensFallback?_of_cellsOfAbstractBytes (n : Nat) :
    ∀ (bs : List AbstractByte) (cs : List (CellVal Val)),
      cellsOfAbstractBytes (Val := Val) bs = some cs →
      decodeByteLensFallback? n cs = none
  | [], cs, h => by
    injection h with h
    subst h
    unfold decodeByteLensFallback?
    cases Nat.beq n 1 <;> rfl
  | b :: bs, cs, h => by
    rw [cellsOfAbstractBytes_cons] at h
    cases hb : cellOfAbstractByte (Val := Val) b with
    | none => rw [hb] at h; exact nomatch h
    | some c =>
      cases hcs : cellsOfAbstractBytes (Val := Val) bs with
      | none => rw [hb, hcs] at h; exact nomatch h
      | some cs' =>
        rw [hb, hcs] at h
        injection h with h
        subst h
        cases b with
        | uninit =>
          injection hb with hc
          subst hc
          unfold decodeByteLensFallback?
          cases Nat.beq n 1 <;> rfl
        | init x p =>
          cases p with
          | none =>
            injection hb with hc
            subst hc
            unfold decodeByteLensFallback?
            cases Nat.beq n 1 <;> rfl
          | some _ => exact nomatch hb

theorem decodeByteLensFallback?_of_length_eq (n : Nat)
    (cells : List (CellVal Val)) (hLen : cells.length = n) :
    decodeByteLensFallback? n cells = none := by
  unfold decodeByteLensFallback?
  cases hBeq : Nat.beq n 1 with
  | true =>
    have hn1 : n = 1 := Nat.eq_of_beq_eq_true hBeq
    subst hn1
    cases cells with
    | nil => rfl
    | cons c1 rest1 =>
      cases rest1 with
      | nil => cases c1 <;> rfl
      | cons _ _ => nomatch hLen
  | false =>
    cases cells with
    | nil => rfl
    | cons c1 rest1 =>
      cases rest1 with
      | nil =>
        subst hLen
        exact nomatch hBeq
      | cons _ _ => cases c1 <;> rfl

/-- **`ByteLensCodec` as a `SpatialCodec`**: a provenance-free trusted byte codec
on `α` of fixed width `n`, embedded into `Val` by the prism `(toVal, ofVal?)`,
encodes `α`'s image as its `n`-byte raw byte window (enforcing exact width
`bs.length == n` on decode) and falls back to `byteLensFallbackCells n v`
(whose length is never `n`) elsewhere. -/
def spatialCodecOfByteLensCodec {α : Type} {n : Nat} (cid : Nat)
    (c : Anneal.SepLogicLenses.ByteLensCodec α n)
    (hProv : ∀ a, provenanceFree (c.encode a) = true)
    (toVal : α → Val) (ofVal? : Val → Option α)
    (toVal_ofVal? : ∀ (v : Val) (a : α), ofVal? v = some a → toVal a = v) :
    SpatialCodec Val where
  codecId := cid
  encode v :=
    match ofVal? v with
    | some a => (cellsOfAbstractBytes (c.encode a)).getD []
    | none => byteLensFallbackCells n v
  decode cells :=
    match decodeByteLensFallback? n cells with
    | some w =>
      match ofVal? w with
      | none => some w
      | some _ => none
    | none =>
      match abstractBytesOfCells cells with
      | some bs =>
        if Nat.beq bs.length n then
          match c.decode bs with
          | some a => some (toVal a)
          | none => none
        else none
      | none => none
  decode_encode v := by
    cases hv : ofVal? v with
    | none =>
      dsimp only
      rw [decodeByteLensFallback?_fallback]
      dsimp only
      rw [hv]
    | some a =>
      dsimp only
      obtain ⟨cs, hcs⟩ := cellsOfAbstractBytes_isSome (Val := Val) (c.encode a)
        (hProv a)
      rw [hcs]
      dsimp only [Option.getD]
      rw [decodeByteLensFallback?_of_cellsOfAbstractBytes n (c.encode a) cs hcs]
      dsimp only
      rw [abstractBytesOfCells_cellsOfAbstractBytes (c.encode a) cs hcs]
      dsimp only
      rw [c.encode_len a, Nat.beq_refl]
      rw [c.decode_encode a]
      exact congrArg some (toVal_ofVal? v a hv)

/-- Every value in the subdomain `ofVal? v = some a` encodes to an exact
`n`-cell window under `spatialCodecOfByteLensCodec`. -/
theorem spatialCodecOfByteLensCodec_encode_length {α : Type} {n : Nat}
    (cid : Nat) (c : Anneal.SepLogicLenses.ByteLensCodec α n)
    (hProv : ∀ a, provenanceFree (c.encode a) = true)
    (toVal : α → Val) (ofVal? : Val → Option α)
    (toVal_ofVal? : ∀ (v : Val) (a : α), ofVal? v = some a → toVal a = v)
    (v : Val) (a : α) (hv : ofVal? v = some a) :
    ((spatialCodecOfByteLensCodec cid c hProv toVal ofVal?
        toVal_ofVal?).encode v).length = n := by
  unfold spatialCodecOfByteLensCodec
  dsimp only
  rw [hv]
  dsimp only
  obtain ⟨cs, hcs⟩ := cellsOfAbstractBytes_isSome (Val := Val) (c.encode a)
    (hProv a)
  rw [hcs]
  dsimp only [Option.getD]
  rw [cellsOfAbstractBytes_length (c.encode a) cs hcs]
  exact c.encode_len a

/-- Any non-fallback cell slice whose length differs from `n` is rejected by
`spatialCodecOfByteLensCodec.decode`. -/
theorem spatialCodecOfByteLensCodec_decode_wrong_length {α : Type} {n : Nat}
    (cid : Nat) (c : Anneal.SepLogicLenses.ByteLensCodec α n)
    (hProv : ∀ a, provenanceFree (c.encode a) = true)
    (toVal : α → Val) (ofVal? : Val → Option α)
    (toVal_ofVal? : ∀ (v : Val) (a : α), ofVal? v = some a → toVal a = v)
    (cells : List (CellVal Val)) (hLen : Nat.beq cells.length n = false)
    (hNoFallback : decodeByteLensFallback? n cells = none) :
    (spatialCodecOfByteLensCodec cid c hProv toVal ofVal?
      toVal_ofVal?).decode cells = none := by
  unfold spatialCodecOfByteLensCodec
  dsimp only
  rw [hNoFallback]
  dsimp only
  cases hBytes : abstractBytesOfCells cells with
  | none => rfl
  | some bs =>
    dsimp only
    rw [abstractBytesOfCells_length cells bs hBytes, hLen]
    rfl

/-- **No-retyping / In-subdomain preservation**: on any cell slice of length `n`
(such as a spatial block frozen from an in-subdomain value and mutated via
`mutateSpatialInState`), `spatialCodecOfByteLensCodec.decode` never takes the
fallback branch; if it succeeds with `some v'`, then `cells` is a pure byte
window (`abstractBytesOfCells cells = some bs`) and `v' = toVal a` for some
decoded `a : α`. -/
theorem spatialCodecOfByteLensCodec_decode_in_subdomain {α : Type} {n : Nat}
    (cid : Nat) (c : Anneal.SepLogicLenses.ByteLensCodec α n)
    (hProv : ∀ a, provenanceFree (c.encode a) = true)
    (toVal : α → Val) (ofVal? : Val → Option α)
    (toVal_ofVal? : ∀ (v : Val) (a : α), ofVal? v = some a → toVal a = v)
    (cells : List (CellVal Val)) (v' : Val)
    (hLen : cells.length = n)
    (hDec : (spatialCodecOfByteLensCodec cid c hProv toVal ofVal?
      toVal_ofVal?).decode cells = some v') :
    Exists fun bs => Exists fun a =>
      abstractBytesOfCells cells = some bs ∧
      c.decode bs = some a ∧
      v' = toVal a := by
  unfold spatialCodecOfByteLensCodec at hDec
  dsimp only at hDec
  rw [decodeByteLensFallback?_of_length_eq n cells hLen] at hDec
  dsimp only at hDec
  cases hBytes : abstractBytesOfCells cells with
  | none => rw [hBytes] at hDec; exact nomatch hDec
  | some bs =>
    rw [hBytes] at hDec
    dsimp only at hDec
    have hBsLen : bs.length = n :=
      (abstractBytesOfCells_length cells bs hBytes).trans hLen
    rw [hBsLen, Nat.beq_refl] at hDec
    cases hC : c.decode bs with
    | none => rw [hC] at hDec; exact nomatch hDec
    | some a =>
      rw [hC] at hDec
      injection hDec with hEq
      exact ⟨bs, a, rfl, hC, hEq.symm⟩

/-- If `c.encode a` is fully initialized (`BitValidity.allBytesInitialized`),
then `spatialCodecOfByteLensCodec` encodes `v` (with `ofVal? v = some a`) to an
`.uninit`-free cell window (`hasUninitCell = false`). -/
theorem spatialCodecOfByteLensCodec_hasUninitCell_false {α : Type} {n : Nat}
    (cid : Nat) (c : Anneal.SepLogicLenses.ByteLensCodec α n)
    (hProv : ∀ a, provenanceFree (c.encode a) = true)
    (toVal : α → Val) (ofVal? : Val → Option α)
    (toVal_ofVal? : ∀ (v : Val) (a : α), ofVal? v = some a → toVal a = v)
    (v : Val) (a : α) (hv : ofVal? v = some a)
    (hInit : Anneal.BitValidity.allBytesInitialized (c.encode a) = true) :
    hasUninitCell
      ((spatialCodecOfByteLensCodec cid c hProv toVal ofVal?
          toVal_ofVal?).encode v) = false := by
  unfold spatialCodecOfByteLensCodec
  dsimp only
  rw [hv]
  dsimp only
  obtain ⟨cs, hcs⟩ := cellsOfAbstractBytes_isSome (Val := Val) (c.encode a)
    (hProv a)
  rw [hcs]
  dsimp only [Option.getD]
  rw [hasUninitCell_cellsOfAbstractBytes (c.encode a) cs hcs, hInit]
  rfl

/-- Trusted little-endian encodings carry no pointer provenance. -/
theorem provenanceFree_encodeLittleEndianBytes :
    ∀ (sz bits : Nat), provenanceFree (encodeLittleEndianBytes bits sz none) = true
  | 0, _ => rfl
  | sz + 1, bits => by
    show provenanceFree
      (.init (UInt8.ofNat bits) none :: encodeLittleEndianBytes (Nat.div bits 256) sz none) =
        true
    simp only [provenanceFree, List.all_cons, Bool.true_and]
    exact provenanceFree_encodeLittleEndianBytes sz (Nat.div bits 256)

/-- Trusted little-endian encodings are fully initialized (`allBytesInitialized`). -/
theorem allBytesInitialized_encodeLittleEndianBytes :
    ∀ (sz bits : Nat),
      Anneal.BitValidity.allBytesInitialized
        (encodeLittleEndianBytes bits sz none) = true
  | 0, _ => rfl
  | sz + 1, bits =>
    allBytesInitialized_encodeLittleEndianBytes sz (Nat.div bits 256)

end ByteWindows

/-! ## Episode 2 Compatibility Helpers (No Change to the PureLift Core)

`main`'s `SpatialPin` no longer exports the `unpinFromSpatialInState` alias of
`reabsorbFromSpatialInState`, and `main`'s `Plan` dropped the `while`-loop plan
equation; the `V2026_06_01` bridge uses both. They are restated here against
`main`'s definitions, together with the handle-freedom and sub-identity facts
that a block-level simulation of an embedded `stepBasicBlock` CFG needs. -/

section Episode2Compat

/-- The `V2026_06_01` bridge's name for `main`'s `reabsorbFromSpatialInState`. -/
abbrev unpinFromSpatialInState := @reabsorbFromSpatialInState

/-- The `while`-loop plan equation for `main`'s `WfPlan`: a well-formed loop
body makes `evalPlan` of `FlowPlan.whileLoop` exactly `runWhileFlowSteps` over
`evalPlan` of the body. -/
theorem evalPlan_whileLoop {Val : Type} (alg : ValAlgebra Val)
    (fuel : Nat) (cond : RvalOp Val) (body : FlowPlan Val) (s0 : SymState Val)
    (hWfB : WfPlan alg body) :
    evalPlan alg (.whileLoop fuel cond body) s0 =
      runWhileFlowSteps alg cond (evalPlan alg body) fuel s0 := by
  change
    (match stepPlanOp alg (.whileLoopOp fuel cond)
        (evalPlanOps alg body.ops (true, [])) with
     | (true, [evalFn]) => evalFn s0
     | _ => .fail) = _
  rw [hWfB true []]
  rfl

/-- `handleFreeOutOpt` only rejects values: it is a sub-identity wrapper. -/
theorem subIdWrap_handleFreeOutOpt {Val : Type} (alg : ValAlgebra Val) :
    SubIdWrap (handleFreeOutOpt alg) := by
  intro out out' h
  unfold handleFreeOutOpt at h
  revert h
  cases handleFreeOut alg out with
  | true =>
    intro h
    injection h with hEq
    exact hEq.symm
  | false =>
    intro h
    exact nomatch h

/-- **Every halt of an embedded `stepBasicBlock` CFG is handle-free**
(`runBlockCfgLoop_stepBasicBlock_handleFree` through the exact embedding): from
a state with the identity wrapper and any pending delay, a halted value carries
no borrow handle. -/
theorem evalFuel_blockCfgStep_stepBasicBlock_handleFree {Val : Type}
    (alg : ValAlgebra Val) (blocks : List (BasicBlock Val))
    {k : Nat} {bb : Nat} {st : SymState Val} {wait : Nat} {out : FuncOut Val}
    (h : PureMirExec.evalFuel (blockCfgStep (stepBasicBlock alg blocks)) k
      ⟨some, bb, st, wait⟩ = .halted out) :
    handleFreeOut alg out = true := by
  have hRun : outcomeToFuel some
      (runBlockCfgLoop (forkFree (stepBasicBlock alg blocks)) k wait bb st) =
        .halted out :=
    (evalFuel_blockCfgStep_loop (stepBasicBlock alg blocks) k
      ⟨some, bb, st, wait⟩).symm.trans h
  cases hFF : runBlockCfgLoop (forkFree (stepBasicBlock alg blocks)) k wait bb st with
  | ret v =>
    rw [hFF] at hRun
    dsimp only [outcomeToFuel] at hRun
    injection hRun with hEq
    subst hEq
    exact runBlockCfgLoop_stepBasicBlock_handleFree alg blocks k wait bb st v
      (runBlockCfgLoop_of_forkFree_ret (stepBasicBlock alg blocks) k wait bb st v
        hFF)
  | diverged =>
    rw [hFF] at hRun
    exact nomatch hRun
  | fault =>
    rw [hFF] at hRun
    exact nomatch hRun

/-- `WpConverges` form of `evalFuel_blockCfgStep_stepBasicBlock_handleFree`:
convergence of an embedded `stepBasicBlock` CFG is strengthened with
handle-freedom of the returned value for free. -/
theorem wpConverges_blockCfgStep_stepBasicBlock_handleFree {Val : Type}
    (alg : ValAlgebra Val) (blocks : List (BasicBlock Val))
    {bb : Nat} {st : SymState Val} {wait : Nat} {P : FuncOut Val → Prop}
    (h : PureMirExec.WpConverges (blockCfgStep (stepBasicBlock alg blocks))
      ⟨some, bb, st, wait⟩ P) :
    PureMirExec.WpConverges (blockCfgStep (stepBasicBlock alg blocks))
      ⟨some, bb, st, wait⟩ (fun out => P out ∧ handleFreeOut alg out = true) := by
  obtain ⟨k, v, hk, hP⟩ := h
  exact ⟨k, v, hk, hP, evalFuel_blockCfgStep_stepBasicBlock_handleFree alg blocks hk⟩

end Episode2Compat

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

/-- **`CfgCertificate` adequacy for the embedded CFG machine**: a `CfgCertificate`
together with `HoldsFnSpec (evalFnValue ...)` and invariant-scoped fork-freedom
yields fuel-free `WpConverges` of `blockCfgStep`. -/
theorem wpConverges_of_cfgCertificate {Val : Type}
    (alg : ValAlgebra Val) (cert : CfgCertificate alg)
    (params : List (ParamInput Val)) (st0 : SymState Val)
    (post : FuncOut Val → Prop)
    (hInit : initFnState alg params = .ok st0)
    (hSpec : HoldsFnSpec (evalFnValue alg params cert.plan cert.retExpr) post)
    (BlockInv : Nat → SymState Val → Prop) (PostRet : FuncOut Val → Prop)
    (hLocal : LocalBlockVC (stepBasicBlock alg cert.blocks) BlockInv PostRet)
    (hNoFork : ∀ bb st, BlockInv bb st →
      ∀ mergeRet thenBb elseBb st',
        stepBasicBlock alg cert.blocks bb st ≠
          .branchJump mergeRet thenBb elseBb st')
    (hInv0 : BlockInv cert.entryBb st0) :
    PureMirExec.WpConverges (blockCfgStep (stepBasicBlock alg cert.blocks))
      ⟨some, cert.entryBb, st0, 0⟩ post := by
  cases hEval : evalFnValue alg params cert.plan cert.retExpr with
  | fail =>
    rw [hEval] at hSpec
    exact nomatch hSpec
  | ok out =>
    rw [hEval] at hSpec
    exact (wpConverges_blockCfgStep_iff_of_blockInv
      (stepBasicBlock alg cert.blocks) BlockInv PostRet hLocal hNoFork
      cert.entryBb st0 hInv0 post).mpr
      ⟨cert.fuel, out, cert.sound params st0 out hInit hEval, hSpec⟩

/-- **`CfgCertificate` refines live MIR**: composes `wpConverges_of_cfgCertificate`
with `mirWpConverges_of_blockCfg_forwardSim` to transport a `CfgCertificate` and
`HoldsFnSpec` proof to live `MirWpConverges`. -/
theorem mirWpConverges_of_cfgCertificate {Val : Type}
    (alg : ValAlgebra Val) (cert : CfgCertificate alg)
    (params : List (ParamInput Val)) (st0 : SymState Val)
    (post : FuncOut Val → Prop)
    (hInit : initFnState alg params = .ok st0)
    (hSpec : HoldsFnSpec (evalFnValue alg params cert.plan cert.retExpr) post)
    (BlockInv : Nat → SymState Val → Prop) (PostRet : FuncOut Val → Prop)
    (hLocal : LocalBlockVC (stepBasicBlock alg cert.blocks) BlockInv PostRet)
    (hNoFork : ∀ bb st, BlockInv bb st →
      ∀ mergeRet thenBb elseBb st',
        stepBasicBlock alg cert.blocks bb st ≠
          .branchJump mergeRet thenBb elseBb st')
    (hInv0 : BlockInv cert.entryBb st0)
    {body : CapturedMir}
    {R : BlockMachineState (SymState Val) (FuncOut Val) → MachineState → Prop}
    {RetRel : FuncOut Val → MirOutcome → Prop}
    (hSim : ForwardSim (blockCfgStep (stepBasicBlock alg cert.blocks))
      (PureMirExec.mirStep body) R RetRel)
    {ms : MachineState} (hR : R ⟨some, cert.entryBb, st0, 0⟩ ms) :
    Anneal.MirFuelFree.MirWpConverges body ms
      (fun o => Exists fun v => post v ∧ RetRel v o) :=
  mirWpConverges_of_blockCfg_forwardSim hSim
    (wpConverges_of_cfgCertificate alg cert params st0 post hInit hSpec BlockInv
      PostRet hLocal hNoFork hInv0)
    hR

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

/-- A `runBlockCfgToBlock` arrival is a MirLiftCore `StepsTo` segment of the
embedded CFG machine. -/
theorem stepsTo_of_runBlockCfgToBlock_reached
    {stepBb : Nat → State → BlockStepResult State Ret} {target bound : Nat}
    {s s' : BlockMachineState State Ret}
    (h : runBlockCfgToBlock stepBb target bound s = .reached s') :
    PureMirExec.StepsTo (blockCfgStep stepBb) s (· = s') :=
  PureMirExec.stepsTo_of_runToTarget_reached h

/-- **Verified PureLift header-targeted runs become MirLiftCore join paths**:
under a fork-free per-block VC, a `runBlockCfgToBlock` arrival `s'` at the
PureLift join block satisfies `MachineInv` and has no pending `.convergedJump`
delay (`runBlockCfgToBlock_sound`), so the MIR join correspondence `hJoin` may
use the PureLift block invariant at the join; with a per-step simulation into
live MIR this yields `MirLiftCore.LiftBlockToJoin`, i.e. the MIR join block is
proved once for every downstream continuation. -/
theorem liftBlockToJoin_of_runBlockCfgToBlock
    {stepBb : Nat → State → BlockStepResult State Ret} {body : CapturedMir}
    {BlockInv : Nat → State → Prop} {PostRet : Ret → Prop}
    (hLocal : LocalBlockVC (forkFree stepBb) BlockInv PostRet)
    {R : BlockMachineState State Ret → MachineState → Prop}
    (hSim : SegmentSim (blockCfgStep stepBb) (PureMirExec.mirStep body) R)
    {joinPb bound : Nat} {s s' : BlockMachineState State Ret}
    (hs : MachineInv BlockInv PostRet s)
    (hRun : runBlockCfgToBlock stepBb joinPb bound s = .reached s')
    {bbIdx joinBb : BasicBlockIdx} {env : MirLiftCore.PureEnv}
    {JoinInv : MirLiftCore.PureEnv → Prop}
    (hR : R s (({ bb := bbIdx, stmtIdx := 0, env := env } :
      PureMirExec.PureState).toMachineState emptyMemory))
    (hJoin : ∀ ms', MachineInv BlockInv PostRet s' → s'.bb = joinPb →
      s'.wait = 0 → R s' ms' →
      ms' = ({ bb := joinBb, stmtIdx := 0, env := ms'.frame.locals } :
        PureMirExec.PureState).toMachineState emptyMemory ∧
      JoinInv ms'.frame.locals) :
    MirLiftCore.LiftBlockToJoin body bbIdx env joinBb JoinInv := by
  have hSound := runBlockCfgToBlock_sound stepBb BlockInv PostRet hLocal joinPb
    bound s hs
  rw [hRun] at hSound
  refine liftBlockToJoin_of_blockCfg_segment hSim
    (stepsTo_of_runBlockCfgToBlock_reached hRun) hR ?_
  intro s'' ms' hEq hR'
  subst hEq
  exact hJoin ms' hSound.2.2 hSound.1 hSound.2.1 hR'

/-- **Verified PureLift `while` cutpoints become MirLiftCore join paths**:
for a `while` loop (`whileLoopBlocks cond bodyPlan retExpr`) satisfying a
cutpoint invariant `Inv` and strong well-founded ranking measure `rank`
(`rank s' < rank s`), any entry state `st` with `Inv st` reaches exit block `2`
in a state `stFinal` satisfying `Inv stFinal` and false loop condition; under a
per-step simulation into live MIR, the join correspondence `hJoin` may use
`Inv stFinal` and the false loop condition to establish
`MirLiftCore.LiftBlockToJoin` at the MIR loop exit block. -/
theorem liftBlockToJoin_of_whileCutpoint {Val : Type}
    (alg : ValAlgebra Val) (cond : RvalOp Val) (bodyPlan : FlowPlan Val)
    (retExpr : RvalOp Val) (Inv : SymState Val → Prop) (rank : SymState Val → Nat)
    (hStep : ∀ s, Inv s →
      Exists fun cv => evalRval alg cond s = some cv ∧
        (alg.asBool cv = some false ∨
         (alg.asBool cv = some true ∧
          Exists fun s' =>
            evalPlan alg bodyPlan s = .ok (.continuing s') ∧
            Inv s' ∧ rank s' < rank s)))
    {body : CapturedMir}
    {R : BlockMachineState (SymState Val) (FuncOut Val) → MachineState → Prop}
    (hSim : SegmentSim
      (blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond bodyPlan retExpr)))
      (PureMirExec.mirStep body) R)
    (wrap : FuncOut Val → Option (FuncOut Val)) (st : SymState Val) (hInv : Inv st)
    {bbIdx joinBb : BasicBlockIdx} {env : MirLiftCore.PureEnv}
    {JoinInv : MirLiftCore.PureEnv → Prop}
    (hR : R ⟨wrap, 0, st, 0⟩ (({ bb := bbIdx, stmtIdx := 0, env := env } :
      PureMirExec.PureState).toMachineState emptyMemory))
    (hJoin : ∀ stFinal ms',
      Inv stFinal →
      (Exists fun cv =>
        evalRval alg cond stFinal = some cv ∧ alg.asBool cv = some false) →
      R ⟨wrap, 2, stFinal, 0⟩ ms' →
      ms' = ({ bb := joinBb, stmtIdx := 0, env := ms'.frame.locals } :
        PureMirExec.PureState).toMachineState emptyMemory ∧
      JoinInv ms'.frame.locals) :
    MirLiftCore.LiftBlockToJoin body bbIdx env joinBb JoinInv := by
  obtain ⟨stFinal, hWhile, hInvF, hCondF⟩ :=
    runWhileFlowSteps_cutpoint_sound alg cond (evalPlan alg bodyPlan) Inv rank
      hStep (rank st) st hInv (Nat.le_refl (rank st))
  refine liftBlockToJoin_of_blockCfg_segment hSim
    (stepsTo_whileExit_of_runWhileFlowSteps alg cond bodyPlan retExpr (rank st)
      wrap st stFinal hWhile) hR ?_
  intro s' ms' hEq hR'
  subst hEq
  exact hJoin stFinal ms' hInvF hCondF hR'

/-- **Verified PureLift counted `forRangeUp` loops become MirLiftCore join paths**:
for a counted `while` loop (`whileLoopBlocks cond bodyPlan retExpr`) driven by
`whileLoop_stepsTo_exit_forRangeUp` over `[lo, hi)`, any entry state `s₀`
satisfying `abs lo init s₀` reaches exit block `2` in a state `stFinal`
satisfying `abs hi (PureMirExec.forRangeUp lo hi init f) stFinal`; under a
per-step simulation into live MIR, this yields `MirLiftCore.LiftBlockToJoin` at
the MIR loop exit block. -/
theorem liftBlockToJoin_of_whileForRangeUp {Val α : Type}
    (alg : ValAlgebra Val) (cond : RvalOp Val) (bodyPlan : FlowPlan Val)
    (retExpr : RvalOp Val)
    (lo hi : Nat) (init : α) (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (abs : Nat → α → SymState Val → Prop)
    (hIter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s, abs i a s →
      (Exists fun cv => evalRval alg cond s = some cv ∧ alg.asBool cv = some true) ∧
      Exists fun s' => evalPlan alg bodyPlan s = .ok (.continuing s') ∧
        abs (i + 1) (f i hlo hlt a) s')
    (hExit : ∀ s, abs hi (PureMirExec.forRangeUp lo hi init f) s →
      Exists fun cv => evalRval alg cond s = some cv ∧ alg.asBool cv = some false)
    {body : CapturedMir}
    {R : BlockMachineState (SymState Val) (FuncOut Val) → MachineState → Prop}
    (hSim : SegmentSim
      (blockCfgStep (stepBasicBlock alg (whileLoopBlocks cond bodyPlan retExpr)))
      (PureMirExec.mirStep body) R)
    (wrap : FuncOut Val → Option (FuncOut Val)) (s₀ : SymState Val) (hle : lo ≤ hi)
    (hInit : abs lo init s₀)
    {bbIdx joinBb : BasicBlockIdx} {env : MirLiftCore.PureEnv}
    {JoinInv : MirLiftCore.PureEnv → Prop}
    (hR : R ⟨wrap, 0, s₀, 0⟩ (({ bb := bbIdx, stmtIdx := 0, env := env } :
      PureMirExec.PureState).toMachineState emptyMemory))
    (hJoin : ∀ stFinal ms',
      abs hi (PureMirExec.forRangeUp lo hi init f) stFinal →
      R ⟨wrap, 2, stFinal, 0⟩ ms' →
      ms' = ({ bb := joinBb, stmtIdx := 0, env := ms'.frame.locals } :
        PureMirExec.PureState).toMachineState emptyMemory ∧
      JoinInv ms'.frame.locals) :
    MirLiftCore.LiftBlockToJoin body bbIdx env joinBb JoinInv := by
  refine liftBlockToJoin_of_blockCfg_segment hSim
    (whileLoop_stepsTo_exit_forRangeUp alg cond bodyPlan retExpr lo hi init f
      abs hIter hExit wrap s₀ hle hInit) hR ?_
  intro s' ms' hs' hR'
  cases s' with
  | mk w bb stFinal wait =>
    obtain ⟨hWrap, hBb, hWait, hAbs⟩ := hs'
    dsimp only at hWrap hBb hWait hAbs
    subst hWrap
    subst hBb
    subst hWait
    exact hJoin stFinal ms' hAbs hR'

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

theorem countdown_rank_converged :
    ∀ bb st armSteps wrapRet nextBb st', countdownInv bb st →
      testCfgStep bb st = .convergedJump armSteps wrapRet nextBb st' →
      countdownRank nextBb st' < countdownRank bb st := by
  intro bb st armSteps wrapRet nextBb st' hInv hStep
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
    PureMirExec.WpConverges (blockCfgStep testCfgStep) ⟨some, 0, n, 0⟩ (· = 100) :=
  wpConverges_blockCfgStep_of_rank testCfgStep countdownInv (· = 100)
    countdown_localBlockVC countdownRank countdown_rank_jump
    countdown_rank_jumpWrapped countdown_rank_converged
    ⟨some, 0, n, 0⟩ ⟨Or.inl rfl, fun _ hv => hv⟩

/-- **Non-vacuity of `runBlockCfg_total_of_rank`**: some fuel makes the
countdown CFG return `100` from every start value `n`. -/
theorem countdown_runBlockCfg_total (n : Nat) :
    Exists fun k => runBlockCfg testCfgStep 0 n k = .ret 100 := by
  obtain ⟨k, v, hRun, hv⟩ := runBlockCfg_total_of_rank testCfgStep countdownInv
    (· = 100) countdown_localBlockVC countdownRank countdown_rank_jump
    countdown_rank_jumpWrapped countdown_rank_converged 0 n (Or.inl rfl)
  subst hv
  exact ⟨k, hRun⟩

/-- Concrete embedding canaries: header-targeted stepping reaches the exit
block, `evalFuel` agrees with `runBlockCfg` (enough fuel halts with `100`, too
little fuel is `.outOfFuel`, never a fault), and a faulting block is `.stuck`. -/
theorem countdown_embedding_canaries :
    runBlockCfgToBlock testCfgStep 2 10 ⟨some, 0, 3, 0⟩ =
      .reached ⟨some, 2, 0, 0⟩ ∧
    PureMirExec.evalFuel (blockCfgStep testCfgStep) 8 ⟨some, 0, 3, 0⟩ =
      .halted 100 ∧
    PureMirExec.evalFuel (blockCfgStep testCfgStep) 2 ⟨some, 0, 3, 0⟩ =
      .outOfFuel ∧
    runBlockCfgToBlock testCfgStep 2 5 ⟨some, 99, 0, 0⟩ = .stuck :=
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
  s.wrap = some ∧ s.wait = 0 ∧
    ((s.bb = 0 ∧ m = s.st) ∨ (s.bb = 1 ∧ m = s.st) ∨
     (s.bb = 2 ∧ s.st = 0 ∧ m = 0))

/-- The countdown CFG machine forward-simulates into `natCountdownStep`,
including stuttering (`0`-step) segments for the `bb1 → bb0` and `bb0 → bb2`
edges. -/
theorem countdown_forwardSim :
    ForwardSim (blockCfgStep testCfgStep) natCountdownStep countdownSimRel
      (fun v o => v = o) := by
  intro s m hR
  obtain ⟨hWrap, hWait, hCase⟩ := hR
  cases s with
  | mk wrap bb st wait =>
    dsimp only at hWrap hWait hCase
    subst hWrap
    subst hWait
    rcases hCase with ⟨h0, hm⟩ | ⟨h1, hm⟩ | ⟨h2, hst, hm⟩
    · subst h0
      rw [hm]
      cases st with
      | zero =>
        show PureMirExec.StepsTo natCountdownStep 0
          (countdownSimRel ⟨some, 2, 0, 0⟩)
        exact PureMirExec.StepsTo.refl ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
      | succ n =>
        show PureMirExec.StepsTo natCountdownStep (n + 1)
          (countdownSimRel ⟨some, 1, n + 1 - 1, 0⟩)
        exact PureMirExec.StepsTo.step rfl
          (PureMirExec.StepsTo.refl ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
    · subst h1
      rw [hm]
      show PureMirExec.StepsTo natCountdownStep st
        (countdownSimRel ⟨some, 0, st, 0⟩)
      exact PureMirExec.StepsTo.refl ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
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
    ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

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
      blockCfgStep (stepBasicBlock stdValAlg symForkCfg) ⟨some, 0, st, 0⟩ =
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
      (stdValAlg.asBool cv = some false ∨
       (stdValAlg.asBool cv = some true ∧
        Exists fun s' =>
          evalPlan stdValAlg countUpBody s = .ok (.continuing s') ∧
          countUpInv n s' ∧ countUpRank n s' < countUpRank n s)) := by
  intro s hs
  obtain ⟨i, hi, hEq⟩ := hs
  subst hEq
  refine ⟨.bool (Nat.blt i n), countUp_eval_cond n i, ?_⟩
  cases hb : Nat.blt i n with
  | true =>
    have hlt : i < n := Nat.le_of_ble_eq_true hb
    refine Or.inr ⟨rfl, countUpState n (i + 1), countUp_eval_body n i,
      ⟨i + 1, hlt, rfl⟩, ?_⟩
    show n - (i + 1) < n - i
    omega
  | false =>
    exact Or.inl rfl

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
      ⟨some, 0, countUpState n i, 0⟩ (· = ⟨.unit, [.nat n]⟩) :=
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
      ⟨some, 0, countUpState n i, 0⟩ (· = ⟨.unit, [.nat n]⟩) := by
  refine (whileLoop_stepsTo_forRangeUp stdValAlg countUpCond countUpBody
    (.constVal .unit) i n i (fun _ _ _ a => a + 1)
    (fun j a s => a = j ∧ s = countUpState n j) ?_ some
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
    obtain ⟨hw, hbb, hwait, _, hst⟩ := ht
    cases t with
    | mk w bb st wait =>
      dsimp only at hw hbb hwait hst
      subst hw
      subst hbb
      subst hwait
      subst hst
      exact PureMirExec.WpConverges.of_cont
        (blockCfgStep_whileHeader_false stdValAlg countUpCond countUpBody
          (.constVal .unit) some (countUpState n n) (.bool (Nat.blt n n))
          (countUp_eval_cond n n)
          (by rw [nat_blt_self_eq_false]; rfl))
        (PureMirExec.WpConverges.of_done
          (blockCfgStep_whileExit stdValAlg countUpCond countUpBody
            (.constVal .unit) some (countUpState n n) .unit
            ⟨.unit, [.nat n]⟩ rfl rfl rfl rfl)
          rfl)

/-- Concrete header-targeted canary for `S6`: from `*x = 1, n = 3` the loop
CFG reaches its exit block with `*x = 3`, and `runBlockCfgToBlock_sound`
predicts exactly this (`countUpInv` holds there). -/
theorem countUp_runToBlock_canary :
    runBlockCfgToBlock (stepBasicBlock stdValAlg countUpBlocks) 2 8
      ⟨some, 0, countUpState 3 1, 0⟩ =
      .reached ⟨some, 2, countUpState 3 3, 0⟩ := rfl

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
  s.wrap = some ∧ s.st = 0 ∧ s.wait = 0 ∧
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
  obtain ⟨hWrap, hSt, hWait, hCases⟩ := hR
  cases s with
  | mk wrap bb st wait =>
    dsimp only at hWrap hSt hWait hCases
    subst hWrap
    subst hSt
    subst hWait
    rcases hCases with ⟨hBb, hMs⟩ | ⟨hBb, hMs⟩
    · subst hBb
      subst hMs
      show PureMirExec.StepsTo (PureMirExec.mirStep liveInteropMirBody)
        (liveInteropMs 0) (liveInteropRel ⟨some, 2, 0, 0⟩)
      exact stepsTo_of_runMirToBlock_reached
        (rfl : PureMirExec.runMirToBlock liveInteropMirBody 1
          (liveInteropMs 0) = .reached (liveInteropMs 1))
        ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
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
    (countdown_wpConverges 0) ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- **Non-vacuity of `liftBlockToJoin_of_blockCfg_segment`**: a PureLift CFG
segment from block `0` to join block `2` lifts via `liveInterop_forwardSim` to
`MirLiftCore.LiftBlockToJoin liveInteropMirBody 0 liveInteropEnv 1`. -/
theorem liveInterop_liftBlockToJoin_canary :
    MirLiftCore.LiftBlockToJoin liveInteropMirBody 0 liveInteropEnv 1
      (· = liveInteropEnv) := by
  have hSeg :
      PureMirExec.StepsTo (blockCfgStep testCfgStep) ⟨some, 0, 0, 0⟩
        (· = ⟨some, 2, 0, 0⟩) :=
    PureMirExec.StepsTo.step rfl (PureMirExec.StepsTo.refl rfl)
  refine liftBlockToJoin_of_blockCfg_segment liveInterop_forwardSim.segmentSim
    hSeg ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩ ?_
  intro s' ms' hPJ hR'
  subst hPJ
  rcases hR'.2.2.2 with ⟨hBad, _⟩ | ⟨_, hMs⟩
  · exact nomatch hBad
  · subst hMs
    exact ⟨rfl, rfl⟩

/-- **Non-vacuity of `liftBlockToJoin_of_runBlockCfgToBlock`**: the verified
countdown CFG (`countdown_localBlockVC`) runs from block `0` to its join block
`2` by header-targeted stepping, and the live MIR join path follows from the
segment simulation `liveInterop_forwardSim` with the join correspondence
read off the PureLift invariant at the join. -/
theorem liveInterop_liftBlockToJoin_of_runBlockCfgToBlock_canary :
    MirLiftCore.LiftBlockToJoin liveInteropMirBody 0 liveInteropEnv 1
      (· = liveInteropEnv) :=
  liftBlockToJoin_of_runBlockCfgToBlock countdown_localBlockVC
    liveInterop_forwardSim.segmentSim (s := ⟨some, 0, 0, 0⟩)
    ⟨Or.inl rfl, fun _ hv => hv⟩
    (rfl : runBlockCfgToBlock testCfgStep 2 5 ⟨some, 0, 0, 0⟩ =
      .reached ⟨some, 2, 0, 0⟩)
    ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
    (fun ms' _ _ _ hR' => by
      rcases hR'.2.2.2 with ⟨hBad, _⟩ | ⟨_, hMs⟩
      · exact nomatch hBad
      · subst hMs
        exact ⟨rfl, rfl⟩)

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
    PureMirExec.WpConverges (blockCfgStep testCfgStep) ⟨some, 0, 3, 0⟩
      (· = 100) :=
  (wpConverges_blockCfgStep_iff_of_noFork testCfgStep testCfgStep_noFork 0 3
    (· = 100)).mpr ⟨10, 100, rfl, rfl⟩

/-- **Why invariant-scoped `wpConverges_blockCfgStep_iff_of_blockInv` is strictly
more general than global `wpConverges_blockCfgStep_iff_of_noFork`**:
`sampleBranchBlockCfg` has a `.branch (.use (.localSub 0 [])) 1 2` terminator,
so on an unreachable state where `_0` holds `.symBool true` and `spatial` is
non-empty (causing `joinSymState` to reject the arm join), it emits
`.branchJump`, refuting the global `hNoFork` hypothesis. Under the concrete
entry invariant `BlockInv`, however, it never forks and
`wpConverges_blockCfgStep_iff_of_blockInv` applies cleanly. -/
theorem sampleBranchBlockCfg_not_global_noFork :
    ¬ (∀ bb st mergeRet thenBb elseBb st',
        stepBasicBlock stdValAlg sampleBranchBlockCfg bb st ≠
          .branchJump mergeRet thenBb elseBb st') := by
  intro hAll
  let pinnedSp : List (SpatialBlock StdVal) :=
    [⟨0, 0, .readWrite, 0, 0, []⟩]
  let stPinned : SymState StdVal :=
    ⟨[⟨.symBool true, .unborrowed⟩, ⟨.nat 0, .unborrowed⟩],
     [], [], [], pinnedSp, 1⟩
  exact hAll 0 stPinned
    (fun tOut fOut =>
      handleFreeOutOpt stdValAlg (mergeFuncOut stdValAlg (.symBool true) tOut fOut))
    1 2 stPinned rfl

def sampleBranchTrueInv (bb : Nat) (st : SymState StdVal) : Prop :=
  (bb = 0 ∧ st = ⟨[⟨.bool true, .unborrowed⟩], [], [], [], [], 0⟩) ∨
  (bb = 1 ∧ st = ⟨[⟨.bool true, .unborrowed⟩], [], [], [], [], 0⟩) ∨
  (bb = 3 ∧
    st = ⟨[⟨.bool true, .unborrowed⟩, ⟨.nat 10, .unborrowed⟩],
          [], [], [], [], 0⟩)

theorem sampleBranchTrue_localVC :
    LocalBlockVC (stepBasicBlock stdValAlg sampleBranchBlockCfg)
      sampleBranchTrueInv (· = ⟨.nat 10, []⟩) := by
  intro bb st hInv
  rcases hInv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact rfl

theorem sampleBranchTrue_noFork :
    ∀ bb st, sampleBranchTrueInv bb st →
      ∀ mergeRet thenBb elseBb st',
        stepBasicBlock stdValAlg sampleBranchBlockCfg bb st ≠
          .branchJump mergeRet thenBb elseBb st' := by
  intro bb st hInv mergeRet thenBb elseBb st' hStep
  rcases hInv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact nomatch hStep
  · exact nomatch hStep
  · exact nomatch hStep

theorem sampleBranchBlockCfg_wpConverges_of_blockInv :
    PureMirExec.WpConverges
      (blockCfgStep (stepBasicBlock stdValAlg sampleBranchBlockCfg))
      ⟨some, 0, ⟨[⟨.bool true, .unborrowed⟩], [], [], [], [], 0⟩, 0⟩
      (· = ⟨.nat 10, []⟩) :=
  (wpConverges_blockCfgStep_iff_of_blockInv
    (stepBasicBlock stdValAlg sampleBranchBlockCfg)
    sampleBranchTrueInv (· = ⟨.nat 10, []⟩)
    sampleBranchTrue_localVC sampleBranchTrue_noFork
    0 ⟨[⟨.bool true, .unborrowed⟩], [], [], [], [], 0⟩
    (Or.inl ⟨rfl, rfl⟩) (· = ⟨.nat 10, []⟩)).mpr
    ⟨4, ⟨.nat 10, []⟩, rfl, rfl⟩


/-! ### Trusted byte windows: a `u32` `SpatialCodec` over MIR `Value` -/

/-- `u32` scalars as MIR values. -/
def u32ToValue (a : {n : Nat // n < 256 ^ 4}) : Value :=
  .scalar { bits := a.val, sizeBytes := 4 }

/-- MIR values that are in-range `u32` scalars. -/
def u32OfValue? (v : Value) : Option {n : Nat // n < 256 ^ 4} :=
  match v with
  | .scalar sc =>
    if sc.sizeBytes = 4 then
      if h : sc.bits < 256 ^ 4 then some ⟨sc.bits, h⟩ else none
    else none
  | _ => none

theorem u32ToValue_ofValue? (v : Value) (a : {n : Nat // n < 256 ^ 4})
    (h : u32OfValue? v = some a) : u32ToValue a = v := by
  unfold u32OfValue? at h
  split at h
  · rename_i sc
    split at h
    · rename_i hs
      split at h
      · injection h with h
        subst h
        cases sc
        simp only at hs
        subst hs
        rfl
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- The trusted little-endian `u32` byte codec of `SepLogicLenses` as a
`SpatialCodec` over MIR `Value`. -/
def u32ValueSpatialCodec : SpatialCodec Value :=
  spatialCodecOfByteLensCodec 32 Anneal.SepLogicLenses.ByteLensCodec.u32LE
    (fun a => provenanceFree_encodeLittleEndianBytes 4 a.val)
    u32ToValue u32OfValue? u32ToValue_ofValue?

/-- Every in-range `u32` MIR scalar encodes under `u32ValueSpatialCodec` to an
`.uninit`-free 4-cell byte window. -/
theorem u32ValueSpatialCodec_hasUninitCell_false (v : Value)
    (a : {n : Nat // n < 256 ^ 4}) (hv : u32OfValue? v = some a) :
    hasUninitCell (u32ValueSpatialCodec.encode v) = false :=
  spatialCodecOfByteLensCodec_hasUninitCell_false 32
    Anneal.SepLogicLenses.ByteLensCodec.u32LE
    (fun x => provenanceFree_encodeLittleEndianBytes 4 x.val)
    u32ToValue u32OfValue? u32ToValue_ofValue? v a hv
    (allBytesInitialized_encodeLittleEndianBytes 4 a.val)

/-- **Episode 2 readiness canary**: a `u32` MIR scalar encodes to its
little-endian raw byte window, a single-byte mutation of that window decodes to
the updated scalar, an `.uninit` byte or an out-of-range window (`2 ^ 32`) or a
wrong-width window (`0`, `1`, or `5` bytes with trailing `0`) fails to decode,
and a non-`u32` value falls back to a value cell. -/
theorem u32ValueSpatialCodec_canaries :
    u32ValueSpatialCodec.encode (.scalar { bits := 0x01020304, sizeBytes := 4 }) =
      [.rawByte 4, .rawByte 3, .rawByte 2, .rawByte 1] ∧
    u32ValueSpatialCodec.decode [.rawByte 5, .rawByte 3, .rawByte 2, .rawByte 1] =
      some (.scalar { bits := 0x01020305, sizeBytes := 4 }) ∧
    u32ValueSpatialCodec.decode [.rawByte 5, .uninit, .rawByte 2, .rawByte 1] =
      none ∧
    u32ValueSpatialCodec.decode [] = none ∧
    u32ValueSpatialCodec.decode [.rawByte 5] = none ∧
    u32ValueSpatialCodec.decode
      [.rawByte 4, .rawByte 3, .rawByte 2, .rawByte 1, .rawByte 0] = none ∧
    u32ValueSpatialCodec.decode
      [.rawByte 0, .rawByte 0, .rawByte 0, .rawByte 0, .rawByte 1] = none ∧
    u32ValueSpatialCodec.encode (.scalar { bits := 7, sizeBytes := 1 }) =
      [.init (.scalar { bits := 7, sizeBytes := 1 })] ∧
    hasUninitCell
      (u32ValueSpatialCodec.encode (.scalar { bits := 0x01020304, sizeBytes := 4 })) =
      false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 1-byte `ByteLensCodec` for Rust `bool` (`0x00 ↔ false`, `0x01 ↔ true`,
rejecting `0x02..0xFF`, `.uninit`, and wrong-width windows). -/
def boolByteLensCodec : Anneal.SepLogicLenses.ByteLensCodec Bool 1 where
  encode b := [.init (if b then 1 else 0) none]
  decode bs :=
    match bs with
    | [.init b _] =>
      if b == 0 then some false
      else if b == 1 then some true
      else none
    | _ => none
  encode_len _ := rfl
  decode_encode b := by cases b <;> rfl

theorem provenanceFree_boolByteLensCodec (b : Bool) :
    provenanceFree (boolByteLensCodec.encode b) = true := by
  cases b <;> rfl

def boolToValue (b : Bool) : Value :=
  .scalar (boolToScalar b)

def boolOfValue? (v : Value) : Option Bool :=
  match v with
  | .scalar sc =>
    if sc.sizeBytes = 1 then
      if sc.bits = 0 then some false
      else if sc.bits = 1 then some true
      else none
    else none
  | _ => none

theorem boolToValue_ofValue? (v : Value) (b : Bool)
    (h : boolOfValue? v = some b) : boolToValue b = v := by
  unfold boolOfValue? at h
  split at h
  · rename_i sc
    split at h
    · rename_i hs
      split at h
      · rename_i hb0
        injection h with h
        subst h
        cases sc
        simp only at hs hb0
        subst hs
        subst hb0
        rfl
      · split at h
        · rename_i hb1
          injection h with h
          subst h
          cases sc
          simp only at hs hb1
          subst hs
          subst hb1
          rfl
        · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- `SpatialCodec` over MIR `Value` for 1-byte Rust `bool` scalars (`0x00` and
`0x01`), rejecting invalid bit patterns (`0x02`), `.uninit` bytes, and
wrong-width windows. -/
def boolValueSpatialCodec : SpatialCodec Value :=
  spatialCodecOfByteLensCodec 33 boolByteLensCodec
    provenanceFree_boolByteLensCodec
    boolToValue boolOfValue? boolToValue_ofValue?

/-- **Episode 2 `TryFromBytes` / `bool` bit-validity & no-retyping canary**:
valid `bool` scalars (`false`, `true`) encode to `[.rawByte 0]` / `[.rawByte 1]`
and decode back, while `.uninit`, invalid bit-pattern `0x02`, wrong-width
windows, and width-1 value cells `[.init w]` all decode to `none`; and every
1-cell slice that decodes under `boolValueSpatialCodec` produces a valid Rust
`bool` scalar (`spatialCodecOfByteLensCodec_decode_in_subdomain`). -/
theorem boolValueSpatialCodec_canaries :
    boolValueSpatialCodec.encode (.scalar (boolToScalar false)) = [.rawByte 0] ∧
    boolValueSpatialCodec.encode (.scalar (boolToScalar true)) = [.rawByte 1] ∧
    boolValueSpatialCodec.decode [.rawByte 0] =
      some (.scalar (boolToScalar false)) ∧
    boolValueSpatialCodec.decode [.rawByte 1] =
      some (.scalar (boolToScalar true)) ∧
    boolValueSpatialCodec.decode [.rawByte 2] = none ∧
    boolValueSpatialCodec.decode [.uninit] = none ∧
    boolValueSpatialCodec.decode [.rawByte 0, .rawByte 0] = none ∧
    (∀ w : Value, boolValueSpatialCodec.decode [.init w] = none) ∧
    (∀ (cell : CellVal Value) (v' : Value),
      boolValueSpatialCodec.decode [cell] = some v' →
      Exists fun b : Bool => v' = .scalar (boolToScalar b)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   fun _ => rfl,
   fun cell v' hDec => by
     obtain ⟨_, b, _, _, hEq⟩ :=
       spatialCodecOfByteLensCodec_decode_in_subdomain 33 boolByteLensCodec
         provenanceFree_boolByteLensCodec boolToValue boolOfValue?
         boolToValue_ofValue? [cell] v' rfl hDec
     exact ⟨b, hEq⟩⟩


/-! ### Non-vacuity of the remaining composition theorems -/

/-- The countdown VC for the original (fork-free) step function. -/
theorem countdown_localBlockVC_orig :
    LocalBlockVC testCfgStep countdownInv (· = 100) :=
  forkFree_eq_of_noFork testCfgStep testCfgStep_noFork ▸ countdown_localBlockVC

/-- **Non-vacuity of `evalFuel_blockCfgStep_ne_faulted`,
`wpConverges_blockCfgStep_postRet`, `localBlockVC_forkFree`, and
`StepsTo.exists_stepPath`** on the countdown CFG (symbolic start value `n` and
fuel `k`). -/
theorem countdown_transfer_canaries (n k : Nat) :
    PureMirExec.evalFuel (blockCfgStep testCfgStep) k ⟨some, 0, n, 0⟩ ≠
      .faulted ∧
    PureMirExec.WpConverges (blockCfgStep testCfgStep) ⟨some, 0, n, 0⟩
      (fun v => v = 100 ∧ v = 100) ∧
    LocalBlockVC (forkFree testCfgStep) countdownInv (· = 100) ∧
    (Exists fun j =>
      StepPath (blockCfgStep testCfgStep) ⟨some, 0, 0, 0⟩ j ⟨some, 2, 0, 0⟩) := by
  refine ⟨evalFuel_blockCfgStep_ne_faulted testCfgStep countdownInv (· = 100)
      countdown_localBlockVC ⟨some, 0, n, 0⟩ ⟨Or.inl rfl, fun _ hv => hv⟩ k,
    wpConverges_blockCfgStep_postRet testCfgStep countdownInv (· = 100)
      countdown_localBlockVC_orig (Or.inl rfl) (countdown_wpConverges n),
    localBlockVC_forkFree testCfgStep countdownInv (· = 100)
      countdown_localBlockVC_orig (fun bb st _ => testCfgStep_noFork bb st), ?_⟩
  obtain ⟨j, t, hPath, ht⟩ := StepsTo.exists_stepPath
    (stepsTo_of_runBlockCfgToBlock_reached
      (rfl : runBlockCfgToBlock testCfgStep 2 5 ⟨some, 0, 0, 0⟩ =
        .reached ⟨some, 2, 0, 0⟩))
  subst ht
  exact ⟨j, hPath⟩

/-- Simulation relation for the multi-iteration symbolic `S6` loop (`*x = i ≤ n`
with `n - i` iterations): while inside the loop (`bb = 0` or `bb = 1`), the
state satisfies `countUpInv n` (or `i < n` at `bb = 1`) and stutters on `bb0`
of `liveInteropMirBody`; when the loop exits (`bb = 2` at `*x = n`), it steps
`bb0 → bb1` of `liveInteropMirBody`. -/
def countUpLoopRel (n : Nat)
    (s : BlockMachineState (SymState StdVal) (FuncOut StdVal))
    (ms : MachineState) : Prop :=
  s.wrap = some ∧ s.wait = 0 ∧
    ((s.bb = 0 ∧ countUpInv n s.st ∧ ms = liveInteropMs 0) ∨
     (s.bb = 1 ∧ (Exists fun j => j < n ∧ s.st = countUpState n j) ∧
       ms = liveInteropMs 0) ∨
     (s.bb = 2 ∧ s.st = countUpState n n ∧ ms = liveInteropMs 1))

/-- The symbolic `n - i`-iteration `S6` loop CFG simulates into
`liveInteropMirBody` for every bound `n`. -/
theorem countUpLoop_segmentSim (n : Nat) :
    SegmentSim
      (blockCfgStep (stepBasicBlock stdValAlg
        (whileLoopBlocks countUpCond countUpBody (.constVal .unit))))
      (PureMirExec.mirStep liveInteropMirBody) (countUpLoopRel n) := by
  intro s t s' hR hCont
  obtain ⟨hWrap, hWait, hCase⟩ := hR
  cases s with
  | mk w bb st wait =>
    dsimp only at hWrap hWait hCase
    subst hWrap
    subst hWait
    rcases hCase with ⟨hBb, ⟨j, hj, hSt⟩, hT⟩ | ⟨hBb, ⟨j, hlt, hSt⟩, hT⟩ | ⟨hBb, hSt, hT⟩
    · subst hBb
      subst hSt
      subst hT
      cases hb : Nat.blt j n with
      | true =>
        have hlt : j < n := Nat.le_of_ble_eq_true hb
        rw [blockCfgStep_whileHeader_true stdValAlg countUpCond countUpBody
          (.constVal .unit) some (countUpState n j) (.bool (Nat.blt j n))
          (countUp_eval_cond n j) (by rw [hb]; rfl)] at hCont
        injection hCont with hEq
        subst hEq
        exact PureMirExec.StepsTo.refl
          ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, ⟨j, hlt, rfl⟩, rfl⟩)⟩
      | false =>
        have hge : n ≤ j := Nat.ge_of_not_lt (fun hlt =>
          Bool.noConfusion ((Nat.ble_eq_true_of_le hlt).symm.trans hb))
        have hEqJ : j = n := Nat.le_antisymm hj hge
        subst hEqJ
        rw [blockCfgStep_whileHeader_false stdValAlg countUpCond countUpBody
          (.constVal .unit) some (countUpState j j) (.bool (Nat.blt j j))
          (countUp_eval_cond j j) (by rw [hb]; rfl)] at hCont
        injection hCont with hEq
        subst hEq
        exact PureMirExec.StepsTo.step liveInterop_mirStep_bb0
          (PureMirExec.StepsTo.refl ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩)
    · subst hBb
      subst hSt
      subst hT
      rw [blockCfgStep_whileBody stdValAlg countUpCond countUpBody
        (.constVal .unit) some (countUpState n j) (countUpState n (j + 1))
        (countUp_eval_body n j)] at hCont
      injection hCont with hEq
      subst hEq
      exact PureMirExec.StepsTo.refl
        ⟨rfl, rfl, Or.inl ⟨rfl, ⟨j + 1, hlt, rfl⟩, rfl⟩⟩
    · subst hBb
      subst hSt
      subst hT
      rw [blockCfgStep_whileExit stdValAlg countUpCond countUpBody
        (.constVal .unit) some (countUpState n n) .unit
        ⟨.unit, [.nat n]⟩ rfl rfl rfl rfl] at hCont
      exact nomatch hCont

/-- **Non-vacuity of `liftBlockToJoin_of_whileCutpoint` (multi-iteration symbolic
bounds `i ≤ n`)**: for every `i ≤ n`, the `n - i`-iteration `S6` loop verified
by `countUpInv n`, `countUpRank n`, and `countUp_cutpoint_step n` yields the
live MIR join path of `liveInteropMirBody` from `bb0` to `bb1`. -/
theorem countUp_liftBlockToJoin_of_whileCutpoint_canary (n i : Nat) (hi : i ≤ n) :
    MirLiftCore.LiftBlockToJoin liveInteropMirBody 0 liveInteropEnv 1
      (· = liveInteropEnv) :=
  liftBlockToJoin_of_whileCutpoint stdValAlg countUpCond countUpBody
    (.constVal .unit) (countUpInv n) (countUpRank n) (countUp_cutpoint_step n)
    (countUpLoop_segmentSim n) some (countUpState n i) ⟨i, hi, rfl⟩
    ⟨rfl, rfl, Or.inl ⟨rfl, ⟨i, hi, rfl⟩, rfl⟩⟩
    (fun _ ms' _ _ hR' => by
      rcases hR'.2.2 with ⟨hBad, _⟩ | ⟨hBad, _⟩ | ⟨_, _, hMs⟩
      · exact nomatch hBad
      · exact nomatch hBad
      · subst hMs
        exact ⟨rfl, rfl⟩)

/-- **Non-vacuity of `liftBlockToJoin_of_whileForRangeUp` (multi-iteration
symbolic bounds `i ≤ n`)**: for every `i ≤ n`, the `S6` loop driven by
MirLiftCore's `forRangeUp` over `[i, n)` yields the live MIR join path of
`liveInteropMirBody` from `bb0` to `bb1`. -/
theorem countUp_liftBlockToJoin_of_whileForRangeUp_canary (n i : Nat) (hi : i ≤ n) :
    MirLiftCore.LiftBlockToJoin liveInteropMirBody 0 liveInteropEnv 1
      (· = liveInteropEnv) :=
  liftBlockToJoin_of_whileForRangeUp stdValAlg countUpCond countUpBody
    (.constVal .unit) i n i (fun _ _ _ a => a + 1)
    (fun j a s => a = j ∧ s = countUpState n j)
    (fun j _ hlt a s hs => by
      obtain ⟨ha, hsEq⟩ := hs
      subst ha
      subst hsEq
      have hb : Nat.blt a n = true := Nat.ble_eq_true_of_le hlt
      refine ⟨⟨.bool (Nat.blt a n), countUp_eval_cond n a, ?_⟩,
        countUpState n (a + 1), countUp_eval_body n a, rfl, rfl⟩
      rw [hb]
      rfl)
    (fun s hs => by
      obtain ⟨_, hsEq⟩ := hs
      subst hsEq
      exact ⟨.bool (Nat.blt n n), countUp_eval_cond n n,
        by rw [nat_blt_self_eq_false]; rfl⟩)
    (countUpLoop_segmentSim n) some (countUpState n i) hi ⟨rfl, rfl⟩
    ⟨rfl, rfl, Or.inl ⟨rfl, ⟨i, hi, rfl⟩, rfl⟩⟩
    (fun _ ms' _ hR' => by
      rcases hR'.2.2 with ⟨hBad, _⟩ | ⟨hBad, _⟩ | ⟨_, _, hMs⟩
      · exact nomatch hBad
      · exact nomatch hBad
      · subst hMs
        exact ⟨rfl, rfl⟩)

/-- Single-block certificate of a parameterless function returning `100`. -/
def ret100Cert : CfgCertificate stdValAlg :=
  CfgCertificate.singleBlock stdValAlg .skip (.constVal (.nat 100))

/-- Block invariant of `ret100Cert`: the entry block with the empty frame. -/
def ret100Inv (bb : Nat) (st : SymState StdVal) : Prop :=
  bb = 0 ∧ st = ⟨[], [], [], [], [], 0⟩

theorem ret100_localBlockVC :
    LocalBlockVC (stepBasicBlock stdValAlg ret100Cert.blocks) ret100Inv
      (fun _ => True) := by
  intro bb st hInv
  obtain ⟨hBb, hSt⟩ := hInv
  subst hBb
  subst hSt
  exact trivial

theorem ret100_noFork : ∀ bb st, ret100Inv bb st →
    ∀ mergeRet thenBb elseBb st',
      stepBasicBlock stdValAlg ret100Cert.blocks bb st ≠
        .branchJump mergeRet thenBb elseBb st' := by
  intro bb st hInv mergeRet thenBb elseBb st' h
  obtain ⟨hBb, hSt⟩ := hInv
  subst hBb
  subst hSt
  exact nomatch h

/-- The `ret100Cert` CFG machine forward-simulates into `liveInteropMirBody`,
whose `bb0: goto bb1; bb1: return` returns `_0 = 100`. -/
theorem ret100_forwardSim :
    ForwardSim (blockCfgStep (stepBasicBlock stdValAlg ret100Cert.blocks))
      (PureMirExec.mirStep liveInteropMirBody)
      (fun s ms => s = ⟨some, 0, ⟨[], [], [], [], [], 0⟩, 0⟩ ∧ ms = liveInteropMs 0)
      (fun out o => out = ⟨.nat 100, []⟩ ∧ o = liveInteropMirOutcome) := by
  intro s ms hR
  obtain ⟨hS, hMs⟩ := hR
  subst hS
  subst hMs
  exact PureMirExec.WpConverges.of_cont liveInterop_mirStep_bb0
    (PureMirExec.WpConverges.of_done rfl ⟨rfl, rfl⟩)

/-- **Non-vacuity of `mirWpConverges_of_cfgCertificate`**: the single-block
certificate of a function returning `100` refines live `liveInteropMirBody`. -/
theorem ret100_mirWpConverges_of_cfgCertificate_canary :
    Anneal.MirFuelFree.MirWpConverges liveInteropMirBody (liveInteropMs 0)
      (fun o => Exists fun (v : FuncOut StdVal) =>
        v.ret = .nat 100 ∧ (v = ⟨.nat 100, []⟩ ∧ o = liveInteropMirOutcome)) :=
  mirWpConverges_of_cfgCertificate stdValAlg ret100Cert [] ⟨[], [], [], [], [], 0⟩
    (fun out => out.ret = .nat 100) rfl rfl ret100Inv (fun _ => True)
    ret100_localBlockVC ret100_noFork ⟨rfl, rfl⟩ ret100_forwardSim ⟨rfl, rfl⟩

/-- **Non-vacuity of `spatialCodecOfByteLensCodec_encode_length` and
`spatialCodecOfByteLensCodec_decode_wrong_length`** for `u32` MIR scalars. -/
theorem u32ValueSpatialCodec_width_canaries :
    (∀ v a, u32OfValue? v = some a → (u32ValueSpatialCodec.encode v).length = 4) ∧
    (∀ b0 b1 b2 : UInt8,
      u32ValueSpatialCodec.decode [.rawByte b0, .rawByte b1, .rawByte b2] = none) :=
  ⟨fun v a hv =>
    spatialCodecOfByteLensCodec_encode_length 32
      Anneal.SepLogicLenses.ByteLensCodec.u32LE
      (fun x => provenanceFree_encodeLittleEndianBytes 4 x.val)
      u32ToValue u32OfValue? u32ToValue_ofValue? v a hv,
   fun _ _ _ =>
    spatialCodecOfByteLensCodec_decode_wrong_length 32
      Anneal.SepLogicLenses.ByteLensCodec.u32LE
      (fun x => provenanceFree_encodeLittleEndianBytes 4 x.val)
      u32ToValue u32OfValue? u32ToValue_ofValue? _ rfl rfl⟩

/-! ### `.convergedJump`, Partial `Option Ret` Wrappers, and Strong-Descent Cutpoint Canaries -/

/-- Test CFG exercising `.convergedJump armSteps wrapRet` with non-zero
`armSteps = 2` and a partial wrapper (`some (v + 10)` when `wrapOk = true`,
`none` when `wrapOk = false`). -/
def convergedJumpTestCfg (wrapOk : Bool) (bb : Nat) (st : Nat) :
    BlockStepResult Nat Nat :=
  match bb with
  | 0 =>
    .convergedJump 2
      (fun v => if wrapOk then some (v + 10) else none)
      1 (st + 5)
  | 1 => .ret (st * 2)
  | _ => .fault

def convergedJumpTestInv (n : Nat) (bb st : Nat) : Prop :=
  (bb = 0 ∧ st = n) ∨ (bb = 1 ∧ st = n + 5)

def convergedJumpTestRank (bb _st : Nat) : Nat :=
  match bb with
  | 0 => 1
  | _ => 0

theorem convergedJumpTestCfg_noFork (wrapOk : Bool) :
    ∀ bb st mergeRet thenBb elseBb st',
      convergedJumpTestCfg wrapOk bb st ≠
        .branchJump mergeRet thenBb elseBb st' := by
  intro bb st mergeRet thenBb elseBb st' h
  match bb with
  | 0 => exact nomatch h
  | 1 => exact nomatch h
  | _ + 2 => exact nomatch h

theorem convergedJumpTest_localBlockVC (n : Nat) :
    LocalBlockVC (forkFree (convergedJumpTestCfg true))
      (convergedJumpTestInv n) (fun v => (n + 5) * 2 ≤ v) := by
  intro bb st hInv
  rcases hInv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
    intro v hv
    exact Nat.le_trans hv (Nat.le_add_right v 10)
  · exact Nat.le_refl ((n + 5) * 2)

theorem convergedJumpTest_rank_converged (n : Nat) :
    ∀ bb st armSteps wrapRet nextBb st',
      convergedJumpTestInv n bb st →
      convergedJumpTestCfg true bb st =
        .convergedJump armSteps wrapRet nextBb st' →
      convergedJumpTestRank nextBb st' < convergedJumpTestRank bb st := by
  intro bb st armSteps wrapRet nextBb st' hInv hStep
  rcases hInv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · injection hStep with _ _ hNext _
    subst hNext
    exact Nat.zero_lt_one
  · exact nomatch hStep

/-- **Non-vacuity of `wpConverges_blockCfgStep_of_rank` and
`runBlockCfg_total_of_rank` on `.convergedJump`**: from any start state `n`,
`convergedJumpTestCfg true` converges through the `armSteps = 2` delay to
`(n + 5) * 2 + 10`. -/
theorem convergedJumpTest_wpConverges_of_rank (n : Nat) :
    PureMirExec.WpConverges (blockCfgStep (convergedJumpTestCfg true))
      ⟨some, 0, n, 0⟩ (fun v => (n + 5) * 2 ≤ v) ∧
    (Exists fun k => Exists fun v =>
      runBlockCfg (convergedJumpTestCfg true) 0 n k = .ret v ∧
      (n + 5) * 2 ≤ v) :=
  ⟨wpConverges_blockCfgStep_of_rank (convergedJumpTestCfg true)
      (convergedJumpTestInv n) (fun v => (n + 5) * 2 ≤ v)
      (convergedJumpTest_localBlockVC n) convergedJumpTestRank
      (fun _ _ _ _ hInv hStep => by
        rcases hInv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact nomatch hStep)
      (fun _ _ _ _ _ hInv hStep => by
        rcases hInv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact nomatch hStep)
      (convergedJumpTest_rank_converged n)
      ⟨some, 0, n, 0⟩ ⟨Or.inl ⟨rfl, rfl⟩, fun _ hv => hv⟩,
   runBlockCfg_total_of_rank (convergedJumpTestCfg true)
      (convergedJumpTestInv n) (fun v => (n + 5) * 2 ≤ v)
      (convergedJumpTest_localBlockVC n) convergedJumpTestRank
      (fun _ _ _ _ hInv hStep => by
        rcases hInv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact nomatch hStep)
      (fun _ _ _ _ _ hInv hStep => by
        rcases hInv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact nomatch hStep)
      (convergedJumpTest_rank_converged n) 0 n (Or.inl ⟨rfl, rfl⟩)⟩

/-- **Exact `armSteps` fuel accounting and fault propagation for `.convergedJump`**:
1. With `armSteps = 2`, fuels `1`, `2`, and `3` are `.outOfFuel` (`.diverged`),
   and fuel `4` (`1` step for block `0` + `2` arm wait steps + `1` step for
   block `1`) halts with `(n + 5) * 2 + 10` when `wrapOk = true`.
2. `runBlockCfgToBlock` reaches block `1` only after `wait` counts down to `0`
   (requiring bound `≥ 2`, returning `.outOfFuel` at bound `1`).
3. When `wrapOk = false` (`wrapRet` returns `none`), fuels `1..3` are still
   `.outOfFuel` (`.diverged`), fuel `≥ 4` faults (`.faulted` / `.fault`), and
   `WpConverges` is refutable for every postcondition `P`. -/
theorem convergedJump_fuel_and_fault_canaries (n : Nat) :
    PureMirExec.evalFuel (blockCfgStep (convergedJumpTestCfg true)) 3
      ⟨some, 0, n, 0⟩ = .outOfFuel ∧
    PureMirExec.evalFuel (blockCfgStep (convergedJumpTestCfg true)) 4
      ⟨some, 0, n, 0⟩ = .halted ((n + 5) * 2 + 10) ∧
    runBlockCfg (convergedJumpTestCfg true) 0 n 3 = .diverged ∧
    runBlockCfg (convergedJumpTestCfg true) 0 n 4 = .ret ((n + 5) * 2 + 10) ∧
    PureMirExec.WpConverges (blockCfgStep (convergedJumpTestCfg true))
      ⟨some, 0, n, 0⟩ (· = (n + 5) * 2 + 10) ∧
    runBlockCfgToBlock (convergedJumpTestCfg true) 1 1 ⟨some, 0, n, 0⟩ =
      .outOfFuel ∧
    runBlockCfgToBlock (convergedJumpTestCfg true) 1 2 ⟨some, 0, n, 0⟩ =
      .reached ⟨composeWrap some (fun v => some (v + 10)), 1, n + 5, 0⟩ ∧
    PureMirExec.evalFuel (blockCfgStep (convergedJumpTestCfg false)) 3
      ⟨some, 0, n, 0⟩ = .outOfFuel ∧
    PureMirExec.evalFuel (blockCfgStep (convergedJumpTestCfg false)) 4
      ⟨some, 0, n, 0⟩ = .faulted ∧
    runBlockCfg (convergedJumpTestCfg false) 0 n 4 = .fault ∧
    (∀ P, ¬ PureMirExec.WpConverges (blockCfgStep (convergedJumpTestCfg false))
      ⟨some, 0, n, 0⟩ P) := by
  refine ⟨rfl, rfl, rfl, rfl, ⟨4, (n + 5) * 2 + 10, rfl, rfl⟩, rfl, rfl, rfl,
    rfl, rfl, ?_⟩
  intro P ⟨k, v, hk, _⟩
  match k with
  | 0 => exact nomatch hk
  | 1 => exact nomatch hk
  | 2 => exact nomatch hk
  | 3 => exact nomatch hk
  | _ + 4 => exact nomatch hk

/-- **Live `stepBasicBlock` symbolic diamond convergence via `.convergedJump`**:
on `sampleBranchBlockCfg` with a 2-local state where `_0 = .symBool true`,
`stepBasicBlock` reconverges the two arms at block `3` via `.convergedJump 1`
(rather than `.branchJump`), so `blockCfgStep` executes it deterministically
without faulting, exhausts fuel at `k = 2`, and halts with the zipped output at
`k = 3`. -/
theorem sampleBranchBlockCfg_symDiamond_convergedJump_canary :
    let stSym2 : SymState StdVal :=
      ⟨[⟨.symBool true, .unborrowed⟩, ⟨.nat 0, .unborrowed⟩],
       [], [], [], [], 0⟩
    let expectedOut : FuncOut StdVal :=
      ⟨stdValAlg.zipVal (.symBool true) (.nat 10) (.nat 20), []⟩
    PureMirExec.evalFuel
      (blockCfgStep (stepBasicBlock stdValAlg sampleBranchBlockCfg)) 2
      ⟨some, 0, stSym2, 0⟩ = .outOfFuel ∧
    PureMirExec.evalFuel
      (blockCfgStep (stepBasicBlock stdValAlg sampleBranchBlockCfg)) 3
      ⟨some, 0, stSym2, 0⟩ = .halted expectedOut ∧
    runBlockCfg (stepBasicBlock stdValAlg sampleBranchBlockCfg) 0 stSym2 2 =
      .diverged ∧
    runBlockCfg (stepBasicBlock stdValAlg sampleBranchBlockCfg) 0 stSym2 3 =
      .ret expectedOut ∧
    PureMirExec.WpConverges
      (blockCfgStep (stepBasicBlock stdValAlg sampleBranchBlockCfg))
      ⟨some, 0, stSym2, 0⟩ (· = expectedOut) :=
  ⟨rfl, rfl, rfl, rfl, ⟨3, _, rfl, rfl⟩⟩

/-- Test CFG exercising `.jumpWrapped` returning `none` (post-return wrapper
rejection) as well as nested `.jumpWrapped` + `.convergedJump` wrapper
composition. -/
def jumpWrappedPartialCfg (wrapOk : Bool) (bb : Nat) (st : Nat) :
    BlockStepResult Nat Nat :=
  match bb with
  | 0 =>
    .jumpWrapped (fun v => if wrapOk then some (v + 1) else none) 1 (st + 10)
  | 1 => .ret st
  | _ => .fault

def nestedWrappedConvergedCfg (bb : Nat) (st : Nat) :
    BlockStepResult Nat Nat :=
  match bb with
  | 0 => .jumpWrapped (fun v => some (v * 3)) 1 (st + 1)
  | 1 => .convergedJump 1 (fun v => some (v + 2)) 2 (st + 4)
  | 2 => .ret st
  | _ => .fault

/-- **`.jumpWrapped` fault propagation (`none` maps to `.fault`) and nested
`.jumpWrapped` + `.convergedJump` Kleisli composition order**:
1. When `.jumpWrapped`'s wrapper returns `none`, block `1`'s `.ret` steps to
   `PureMirExec.Step.fault` (`evalFuel = .faulted`), and `WpConverges` is
   refuted for every `P`.
2. When block `0` wraps with `(* 3)` via `.jumpWrapped` and block `1` wraps with
   `(+ 2)` via `.convergedJump 1`, the inner wrapper `(+ 2)` applies first to
   block `2`'s return value `n + 5` and the outer wrapper `(* 3)` applies second,
   producing `((n + 5) + 2) * 3` at fuel `4`. -/
theorem jumpWrapped_none_fault_and_nested_composition_canaries (n : Nat) :
    blockCfgStep (jumpWrappedPartialCfg false)
      ⟨composeWrap some (fun _ => none), 1, n + 10, 0⟩ = .fault ∧
    PureMirExec.evalFuel (blockCfgStep (jumpWrappedPartialCfg false)) 1
      ⟨some, 0, n, 0⟩ = .outOfFuel ∧
    PureMirExec.evalFuel (blockCfgStep (jumpWrappedPartialCfg false)) 2
      ⟨some, 0, n, 0⟩ = .faulted ∧
    runBlockCfg (jumpWrappedPartialCfg false) 0 n 2 = .fault ∧
    (∀ P, ¬ PureMirExec.WpConverges
      (blockCfgStep (jumpWrappedPartialCfg false)) ⟨some, 0, n, 0⟩ P) ∧
    PureMirExec.evalFuel (blockCfgStep nestedWrappedConvergedCfg) 3
      ⟨some, 0, n, 0⟩ = .outOfFuel ∧
    PureMirExec.evalFuel (blockCfgStep nestedWrappedConvergedCfg) 4
      ⟨some, 0, n, 0⟩ = .halted ((n + 5 + 2) * 3) ∧
    runBlockCfg nestedWrappedConvergedCfg 0 n 4 = .ret ((n + 5 + 2) * 3) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro P ⟨k, v, hk, _⟩
  match k with
  | 0 => exact nomatch hk
  | 1 => exact nomatch hk
  | _ + 2 => exact nomatch hk

/-- Unary operation incrementing a `StdVal.nat` by stride `3`. -/
def stdAdd3 : StdVal → Option StdVal
  | ⟨_, .nat k⟩ => some (.nat (k + 3))
  | _ => none

/-- Loop body incrementing `*_0` by `3` per iteration (`*x += 3`), so `countUpRank`
(`n - *x`) decreases by `3` (or by `n - *x ≥ 2`) in a single iteration. -/
def stride3Body : FlowPlan StdVal :=
  .act (.assign (.derefSub 0 []) (.unary stdAdd3 (.derefSub 0 [])))

def stride3Blocks : List (BasicBlock StdVal) :=
  whileLoopBlocks countUpCond stride3Body (.constVal .unit)

theorem stride3_eval_body (n i : Nat) :
    evalPlan stdValAlg stride3Body (countUpState n i) =
      .ok (.continuing (countUpState n (i + 3))) := rfl

def stride3Inv (n : Nat) (s : SymState StdVal) : Prop :=
  Exists fun i => s = countUpState n i

/-- **Strong well-founded descent (`rank s' < rank s`) for variable/multi-step
stride**: unlike unit-decrement `rank s = rank s' + 1`, `stride3_cutpoint_step`
uses the natural remaining-distance rank `n - *x` directly even though each
iteration decreases `n - *x` by up to `3` (e.g. `5 → 2 → 0`). -/
theorem stride3_cutpoint_step (n : Nat) : ∀ s, stride3Inv n s →
    Exists fun cv => evalRval stdValAlg countUpCond s = some cv ∧
      (stdValAlg.asBool cv = some false ∨
       (stdValAlg.asBool cv = some true ∧
        Exists fun s' =>
          evalPlan stdValAlg stride3Body s = .ok (.continuing s') ∧
          stride3Inv n s' ∧ countUpRank n s' < countUpRank n s)) := by
  intro s ⟨i, hEq⟩
  subst hEq
  refine ⟨.bool (Nat.blt i n), countUp_eval_cond n i, ?_⟩
  cases hb : Nat.blt i n with
  | true =>
    have hlt : i < n := Nat.le_of_ble_eq_true hb
    refine Or.inr ⟨rfl, countUpState n (i + 3), stride3_eval_body n i,
      ⟨i + 3, rfl⟩, ?_⟩
    show n - (i + 3) < n - i
    omega
  | false =>
    exact Or.inl rfl

theorem stride3_cutpoint_exit (n : Nat) : ∀ s, stride3Inv n s →
    (Exists fun cv => evalRval stdValAlg countUpCond s = some cv ∧
      stdValAlg.asBool cv = some false) →
    stateCleanAtReturn s = true ∧
      Exists fun rv => evalRval stdValAlg (.constVal .unit) s = some rv ∧
        handleFreeOut stdValAlg ⟨rv, collectRootMutVals s.loans⟩ = true ∧
        Exists fun i => n ≤ i ∧
          (⟨rv, collectRootMutVals s.loans⟩ : FuncOut StdVal) =
            ⟨.unit, [.nat i]⟩ := by
  intro s ⟨i, hEq⟩ ⟨cv, hcv, hb⟩
  subst hEq
  rw [countUp_eval_cond] at hcv
  injection hcv with hcv
  subst hcv
  change some (Nat.blt i n) = some false at hb
  injection hb with hb
  have hge : n ≤ i := Nat.ge_of_not_lt (fun hlt =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le hlt).symm.trans hb))
  exact ⟨rfl, .unit, rfl, rfl, i, hge, rfl⟩

/-- **Non-vacuity of `while_cutpoint_wpConverges` under multi-step strong
descent (`rank s' < rank s`)**: for all `n, i : Nat`, the stride-3 loop CFG
converges without fuel to a state with `*x ≥ n`, and for `n = 5, i = 0` the rank
drops `5 → 2 → 0` (by `3` and `2` in successive iterations). -/
theorem stride3_while_cutpoint_wpConverges (n i : Nat) :
    PureMirExec.WpConverges
      (blockCfgStep (stepBasicBlock stdValAlg stride3Blocks))
      ⟨some, 0, countUpState n i, 0⟩
      (fun out => Exists fun j => n ≤ j ∧ out = ⟨.unit, [.nat j]⟩) ∧
    countUpRank 5 (countUpState 5 0) = 5 ∧
    countUpRank 5 (countUpState 5 3) = 2 ∧
    countUpRank 5 (countUpState 5 6) = 0 :=
  ⟨while_cutpoint_wpConverges stdValAlg countUpCond stride3Body (.constVal .unit)
     (stride3Inv n) (countUpRank n) (stride3_cutpoint_step n)
     (fun out => Exists fun j => n ≤ j ∧ out = ⟨.unit, [.nat j]⟩)
     (stride3_cutpoint_exit n) (countUpState n i) ⟨i, rfl⟩,
   rfl, rfl, rfl⟩

def stride3LoopRel (n : Nat)
    (s : BlockMachineState (SymState StdVal) (FuncOut StdVal))
    (ms : MachineState) : Prop :=
  s.wrap = some ∧ s.wait = 0 ∧
    ((s.bb = 0 ∧ stride3Inv n s.st ∧ ms = liveInteropMs 0) ∨
     (s.bb = 1 ∧ (Exists fun j => j < n ∧ s.st = countUpState n j) ∧
       ms = liveInteropMs 0) ∨
     (s.bb = 2 ∧ (Exists fun j => n ≤ j ∧ s.st = countUpState n j) ∧
       ms = liveInteropMs 1))

theorem stride3Loop_segmentSim (n : Nat) :
    SegmentSim
      (blockCfgStep (stepBasicBlock stdValAlg stride3Blocks))
      (PureMirExec.mirStep liveInteropMirBody) (stride3LoopRel n) := by
  intro s t s' hR hCont
  obtain ⟨hWrap, hWait, hCase⟩ := hR
  cases s with
  | mk w bb st wait =>
    dsimp only at hWrap hWait hCase
    subst hWrap
    subst hWait
    dsimp only [stride3Blocks] at hCont
    rcases hCase with ⟨hBb, ⟨j, hSt⟩, hT⟩ | ⟨hBb, ⟨j, hlt, hSt⟩, hT⟩ | ⟨hBb, ⟨j, _, hSt⟩, hT⟩
    · subst hBb
      subst hSt
      subst hT
      cases hb : Nat.blt j n with
      | true =>
        have hlt : j < n := Nat.le_of_ble_eq_true hb
        rw [blockCfgStep_whileHeader_true stdValAlg countUpCond stride3Body
          (.constVal .unit) some (countUpState n j) (.bool (Nat.blt j n))
          (countUp_eval_cond n j) (by rw [hb]; rfl)] at hCont
        injection hCont with hEq
        subst hEq
        exact PureMirExec.StepsTo.refl
          ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, ⟨j, hlt, rfl⟩, rfl⟩)⟩
      | false =>
        have hge : n ≤ j := Nat.ge_of_not_lt (fun hlt =>
          Bool.noConfusion ((Nat.ble_eq_true_of_le hlt).symm.trans hb))
        rw [blockCfgStep_whileHeader_false stdValAlg countUpCond stride3Body
          (.constVal .unit) some (countUpState n j) (.bool (Nat.blt j n))
          (countUp_eval_cond n j) (by rw [hb]; rfl)] at hCont
        injection hCont with hEq
        subst hEq
        exact PureMirExec.StepsTo.step liveInterop_mirStep_bb0
          (PureMirExec.StepsTo.refl
            ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, ⟨j, hge, rfl⟩, rfl⟩)⟩)
    · subst hBb
      subst hSt
      subst hT
      rw [blockCfgStep_whileBody stdValAlg countUpCond stride3Body
        (.constVal .unit) some (countUpState n j) (countUpState n (j + 3))
        (stride3_eval_body n j)] at hCont
      injection hCont with hEq
      subst hEq
      exact PureMirExec.StepsTo.refl
        ⟨rfl, rfl, Or.inl ⟨rfl, ⟨j + 3, rfl⟩, rfl⟩⟩
    · subst hBb
      subst hSt
      subst hT
      rw [blockCfgStep_whileExit stdValAlg countUpCond stride3Body
        (.constVal .unit) some (countUpState n j) .unit
        ⟨.unit, [.nat j]⟩ rfl rfl rfl rfl] at hCont
      exact nomatch hCont

/-- **Non-vacuity of `liftBlockToJoin_of_whileCutpoint` under multi-step strong
descent (`rank s' < rank s`)**: for all `n, i : Nat`, the stride-3 loop lifts to
`MirLiftCore.LiftBlockToJoin liveInteropMirBody 0 liveInteropEnv 1`. -/
theorem stride3_liftBlockToJoin_of_whileCutpoint_canary (n i : Nat) :
    MirLiftCore.LiftBlockToJoin liveInteropMirBody 0 liveInteropEnv 1
      (· = liveInteropEnv) :=
  liftBlockToJoin_of_whileCutpoint stdValAlg countUpCond stride3Body
    (.constVal .unit) (stride3Inv n) (countUpRank n) (stride3_cutpoint_step n)
    (stride3Loop_segmentSim n) some (countUpState n i) ⟨i, rfl⟩
    ⟨rfl, rfl, Or.inl ⟨rfl, ⟨i, rfl⟩, rfl⟩⟩
    (fun _ ms' _ _ hR' => by
      rcases hR'.2.2 with ⟨hBad, _⟩ | ⟨hBad, _⟩ | ⟨_, _, hMs⟩
      · exact nomatch hBad
      · exact nomatch hBad
      · subst hMs
        exact ⟨rfl, rfl⟩)

/-- **The stride-3 loop really needs strong descent**: from `*x = 0` with
`n = 5`, one header-to-header iteration of the embedded loop CFG moves `*x`
from `0` to `3`, so `countUpRank 5` drops from `5` to `2` in a single
iteration, refuting the old unit-decrement hypothesis
`rank s = rank s' + 1` on an actual loop transition; the run then exits after a
second iteration (`*x = 6`) and halts with `⟨(), [6]⟩` at fuel `6` (`5` is
`.outOfFuel`). -/
theorem stride3_concrete_strong_descent_canary :
    runBlockCfgToBlock (stepBasicBlock stdValAlg stride3Blocks) 0 1
      ⟨some, 0, countUpState 5 0, 0⟩ = .reached ⟨some, 0, countUpState 5 3, 0⟩ ∧
    countUpRank 5 (countUpState 5 3) < countUpRank 5 (countUpState 5 0) ∧
    countUpRank 5 (countUpState 5 0) ≠ countUpRank 5 (countUpState 5 3) + 1 ∧
    PureMirExec.evalFuel (blockCfgStep (stepBasicBlock stdValAlg stride3Blocks)) 5
      ⟨some, 0, countUpState 5 0, 0⟩ = .outOfFuel ∧
    PureMirExec.evalFuel (blockCfgStep (stepBasicBlock stdValAlg stride3Blocks)) 6
      ⟨some, 0, countUpState 5 0, 0⟩ = .halted ⟨.unit, [.nat 6]⟩ :=
  ⟨rfl, by decide, by decide, rfl, rfl⟩

/-! ### Genuinely partial wrappers and merges, fault adequacy, and wrapper frames -/

/-- `.convergedJump` (`armSteps = 1`) whose wrapper is genuinely partial: it
accepts exactly the values `≥ 10` (adding `1`) and rejects the others. -/
def partialWrapCfg (bb st : Nat) : BlockStepResult Nat Nat :=
  match bb with
  | 0 => .convergedJump 1 (fun v => if 10 ≤ v then some (v + 1) else none) 1 st
  | 1 => .ret st
  | _ => .fault

def partialWrapInv (bb st : Nat) : Prop :=
  (bb = 0 ∨ bb = 1) ∧ 10 ≤ st

def partialWrapRank (bb _st : Nat) : Nat :=
  match bb with
  | 0 => 1
  | _ => 0

/-- The acceptance clause of `LocalBlockVC` for `.convergedJump` is discharged
from `PostRet` (`10 ≤ v`), not from a total wrapper. -/
theorem partialWrap_localBlockVC :
    LocalBlockVC (forkFree partialWrapCfg) partialWrapInv (10 ≤ ·) := by
  intro bb st hInv
  obtain ⟨hBb, hSt⟩ := hInv
  rcases hBb with rfl | rfl
  · refine ⟨⟨Or.inr rfl, hSt⟩, ?_⟩
    intro v hv
    dsimp only
    rw [ite_eq_left hv]
    exact Nat.le_succ_of_le hv
  · exact hSt

/-- **Non-vacuity of partial `.convergedJump` wrappers**: the wrapper of
`partialWrapCfg` rejects `9` and accepts `10`; from every invariant start state
`n + 10` the embedded CFG converges (via `wpConverges_blockCfgStep_of_rank`,
using `LocalBlockVC` to show the wrapper accepts) and halts with `n + 11` at
fuel `3` (block `0`, one arm-delay step, block `1`; fuel `2` is `.outOfFuel`);
from the non-invariant start state `3` the wrapper rejects, `runBlockCfg`
faults, the machine faults at the same fuel, and no postcondition is reachable
(`not_wpConverges_blockCfgStep_of_runBlockCfg_fault`). -/
theorem partialWrap_canaries (n : Nat) :
    (fun v => if 10 ≤ v then some (v + 1) else none) 9 = none ∧
    (fun v => if 10 ≤ v then some (v + 1) else none) 10 = some 11 ∧
    PureMirExec.WpConverges (blockCfgStep partialWrapCfg) ⟨some, 0, n + 10, 0⟩
      (10 ≤ ·) ∧
    PureMirExec.evalFuel (blockCfgStep partialWrapCfg) 2 ⟨some, 0, n + 10, 0⟩ =
      .outOfFuel ∧
    PureMirExec.evalFuel (blockCfgStep partialWrapCfg) 3 ⟨some, 0, n + 10, 0⟩ =
      .halted (n + 11) ∧
    runBlockCfg partialWrapCfg 0 3 3 = .fault ∧
    PureMirExec.evalFuel (blockCfgStep partialWrapCfg) 3 ⟨some, 0, 3, 0⟩ =
      .faulted ∧
    (∀ P, ¬ PureMirExec.WpConverges (blockCfgStep partialWrapCfg)
      ⟨some, 0, 3, 0⟩ P) :=
  ⟨rfl, rfl,
   wpConverges_blockCfgStep_of_rank partialWrapCfg partialWrapInv (10 ≤ ·)
     partialWrap_localBlockVC partialWrapRank
     (fun _ _ _ _ hInv hStep => by
       obtain ⟨hBb, _⟩ := hInv
       rcases hBb with rfl | rfl <;> exact nomatch hStep)
     (fun _ _ _ _ _ hInv hStep => by
       obtain ⟨hBb, _⟩ := hInv
       rcases hBb with rfl | rfl <;> exact nomatch hStep)
     (fun _ _ _ _ _ _ hInv hStep => by
       obtain ⟨hBb, _⟩ := hInv
       rcases hBb with rfl | rfl
       · injection hStep with _ _ hNext _
         subst hNext
         exact Nat.zero_lt_one
       · exact nomatch hStep)
     ⟨some, 0, n + 10, 0⟩ ⟨⟨Or.inl rfl, Nat.le_add_left 10 n⟩, fun _ hv => hv⟩,
   rfl, rfl, rfl,
   evalFuel_blockCfgStep_of_runBlockCfg_fault partialWrapCfg 3 some 0 3 rfl,
   fun P => not_wpConverges_blockCfgStep_of_runBlockCfg_fault partialWrapCfg
     (k := 3) rfl P⟩

/-- Order-sensitive nested partial wrappers: block `0` installs the outer
wrapper "even values only" via `.jumpWrapped`, block `1` installs the inner
wrapper `(+ 1)` via `.convergedJump 2`, and block `2` returns its state. -/
def parityNestedCfg (bb st : Nat) : BlockStepResult Nat Nat :=
  match bb with
  | 0 => .jumpWrapped (fun v => if v % 2 == 0 then some v else none) 1 st
  | 1 => .convergedJump 2 (fun v => some (v + 1)) 2 st
  | 2 => .ret st
  | _ => .fault

/-- **Kleisli composition order with partial wrappers**: the inner wrapper runs
first, so from `1` the run halts with `2` (`(1 + 1)` is even) at fuel `5` and
is `.outOfFuel` at fuel `4`, and from `2` it faults (`(2 + 1)` is odd), exactly
as `runBlockCfg` computes; the reversed (outer-first) composition would instead
reject `1` and map `2` to `3`. -/
theorem parityNested_order_canaries :
    PureMirExec.evalFuel (blockCfgStep parityNestedCfg) 4 ⟨some, 0, 1, 0⟩ =
      .outOfFuel ∧
    PureMirExec.evalFuel (blockCfgStep parityNestedCfg) 5 ⟨some, 0, 1, 0⟩ =
      .halted 2 ∧
    runBlockCfg parityNestedCfg 0 1 5 = .ret 2 ∧
    PureMirExec.evalFuel (blockCfgStep parityNestedCfg) 5 ⟨some, 0, 2, 0⟩ =
      .faulted ∧
    runBlockCfg parityNestedCfg 0 2 5 = .fault ∧
    composeWrap (fun v => some (v + 1))
      (fun v => if v % 2 == 0 then some v else none) 1 = none ∧
    composeWrap (fun v => some (v + 1))
      (fun v => if v % 2 == 0 then some v else none) 2 = some 3 ∧
    (∀ P, ¬ PureMirExec.WpConverges (blockCfgStep parityNestedCfg)
      ⟨some, 0, 2, 0⟩ P) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   fun P => not_wpConverges_blockCfgStep_of_runBlockCfg_fault parityNestedCfg
     (k := 5) rfl P⟩

/-- `.branchJump` with a partial merge function (`accept = false` rejects every
pair of arm values), and (blocks `3`-`5`) a fork whose then-arm diverges while
its else-arm faults. -/
def mergeCfg (accept : Bool) (bb st : Nat) : BlockStepResult Nat Nat :=
  match bb with
  | 0 => .branchJump (fun vt vf => if accept then some (vt + vf) else none) 1 2 st
  | 1 => .ret (st + 1)
  | 2 => .ret (st + 2)
  | 3 => .branchJump (fun vt vf => some (vt + vf)) 4 5 st
  | 4 => .jump 4 st
  | _ => .fault

/-- Block `4` of `mergeCfg` jumps to itself, so it diverges at every fuel. -/
theorem mergeCfg_selfLoop_diverges (n : Nat) :
    ∀ k, runBlockCfg (mergeCfg true) 4 n k = .diverged
  | 0 => rfl
  | k + 1 => by
    rw [runBlockCfg_succ]
    exact mergeCfg_selfLoop_diverges n k

/-- The fork at block `3` of `mergeCfg` (diverging then-arm, faulting else-arm)
faults at every fuel `≥ 2`. -/
theorem mergeCfg_divergeFault (n k : Nat) :
    runBlockCfg (mergeCfg true) 3 n (k + 2) = .fault := by
  have hs3 : mergeCfg true 3 n =
      .branchJump (fun vt vf => some (vt + vf)) 4 5 n := rfl
  rw [runBlockCfg_succ, hs3]
  dsimp only
  rw [mergeCfg_selfLoop_diverges n (k + 1)]
  rfl

/-- **Partial `.branchJump` merges and fault adequacy**:
1. When the merge rejects (`accept = false`), `runBlockCfg` faults even though
   both arms return, the embedded machine faults at the same fuel, and no
   postcondition is reachable.
2. When the merge accepts, `runBlockCfg` returns the merged value but the
   embedding faults on the fork: the fault disjunct of
   `evalFuel_blockCfgStep_eq_or_faulted` is genuinely needed.
3. A fork whose then-arm diverges and whose else-arm faults faults at every
   fuel `≥ 2` (`runBlockCfg` lets a fault dominate a divergence), and the
   embedding faults with it. -/
theorem mergeCfg_fault_adequacy_canaries (n : Nat) :
    runBlockCfg (mergeCfg false) 0 n 2 = .fault ∧
    PureMirExec.evalFuel (blockCfgStep (mergeCfg false)) 2 ⟨some, 0, n, 0⟩ =
      .faulted ∧
    (∀ P, ¬ PureMirExec.WpConverges (blockCfgStep (mergeCfg false))
      ⟨some, 0, n, 0⟩ P) ∧
    runBlockCfg (mergeCfg true) 0 n 2 = .ret (n + 1 + (n + 2)) ∧
    PureMirExec.evalFuel (blockCfgStep (mergeCfg true)) 2 ⟨some, 0, n, 0⟩ =
      .faulted ∧
    (∀ k, runBlockCfg (mergeCfg true) 3 n (k + 2) = .fault) ∧
    (∀ P, ¬ PureMirExec.WpConverges (blockCfgStep (mergeCfg true))
      ⟨some, 3, n, 0⟩ P) :=
  ⟨rfl,
   evalFuel_blockCfgStep_of_runBlockCfg_fault (mergeCfg false) 2 some 0 n rfl,
   fun P => not_wpConverges_blockCfgStep_of_runBlockCfg_fault (mergeCfg false)
     (k := 2) rfl P,
   rfl, rfl,
   fun k => mergeCfg_divergeFault n k,
   fun P => not_wpConverges_blockCfgStep_of_runBlockCfg_fault (mergeCfg true)
     (k := 2) rfl P⟩

/-- **Completeness on a `.convergedJump` CFG**
(`wpConverges_blockCfgStep_iff_of_noFork`): the fork-free
`convergedJumpTestCfg true` converges to its exact `runBlockCfg` return, read
off a concrete run at fuel `4`; `convergedJumpTestCfg false` returns at no
fuel at all (fuels `≤ 3` diverge and fuels `≥ 4` fault). -/
theorem convergedJump_completeness_canary (n : Nat) :
    PureMirExec.WpConverges (blockCfgStep (convergedJumpTestCfg true))
      ⟨some, 0, n, 0⟩ (· = (n + 5) * 2 + 10) ∧
    ¬ (Exists fun k => Exists fun v =>
      runBlockCfg (convergedJumpTestCfg false) 0 n k = .ret v) := by
  refine ⟨(wpConverges_blockCfgStep_iff_of_noFork (convergedJumpTestCfg true)
    (convergedJumpTestCfg_noFork true) 0 n _).mpr ⟨4, _, rfl, rfl⟩, ?_⟩
  intro ⟨k, v, hRun⟩
  match k with
  | 0 => exact nomatch hRun
  | 1 => exact nomatch hRun
  | 2 => exact nomatch hRun
  | 3 => exact nomatch hRun
  | _ + 4 => exact nomatch hRun

/-- **Live `stepBasicBlock` `.convergedJump` transition**: on the symbolic
diamond of `sampleBranchBlockCfg`, the embedded machine's first step jumps to
join block `3` with the `armSteps = 1` delay pending and the pending wrapper
extended by the sub-identity guard `handleFreeOutOpt stdValAlg`. -/
theorem sampleBranchBlockCfg_convergedJump_transition_canary :
    let stSym2 : SymState StdVal :=
      ⟨[⟨.symBool true, .unborrowed⟩, ⟨.nat 0, .unborrowed⟩],
       [], [], [], [], 0⟩
    (Exists fun stJoined =>
      blockCfgStep (stepBasicBlock stdValAlg sampleBranchBlockCfg)
          ⟨some, 0, stSym2, 0⟩ =
        .cont ⟨composeWrap some (handleFreeOutOpt stdValAlg), 3, stJoined, 1⟩) ∧
    SubIdWrap (composeWrap some (handleFreeOutOpt stdValAlg)) :=
  ⟨⟨_, rfl⟩,
   subIdWrap_composeWrap subIdWrap_some (subIdWrap_handleFreeOutOpt stdValAlg)⟩

/-- **Non-vacuity of the wrapper frame rule** (`wpConverges_blockCfgStep_wrap_iff`)
on the countdown CFG: under the pending wrapper `(+ 1)` it converges to `101`,
and under the everywhere-rejecting wrapper it converges to nothing. -/
theorem countdown_wrapper_frame_canaries (n : Nat) :
    PureMirExec.WpConverges (blockCfgStep testCfgStep)
      ⟨fun v => some (v + 1), 0, n, 0⟩ (· = 101) ∧
    (∀ P, ¬ PureMirExec.WpConverges (blockCfgStep testCfgStep)
      ⟨fun _ => none, 0, n, 0⟩ P) := by
  refine ⟨(wpConverges_blockCfgStep_wrap_iff testCfgStep _ 0 n 0 _).mpr ?_, ?_⟩
  · exact PureMirExec.WpConverges.mono
      (fun v (hv : v = 100) => ⟨v + 1, rfl, by subst hv; rfl⟩)
      (countdown_wpConverges n)
  · intro P h
    obtain ⟨_, _, _, _, hNone, _⟩ :=
      (wpConverges_blockCfgStep_wrap_iff testCfgStep _ 0 n 0 P).mp h
    exact nomatch hNone

end Canaries

end Anneal.PureLift.MirLiftCoreInterop
